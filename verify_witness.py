#!/usr/bin/env python3
"""verify_witness — independent verifier for the Lodestone witness chain.

One command, zero dependencies beyond Python 3:

    python3 verify_witness.py [witness.jsonl] [witness_pub.json]

Defaults: ./witness.jsonl and ./witness_pub.json (run it inside the feed repo).

The witness is a SECOND, independent observer with its own Ed25519 key —
distinct from the feed key that signs attestations.jsonl. On a schedule it
re-derives the operating contract's two stored surfaces from raw bytes (never
trusting any stored verdict) and appends one signed, hash-chained observation.
Publishing that chain here means a forgery of the contract surfaces must also
rewrite THIS public history consistently — which your clone will refuse to
extend.

What this verifies, per line:
  1. CHAIN  — "prev" equals sha256(previous line's exact bytes); line 1 must
              carry the literal "genesis". Any retroactive edit breaks every
              later link.
  2. SIG    — the Ed25519 signature (hex) verifies over the canonical form
              (the JSON object minus "signature", keys sorted, separators
              (",",":"), UTF-8) against the published witness public key.
  3. SHAPE  — every field matches the fixed allowlist (hashes, generations,
              booleans, a closed verdict set — no free text ever).

Exit 0 = full chain PASS. Exit 1 = the first broken line, named. This file
embeds a pure-Python Ed25519 verifier (RFC 8032) so you don't have to trust
our tooling — read it, or swap in your own.
"""
import sys
import json
import hashlib
import re

# ---- pure-Python Ed25519 verify (RFC 8032; verify-only, no signing here) ------------
_q = 2 ** 255 - 19
_l = 2 ** 252 + 27742317777372353535851937790883648493


def _inv(x):
    return pow(x, _q - 2, _q)


_d = -121665 * _inv(121666) % _q
_I = pow(2, (_q - 1) // 4, _q)


def _xrecover(y):
    xx = (y * y - 1) * _inv(_d * y * y + 1)
    x = pow(xx, (_q + 3) // 8, _q)
    if (x * x - xx) % _q != 0:
        x = (x * _I) % _q
    if (x * x - xx) % _q != 0:
        raise ValueError("no square root — bad point")
    if x % 2 != 0:
        x = _q - x
    return x


_By = 4 * _inv(5) % _q
_Bx = _xrecover(_By)
_B = (_Bx, _By)


def _edwards_add(P, Q):
    x1, y1 = P
    x2, y2 = Q
    x3 = (x1 * y2 + x2 * y1) * _inv(1 + _d * x1 * x2 * y1 * y2)
    y3 = (y1 * y2 + x1 * x2) * _inv(1 - _d * x1 * x2 * y1 * y2)
    return (x3 % _q, y3 % _q)


def _scalarmult(P, e):
    Q = (0, 1)
    while e:
        if e & 1:
            Q = _edwards_add(Q, P)
        P = _edwards_add(P, P)
        e >>= 1
    return Q


def _encodepoint(P):
    x, y = P
    n = y | ((x & 1) << 255)
    return n.to_bytes(32, "little")


def _isoncurve(P):
    x, y = P
    return (-x * x + y * y - 1 - _d * x * x * y * y) % _q == 0


def _decodepoint(s):
    n = int.from_bytes(s, "little")
    y = n & ((1 << 255) - 1)
    x = _xrecover(y)
    if x & 1 != (n >> 255) & 1:
        x = _q - x
    P = (x, y)
    if not _isoncurve(P):
        raise ValueError("point not on curve")
    return P


def ed25519_verify(pub32, msg, sig64):
    """True iff sig64 is a valid Ed25519 signature of msg under pub32."""
    if len(pub32) != 32 or len(sig64) != 64:
        return False
    try:
        R = _decodepoint(sig64[:32])
        A = _decodepoint(pub32)
    except ValueError:
        return False
    S = int.from_bytes(sig64[32:], "little")
    if S >= _l:
        return False
    h = int.from_bytes(hashlib.sha512(sig64[:32] + pub32 + msg).digest(), "little") % _l
    left = _scalarmult(_B, S)
    right = _edwards_add(R, _scalarmult(A, h))
    return _encodepoint(left) == _encodepoint(right)


# ---- witness rules (must mirror the observer's published spec) -----------------------
GENESIS_PREV = "genesis"
_HEX64 = re.compile(r"^[0-9a-f]{64}$")
STR_SHAPES = {
    "ts": re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\+00:00$"),
    "observer": re.compile(r"^witness$"),
    "verdict": re.compile(r"^(MATCH|GENERATION-SKEW|DIVERGED|PARTIAL|UNOBSERVABLE)$"),
    "pub": _HEX64,
    "signature": re.compile(r"^[0-9a-f]{128}$"),
    "prev": re.compile(r"^(genesis|[0-9a-f]{64})$"),
}
# hash/claim fields: 64-hex, empty string (an absent stored claim), or null (unobservable)
NULLABLE_HASH = {"git_hash", "slate_hash"}
CLAIM_FIELDS = {"git_meta_claims", "slate_claims"}
NULLABLE_INT = {"git_generation", "slate_generation"}
BOOL_FIELDS = {"git_meta_honest", "slate_honest", "slate_unreachable"}
REQUIRED = {"ts", "observer", "verdict", "prev", "pub", "signature"}
KNOWN = (set(STR_SHAPES) | NULLABLE_HASH | CLAIM_FIELDS | NULLABLE_INT | BOOL_FIELDS)


def canonical(obj):
    body = {k: v for k, v in obj.items() if k != "signature"}
    return json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")


def check_line(raw, obj, prev_hash, pub):
    unknown = set(obj) - KNOWN
    if unknown:
        return "unknown field(s) %s — the allowlist is closed" % sorted(unknown)
    missing = REQUIRED - set(obj)
    if missing:
        return "missing required field(s) %s" % sorted(missing)
    for k, rx in STR_SHAPES.items():
        if not isinstance(obj[k], str) or not rx.match(obj[k]):
            return "field %r fails its shape" % k
    for k in NULLABLE_HASH | CLAIM_FIELDS:
        if k in obj:
            v = obj[k]
            if v is not None and not (isinstance(v, str) and (v == "" or _HEX64.match(v))):
                return "field %r must be 64-hex, empty, or null" % k
    for k in NULLABLE_INT:
        if k in obj:
            v = obj[k]
            if v is not None and (not isinstance(v, int) or isinstance(v, bool)
                                  or not (0 <= v <= 1_000_000_000)):
                return "field %r must be an int in [0, 1e9] or null" % k
    for k in BOOL_FIELDS:
        if k in obj and not isinstance(obj[k], bool):
            return "field %r must be a boolean" % k
    if obj["prev"] != prev_hash:
        return "CHAIN BROKEN: prev=%s, expected %s" % (str(obj["prev"])[:16],
                                                       str(prev_hash)[:16])
    try:
        sig = bytes.fromhex(obj["signature"])
    except ValueError:
        return "signature is not valid hex"
    if not ed25519_verify(pub, canonical(obj), sig):
        return "SIGNATURE INVALID"
    return None


def main(argv):
    feed = argv[1] if len(argv) > 1 else "witness.jsonl"
    pubf = argv[2] if len(argv) > 2 else "witness_pub.json"
    try:
        pub = bytes.fromhex(json.load(open(pubf))["witness_pub_ed25519"])
    except Exception as e:
        print("FAIL: cannot read witness public key %s (%s)" % (pubf, e))
        return 1
    try:
        raw_lines = [ln.rstrip(b"\n") for ln in open(feed, "rb") if ln.strip()]
    except Exception as e:
        print("FAIL: cannot read witness chain %s (%s)" % (feed, e))
        return 1
    if not raw_lines:
        print("FAIL: witness chain is empty — nothing to verify is not a pass")
        return 1
    prev = GENESIS_PREV
    for i, raw in enumerate(raw_lines, 1):
        try:
            obj = json.loads(raw)
        except ValueError:
            print("FAIL line %d: not valid JSON" % i)
            return 1
        err = check_line(raw, obj, prev, pub)
        if err:
            print("FAIL line %d: %s" % (i, err))
            return 1
        prev = hashlib.sha256(raw).hexdigest()
    first = json.loads(raw_lines[0])["ts"]
    last = json.loads(raw_lines[-1])["ts"]
    verdicts = {}
    for raw in raw_lines:
        v = json.loads(raw)["verdict"]
        verdicts[v] = verdicts.get(v, 0) + 1
    tally = ", ".join("%s x%d" % (k, verdicts[k]) for k in sorted(verdicts))
    print("PASS: %d observation(s), chain + signatures + shapes all valid (%s .. %s; %s)"
          % (len(raw_lines), first, last, tally))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
