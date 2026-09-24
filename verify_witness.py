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
              booleans, a closed verdict set — no free text ever), in ASCII digits.
  4. FORM   — the line's bytes are exactly the writer's serialisation of the
              object (sorted keys, separators (",",":"), ASCII escapes) and carry
              no duplicate key, so the newest line — which no later "prev" pins —
              has one spelling only.

The Ed25519 check refuses a key with any torsion component ([l]A must be the
identity), not only a small-order one.

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
    # CANONICAL decoding only (RFC 8032 section 5.1.3 steps 1 and 4). A y at or above q is a
    # second spelling of the point y - q, and x = 0 with the sign bit set is a second spelling
    # of x = 0; accepting either lets one point carry two encodings (malleability).
    n = int.from_bytes(s, "little")
    y = n & ((1 << 255) - 1)
    if y >= _q:
        raise ValueError("non-canonical point encoding: y >= q")
    x = _xrecover(y)
    if x == 0 and (n >> 255) & 1:
        raise ValueError("non-canonical point encoding: x = 0 with the sign bit set")
    if x & 1 != (n >> 255) & 1:
        x = _q - x
    P = (x, y)
    if not _isoncurve(P):
        raise ValueError("point not on curve")
    return P


def _is_small_order(P):
    """True iff [8]P is the identity — P lies in the cofactor-8 torsion subgroup."""
    x, y = _scalarmult(P, 8)
    return x % _q == 0 and y % _q == 1


_TORSION_FREE = {}


def _is_torsion_free(pub32, A):
    """True iff [l]A is the identity — A lies in the prime-order subgroup. Cached per encoded
    key: a chain carries one key on every line and [l]A is a full 253-bit multiplication."""
    got = _TORSION_FREE.get(pub32)
    if got is None:
        x, y = _scalarmult(A, _l)
        got = _TORSION_FREE[pub32] = (x % _q == 0 and y % _q == 1)
    return got


def ed25519_verify(pub32, msg, sig64):
    """True iff sig64 is a valid Ed25519 signature of msg under pub32."""
    if len(pub32) != 32 or len(sig64) != 64:
        return False
    try:
        R = _decodepoint(sig64[:32])
        A = _decodepoint(pub32)
    except ValueError:
        return False
    # A small-order key verifies S = 0 for EVERY message ([h]A is torsion, so R = -[h]A works),
    # and a small-order R lets whoever knows the key's scalar sign without a nonce. Neither is
    # ever produced by an honest signer, so both are refused.
    if _is_small_order(A) or _is_small_order(R):
        return False
    # A key with a torsion COMPONENT is also refused. A' = [a]B + T (T of order n in {2, 4, 8})
    # is not small order, yet the scalar a signs under it honestly whenever n divides h: then
    # R + [h]A' = [r]B + [h*a]B + [h]T = [S]B. So a mixed-order key CAN sign honestly — for
    # about 1/n of messages (the order-2 case verified 10 of 20) — which makes it a key whose
    # verdict depends on the message hash, and no honest keygen ever emits one. [l]A must be
    # the identity. With A torsion-free the cofactorless equation forces R into the prime-order
    # subgroup too, so R needs no second check.
    if not _is_torsion_free(pub32, A):
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
# re.ASCII on EVERY shape: in a str pattern `\d` matches any Unicode decimal digit, so without it
# a ts spelled in Arabic-Indic digits ("٢٠٢٦-...") passed the wall.
_A = re.ASCII
_HEX64 = re.compile(r"^[0-9a-f]{64}$", _A)
STR_SHAPES = {
    "ts": re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\+00:00$", _A),
    "observer": re.compile(r"^witness$", _A),
    "verdict": re.compile(r"^(MATCH|GENERATION-SKEW|DIVERGED|PARTIAL|UNOBSERVABLE)$", _A),
    "pub": _HEX64,
    "signature": re.compile(r"^[0-9a-f]{128}$", _A),
    "prev": re.compile(r"^(genesis|[0-9a-f]{64})$", _A),
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


# ---- the LINE's bytes, not only its parsed object ------------------------------------------
# The signature covers the PARSED object and the chain covers the previous line's BYTES, so the
# NEWEST line — which no successor's prev pins yet — could be re-spelled and still pass: a
# duplicate key (json keeps the last; a first-wins reader sees the other), whitespace,
# \u-escapes, key order. So every line must be byte-for-byte the WRITER's serialisation of the
# object it carries: witness.py / drill_witness.py write json.dumps(obs, sort_keys=True,
# separators=(",", ":")) with the default ensure_ascii, which is exactly serialise() below.

def _refuse_duplicate_keys(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise ValueError("duplicate key %r" % k)
        out[k] = v
    return out


def serialise(obj):
    """The writer's exact line bytes for an observation object (newline excluded)."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")


def line_form_error(raw, obj):
    """None iff `raw` is the writer's serialisation of `obj`, with no duplicate key; else why."""
    if isinstance(raw, str):
        raw = raw.encode("utf-8")
    try:
        parsed = json.loads(raw, object_pairs_hook=_refuse_duplicate_keys)
    except ValueError as e:
        if "duplicate key" in str(e):
            return ("%s — one line, two values: a reader that keeps the first sees a different "
                    "observation from the one whose signature was checked" % e)
        return "not valid JSON"
    if parsed != obj:
        return "the line's bytes do not parse to the object checked — not the object signed"
    if serialise(parsed) != raw:
        return ("NON-CANONICAL LINE: the bytes are not the writer's serialisation (sorted keys, "
                "tight separators, ASCII escapes) — a second spelling of a signed observation")
    return None


def check_line(raw, obj, prev_hash, pub):
    form = line_form_error(raw, obj)
    if form:
        return form
    unknown = set(obj) - KNOWN
    if unknown:
        return "unknown field(s) %s — the allowlist is closed" % sorted(unknown)
    missing = REQUIRED - set(obj)
    if missing:
        return "missing required field(s) %s" % sorted(missing)
    # fullmatch, never match: under re.match a trailing `$` also matches just before a final
    # "\n", so "MATCH\n" would pass the closed verdict set.
    for k, rx in STR_SHAPES.items():
        if not isinstance(obj[k], str) or not rx.fullmatch(obj[k]):
            return "field %r fails its shape" % k
    for k in NULLABLE_HASH | CLAIM_FIELDS:
        if k in obj:
            v = obj[k]
            if v is not None and not (isinstance(v, str) and (v == "" or _HEX64.fullmatch(v))):
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


# dr:287 — UNKNOWN ARGV MUST NOT REACH THE DEFAULT PATH. This script's main fell through on an
# unrecognised flag and its default path WRITES, which is the dr:245 damage class: a usage probe
# or a typo ran the real thing. -h/--help prints the accepted forms and exits 0 having run
# nothing; an unknown flag prints them and exits 2 having run nothing; a recognised flag, a
# --key=value and any positional pass straight through, so no working invocation changes.
# The lint that holds the class is setup/hooks/cli_argv_safety_lint.py.
_ARGV_KNOWN = {"--help", "-h"}


def _argv_gate(argv=None):
    import sys as _sys
    argv = list(_sys.argv[1:] if argv is None else argv)
    _usage = "usage: verify_witness.py [%s]" % " | ".join(sorted(_ARGV_KNOWN))
    if "-h" in argv or "--help" in argv:
        print(_usage)
        raise SystemExit(0)
    unknown = [a for a in argv if a.startswith("-") and a not in _ARGV_KNOWN
               and a.split("=", 1)[0] + "=" not in _ARGV_KNOWN]
    if unknown:
        _sys.stderr.write("verify_witness.py: unknown argv %s\n%s\n" % (" ".join(unknown), _usage))
        raise SystemExit(2)





if __name__ == "__main__":
    _argv_gate()
    sys.exit(main(sys.argv))
