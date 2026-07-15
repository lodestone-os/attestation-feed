#!/usr/bin/env python3
"""verify_feed — independent verifier for the Lodestone attestation feed.

One command, zero dependencies beyond Python 3:

    python3 verify_feed.py [feed.jsonl] [pubkey.hex]

Defaults: ./attestations.jsonl and ./lodestone_feed.pub (run it inside the feed repo).

What it proves, per line:
  1. CHAIN  — prev_attestation_sha256 equals sha256(previous line's exact bytes);
              line 1 must carry 64 zeros. Any retroactive edit breaks every later link.
  2. SIG    — the Ed25519 signature verifies over the canonical form (the JSON object
              minus "signature", keys sorted, separators (",",":"), UTF-8) against the
              published public key.
  3. SHAPE  — every field matches the fixed allowlist shape (no free text ever).

Exit 0 = full chain PASS. Exit 1 = the first broken line, named. This file embeds a
pure-Python Ed25519 verifier (RFC 8032) so you don't have to trust our tooling — read
it, or swap in your own implementation; the feed's canonical form is documented above
and in README.md.
"""
import sys
import json
import base64
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


# ---- feed rules (must mirror the emitter's published spec) ---------------------------
GENESIS_PREV = "0" * 64
FIELD_SHAPES = {
    "timestamp": re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$"),
    "contract_self_sha256": re.compile(r"^[0-9a-f]{64}$"),
    "reflects_commit": re.compile(r"^[0-9a-f]{7,12}$"),
    "gates_summary": re.compile(r"^\d{1,3}/\d{1,3} (PASS|FAIL)$"),
    "tenant": re.compile(r"^tenant-\d{2}$"),
    "prev_attestation_sha256": re.compile(r"^[0-9a-f]{64}$"),
}
INT_FIELDS = {"consent_receipts_count": (0, 1_000_000)}
EXPECTED = set(FIELD_SHAPES) | set(INT_FIELDS) | {"signature"}


def canonical(obj):
    body = {k: v for k, v in obj.items() if k != "signature"}
    return json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")


def check_line(raw, obj, prev_hash, pub):
    if set(obj) != EXPECTED:
        return "field set mismatch (got %s)" % sorted(obj)
    for k, rx in FIELD_SHAPES.items():
        if not isinstance(obj[k], str) or not rx.match(obj[k]):
            return "field %r fails its shape" % k
    for k, (lo, hi) in INT_FIELDS.items():
        if not isinstance(obj[k], int) or isinstance(obj[k], bool) or not (lo <= obj[k] <= hi):
            return "field %r out of range" % k
    if obj["prev_attestation_sha256"] != prev_hash:
        return "CHAIN BROKEN: prev=%s, expected %s" % (obj["prev_attestation_sha256"][:16],
                                                       prev_hash[:16])
    try:
        sig = base64.b64decode(obj["signature"], validate=True)
    except Exception:
        return "signature is not valid base64"
    if not ed25519_verify(pub, canonical(obj), sig):
        return "SIGNATURE INVALID"
    return None


def main(argv):
    feed = argv[1] if len(argv) > 1 else "attestations.jsonl"
    pubf = argv[2] if len(argv) > 2 else "lodestone_feed.pub"
    try:
        pub = bytes.fromhex(open(pubf).read().strip())
    except Exception as e:
        print("FAIL: cannot read public key %s (%s)" % (pubf, e))
        return 1
    try:
        raw_lines = [ln.rstrip(b"\n") for ln in open(feed, "rb") if ln.strip()]
    except Exception as e:
        print("FAIL: cannot read feed %s (%s)" % (feed, e))
        return 1
    if not raw_lines:
        print("FAIL: feed is empty — nothing to verify is not a pass")
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
    first = json.loads(raw_lines[0])["timestamp"]
    last = json.loads(raw_lines[-1])["timestamp"]
    print("PASS: %d attestation(s), chain + signatures + shapes all valid (%s .. %s)"
          % (len(raw_lines), first, last))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
