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
  4. SIGNER — the signing key is IN THE PUBLISHED SIGNER SET at that height. The set is
              not a side file you have to be given: it is derived from this chain alone,
              starting at the published genesis key and growing only through
              authorisation lines that were themselves already verified. A signature from
              a key outside the set at its height is REFUSED loudly (fail-closed).
  5. FORK   — no two records may extend the same head. Three machines append to this
              chain independently; a fork is a loud failure, never a silent divergence.

THE THREE-SIGNER TRUST ROOT (row 1638). This feed is signed by more than one machine, so
the verifier answers three questions the single-key version never had to:

  WHO MAY SIGN — the published signer set, above. Append-only: the set may only GROW,
  except at an explicit revocation line, and that invariant is checked rather than assumed.

  HOW A SIGNER IS REMOVED — a `signer_revocation` line, under three rules that exist
  because the naive version can be turned around by whoever stole a machine:
    · it may NOT be signed by the key it revokes — revocation must never require the
      cooperation, the presence, or the consent of the machine being revoked;
    · a single entry that names EVERY other signer is refused outright — otherwise the
      thief of one laptop revokes the legitimate machines and keeps the chain;
    · the set never falls below two members by revocation. To remove a signer from a
      two-member set, authorise a replacement first. This is what stops the same attack
      run one entry at a time: a stolen key can shrink the set to two and no further,
      which leaves a legitimate signer standing who can authorise a replacement and
      revoke the thief. HONEST BOUND, stated not hidden: with three keys, whoever holds
      one can still force that stand-off. What the design buys is attribution and
      recoverability, never prevention.

  WHETHER A SIGNER IS ALIVE — `proof_of_life` lines carry a per-machine identity, so a
  signer that has not signed inside its window is a NAMED DEFECT rather than quiet health.
  An unexercised signer is the same object as an unrestored backup: believed good, never
  tested, discovered broken at the moment of need. `signer_liveness()` is the reading the
  board renders; this verifier computes it, so there is one definition of "silent".

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


# Group arithmetic runs in extended homogeneous coordinates (RFC 8032 §5.1.4:
# (x, y) ↔ (X, Y, Z, T) with x = X/Z, y = Y/Z, T = XY/Z) so the add/double loop
# is inversion-free — a field inversion is a full 255-bit modexp, and paying two
# of them per point addition made every signature check cost ~130ms (decl:1682:3).
# _inv is spent only at the decode/encode boundaries.
_2d = (2 * _d) % _q


def _ext(P):
    x, y = P
    return (x, y, 1, (x * y) % _q)


def _affine(P):
    X, Y, Z, _T = P
    zi = _inv(Z)
    return ((X * zi) % _q, (Y * zi) % _q)


def _ext_add(P, Q):
    # add-2008-hwcd-3 for a = -1 twisted Edwards; unified (doubles too).
    X1, Y1, Z1, T1 = P
    X2, Y2, Z2, T2 = Q
    A = ((Y1 - X1) * (Y2 - X2)) % _q
    B = ((Y1 + X1) * (Y2 + X2)) % _q
    C = (T1 * _2d * T2) % _q
    D = (2 * Z1 * Z2) % _q
    E = B - A
    F = D - C
    G = D + C
    H = B + A
    return ((E * F) % _q, (G * H) % _q, (F * G) % _q, (E * H) % _q)


def _edwards_add(P, Q):
    return _affine(_ext_add(_ext(P), _ext(Q)))


def _scalarmult(P, e):
    Q = (0, 1, 1, 0)  # neutral element
    R = _ext(P)
    while e:
        if e & 1:
            Q = _ext_add(Q, R)
        R = _ext_add(R, R)
        e >>= 1
    return _affine(Q)


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
    "timestamp": re.compile(r"\A\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z\Z"),
    "contract_self_sha256": re.compile(r"\A[0-9a-f]{64}\Z"),
    "reflects_commit": re.compile(r"\A[0-9a-f]{7,12}\Z"),
    "gates_summary": re.compile(r"\A\d{1,3}/\d{1,3} (PASS|FAIL)\Z"),
    "tenant": re.compile(r"\Atenant-\d{2}\Z"),
    "prev_attestation_sha256": re.compile(r"\A[0-9a-f]{64}\Z"),
}
INT_FIELDS = {"consent_receipts_count": (0, 1_000_000)}

# Record kind 2 — the pre-announced key rollover (see README.md "Succession").
#
# WHY A FEED HAS THIS AT ALL: the chains this key signs live on GitHub and survive the
# machine, but the IDENTITY does not. If the signing key is lost, honesty rule 1 (no
# backfill, ever) means the chain can never be honestly extended, and a rotation announced
# AFTER the loss is exactly what you — the stranger — cannot distinguish from a forgery. So
# the current key, WHILE IT IS ALIVE, signs a statement naming its successor. You verify the
# handoff against a statement already inside the chain you already trust.
#
# WHAT THIS MEANS FOR YOU AS A VERIFIER: after a valid successor_authorisation line, the
# named successor key becomes an ADDITIONAL accepted signer for later lines. The authorising
# key stays accepted too — that is what makes it a rollover rather than a cliff. Both are
# visible in the chain; neither can be added retroactively without breaking every link after
# it. If you do not want to honour rollovers at all, run with --no-rollover and only the
# published genesis key is accepted.
SUCCESSOR_SHAPES = {
    "timestamp": FIELD_SHAPES["timestamp"],
    "record_type": re.compile(r"\Asuccessor_authorisation\Z"),
    "successor_pubkey": re.compile(r"\A[0-9a-f]{64}\Z"),
    "authorised_by_pubkey": re.compile(r"\A[0-9a-f]{64}\Z"),
    "tenant": FIELD_SHAPES["tenant"],
    "prev_attestation_sha256": FIELD_SHAPES["prev_attestation_sha256"],
}
# ---- record kinds 3-5: the three-signer trust root (row 1638 A2/A4) ------------------
#
# EXTENDING, NOT REPLACING. `signer_authorisation` is the successor_authorisation record
# above with one field added — `machine`, the per-machine identity A2 needs — and it is a
# SEPARATE kind for exactly the reason succession was: every already-published line stays
# byte-valid and re-verifies unchanged, and the allowlist stays CLOSED in every direction.
# A line is one kind or it is REFUSED; there is still no free-text field anywhere.
#
# successor_authorisation remains fully honoured. It names a key with no machine attached,
# which is the honest record of what it is: a signer whose machine was never published.
HEX64 = re.compile(r"\A[0-9a-f]{64}\Z")
MACHINE = re.compile(r"\A[a-z][a-z0-9-]{2,31}\Z")

SIGNER_AUTHORISATION_SHAPES = {
    "timestamp": FIELD_SHAPES["timestamp"],
    "record_type": re.compile(r"\Asigner_authorisation\Z"),
    "signer_pubkey": HEX64,
    "machine": MACHINE,
    "authorised_by_pubkey": HEX64,
    "tenant": FIELD_SHAPES["tenant"],
    "prev_attestation_sha256": FIELD_SHAPES["prev_attestation_sha256"],
}
SIGNER_REVOCATION_SHAPES = {
    "timestamp": FIELD_SHAPES["timestamp"],
    "record_type": re.compile(r"\Asigner_revocation\Z"),
    "revoked_by_pubkey": HEX64,
    "tenant": FIELD_SHAPES["tenant"],
    "prev_attestation_sha256": FIELD_SHAPES["prev_attestation_sha256"],
}
PROOF_OF_LIFE_SHAPES = {
    "timestamp": FIELD_SHAPES["timestamp"],
    "record_type": re.compile(r"\Aproof_of_life\Z"),
    "machine": MACHINE,
    "signer_pubkey": HEX64,
    "tenant": FIELD_SHAPES["tenant"],
    "prev_attestation_sha256": FIELD_SHAPES["prev_attestation_sha256"],
}
# List-valued fields: {field: (element shape, min length, max length)}. The wall stays
# closed — every element must match its shape, and the list has a bounded length.
REVOCATION_LISTS = {"revoked_pubkeys": (HEX64, 1, 16)}

# Field set -> (name, str-shapes, int-ranges, list-shapes). Resolution is by EXACT field
# set, so a line that is neither kind is never coerced into the nearer one.
RECORD_KINDS = {
    frozenset(list(FIELD_SHAPES) + list(INT_FIELDS) + ["signature"]):
        ("attestation", FIELD_SHAPES, INT_FIELDS, {}),
    frozenset(list(SUCCESSOR_SHAPES) + ["signature"]):
        ("successor_authorisation", SUCCESSOR_SHAPES, {}, {}),
    frozenset(list(SIGNER_AUTHORISATION_SHAPES) + ["signature"]):
        ("signer_authorisation", SIGNER_AUTHORISATION_SHAPES, {}, {}),
    frozenset(list(SIGNER_REVOCATION_SHAPES) + list(REVOCATION_LISTS) + ["signature"]):
        ("signer_revocation", SIGNER_REVOCATION_SHAPES, {}, REVOCATION_LISTS),
    frozenset(list(PROOF_OF_LIFE_SHAPES) + ["signature"]):
        ("proof_of_life", PROOF_OF_LIFE_SHAPES, {}, {}),
}
# The kinds that mutate the signer set. Every other kind may only be checked against it.
SET_MUTATING = ("successor_authorisation", "signer_authorisation", "signer_revocation")
# Default proof-of-life window. A machine that has not signed inside it is a named defect,
# not a quiet one. Widened here rather than in each caller so there is ONE definition.
DEFAULT_WINDOW_HOURS = 26


class SignerSet:
    """The published signer set at a given height — derived from the chain, never given.

    The set starts as the single published genesis key and is grown ONLY by authorisation
    lines that have ALREADY passed chain, shape and signature verification. That ordering
    is the whole guarantee: by the time a key is accepted, the line that authorised it was
    itself signed by a key already accepted, and could not have been inserted retroactively
    without breaking every link after it.

    APPEND-ONLY IS CHECKED, NOT ASSUMED. Every mutation records (before, after, kind); a
    set that shrinks on anything but a revocation line, or shrinks by anything other than
    exactly that line's named keys, is a LOUD failure at the end of the walk. The
    derivation makes that true by construction — the check exists so that a future edit
    which breaks the construction is caught rather than trusted.
    """

    def __init__(self, genesis_pub_hex):
        self.keys = [genesis_pub_hex]
        self.machines = {genesis_pub_hex: None}
        self.revoked = []
        self.history = []          # (line_no, kind, before frozenset, after frozenset, removed)

    def key_bytes(self):
        return [bytes.fromhex(k) for k in self.keys]

    def snapshot(self):
        return frozenset(self.keys)

    def _record(self, line_no, kind, before, removed=()):
        self.history.append((line_no, kind, before, self.snapshot(), frozenset(removed)))

    def authorise(self, line_no, kind, pub_hex, machine=None):
        before = self.snapshot()
        if pub_hex not in self.keys:
            self.keys.append(pub_hex)
        self.machines[pub_hex] = machine
        self._record(line_no, kind, before)

    def revoke(self, line_no, revoked_hexes):
        before = self.snapshot()
        for h in revoked_hexes:
            if h in self.keys:
                self.keys.remove(h)
            if h not in self.revoked:
                self.revoked.append(h)
        self._record(line_no, "signer_revocation", before, revoked_hexes)

    def check_append_only(self):
        """None if the set only ever grew except at revocations; else the violation."""
        for line_no, kind, before, after, removed in self.history:
            lost = before - after
            if kind != "signer_revocation":
                if lost:
                    return ("APPEND-ONLY VIOLATED at line %d: a %s line removed signer(s) %s "
                            "from the published set — the set shrinks only by an explicit "
                            "revocation entry" % (line_no, kind,
                                                  sorted(k[:16] + "…" for k in lost)))
            elif lost != (removed & before):
                return ("APPEND-ONLY VIOLATED at line %d: the revocation removed %s but named "
                        "%s — a revocation removes exactly the signers it names, and nothing "
                        "else" % (line_no, sorted(k[:16] + "…" for k in lost),
                                  sorted(k[:16] + "…" for k in (removed & before))))
        return None


def canonical(obj):
    body = {k: v for k, v in obj.items() if k != "signature"}
    return json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")


def detect_fork(objs):
    """None, or a named FORK. Two records that carry the same prev extend the same head.

    A3: three machines append independently, so two of them WILL eventually build on the
    same head. In a single file the second one also breaks the linear chain check, but that
    reads as 'CHAIN BROKEN' and sends the reader looking for tampering. This runs first so
    the diagnosis names what actually happened. It is also the check a merging appender
    runs before it publishes anything.
    """
    seen = {}
    for i, obj in enumerate(objs, 1):
        prev = obj.get("prev_attestation_sha256")
        if prev in seen:
            return ("FORK at line %d: prev %s… is already extended by line %d — two records "
                    "build on the same head. A fork is a loud failure, never a silent "
                    "divergence: one of these appends lost the race and must be re-signed "
                    "against the new head." % (i, str(prev)[:16], seen[prev]))
        seen[prev] = i
    return None


def check_line(raw, obj, prev_hash, state):
    """Verify one line against the chain and the PUBLISHED SIGNER SET at this height.

    `state` is a SignerSet: the published genesis key plus every key authorised by an
    EARLIER, ALREADY-VERIFIED line, minus every key an earlier verified revocation removed.
    A signer can therefore never authorise itself retroactively — by the time its key is
    accepted, the line that authorised it has already been signature- and chain-verified.

    Returns (error_or_None, kind_name, signer_hex_or_None).
    """
    kind = RECORD_KINDS.get(frozenset(obj))
    if kind is None:
        return "field set matches no record kind (got %s)" % sorted(obj), None, None
    name, shapes, ints, lists = kind
    for k, rx in shapes.items():
        if not isinstance(obj[k], str) or not rx.match(obj[k]):
            return "field %r fails its shape" % k, name, None
    for k, (lo, hi) in ints.items():
        if not isinstance(obj[k], int) or isinstance(obj[k], bool) or not (lo <= obj[k] <= hi):
            return "field %r out of range" % k, name, None
    for k, (rx, lo, hi) in lists.items():
        v = obj[k]
        if not isinstance(v, list) or not (lo <= len(v) <= hi):
            return "field %r must be a list of %d..%d entries" % (k, lo, hi), name, None
        for el in v:
            if not isinstance(el, str) or not rx.match(el):
                return "field %r has an entry that fails its shape" % k, name, None
        if len(set(v)) != len(v):
            return "field %r repeats an entry" % k, name, None
    if obj["prev_attestation_sha256"] != prev_hash:
        return ("CHAIN BROKEN: prev=%s, expected %s" % (obj["prev_attestation_sha256"][:16],
                                                        prev_hash[:16])), name, None
    try:
        sig = base64.b64decode(obj["signature"], validate=True)
    except Exception:
        return "signature is not valid base64", name, None
    msg = canonical(obj)

    # ---- the signer-set gate (row 1638): fail-closed, and LOUD about which failure ----
    signer = None
    for k_hex in state.keys:
        if ed25519_verify(bytes.fromhex(k_hex), msg, sig):
            signer = k_hex
            break
    if signer is None:
        revoked_hit = next((k for k in state.revoked
                            if ed25519_verify(bytes.fromhex(k), msg, sig)), None)
        if revoked_hit:
            return ("SIGNED BY A REVOKED KEY %s… — the revocation is earlier in this same "
                    "chain, so this line is refused, not merely doubted"
                    % revoked_hit[:16]), name, None
        return ("SIGNATURE INVALID — SIGNED BY A KEY OUTSIDE THE PUBLISHED SIGNER SET at "
                "this height (%d accepted signer(s) here). Either the signature is corrupt "
                "or the key was never published in this chain; the two are indistinguishable "
                "from outside and both are refused, fail-closed"
                % len(state.keys)), name, None

    # A line that NAMES its signer must name it truthfully. Without this a legitimate
    # signer could sign a line attributing itself to another machine, and the human-readable
    # record would lie while the cryptography passed.
    for field in ("authorised_by_pubkey", "revoked_by_pubkey", "signer_pubkey"):
        if name == "signer_authorisation" and field == "signer_pubkey":
            continue                      # that field names the key being ADDED, not the signer
        if field in obj and obj[field] != signer:
            if obj[field] not in state.keys:
                return ("%s is not in the published signer set at this height" % field), name, None
            return ("%s is not the key that actually signed this line" % field), name, None

    if name in ("successor_authorisation", "signer_authorisation"):
        added = obj.get("successor_pubkey") or obj.get("signer_pubkey")
        if added == signer:
            return ("a key cannot authorise itself — that publishes a succession that "
                    "never happened"), name, None
        if added in state.revoked:
            return ("REFUSED: %s… is a REVOKED key — a revoked signer is never silently "
                    "re-authorised; mint a new key" % added[:16]), name, None

    if name == "signer_revocation":
        revoked = obj["revoked_pubkeys"]
        # A4 rule 1 — never signed by, and never dependent on, the machine being revoked.
        if signer in revoked:
            return ("REFUSED: a revocation may not be signed by the key it revokes. A "
                    "revocation must never require the cooperation, the presence, or the "
                    "consent of the machine being revoked — that is the entire point of "
                    "having a second signer"), name, None
        unknown = [r for r in revoked if r not in state.keys]
        if unknown:
            return ("REFUSED: revokes %s, which is not in the published signer set at this "
                    "height — revoking a key the chain never accepted asserts a removal that "
                    "did not happen" % sorted(r[:16] + "…" for r in unknown)), name, None
        # A4 rule 3 — a single entry naming every other signer is refused outright.
        others = set(state.keys) - {signer}
        if len(others) > 1 and others.issubset(set(revoked)):
            return ("REFUSED: this entry revokes EVERY other signer (%d of %d) and would "
                    "leave its own key alone in the set. Whoever holds one stolen machine "
                    "does not get to lock out the legitimate ones and keep the chain"
                    % (len(others), len(state.keys))), name, None
        # A4 quorum floor — the same attack run one entry at a time.
        remaining = len(set(state.keys) - set(revoked))
        if remaining < 2:
            return ("REFUSED: this revocation would reduce the published signer set to %d "
                    "signer(s). The set never falls below two by revocation — to remove a "
                    "signer from a two-member set, authorise a replacement first. This is "
                    "what stops a stolen key draining the set one entry at a time"
                    % remaining), name, None

    if name == "proof_of_life":
        published_machine = state.machines.get(signer)
        if published_machine is not None and obj["machine"] != published_machine:
            return ("proof_of_life claims machine %r, but %s… is published in this chain as "
                    "%r — an attestation is attributed to the machine that signed it, or it "
                    "is attributed to nothing" % (obj["machine"], signer[:16],
                                                  published_machine)), name, None
    return None, name, signer


def _parse_ts(ts):
    """Feed timestamps are a fixed shape; parse without importing anything exotic."""
    import datetime
    return datetime.datetime.strptime(ts, "%Y-%m-%dT%H:%M:%SZ")


def signer_liveness(objs, state, now=None, window_hours=DEFAULT_WINDOW_HOURS,
                    attribution=None):
    """A2's reading: per-machine proof of life, with silence NAMED as the defect it is.

    Returns one row per published signer, silent rows first:
      machine · pubkey · last_ts · age_hours · state (LIVE | SILENT | NEVER) · line

    WHAT COUNTS AS A SIGN OF LIFE. Any line the key actually signed — not only
    `proof_of_life` lines. The question A2 asks is whether a signer is being EXERCISED, and
    an attestation exercises a key exactly as well as a proof of life does. Scoring only the
    dedicated record would have rendered the one machine that signs every single day as
    NEVER, which is a false defect, and a board that raises false defects gets ignored
    precisely when it starts raising true ones. The `proof_of_life` record exists for the
    machines that have no OTHER reason to sign — it is the floor, not the definition.

    `attribution` is the (signer_hex, timestamp) list the walk resolved cryptographically.
    Passed in rather than re-derived because only the walk knows which key verified a bare
    attestation, and guessing from a self-declared field is how a chain gets misattributed.

    A signer that has never signed is NEVER, not merely stale — the distinction matters
    because an unexercised signer is the same object as an unrestored backup: believed
    good, never tested, discovered broken at the moment of need. Neither state is allowed
    to render as quiet health; both carry a sentence whose subject is the machine, not an
    identifier.
    """
    import datetime
    now = now or datetime.datetime.utcnow()
    last = {}
    if attribution is None:
        # Fallback for callers with no walk in hand: only lines that NAME their signer.
        attribution = [(o["signer_pubkey"], o["timestamp"]) for o in objs
                       if o.get("record_type") == "proof_of_life" and o.get("signer_pubkey")]
    for who, ts in attribution:
        if who and (last.get(who) is None or ts > last[who]):
            last[who] = ts
    rows = []
    for pub in state.keys:
        machine = state.machines.get(pub)
        name = machine or ("the genesis signer" if pub == state.keys[0] else "an unnamed signer")
        ts = last.get(pub)
        if ts is None:
            rows.append({"machine": machine, "pubkey": pub, "last_ts": None,
                         "age_hours": None, "state": "NEVER",
                         "line": "%s has never signed a proof of life on the attestation "
                                 "chain. It is a published signer that has not been "
                                 "exercised once — believed good, never tested."
                                 % name.capitalize()})
            continue
        age = (now - _parse_ts(ts)).total_seconds() / 3600.0
        if age > window_hours:
            rows.append({"machine": machine, "pubkey": pub, "last_ts": ts,
                         "age_hours": round(age, 1), "state": "SILENT",
                         "line": "%s has not signed the attestation chain for %.0f hours "
                                 "(its window is %d). That signer is unproven, not quiet."
                                 % (name.capitalize(), age, window_hours)})
        else:
            rows.append({"machine": machine, "pubkey": pub, "last_ts": ts,
                         "age_hours": round(age, 1), "state": "LIVE",
                         "line": "%s signed %.0f hours ago." % (name.capitalize(), age)})
    rows.sort(key=lambda r: (r["state"] == "LIVE", r["age_hours"] is None,
                             -(r["age_hours"] or 0)))
    return rows


class WalkResult(object):
    """One walk of the chain — the single derivation every caller reads.

    main(), the proof harness, and the board's signer band all call walk(). There is one
    verifier and therefore one definition of valid, of published-signer-set, and of silent.
    """

    def __init__(self, ok, error=None, line_no=None, objs=None, state=None, events=None,
                 attribution=None):
        self.ok = ok
        self.error = error
        self.line_no = line_no
        self.objs = objs or []
        self.state = state
        self.events = events or []            # (line_no, kind, timestamp, detail)
        self.attribution = attribution or []  # (signer_hex, timestamp), cryptographically resolved

    def liveness(self, now=None, window_hours=DEFAULT_WINDOW_HOURS):
        if not self.state:
            return []
        return signer_liveness(self.objs, self.state, now, window_hours, self.attribution)


def walk(raw_lines, genesis_pub_hex, no_rollover=False):
    """Verify the whole chain and derive the published signer set. Returns a WalkResult."""
    objs = []
    for i, raw in enumerate(raw_lines, 1):
        try:
            objs.append(json.loads(raw))
        except ValueError:
            return WalkResult(False, "not valid JSON", i)
    fork = detect_fork(objs)
    if fork:
        return WalkResult(False, fork, None, objs)
    state = SignerSet(genesis_pub_hex)
    prev = GENESIS_PREV
    events = []
    attribution = []
    for i, (raw, obj) in enumerate(zip(raw_lines, objs), 1):
        err, kind, signer = check_line(raw, obj, prev, state)
        if err:
            return WalkResult(False, err, i, objs, state, events, attribution)
        attribution.append((signer, obj["timestamp"]))
        if kind in SET_MUTATING and not no_rollover:
            if kind == "signer_revocation":
                state.revoke(i, obj["revoked_pubkeys"])
                events.append((i, kind, obj["timestamp"],
                               "revoked %s (by %s…)" % (
                                   [r[:16] + "…" for r in obj["revoked_pubkeys"]], signer[:16])))
            else:
                added = obj.get("successor_pubkey") or obj.get("signer_pubkey")
                state.authorise(i, kind, added, obj.get("machine"))
                events.append((i, kind, obj["timestamp"],
                               "authorised %s%s (by %s…)" % (
                                   added, " for machine %r" % obj["machine"]
                                   if obj.get("machine") else "", signer[:16])))
        prev = hashlib.sha256(raw).hexdigest()
    violation = state.check_append_only()
    if violation:
        return WalkResult(False, violation, None, objs, state, events, attribution)
    return WalkResult(True, None, None, objs, state, events, attribution)


def main(argv):
    no_rollover = "--no-rollover" in argv
    liveness = "--liveness" in argv
    argv = [a for a in argv if a not in ("--no-rollover", "--liveness")]
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
    res = walk(raw_lines, pub.hex(), no_rollover=no_rollover)
    if not res.ok:
        print("FAIL%s: %s" % ((" line %d" % res.line_no) if res.line_no else "", res.error))
        return 1
    first = res.objs[0]["timestamp"]
    last = res.objs[-1]["timestamp"]
    print("PASS: %d record(s), chain + signatures + shapes + signer set all valid (%s .. %s)"
          % (len(raw_lines), first, last))
    print("  published signer set: %d key(s)%s"
          % (len(res.state.keys),
             " [rollovers NOT honoured: --no-rollover]" if no_rollover else ""))
    for pub_hex in res.state.keys:
        m = res.state.machines.get(pub_hex)
        print("    %s  %s" % (pub_hex, ("machine %r" % m) if m else "(machine not published)"))
    for k in res.state.revoked:
        print("    REVOKED %s" % k)
    for i, kind, ts, detail in res.events:
        # `succession` is the published name for the successor_authorisation event and stays
        # the word this verifier prints — a stranger's tooling reads this output.
        label = "succession" if kind == "successor_authorisation" else kind
        print("  %s: line %d (%s) %s" % (label, i, ts, detail))
    if not liveness:
        return 0
    print("  proof of life (window %dh):" % DEFAULT_WINDOW_HOURS)
    for row in res.liveness():
        print("    [%s] %s" % (row["state"], row["line"]))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
