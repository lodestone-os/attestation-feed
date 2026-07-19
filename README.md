# Lodestone Attestation Feed

A public, append-only, independently verifiable record that a governed,
machine-operated business system is running — continuously, under integrity
gates, with human consent receipts. It publishes **integrity and cadence,
never content**: hashes and counts only.

## Verify it yourself

```
python3 verify_feed.py
```

No dependencies beyond Python 3. The verifier is self-contained (it embeds a
pure-Python Ed25519 implementation you can read, or replace with your own —
the canonical form is documented below). It checks, for every line: the hash
chain, the signature, and the field shapes. Exit 0 means the full chain is
valid; exit 1 names the first broken line.

## The record

One JSON line per attestation in `attestations.jsonl`:

| field | meaning |
|---|---|
| `timestamp` | UTC time of the attestation (ISO-8601, seconds, `Z`) |
| `contract_self_sha256` | content hash of the operating contract — the system's governing record — at attestation time |
| `reflects_commit` | short commit hash of the private operating repo the attestation reflects |
| `gates_summary` | pass/fail tally of the integrity gates that ran (counts only, e.g. `20/20 PASS`) |
| `consent_receipts_count` | running count of entries in the operator's consent/decision receipt register |
| `tenant` | pseudonymous tenant id (`tenant-01`) |
| `prev_attestation_sha256` | sha256 (hex) of the previous line's exact bytes — the chain link; line 1 carries 64 zeros |
| `signature` | Ed25519 signature (base64) over the canonical form of the line minus this field |

**Canonical form** (the signed bytes): the JSON object without `signature`,
serialized with sorted keys, separators `(",", ":")`, UTF-8. The public key is
`lodestone_feed.pub` (32 raw bytes, hex), published once at genesis.

Every field is shape-locked (exact regexes are in `verify_feed.py`). There is
no free-text field anywhere in the record — by construction, nothing private
can leak into it, and nothing promotional can be smuggled through it.

## Honesty rules

These rules are the point of the feed. They are not aspirations; the chain
enforces most of them and daylight enforces the rest.

1. **The streak starts at attestation #1.** There is no backfilled history and
   there never will be. Prior operation may be *cited* as context elsewhere;
   it does not appear in this chain.
2. **A missed day is a missed day.** Attestations are emitted at every session
   close and at least once daily by a scheduled job. A silent day is visible
   as a gap in the timestamps and is never papered over.
3. **Retroactive edits break the chain publicly and permanently.** Each line
   binds the exact bytes of the line before it. Rewriting history here is
   detectable by anyone with the verifier — including a git force-push, since
   your clone's chain will refuse to extend ours.
4. **Duplicate emissions are fine; fabricated ones are not.** Two attestations
   in a day just means two closes. Every line is signed; a line we didn't sign
   won't verify.
5. **The feed records its own failures.** A `FAIL` gates tally is published as
   `FAIL`. An emission that can't be built honestly is skipped (a gap), never
   faked.

## What this is not

Not a marketing surface, not a metrics dashboard, not proof that the business
is *good* — only proof that a governed machine has been running its gates,
under a stable governing record, with human consent receipts accumulating,
every day since attestation #1. That is the entire claim, and you can check it.

## The witness

`witness.jsonl` is a SECOND chain, signed by a separate Ed25519 key
(`witness_pub.json`) held by an independent scheduled observer. Each line is
one re-derivation of the operating contract's two stored surfaces from raw
bytes — never a copy of any stored verdict. Verify it the same way:

```
python3 verify_witness.py
```

Two keys, two chains, one repo: forging the contract now requires rewriting
both public histories consistently, which any clone detects. The witness
chain obeys the same honesty rules as the attestation chain — append-only,
gaps visible, failures recorded as what they are (`DIVERGED` is published as
`DIVERGED`).
