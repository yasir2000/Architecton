# Trusted evidence ledger

Records **who** ran **which** check on **which exact inputs**, and with what result, so that a claim like "the Lean proofs pass" points at signed, checkable evidence instead of a CI badge. When something changes, the ledger names exactly the checks that must run again.

## How it works

The checks and their dependencies live in [evidence/checks.json](../../evidence/checks.json). For example, `rust-tests` depends on `lean-conformance`, because the Rust oracle is only trustworthy once Lean has checked it.

Each run of a check becomes an **entry** in `evidence/ledger/entries/`:

| Field | Holds |
|---|---|
| `check`, `definition` | which check ran, and its command, inputs and dependencies at the time |
| `inputs` | SHA-256 of every input file (text hashed with LF endings) |
| `depends_on` | the entry IDs of the dependency checks it relied on |
| `result`, `exit_code`, `output_sha256`, `output_tail` | the outcome |
| `validator`, `platform`, `started_at`, `finished_at` | who ran it, where and when |

- **Content-addressed and immutable.** An entry's ID is the SHA-256 of its canonical bytes, so editing an entry changes its ID and is detected.
- **Signed.** The validator signs the entry with an SSH key (`ssh-keygen -Y sign`, namespace `architecton-evidence`). Signatures verify against [evidence/allowed_signers](../../evidence/allowed_signers), which says who is trusted. A trusted key can't sign under another principal's name.
- **Revocable.** `ledger.py revoke` writes a signed revocation record. Forged or unsigned revocations are ignored.

An entry is **valid** when its hash and signature check out, its result is `pass`, it isn't revoked, its check definition and every input file are unchanged, and every entry it depends on is valid.

## What is proved

[formal/Ledger.lean](formal/Ledger.lean) states this validity rule and proves `valid_blockMore_iff`: blocking any set of entries, by revoking them or by changing files they read, invalidates **exactly** the entries that depend on them, directly or transitively. Nothing else loses validity. The theorem uses no axioms at all. Its one assumption, that an ID determines its entry, holds by content addressing.

That set is precisely the **re-verification scope**: `ledger.py plan` lists it, and `ledger.py run` re-runs only those checks and reuses the rest.

The tests ([tests/test_ledger.py](tests/test_ledger.py), 18 of them) cover signing, tampering, untrusted signers, forged revocations, staleness, failures and scoped re-runs. One test checks the same exact-scope property on 300 random dependency graphs. Disabling signature checks makes the three authenticity tests fail.

## Usage

```bash
L=packages/ledger/scripts/ledger.py
python3 $L plan                     # which checks lack valid evidence, and why
python3 $L run --key KEY --principal NAME   # run only those, sign the results
python3 $L verify                   # exit 1 unless every check has valid evidence
python3 $L revoke ENTRY --reason "flaky runner" --key KEY --principal NAME
python3 $L show ENTRY
```

`--key` and `--principal` can also come from `ARCHITECTON_EVIDENCE_KEY` and `ARCHITECTON_EVIDENCE_PRINCIPAL`. A `run` of all 11 checks takes about two minutes.

## Setting up a validator

The repository ships with **no trusted keys**, so no evidence verifies until you add one:

1. Generate a key, ideally one dedicated to signing evidence: `ssh-keygen -t ed25519 -C ci@github-actions -f evidence_key`.
2. Add a line `ci@github-actions <contents of evidence_key.pub>` to `evidence/allowed_signers`, and commit it.
3. For CI, store the private key as the repository secret `ARCHITECTON_EVIDENCE_KEY`. The `signed-evidence` job in [ledger.yml](../../.github/workflows/ledger.yml) then runs every check, signs the results, verifies them and publishes the ledger as a build artifact.

## Limits

- **Declared inputs must be complete.** The ledger only knows about the files listed in `checks.json`. If a check reads an undeclared file, a change to that file won't invalidate its evidence. Tool versions are recorded in the output, not hashed as inputs, and `Cargo.lock` isn't tracked.
- **A signature proves who signed, not that the check was honest.** It shows the holder of a trusted key vouched for the result. Protect the key accordingly; a compromised key can produce valid-looking evidence until its line is removed from `allowed_signers`.
- **Persistence is a policy choice.** CI publishes the ledger as an artifact. Committing entries to the repository, or sending them to a transparency log, would make the history permanent; neither is set up.
