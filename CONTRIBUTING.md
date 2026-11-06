# Contributing to Architecton

Thanks for your interest. Architecton is a research proof of concept, so contributions that sharpen evidence, close stated gaps or make limits clearer are especially welcome.

Read the [license](LICENSE) before contributing. Architecton is source-available, not open source, and contributions are accepted under its terms.

## Before you start

- For anything bigger than a small fix, open an issue first so we can agree on scope.
- Check the [research roadmap](README.md#research-roadmap-next-work-packages) and [assurance limits](docs/assurance.md). New claims must state their assumptions, trusted computing base and coverage.

## Developer Certificate of Origin (DCO)

Every commit must be signed off, or the DCO check fails:

```sh
git commit -s -m "feat: short description"
```

The `Signed-off-by:` line certifies that you wrote the change or have the right to submit it under the project license (see [developercertificate.org](https://developercertificate.org/)).

## Toolchain

- [Lean 4](https://lean-lang.org/) via `elan` (each Lean project pins its version in `lean-toolchain`)
- Rust (stable) with Cargo
- Python 3 (standard library only for the package checks)
- Docker (optional, for the container build)

## Running the checks

CI runs the workflows in [`.github/workflows`](.github/workflows). The main local equivalents are:

```sh
# DriverPass slice (run from examples/driverpass)
python3 scripts/generate.py --check
python3 scripts/check_contracts.py
cargo test --manifest-path backend/Cargo.toml

# Packages (run from the repository root)
python3 -m unittest discover -s packages/ir/tests -v
python3 -m unittest discover -s packages/design/tests -v
python3 -m unittest discover -s packages/ledger/tests -v
python3 packages/ir/scripts/irc.py check examples/driverpass/ir/driverpass.ir.json
```

Lean proof files are checked by the same workflows; see each package README for the exact `lean` commands.

## Conventions

- **Commits:** [Conventional Commits](https://www.conventionalcommits.org/) (`feat:`, `fix:`, `docs:`, `chore:`, …), signed off.
- **Generated files:** don't edit files marked `DO NOT EDIT`. Change the source (for example `requirements/policy.json`) and regenerate.
- **Proofs:** no `sorry` and no project-specific axioms in merged Lean code.
- **Changelog:** add a line under `Unreleased` in [CHANGELOG.md](CHANGELOG.md) for user-visible changes.

## Pull requests

Keep each PR focused on one change, fill in the PR template, and make sure all checks pass. By participating you agree to the [Code of Conduct](CODE_OF_CONDUCT.md).
