# AGENTS.md

## Cursor Cloud specific instructions

This is a **Lean 4 formal verification library** (ArkLib) — there is no web server, database, or runtime service. "Running the application" means **building the library** with `lake build ArkLib`, which type-checks all proofs.

### Key commands

| Task | Command |
|---|---|
| Build library | `lake build ArkLib` |
| Style lint | `./scripts/lint-style.sh` |
| Check imports | `./scripts/check-imports.sh` |
| Update import file | `./scripts/update-lib.sh` |
| Interactive type-check | `echo 'import ArkLib...' \| lake env lean --stdin` |

### Important notes

- **elan** must be on `PATH` (`$HOME/.elan/bin`). It auto-installs the correct Lean toolchain from `lean-toolchain`.
- After `lake update`, run `lake exe cache get` to download pre-built mathlib `.olean` files. Without this, building mathlib from source takes **hours**.
- The CI (`ci.yml`) uses `leanprover/lean-action@v1.4.0` with `lint: false` — the style linter has pre-existing warnings, so a non-zero exit code from `lint-style.sh` is expected.
- When adding new `.lean` files, run `./scripts/update-lib.sh` to regenerate `ArkLib.lean` with all imports. CI checks this via `check-imports.yml`.
- See `CONTRIBUTING.md` for naming conventions, style guidelines, and PR title format.
