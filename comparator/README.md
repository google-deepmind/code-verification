# Comparator check of the headline theorems

This directory sets up [`leanprover/comparator`](https://github.com/leanprover/comparator), the Lean
FRO's proof judge, to check every headline theorem in `Computational/Theorems/` and
`Symbolic/Theorems/`. For each listed theorem, `comparator` checks that:

1. the theorem in the solution has the exact statement of the challenge, and every constant the
   statement transitively references is identical in both;
2. its proof depends only on the standard Lean axioms `propext`, `Quot.sound`, and
   `Classical.choice`;
3. the whole solution environment, exported by `lean4export` rather than loaded from `.olean`
   files, replays in a fresh Lean kernel (`Lean4Checker.Replay`).

## How the challenge and solution are set up

`lakefile.lean` defines two non-default Lake libraries rooted in `comparator/`:

- **`ComparatorChallenge`** (`ComparatorChallenge/{Computational,Symbolic}.lean` and the per-file
  modules under `ComparatorChallenge/{Computational,Symbolic}/`): **trusted** reference statements,
  one file per theorem file in `Computational/Theorems/` and `Symbolic/Theorems/`. Each file
  imports only specification modules (`Computational/Specifications/`,
  `LibsignalBinary/Specifications/`, `Symbolic/Specifications/`—never `Proofs/`, enforced by
  `Computational/scripts/check_computational_deps.py` and
  `Symbolic/scripts/check_symbolic_deps.py`) and restates each headline theorem with the same fully
  qualified name and statement, proved with `sorry`.
- **`ComparatorSolution`** (`ComparatorSolution/{Computational,Symbolic}.lean`): two thin root
  modules that `public import` the theorem files in `Computational/Theorems/` and
  `Symbolic/Theorems/` and declare nothing themselves, exposing the repository's proved theorems to
  `comparator` unchanged.

If you change a headline theorem statement in `Computational/Theorems/` or `Symbolic/Theorems/`,
make the matching change in its `ComparatorChallenge/` file; the challenge files and the
specification modules they import are the baseline `comparator` compares against.

The remaining files in `comparator/` configure and run the check:

| File | Role |
| --- | --- |
| `computational.json`, `symbolic.json` | Comparator configs pairing `ComparatorChallenge.<Side>` (`challenge_module`) with `ComparatorSolution.<Side>` (`solution_module`), listing the fully qualified `theorem_names`, and restricting `permitted_axioms` to `propext`, `Quot.sound`, and `Classical.choice` (`enable_nanoda: false`). |
| `install-tools.sh` | Fetches and builds `leanprover/comparator` and `leanprover/lean4export` at the tag matching `lean-toolchain` (`v4.34.0`), plus `Zouuup/landrun` at a pinned commit, and writes `<out>/env` with `COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT`, and `COMPARATOR_LANDRUN`. |
| `run.sh` | Pre-warms `lake build` of the challenge and solution modules under `.lake/comparator-home` (so comparator's sandboxed `lake build` is a no-op), raises the stack limit (`ulimit -s`), runs `lake env "$COMPARATOR_BIN"` on each config (both configs concurrently by default), streams timestamped logs to `COMPARATOR_LOG_DIR`, prints wall time and max RSS per config, and fails unless every run exits `0` and prints `Lean default kernel accepts the solution` and `Your solution is okay!`. |

## Theorems checked

Computational (`computational.json`), every theorem of `Computational/Theorems/`:

| Paper | Theorem |
| --- | --- |
| Lemma 1 | `SignalPqxdh.Security.headlineδ` |
| Lemma 2 | `CryptoVerification.E2E.session_secure` |
| Lemma 3 | `CryptoVerification.E2E.model_secure_costed` |
| Lemma 4 (relocatable) | `CryptoVerification.SignalSession.libsignal_cli_pq_binary_correct_placed` |
| Main Theorem (relocatable) | `CryptoVerification.LibsignalCli.libsignal_cli_pq_secure_elf_binary_placed` |
| placement witness (`libsignalSessionLib`) | `CryptoVerification.SignalSession.libsignal_cli_elf_linked_in` |
| allocator placement witness (`mallocngLib`) | `CryptoVerification.SignalSession.libsignal_cli_elf_mallocng_linked_in` |
| label gate A | `CryptoVerification.SignalSession.libsignal_cli_labels_from_objects` |

Symbolic (`symbolic.json`), every theorem of `Symbolic/Theorems/`:

| File | Theorems |
| --- | --- |
| `Security.lean` (headline) | `Proven.Security.signal_session_secure_placed`, `Proven.Security.libsignal_cli_elf_linked_in`, `Proven.Security.libsignal_cli_elf_mallocng_linked_in`, `Proven.Security.libsignal_cli_labels_from_objects` |
| `Refinement.lean` | `Proven.Refinement.comp_refines_cli_placed` |
| `RefinementPreservation.lean` | `Proven.RefinementPreservation.comp_refinement_preservation_cli` |
| `ModelSecurity.lean` | `Proven.ForwardSecrecy.forward_secrecy`, `Proven.PostCompromiseSecurity.post_compromise_security`, and in `Proven.Handshake`: `alice_initiator_secrecy`, `bob_responder_secrecy`, `authentication`, `peer_authentication`, `handshake_forward_secrecy`, `kci_resistance`, `session_independence`, `hndl_resistance` |

## Running comparator

Running `comparator/install-tools.sh` and `comparator/run.sh` requires Linux, since `comparator`
sandboxes its builds and exports with [`landrun`](https://github.com/Zouuup/landrun) (Linux
Landlock).

First build the default libraries, the `libsignal-cli` ELF, and `CliElfLib` from the repository
root as described in [`../README.md`](../README.md#building-and-verifying) (`lake exe cache get`,
`lake build`, `./scripts/cli-elf-stock --stdbin --build`, `./scripts/cli-elf-stock --stdbin
--verify-pin --lean-mod LibsignalBinary/Specifications/SignalSession/CliElf.lean`, `lake build
CliElfLib`). Then build the comparator tools and the two comparator libraries, and run
`comparator/run.sh`:

```bash
# 1. Build pinned comparator, lean4export, and landrun (uses `go` on PATH, or downloads a pinned Go
#    tarball into the output directory) and export their paths:
comparator/install-tools.sh /tmp/comparator-tools
set -a; source /tmp/comparator-tools/env; set +a

# 2. Build the challenge and solution libraries, then run both configs concurrently
#    (or pass a single config, e.g. `comparator/symbolic.json`):
ulimit -S -s 524288
lake build ComparatorChallenge ComparatorSolution
COMPARATOR_LOG_DIR=/tmp/comparator-logs comparator/run.sh
```

A full run takes several hours because fresh kernel replay of each headline closure is
single-threaded per config.

## Lean versions

`comparator` and `lean4export` are tagged per Lean release and must match `lean-toolchain`;
`install-tools.sh` fails if they do not. From Lean v4.35.0 on, comparator is part of core
(`lake comparator`, with `lake check`) and the standalone repository is deprecated; when the
repository moves to v4.35.0, switch to `lake comparator` instead of bumping the pins.
