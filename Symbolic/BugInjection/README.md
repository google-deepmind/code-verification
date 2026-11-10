# Bug Injection

## Overview

Each bug in this directory is a Rust patch against `libsignal`: either a reversed upstream fix commit (`kind = "upstream"`, the default) or a forward regression patch against `v0.105.4` (`kind = "synthetic"`, documented in [`Synthetic/README.md`](Synthetic/README.md)). A **witness** pairs a sequence of CLI calls and attacker inputs with the trace `evs` of structured `CliEvent` records produced by the patched `libsignal-cli` binary.

A witness refutes the headline theorem `signal_session_secure_placed : SignalSessionSecurePlaced cliElfBytes` (`Symbolic/Theorems/Security.lean`) on the patched binary by proving `¬ SignalSessionSecurePlaced mutantCliElfBytes` (or `¬ SignalSessionSecure mutantCliElfBytes` on the fixed-image companion predicate for synthetic mutants), where `mutantCliElfBytes` is the mutant's `libsignal-cli` AArch64 ELF built by the stock `ld.lld` recipe (`scripts/cli-elf-stock --stdbin --build --unpinned`, from `cli-elf/stock/inputs_stock_stdbin.lock` and `cli-elf/stock/m4_stock.lock`, matching `cliElfBytes`) with the bug patch applied. Via `not_refines_of_witness` (`Split.lean`) and its CLI instantiation `not_signalSessionSecurePlaced_of_witness` (`Witnesses/CliShapePlaced.lean`, or `not_signalSessionSecure_of_witness` in `Witnesses/CliShape.lean`), the refutation splits into two halves:

- **Spec half `(S)`** (statement only): for every primitive interpretation and setup record satisfying `fits`, the records are well-formed and no symbolic execution (`Explains`) or collision excuse (`CollisionAtCli`) permitted by `SignalSessionSecurePlaced` accounts for `evs`.
- **Implementation half `(I)`** (mutant binary only): some pair satisfying `fits` meets the binary's external contracts, and the parsed ELF `mutantCliElfBytes` (at linked placements `(mpl, mmpl)`) produces `evs` under fresh randomness (`CoinsFresh`).

Together `(S)` and `(I)` imply `¬ SignalSessionSecurePlaced mutantCliElfBytes`. Because `SignalSessionSecurePlaced` holds for the unpatched `cliElfBytes`, `(S)` also implies the unpatched binary cannot produce `evs`.

External cryptographic primitives cannot be fixed to concrete X25519 or ML-KEM implementations inside the specification. Quantifying `(S)` universally and `(I)` existentially over a predicate `fits` keeps `(S)` independent of the machine image while restricting to well-behaved primitives: `cliCompFits` pairs `compFits` (well-formed setup records, `ExternCryptoLawsHold`, `X25519PubCanonical`, and `CompKyberCorrectOn` on trace ciphertexts) with the machine-free CLI contracts `ExternContractsHoldCli` and `HooksMatchInterpretation`.

Each `NonVacuity/<Witness>.lean` module proves `nonvacuous : ∃ i r, fits i r` in the default `lake build` (`decide +kernel` via `cliCompFits_satisfiable` in `NonVacuity/CliSatisfiable.lean`), ensuring `(S)` does not hold vacuously. Because `fits` constrains X25519, AES, and Kyber on `evs` while leaving HMAC, HKDF, XEdDSA, and SPQR uninterpreted, each witness documents which collision excuses (`CollisionAfterExplainedPrefix`) its spec argument assumes do not hold.

## Running

Prerequisites match [`README.md`](../../README.md): `elan`, the pinned Rust toolchain (`rust-toolchain.toml`), `protoc`, and the stock `ld.lld` CLI ELF toolchain (`scripts/cli-elf-stock --stdbin`: `rustc 1.98.1` sysroot `gcc-ld/ld.lld` and `zig 0.16.0` pinned in `third_party/libsignal/libsignal-session/cli-elf/stock/inputs_stock_stdbin.lock`).

```bash
lake exe cache get
lake build
python3 scripts/bug_injection.py verify-patches     # check stored diffs against upstream / v0.105.4
python3 scripts/bug_injection.py run                # replay witnesses on mutant and unpatched host builds
python3 scripts/bug_injection.py gen-ckpt <bug>     # materialize per-call execution checkpoints
python3 scripts/bug_injection.py disproof           # build mutant ELFs and kernel-check disproofs
```

`run` builds the host replayer (`third_party/libsignal/bug-injection/harness/`) against both the patched and unpatched Rust sources, executes each witness (`RunEvent` records `party`, `cmd`, `input`, `coins`, and `exit`; `clear` emits no event), verifies byte-for-byte agreement with `Witnesses/<Witness>.lean`, and classifies each witness as `live` (mutant produces `evs`, unpatched control does not), `refuted-by-control`, or `not-expressible`.

`disproof` stages a temporary per-mutant repo view pointing `vendor/libsignal` at the verified patched checkout (failing closed both before and after the build if `HEAD`, `HEAD^{tree}`, or the patched-vs-clean binary diff SHA-256 do not match the expected bug patch), re-extracts the patched AArch64 Lean model with `rust-obj2lean`, links the mutant's `libsignal-cli` ELF with the stock `ld.lld` recipe (`scripts/cli-elf-stock --stdbin --build --unpinned --repo-root <staged>`), verifies A-LINK provenance on the mutant output (see below), pins `mutantCliElfBytes` in `GeneratedLean.BugInjectionMutant` (asserting both `mutantCliElfSha256 != cleanCliElfSha256` and `sessionCodeSha256 != cleanCodeSha256`), and elaborates `Disproofs/<Witness>.lean` under `CV_BUG_INJECTION=<bug>`. All build artifacts live under `.lake/bug-injection/`, and `#guard` checks reject unpatched or mismatched ELF images; nothing in the default `lake build` imports mutant overlays.

### Mutant Stock Link & A-LINK Provenance Checks

`scripts/stock-pin/alink_check.py` and `third_party/libsignal/libsignal-session/cli-elf/stock/m4_stock.lock` remain untouched for the shipped `cliElfBytes`. Inside `scripts/bug_injection.py`, `verify_mutant_stock_alink` imports `alink_check.py` read-only and checks every mutant build against a policy-only seed lock derived from `cli-elf/stock/m4_stock.lock`:

- **Enforced unchanged**:
  - Pre- and post-build `verify_staged_vendor_libsignal` check on the resolved `vendor/libsignal` checkout (`HEAD` commit SHA, git tree SHA, clean `git status`, and SHA-256 of `git diff --binary <clean_v0.105.4_sha> HEAD`), preventing any stale `vendor/libsignal` symlink from silently building clean code.
  - Non-identity guards in Python and Lean `#guard`s: `mutantCliElfSha256 != cleanCliElfSha256` and `sessionCodeSha256 != cleanCodeSha256`.
  - Toolchain, linker-script, shim, and prebuilt-`std` lock pins in `cli-elf/stock/inputs_stock_stdbin.lock` (`rustc 1.98.1`, `ld.lld`, `zig 0.16.0`, `stock_c2.ld`, `rdl_shim.S`, `libstd_rlib` member pins).
  - `alink_check.py` Rules `(i)`–`(vii)`: `ld.lld --verbose` input classification (`real_proved`, `real_hook_reached`, `retired_stub`, `failstop_z`), link-line flags (`--gc-sections`, `--icf=none`, `--apply-dynamic-relocs`, `-Bstatic`, `-T stock_c2.ld`), unexpected object/section rejection, `failstop_z` live-symbol subset check (`0` unexpected Zone-Z symbols), pure-zero `udf #0` (`0x00000000`) encoding across `.text.stubs` in `extern_stubs_clean.o`, and `d1_extern_data_lock` `kept_count` + `kept_symbols` set equality (`2` kept symbols: `MAX_LOG_LEVEL_FILTER` and `ED25519_BASEPOINT_TABLE`).
- **Skipped or adapted relative to the shipped-ELF `cli-elf/stock/m4_stock.lock` check**:
  - `output_elf.{sha256,size}` exact lock pin — **replaced** by `mutantCliElfSha256 != cleanCliElfSha256` + `sessionCodeSha256 != cleanCodeSha256` (and, on the two proved Cheval'26 carriers, exact `#guard mutantCliElfSha256 == f3TrialElfSha256` in `{SmallSubgroup,WeakState}/F3LayoutData.lean`), because applying a bug patch intentionally changes `.text`/`.rodata` bytes and ELF size.
  - `engine_hooked_externs_sha256` exact lock pin — **skipped** (`""` in the mutant policy lock), because the bug patch shifts branch sites inside `libsignalSessionObj` and changes the raw `externs` digest (`BaseScalarsHooks.base_hooks` kernel-checks the exact hook + panic table on each proved mutant: `44` entries on `cheval26-small-subgroup`, i.e. `26` of the `27` `cliHookTablePlaced` rows after its patch deletes the call to `EdwardsPoint::is_torsion_free` plus all `18` `cliPanicSymbolsPlaced` panics, and `45 = 27 + 18` entries on `cheval26-weak-state`).
  - `stub_object.{sha256,symbol_count}` exact `122`-symbol pin — **adapted** to verify pure-zero `0x00000000` `.text.stubs` bytes while recording `stub_symbol_count_delta` (`Δstub`), because a bug patch that removes a call site can drop an unused extern stub from `extern_stubs_clean.o` (e.g., `cheval26-small-subgroup` drops `EdwardsPoint::is_torsion_free`, leaving `121` stubs, `Δstub = -1`).
  - `d1_extern_data_lock.kept[*].sha256` per-blob SHA-256 — **adapted** to `kept_count` + `kept_symbols` set equality, because `d1_extern_data.o` encodes relocated `.rodata` pointers whose target VMAs shift when `.text` grows or shrinks.
  - `retired_stub_slots[*]` fixed `origAddr` baseline (`2f20c836` baseline in `m4_stock.lock`) — **adapted** to `verify_retired_stub_slots_symbol_relative` (`4 · Δstub` spread rule): all `7` retired symbols (`__retired_0..__retired_6` for the `7` Rust `lib2_*.o` de-hooked rows) must exist in `.symtab` as unique `STB_LOCAL` entries at 4-byte-aligned VMAs in monotonic order, contain `0x00000000` (`udf #0`) in `PT_LOAD`, and shift monotonically relative to `orig_addr` with spread `max(delta) - min(delta) <= 4 * |Δstub|` bytes (accounting for at most `|Δstub|` dropped/added 4-byte stubs sorting ahead of a subset of the `7` retired slots, e.g. `[-576, -572]` on `cheval26-small-subgroup` with `Δstub = -1` and `[-1232, -1232]` on `cheval26-weak-state` with `Δstub = 0`).

## Adding a Bug

1. **Save the Rust patch** and register a `[[bug]]` entry in `third_party/libsignal/bug-injection/bugs.toml` (or `synthetic/bugs.toml`):
   - **Upstream bug (`kind = "upstream"`, default)**: save `https://github.com/signalapp/libsignal/commit/<sha>.diff` to `third_party/libsignal/bug-injection/patches/<bug>/upstream-<sha>.diff` (applied reversed), plus `v0.105.4.diff` if backporting to `v0.105.4` is needed.
   - **Synthetic mutant (`kind = "synthetic"`)**: save a forward diff against `v0.105.4` to `third_party/libsignal/bug-injection/synthetic/patches/<slug>/v0.105.4.diff` with `patch` and `patch_sha256` in `synthetic/bugs.toml`.
2. **Select the target statement**: set `statement = "DY.Libsignal.Composed.Security.SignalSessionSecurePlaced"` on upstream `[[witness]]` entries (or `"DY.Libsignal.Composed.Security.SignalSessionSecure"` for synthetic mutants; keyed in `STATEMENTS` in `scripts/bug_injection.py`).
3. **Write the witness inputs** in `third_party/libsignal/bug-injection/witnesses/<witness>.json` (or `synthetic/witnesses/<slug>.json`), listing `init`, `send`, `recv`, `clear`, and disk-compromise `leak` steps (`KeyInDir`, optional `"with_opk": true`) with literal or derived byte arguments (`slice`, `replace`, `or_at`; see `harness/src/main.rs`).
4. **Record and generate Lean modules**: run `python3 scripts/bug_injection.py run <witness> --record` to write `Witnesses/<Witness>.lean`, `NonVacuity/<Witness>.lean`, and `Disproofs/<Witness>.lean` (under `Synthetic/` for synthetic mutants; add new disproof modules to `EXCLUDED` in `scripts/check_lib_roots.py`).

## Disproofs

Both historical bugs are kernel-refuted in their `CV_BUG_INJECTION=<bug>` builds, with `#print axioms disproof` depending only on `[propext, Classical.choice, Quot.sound]`.

Because `mutantCliElfBytes` depends only on the bug patch, every witness for a given bug shares the same obligation `¬ SignalSessionSecurePlaced mutantCliElfBytes`. `CARRIERS` in `scripts/bug_injection.py` discharges each bug's generated `Disproofs/<Witness>.lean` obligations from a single carrier theorem in `Disproofs/Impl/<CarrierWitness>.lean`:

- `cheval26-small-subgroup`: carrier `cheval26-small-subgroup-high-bit-cli`
- `cheval26-weak-state`: carrier `cheval26-weak-state-idx1-cli`

The alternate traces `cheval26-small-subgroup-torsion-cli` and `cheval26-weak-state-cli` are not separately kernel-stepped. In `cheval26-weak-state-cli`, call 6 reads an SPQR chain key at step index 2 that no prior wire message commits to, allowing an unconstrained `OpaqueSymbolSemantics` to satisfy a collision excuse; `cheval26-weak-state-idx1-cli` refutes the same mutant ELF at step index 1, which call 5 pins on the wire.

Each carrier applies `not_signalSessionSecurePlaced_of_witness` (`Witnesses/CliShapePlaced.lean`) at linked placements `(mpl, mmpl)` and the proof-layer predicate `cliCompFitsPinned setup` (`Proofs/Common/CompFitsPin.lean`), which extends `cliCompFits` with the table-driven interpretation `compI0`, unrecorded setup randomness, party identifiers, and torsion-shift facts:

- **Spec proofs `(S)`** build in the default `BugInjection` library (`Proofs/Cheval26SmallSubgroupHighBitComp443/`, `Proofs/Cheval26WeakStateIdx1/`, `Proofs/Common443/`, and `Proofs/Common/`).
- **Binary execution proofs `(I)`** evaluate `ElfImage.parse mutantCliElfBytes` in the kernel (`Disproofs/Impl/MutantParse.lean`), prove `ElfFullValid` (`Disproofs/Impl/<Bug>/Base*.lean`), step the CLI runs (3 for small subgroup, 7 for weak state) via `Proofs/CliExec/` across `2^0`- to `2^11`-step chunks defined in `Disproofs/Impl/ckpt_chunk_plan.json`, and combine `(S)` and `(I)` in `Disproofs/Impl/<Bug>/Nodes.lean`.
- **Checkpoints**: `Base*` and `Call<k>.lean` aggregators are tracked in git, while `Call<k>/{C*,Ckpt*}.lean` chunk files are gitignored and materialized by `scripts/bug_injection.py gen-ckpt` (using `Disproofs/Impl/CkptDump/{BasePlaced,RunPlaced}.lean` and `scripts/bug_injection_ckpt.py`, which enforces a pure-expression token allowlist and runs `check_axiom_tactics` and `sorry`/template checks before `rfl_kernel` verification).

### Limitations

- **Token-cell offsets on fixed-image synthetic modules**: the two proved Cheval'26 `SignalSessionSecurePlaced` disproofs resolve `STORAGE.0` and `TOKEN` relocatably from `.symtab` via `cliTokenPatchPlaced mpl` (`tokStorageAddr` and `tokOnceAddr` kernel-checked in `BaseScalarsHooks.lean`). The 10 open synthetic `SignalSessionSecure` modules (`Synthetic/Disproofs/*Cli.lean`) still reference the fixed-image companion `cliTokenPatch` (`tokenStorageOff` and `tokenOnceOff` measured on `cliElfBytes`).
- **No `comparator` replay**: mutant disproofs are checked by Lean and `#print axioms` inside their `CV_BUG_INJECTION=<bug>` builds rather than replayed against a separate held-out challenge package.

## Status

| Witness | Bug (upstream fix commit) | Host replay | Obligation (`¬ SignalSessionSecurePlaced mutantCliElfBytes`) | `(S)` status |
|---|---|---|---|---|
| `cheval26-weak-state-cli` | weak state (`cd361186fba60c83186262d91b03af608fb8c7c3`) | `live` | proved via carrier `cheval26-weak-state-idx1-cli` | false under unconstrained SPQR `OpaqueSymbolSemantics` (step index 2 unpinned on wire); unused |
| `cheval26-weak-state-idx1-cli` | weak state (`cd361186fba60c83186262d91b03af608fb8c7c3`) | `live` | proved (carrier) | proved at `cliCompFitsPinned` (open at unpinned `cliCompFits` without SPQR pins) |
| `cheval26-small-subgroup-high-bit-cli` | small subgroup (`5293caa6cad81566b80f3c3731857bedaa78737b`) | `live` | proved (carrier) | proved at `cliCompFitsPinned` (open at unpinned `cliCompFits` on `BobSessionStartCollidesOrImplicitRejects` / `KyberCollisionAt`) |
| `cheval26-small-subgroup-torsion-cli` | small subgroup (`5293caa6cad81566b80f3c3731857bedaa78737b`) | `live` | proved via carrier `cheval26-small-subgroup-high-bit-cli` | open (`cliCompFits` does not pin the torsion shift) |

Synthetic specification-audit mutants (`synthetic-*`, all `live`) live under [`Synthetic/`](Synthetic/README.md), with patches and JSON witnesses in `third_party/libsignal/bug-injection/synthetic/`.
