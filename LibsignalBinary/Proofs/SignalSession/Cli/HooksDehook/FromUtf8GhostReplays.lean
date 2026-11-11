/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FromUtf8RowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Code -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Ghost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8LrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Card `CC-FROMUTF8` — `lsFromUtf8Sym` Row Consumer Spec & Generic-`InvS` Ghost Replay (`HooksDehook.FromUtf8GhostReplays`)

Card **`c`** (`CC-FROMUTF8`) for `core::str::converts::from_utf8` (`lsFromUtf8Sym`) in the
`W2-C11` `CliGhostHooks.extra` framework (`ccard_recipe.md` §§2–5 row 4, modeled 1:1 on pilot
`BcmpGhostReplays.lean`), delivering **Artifact 1** (`GhostRowSpecOk`) and generic-`InvS`
**Artifact 2a** (`GhostRowReplayOn` + `GhostRowOk`) in the lightweight `Cli/HooksDehook` cone
(`0` `CliElfLib` / `ElfF3Relink` / C2 / trusted imports):

1. **Row Anchor & `W`-Independent Ghost (`fromUtf8MplPlacement`, `keepR_fromUtf8`, `fromUtf8SubProg`,
   `fromUtf8Ghost`, `fromUtf8MplGhost`):**
   - `fromUtf8Block` (`156` words = `624` B) is `VerifiedLibraries.RustStd.coreMultiLib.blockLib 1`
     (musl sysroot `core` rlib `Cs2kXltWtc1W`); byte and `256` B `UTF8_CHAR_WIDTH` table identity
     with the stock CLI ELF (`CskxtBwYRO61I`) is established at Cutover-2 / Card R1-a2 (`REV-S2` C1).
   - `fromUtf8Ghost pl` wraps `FromUtf8Ghost.emptyFromUtf8GhostHook (keepR_fromUtf8 pl) pl`
     (`P_run := emptyStdProg`, `fallback := realFromUtf8Fallback`), so it has **zero `W : CliHooks`
     or `mmpl` dependence**. `fromUtf8MplPlacement mpl tbl relax1` specializes `pl.base` to
     `libsignalSessionLib.resolve mpl lsFromUtf8Sym` (`rfl`) and `pl.ρ coreUtf8CharWidthSym` to `tbl`.
2. **Artifact 1 — `GhostRowSpecOk lsFromUtf8Sym` (`fromUtf8Ghost_rowSpecOk`):**
   - Matches `FromUtf8RowSpec` as-is (all `6` consumer arms: `fromUtf8AsciiSpec stk` and
     `fromUtf8AsciiSpecRO stk`, plain, `withVmPreserved`, and `withAlloc A lim`) via
     `FromUtf8RowSpec.of_vm` under pure decidable `hpl : fromUtf8Block.Placeable pl` (`0` memory,
     state, or `W` premises; `fs_eq` and `fsT` hold with `0` premises).
3. **Artifact 2a — Generic-`InvS` `GhostRowReplayOn` & `GhostRowOk` (`F1` + `H1` + `roTableGuard`):**
   - **F1:** `hRealHullNoExt` quantifies over `keepR_fromUtf8 pl pc = true` **only** on the
     de-hooked real program `P_real`. On `P_ghost`, `hGhostNoExtNe` **strictly excludes
     `pc ≠ libsignalSessionLib.resolve mpl lsFromUtf8Sym`** (no single-stub `hother` premise).
   - **H1 + `.rodata` guard:** `hCL` extracts `(fromUtf8SubProg pl).CodeLoaded u.mem` and `hRo`
     extracts `RoDataAt u.mem (pl.ρ coreUtf8CharWidthSym) corePlacedData1` at the intermediate call
     state `u` from `InvS u` (never `s0.mem`).
   - **`.text.lib2` ownership split (`ccard_recipe.md` §2.1):** `from_utf8` is a `.text.lib2` row,
     so C2 `Lib2LayoutFacts` instantiation belongs to the C2 layout / STARTUP seat; per-arm and
     singleton `ExtraEntryGuard` helpers live directly in §5 below.

## Disclosures (`REV-PILOT` `N1–N3`)
- **N1 (post-Cutover-2 only):** `hRealHullNoExt` requires `lsFromUtf8Sym` to be removed from
  `cliHookTablePlaced` (`C2ExternTableFacts`, discharged by `rfl_kernel` at C2 rebase). On
  pre-cutover `train`, `lsFromUtf8Sym` is still hooked on `P_real`, so replay Arm 2 is usable only
  post-Cutover-2.
- **N2 (`K` replay has no spec partner):** `fromUtf8GhostK_rowReplayOn` is honest, but no
  `GhostRowSpecOk lsFromUtf8Sym (fromUtf8GhostK …)` exists because `fromUtf8AsciiSpec.pre` has no
  `lr ∉ keepR` conjunct while `fromUtf8GhostK` raises `.Exception` when `lr ∈ keepR`. The usable
  `ExtraListOk` / `GhostRowOk` route is `fromUtf8Ghost` + `fromUtf8EntryGuard`; `*GhostK` replays
  are spares only.
- **N3 (singleton helper covers 1 row):** `extraEntryGuard_singleton_fromUtf8` covers
  `g.extra = [(lsFromUtf8Sym, …)]` only; multi-row C2 tables assemble `ExtraListEntryGuard` from
  per-arm `extraEntryGuard_fromUtf8_arm` across all active rows.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.RustStd (coreUtf8CharWidthSym corePlacedData1)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced libsignalSessionLib lsFromUtf8Sym
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen keepFsTrace
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FromUtf8RowSpec (
  FromUtf8RowSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (
  ExtraRowSpec GhostRowSpecOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (
  ExtraEntryGuard GhostRowOk GhostRowReplayOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  linkedCallHookG linkedCallHookG_activeRealPre_of_noException
  linkedCallHookG_eq_conj linkedCallHookG_visitedIn roTableGuard roTableGuard_stripS
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (TrapHook)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock (
  fromUtf8Block fromUtf8PatchedWords fromUtf8PatchedWords_length
  fromUtf8Placement pureWordsProg_fromUtf8_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Code (
  fromUtf8Placement_rho_table fromUtf8SpecK masterFromUtf8K_outcome_setPC
  masterFromUtf8K_pre_setPC realFromUtf8Fallback realFromUtf8Fallback_processFieldsPreserved
  specPreservesFsTrace_masterFromUtf8K specStripSInvariant_masterFromUtf8K
  subroutine_ok_masterFromUtf8K_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Ghost (
  emptyFromUtf8GhostHook emptyFromUtf8GhostHookK
  emptyFromUtf8GhostHook_asciiRO_ok emptyFromUtf8GhostHook_ascii_ok
  emptyFromUtf8GhostHook_fs emptyFromUtf8GhostHookK_fs
  emptyFromUtf8GhostHook_fsT emptyFromUtf8GhostHook_vmPreserved
  fromUtf8GhostHook fromUtf8GhostHookK fromUtf8GhostHookK_keepLr_false_of_noException
  fromUtf8GhostHook_visitedIn keepCoversFromUtf8_keepFromUtf8Block keepFromUtf8Block
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8LrTrap (
  FromUtf8EntryGuard emptyFromUtf8GhostHook_keepLr_false_after_hook_of_outcome_post
  fromUtf8ByteLen fromUtf8_codeLoaded_stripExecOutside
  fromUtf8_keepLr_false_after_hook_of_outcome_post keepFromUtf8Block_entry
  keepFromUtf8Block_iff trapHook_emptyFromUtf8GhostHook_of_cover
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_steps_lift_of_visitedIn_noExtern
)

/-! ## 1. Row Anchor Definitions, Algebraic Identities, & `CodeLoaded` Bridges -/

/-- Canonical single-block `Obj.Placement` for `lsFromUtf8Sym` under `mpl`, placing `fromUtf8Block`
    at `libsignalSessionLib.resolve mpl lsFromUtf8Sym` and the `256`-byte `UTF8_CHAR_WIDTH` `.rodata`
    table (`coreUtf8CharWidthSym`) at `tbl` with optional linker relaxation `relax1`. -/
@[expose] def fromUtf8MplPlacement (mpl : Obj.MultiPlacement) (tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false) : Obj.Placement :=
  fromUtf8Placement (libsignalSessionLib.resolve mpl lsFromUtf8Sym) tbl relax1

private theorem fromUtf8Placement_base (entry tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false) :
    (fromUtf8Placement entry tbl relax1).base = entry :=
  rfl

theorem fromUtf8MplPlacement_base (mpl : Obj.MultiPlacement) (tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false) :
    (fromUtf8MplPlacement mpl tbl relax1).base =
      libsignalSessionLib.resolve mpl lsFromUtf8Sym :=
  fromUtf8Placement_base (libsignalSessionLib.resolve mpl lsFromUtf8Sym) tbl relax1

theorem fromUtf8MplPlacement_rho_table (mpl : Obj.MultiPlacement) (tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false) :
    (fromUtf8MplPlacement mpl tbl relax1).ρ coreUtf8CharWidthSym = tbl :=
  fromUtf8Placement_rho_table (libsignalSessionLib.resolve mpl lsFromUtf8Sym) tbl relax1

/-- Kept-region byte predicate `[pl.base, pl.base + 624)` for a `from_utf8` placement `pl`. -/
@[expose] def keepR_fromUtf8 (pl : Obj.Placement) : BitVec 64 → Bool :=
  keepFromUtf8Block pl.base

/-- `MultiPlacement`-indexed kept-region byte predicate `[resolve mpl lsFromUtf8Sym, +624)`. -/
@[expose] def keepR_fromUtf8Mpl (mpl : Obj.MultiPlacement) : BitVec 64 → Bool :=
  keepFromUtf8Block (libsignalSessionLib.resolve mpl lsFromUtf8Sym)

private theorem keepR_fromUtf8_placement (entry tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false) :
    keepR_fromUtf8 (fromUtf8Placement entry tbl relax1) = keepFromUtf8Block entry :=
  rfl

theorem keepR_fromUtf8_mplPlacement (mpl : Obj.MultiPlacement) (tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false) :
    keepR_fromUtf8 (fromUtf8MplPlacement mpl tbl relax1) = keepR_fromUtf8Mpl mpl :=
  keepR_fromUtf8_placement (libsignalSessionLib.resolve mpl lsFromUtf8Sym) tbl relax1

/-- `pl.base` lies inside `keepR_fromUtf8 pl`. -/
theorem keepR_fromUtf8_entry (pl : Obj.Placement) :
    keepR_fromUtf8 pl pl.base = true :=
  keepFromUtf8Block_entry pl.base

theorem keepR_fromUtf8Mpl_entry (mpl : Obj.MultiPlacement) :
    keepR_fromUtf8Mpl mpl (libsignalSessionLib.resolve mpl lsFromUtf8Sym) = true :=
  keepFromUtf8Block_entry (libsignalSessionLib.resolve mpl lsFromUtf8Sym)

/-- Pure `156`-word (`624`-byte) sub-program holding `fromUtf8PatchedWords pl` at `pl.base`. -/
@[expose] def fromUtf8SubProg (pl : Obj.Placement) : Program :=
  pureWordsProg pl.base (fromUtf8PatchedWords pl)

theorem fromUtf8SubProg_base (pl : Obj.Placement) :
    (fromUtf8SubProg pl).base = pl.base :=
  rfl

theorem fromUtf8SubProg_svc (pl : Obj.Placement) :
    (fromUtf8SubProg pl).svc = Syscall.standard :=
  rfl

theorem fromUtf8SubProg_externAt_none (pl : Obj.Placement) (pc : BitVec 64) :
    (fromUtf8SubProg pl).externAt? pc = none :=
  pureWordsProg_externAt_none pl.base (fromUtf8PatchedWords pl) pc

theorem fromUtf8SubProg_hasWords (pl : Obj.Placement) :
    (fromUtf8SubProg pl).hasWords pl.base (fromUtf8PatchedWords pl) :=
  pureWordsProg_fromUtf8_hasWords pl

private theorem pureWordsProg_code_length_aux (base : BitVec 64) (ws : List (BitVec 32)) :
    (pureWordsProg base ws).code.length = 4 * ws.length := by
  change (ws.flatMap Program.wordToBytesLE).length = 4 * ws.length
  induction ws with
  | nil => rfl
  | cons _ rest ih =>
    simp only [List.flatMap_cons, List.length_append, ih]
    change 4 + 4 * rest.length = 4 * (rest.length + 1)
    omega

theorem fromUtf8SubProg_code_length (pl : Obj.Placement) :
    (fromUtf8SubProg pl).code.length = fromUtf8ByteLen := by
  dsimp only [fromUtf8SubProg, fromUtf8ByteLen]
  rw [pureWordsProg_code_length_aux, fromUtf8PatchedWords_length]

theorem keepR_fromUtf8_of_code_offset (pl : Obj.Placement) {off : Nat}
    (hoff : off < (fromUtf8SubProg pl).code.length) :
    keepR_fromUtf8 pl ((fromUtf8SubProg pl).base + BitVec.ofNat 64 off) = true := by
  rw [fromUtf8SubProg_code_length] at hoff
  dsimp only [keepR_fromUtf8, fromUtf8SubProg_base]
  rw [keepFromUtf8Block_iff]
  have hsub : (pl.base + BitVec.ofNat 64 off) - pl.base = BitVec.ofNat 64 off := by bv_omega
  have hoff_lt : off < 2 ^ 64 := by
    have hb : fromUtf8ByteLen = 624 := rfl
    omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]
  exact hoff

/-- Forward `CodeLoaded` projection onto `stripExecOutside (keepR_fromUtf8 pl) mem`. -/
theorem fromUtf8SubProg_codeLoaded_stripExecOutside {pl : Obj.Placement} {mem : Memory}
    (hL : (fromUtf8SubProg pl).CodeLoaded mem) :
    (fromUtf8SubProg pl).CodeLoaded (stripExecOutside (keepR_fromUtf8 pl) mem) :=
  fromUtf8_codeLoaded_stripExecOutside (keepCoversFromUtf8_keepFromUtf8Block pl.base) hL

/-- Reverse `CodeLoaded` projection from `stripExecOutside (keepR_fromUtf8 pl) mem` back to `mem`
    (so STARTUP's `f3CodeInv_rxWords_codeLoaded_strip` directly discharges `H1`'s
    `(fromUtf8SubProg pl).CodeLoaded u.mem` premise). -/
theorem fromUtf8SubProg_codeLoaded_of_stripExecOutside {pl : Obj.Placement} {mem : Memory}
    (hL : (fromUtf8SubProg pl).CodeLoaded (stripExecOutside (keepR_fromUtf8 pl) mem)) :
    (fromUtf8SubProg pl).CodeLoaded mem := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hk : keepR_fromUtf8 pl ((fromUtf8SubProg pl).base + BitVec.ofNat 64 i) = true :=
    keepR_fromUtf8_of_code_offset pl hi
  have hbyte := hL.byte_eq i hi
  have hperm := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [ProofLib.strip_read8] at hbyte
  rw [ProofLib.strip_perm_of_keep hk] at hperm
  rw [ProofLib.strip_isLazyFree] at hlf
  exact ⟨hbyte, hperm, hlf⟩

theorem fromUtf8SubProg_codeLoaded_stripExecOutside_iff {pl : Obj.Placement} {mem : Memory} :
    (fromUtf8SubProg pl).CodeLoaded (stripExecOutside (keepR_fromUtf8 pl) mem) ↔
      (fromUtf8SubProg pl).CodeLoaded mem :=
  ⟨fromUtf8SubProg_codeLoaded_of_stripExecOutside, fromUtf8SubProg_codeLoaded_stripExecOutside⟩

/-- `W`-independent ghost hook for `lsFromUtf8Sym` at placement `pl`
    (`P_run := emptyStdProg`, `fallback := realFromUtf8Fallback`). -/
@[expose] noncomputable def fromUtf8Ghost (pl : Obj.Placement) : State → State :=
  emptyFromUtf8GhostHook (keepR_fromUtf8 pl) pl

/-- `K`-narrowed `W`-independent ghost hook spare for `lsFromUtf8Sym` at placement `pl` (`N2`). -/
@[expose] noncomputable def fromUtf8GhostK (pl : Obj.Placement) : State → State :=
  emptyFromUtf8GhostHookK (keepR_fromUtf8 pl) pl

/-- `(mpl, mmpl, tbl, relax1)`-indexed `W`-independent ghost hook for `CliGhostHooks.extra` entry
    `(lsFromUtf8Sym, fromUtf8MplGhost mpl mmpl tbl relax1)`. -/
@[expose] noncomputable def fromUtf8MplGhost (mpl _mmpl : Obj.MultiPlacement) (tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false) : State → State :=
  fromUtf8Ghost (fromUtf8MplPlacement mpl tbl relax1)

/-- `(mpl, mmpl, tbl, relax1)`-indexed `K`-narrowed ghost hook spare (`N2`). -/
@[expose] noncomputable def fromUtf8MplGhostK (mpl _mmpl : Obj.MultiPlacement) (tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false) : State → State :=
  fromUtf8GhostK (fromUtf8MplPlacement mpl tbl relax1)

/-- Block-`617` entry-state `lr` guard for `lsFromUtf8Sym` (`C11` §6.3, `ccard_recipe.md` §2.2):
    `keepR_fromUtf8Mpl mpl (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ resolve mpl lsFromUtf8Sym`. -/
@[expose] def fromUtf8EntryGuard (mpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  FromUtf8EntryGuard (libsignalSessionLib.resolve mpl lsFromUtf8Sym)
    (libsignalSessionLib.resolve mpl lsFromUtf8Sym) s0

theorem fromUtf8EntryGuard_iff (mpl : Obj.MultiPlacement) (s0 : State) :
    fromUtf8EntryGuard mpl s0 ↔
      keepR_fromUtf8Mpl mpl (s0.readReg64 .lr) = false ∧
        s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl lsFromUtf8Sym :=
  Iff.rfl

/-! ## 2. Artifact 1 — `GhostRowSpecOk lsFromUtf8Sym` -/

theorem fromUtf8Ghost_fs (pl : Obj.Placement) (s : State) :
    (fromUtf8Ghost pl s).fs = s.fs :=
  emptyFromUtf8GhostHook_fs (keepR_fromUtf8 pl) pl s

theorem fromUtf8Ghost_fsT (pl : Obj.Placement) :
    HookFsTraced IsFsC (fromUtf8Ghost pl) :=
  emptyFromUtf8GhostHook_fsT (keepR_fromUtf8 pl) pl

theorem fromUtf8Ghost_vmPreserved {pl : Obj.Placement} (hpl : fromUtf8Block.Placeable pl)
    (s : State) :
    LibsignalBinary.Heap.VmPreserved s (fromUtf8Ghost pl s) :=
  emptyFromUtf8GhostHook_vmPreserved (keepR_fromUtf8 pl) hpl s

/-- `FromUtf8RowSpec` (all `6` consumer arms: RW/RO × plain/`withVmPreserved`/`withAlloc`) for
    `fromUtf8Ghost pl` under pure decidable `hpl : fromUtf8Block.Placeable pl`. -/
theorem fromUtf8Ghost_fromUtf8RowSpec {pl : Obj.Placement} (hpl : fromUtf8Block.Placeable pl) :
    FromUtf8RowSpec (fromUtf8Ghost pl) :=
  FromUtf8RowSpec.of_vm
    (fun stk => emptyFromUtf8GhostHook_ascii_ok (keepR_fromUtf8 pl) hpl stk)
    (fun stk => emptyFromUtf8GhostHook_asciiRO_ok (keepR_fromUtf8 pl) hpl stk)
    (fromUtf8Ghost_vmPreserved hpl)

/-- **Artifact 1 (`C11` §1.2, §6.1):** `GhostRowSpecOk lsFromUtf8Sym (fromUtf8Ghost pl)` under pure
    decidable `hpl : fromUtf8Block.Placeable pl` (`0` runtime/state/memory/`W` premises). -/
theorem fromUtf8Ghost_rowSpecOk [LibsignalPlacement] {pl : Obj.Placement} (hpl : fromUtf8Block.Placeable pl) :
    GhostRowSpecOk lsFromUtf8Sym (fromUtf8Ghost pl) where
  fs_eq := fromUtf8Ghost_fs pl
  fsT := fromUtf8Ghost_fsT pl
  rowSpec := by
    change ExtraRowSpec lsFromUtf8Sym (fromUtf8Ghost pl)
    simpa [ExtraRowSpec, lsFromUtf8Sym] using fromUtf8Ghost_fromUtf8RowSpec hpl

/-- `MultiPlacement`-indexed `GhostRowSpecOk lsFromUtf8Sym` for `fromUtf8MplGhost`. -/
theorem fromUtf8MplGhost_rowSpecOk [LibsignalPlacement] (mpl mmpl : Obj.MultiPlacement) (tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false)
    (hpl : fromUtf8Block.Placeable (fromUtf8MplPlacement mpl tbl relax1)) :
    GhostRowSpecOk lsFromUtf8Sym (fromUtf8MplGhost mpl mmpl tbl relax1) :=
  fromUtf8Ghost_rowSpecOk hpl

/-! ## 3. `ExecFrozen` Preservation & `K`-Route `StepsVisitedIn` Helper -/

/-- `linkedCallHookG` preserves `ExecFrozen` unconditionally whenever `fallback` preserves
    `ExecFrozen`:
    - On `ActiveRealPre ∧ (Guard ∧ ActiveRealRun)`, `ActiveRealRun`'s witness carries
      `ExecFrozen sf.mem`;
    - On `ActiveRealPre ∧ ¬ (Guard ∧ ActiveRealRun)`, `(keepFsTrace fallback u).mem = (fallback u).mem`;
    - On `¬ ActiveRealPre`, `.mem = u.mem`. -/
theorem linkedCallHookG_preserves_execFrozen {α : Type}
    {Guard : State → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hfb : ∀ s : State, ExecFrozen s.mem → ExecFrozen (fallback s).mem)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback u).mem := by
  classical
  rw [linkedCallHookG_eq_conj]
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2.2).2.2.2.2
    · have hmem : (keepFsTrace fallback u).mem = (fallback u).mem := by
        cases u; rfl
      rw [hmem]
      exact hfb u hfr
  · exact hfr

/-- `realFromUtf8Fallback` preserves `m.perm` pointwise (`realFromUtf8Fallback_processFieldsPreserved`),
    so it preserves `ExecFrozen` unconditionally. -/
theorem realFromUtf8Fallback_preserves_execFrozen {s : State} (hfr : ExecFrozen s.mem) :
    ExecFrozen (realFromUtf8Fallback s).mem :=
  hfr.of_perm_eq (realFromUtf8Fallback_processFieldsPreserved s).2.2.2.2.2.2.2

theorem fromUtf8GhostHook_preserves_execFrozen
    (tbl : BitVec 64) (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (fromUtf8GhostHook tbl keep P_real P_sub entryTarget u).mem :=
  linkedCallHookG_preserves_execFrozen (fun _ hs => realFromUtf8Fallback_preserves_execFrozen hs) hfr

theorem fromUtf8GhostHookK_preserves_execFrozen
    (tbl : BitVec 64) (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (fromUtf8GhostHookK tbl keep P_real P_sub entryTarget u).mem :=
  linkedCallHookG_preserves_execFrozen (fun _ hs => realFromUtf8Fallback_preserves_execFrozen hs) hfr

theorem fromUtf8Ghost_preserves_execFrozen (pl : Obj.Placement) {u : State}
    (hfr : ExecFrozen u.mem) :
    ExecFrozen (fromUtf8Ghost pl u).mem :=
  fromUtf8GhostHook_preserves_execFrozen (pl.ρ coreUtf8CharWidthSym) (keepR_fromUtf8 pl)
    emptyStdProg (fromUtf8SubProg pl) pl.base hfr

theorem fromUtf8GhostK_preserves_execFrozen (pl : Obj.Placement) {u : State}
    (hfr : ExecFrozen u.mem) :
    ExecFrozen (fromUtf8GhostK pl u).mem :=
  fromUtf8GhostHookK_preserves_execFrozen (pl.ρ coreUtf8CharWidthSym) (keepR_fromUtf8 pl)
    emptyStdProg (fromUtf8SubProg pl) pl.base hfr

/-- `StepsVisitedIn` witness for `K`-narrowed `fromUtf8GhostHookK` (mirroring
    `FromUtf8Ghost.fromUtf8GhostHook_visitedIn`). -/
theorem fromUtf8GhostHookK_visitedIn
    {keep : BitVec 64 → Bool} {P_run P_sub : Program} {pl : Obj.Placement}
    (hpl : fromUtf8Block.Placeable pl)
    (hsvc_run : P_run.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords pl.base (fromUtf8PatchedWords pl)) {s0 : State}
    (hG : roTableGuard (pl.ρ coreUtf8CharWidthSym) corePlacedData1 s0)
    (hnoex : ∀ msg,
      (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base s0).status ≠
        .Exception msg)
    (hFr : ExecFrozen s0.mem) (hlr_out : keep (s0.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    h2fsgen_StepsVisitedIn keep P_run (s0.setPC pl.base)
        (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base s0) ∧
      ExecFrozen (fromUtf8GhostHookK (pl.ρ coreUtf8CharWidthSym) keep P_run P_sub pl.base s0).mem :=
  linkedCallHookG_visitedIn hsvc_run hsvc_sub hrun_no hsub_no
    (roTableGuard_stripS keep pl.base (pl.ρ coreUtf8CharWidthSym) corePlacedData1)
    (subroutine_ok_masterFromUtf8K_of_hasWords keep hpl hsub_no hwords)
    (specStripSInvariant_masterFromUtf8K keep) (specPreservesFsTrace_masterFromUtf8K keep)
    (masterFromUtf8K_pre_setPC keep) (masterFromUtf8K_outcome_setPC keep) hG
    (linkedCallHookG_activeRealPre_of_noException hnoex) hFr hlr_out hCodeSub

/-! ## 4. Generic-`InvS` `GhostRowReplayOn` (Artifact 2a) & Full `GhostRowOk` -/

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u
  dsimp only [State.setPC] at hpc ⊢
  subst hpc
  rfl

private theorem realProg617_svc (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard :=
  rfl

private theorem emptyStdProg_svc_eq : emptyStdProg.svc = Syscall.standard :=
  rfl

private theorem emptyStdProg_externAt (pc : BitVec 64) :
    emptyStdProg.externAt? pc = none :=
  rfl

/-- **Artifact 2a (`C11` §1.3, §6.2) — Generic-`InvS` `GhostRowReplayOn` for `lsFromUtf8Sym`:**
    - **F1 compliance:** `hRealHullNoExt` quantifies over `keepR_fromUtf8 pl pc = true` **only** on
      the de-hooked real program `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` (`N1`:
      post-Cutover-2). On `P_ghost`, `hGhostNoExtNe` strictly excludes
      `pc ≠ libsignalSessionLib.resolve mpl lsFromUtf8Sym`.
    - **H1 + `.rodata` compliance:** `hCL` supplies `(fromUtf8SubProg pl).CodeLoaded u.mem` and
      `hRo` supplies `RoDataAt u.mem (pl.ρ coreUtf8CharWidthSym) corePlacedData1` at the call state
      `u` from `InvS u` (never `s0.mem`). -/
theorem fromUtf8Ghost_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (pl : Obj.Placement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : fromUtf8Block.Placeable pl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsFromUtf8Sym = pl.base)
    (hCL : ∀ u : State, InvS u → (fromUtf8SubProg pl).CodeLoaded u.mem)
    (hRo : ∀ u : State, ExecFrozen u.mem → InvS u →
      RoDataAt u.mem (pl.ρ coreUtf8CharWidthSym) corePlacedData1)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsFromUtf8Sym) = some (fromUtf8Ghost pl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_fromUtf8 pl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_fromUtf8 pl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsFromUtf8Sym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsFromUtf8Sym (fromUtf8EntryGuard mpl) (fromUtf8Ghost pl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨fromUtf8Ghost_preserves_execFrozen pl hfr, fromUtf8Ghost_fs pl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    right
    have hRealStub :
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
          (libsignalSessionLib.resolve mpl lsFromUtf8Sym) = none := by
      rw [hTargetEq]
      exact hRealHullNoExt W (keepR_fromUtf8_entry pl)
    refine ⟨hRealStub, ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (fromUtf8SubProg pl).CodeLoaded u.mem := hCL u hInvU
    have hGhostBase :
        (cliProgExtPlacedAt mpl EG 617 W).externAt? pl.base =
          some (emptyFromUtf8GhostHook (keepR_fromUtf8 pl) pl) := by
      rw [← hTargetEq]
      exact hGhostAt W
    have hLrS0 : keepFromUtf8Block pl.base (s0.readReg64 .lr) = false := by
      rw [← hTargetEq]
      exact hEntry.1
    have hLrOut : keepR_fromUtf8 pl (u.readReg64 .lr) = false :=
      emptyFromUtf8GhostHook_keepLr_false_after_hook_of_outcome_post
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (keepR := keepR_fromUtf8 pl)
        (pl := pl)
        (keepCoversFromUtf8_keepFromUtf8Block pl.base)
        (fun _ hk hne => hGhostNoExtNe W hk (by rw [hTargetEq]; exact hne))
        (Or.inr hGhostBase)
        hLrS0
        hRetPc
        hNoExSf
        hNotHaltSf
        u
        hStepsAfter
        hrun
        (hCodeU.of_keepsFrozen hkf)
    have hCodeStrip :
        (fromUtf8SubProg pl).CodeLoaded (stripExecOutside (keepR_fromUtf8 pl) u.mem) :=
      fromUtf8SubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨hvis, hfr_fu⟩ :=
      fromUtf8GhostHook_visitedIn
        (keep := keepR_fromUtf8 pl)
        (P_run := emptyStdProg)
        (P_sub := fromUtf8SubProg pl)
        (pl := pl)
        hpl
        emptyStdProg_svc_eq
        (fromUtf8SubProg_svc pl)
        (fun pc _ => emptyStdProg_externAt pc)
        (fromUtf8SubProg_externAt_none pl)
        (fromUtf8SubProg_hasWords pl)
        (hRo u hfr hInvU)
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC pl.base) (fromUtf8Ghost pl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_fromUtf8 pl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc_eq.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC pl.base = u :=
      setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (fromUtf8Ghost pl u) hInvU hkf (fromUtf8Ghost_fs pl u)⟩

/-- `MultiPlacement`-indexed specialization of `fromUtf8Ghost_rowReplayOn`
    (`hTargetEq` discharged by `fromUtf8MplPlacement_base`, `.rodata` table address normalized to `tbl`). -/
theorem fromUtf8MplGhost_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement) (tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : fromUtf8Block.Placeable (fromUtf8MplPlacement mpl tbl relax1))
    (hCL : ∀ u : State, InvS u → (fromUtf8SubProg (fromUtf8MplPlacement mpl tbl relax1)).CodeLoaded u.mem)
    (hRo : ∀ u : State, ExecFrozen u.mem → InvS u → RoDataAt u.mem tbl corePlacedData1)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsFromUtf8Sym) =
          some (fromUtf8MplGhost mpl mmpl tbl relax1))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_fromUtf8Mpl mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_fromUtf8Mpl mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsFromUtf8Sym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsFromUtf8Sym (fromUtf8EntryGuard mpl)
      (fromUtf8MplGhost mpl mmpl tbl relax1) :=
  fromUtf8Ghost_rowReplayOn mpl mmpl (fromUtf8MplPlacement mpl tbl relax1) InvS EG hpl
    (fromUtf8MplPlacement_base mpl tbl relax1).symm hCL
    (fun u hfr hInv => by
      rw [fromUtf8MplPlacement_rho_table mpl tbl relax1]
      exact hRo u hfr hInv)
    hInvKeep hGhostAt
    (fun W {_} hk => hRealHullNoExt W (keepR_fromUtf8_mplPlacement mpl tbl relax1 ▸ hk))
    (fun W {_} hk hne => hGhostNoExtNe W (keepR_fromUtf8_mplPlacement mpl tbl relax1 ▸ hk) hne)

/-- `C4` interior-stub wrapper for `fromUtf8Ghost_rowReplayOn` (accepting split `hRealNone` at
    `stubPc` + `hInteriorGhost` with the `Or.inr` `TrapHook` interior-stub disjunct on
    `pc ≠ resolve mpl lsFromUtf8Sym`). -/
theorem fromUtf8Ghost_rowReplayOn_of_interior
    (mpl mmpl : Obj.MultiPlacement)
    (pl : Obj.Placement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : fromUtf8Block.Placeable pl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsFromUtf8Sym = pl.base)
    (hCL : ∀ u : State, InvS u → (fromUtf8SubProg pl).CodeLoaded u.mem)
    (hRo : ∀ u : State, ExecFrozen u.mem → InvS u →
      RoDataAt u.mem (pl.ρ coreUtf8CharWidthSym) corePlacedData1)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsFromUtf8Sym) = some (fromUtf8Ghost pl))
    (hRealNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsFromUtf8Sym) = none)
    (hInteriorGhost : ∀ (W : CliHooks) (pc : BitVec 64),
      keepR_fromUtf8 pl pc = true → pc ≠ libsignalSessionLib.resolve mpl lsFromUtf8Sym →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none ∧
      ((cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ gStub, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some gStub ∧
          ∀ L : BitVec 64, keepR_fromUtf8 pl L = true → TrapHook L gStub)) :
    GhostRowReplayOn mpl mmpl InvS EG lsFromUtf8Sym (fromUtf8EntryGuard mpl) (fromUtf8Ghost pl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨fromUtf8Ghost_preserves_execFrozen pl hfr, fromUtf8Ghost_fs pl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    have hRealHullNoExt : ∀ {pc : BitVec 64},
        keepR_fromUtf8 pl pc = true →
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl lsFromUtf8Sym
      · rw [hEq]; exact hRealNone W
      · exact (hInteriorGhost W pc hk hEq).1
    have hRegExt : ∀ pc : BitVec 64, keepFromUtf8Block pl.base pc = true →
        (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
          ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
            ∀ L : BitVec 64, keepFromUtf8Block pl.base L = true → TrapHook L f := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl lsFromUtf8Sym
      · rw [hEq]
        exact Or.inr ⟨fromUtf8Ghost pl, hGhostAt W, fun _ hL =>
          trapHook_emptyFromUtf8GhostHook_of_cover pl
            (keepCoversFromUtf8_keepFromUtf8Block pl.base) hL⟩
      · rcases (hInteriorGhost W pc hk hEq).2 with hNone | ⟨gStub, hSome, hTrap⟩
        · exact Or.inl hNone
        · exact Or.inr ⟨gStub, hSome, hTrap⟩
    right
    refine ⟨hRealNone W, ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (fromUtf8SubProg pl).CodeLoaded u.mem := hCL u hInvU
    have hLrS0 : keepFromUtf8Block pl.base (s0.readReg64 .lr) = false := by
      rw [← hTargetEq]
      exact hEntry.1
    have hLrOut : keepR_fromUtf8 pl (u.readReg64 .lr) = false :=
      fromUtf8_keepLr_false_after_hook_of_outcome_post
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_sub := fromUtf8SubProg pl)
        (pl := pl)
        (f_stub := fromUtf8Ghost pl)
        (fromUtf8SubProg_hasWords pl)
        hRegExt
        (fun _ hL => trapHook_emptyFromUtf8GhostHook_of_cover pl
          (keepCoversFromUtf8_keepFromUtf8Block pl.base) hL)
        hLrS0
        hRetPc
        hNoExSf
        hNotHaltSf
        u
        hStepsAfter
        hrun
        (hCodeU.of_keepsFrozen hkf)
    have hCodeStrip :
        (fromUtf8SubProg pl).CodeLoaded (stripExecOutside (keepR_fromUtf8 pl) u.mem) :=
      fromUtf8SubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨hvis, hfr_fu⟩ :=
      fromUtf8GhostHook_visitedIn
        (keep := keepR_fromUtf8 pl)
        (P_run := emptyStdProg)
        (P_sub := fromUtf8SubProg pl)
        (pl := pl)
        hpl
        emptyStdProg_svc_eq
        (fromUtf8SubProg_svc pl)
        (fun pc _ => emptyStdProg_externAt pc)
        (fromUtf8SubProg_externAt_none pl)
        (fromUtf8SubProg_hasWords pl)
        (hRo u hfr hInvU)
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC pl.base) (fromUtf8Ghost pl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_fromUtf8 pl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc_eq.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt hk)
        hvis
    have hSetPC : u.setPC pl.base = u :=
      setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (fromUtf8Ghost pl u) hInvU hkf (fromUtf8Ghost_fs pl u)⟩

/-- `K`-narrowed `fromUtf8GhostK` spare `GhostRowReplayOn` (`entryGuard := fun _ => True`;
    note `N2`: spare only, no `GhostRowSpecOk` partner). -/
theorem fromUtf8GhostK_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (pl : Obj.Placement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : fromUtf8Block.Placeable pl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsFromUtf8Sym = pl.base)
    (hCL : ∀ u : State, InvS u → (fromUtf8SubProg pl).CodeLoaded u.mem)
    (hRo : ∀ u : State, ExecFrozen u.mem → InvS u →
      RoDataAt u.mem (pl.ρ coreUtf8CharWidthSym) corePlacedData1)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_fromUtf8 pl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsFromUtf8Sym (fun _ => True) (fromUtf8GhostK pl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨fromUtf8GhostK_preserves_execFrozen pl hfr, emptyFromUtf8GhostHookK_fs (keepR_fromUtf8 pl) pl u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    have hRealStub :
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
          (libsignalSessionLib.resolve mpl lsFromUtf8Sym) = none := by
      rw [hTargetEq]
      exact hRealHullNoExt W (keepR_fromUtf8_entry pl)
    refine ⟨hRealStub, ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hCodeStrip :
        (fromUtf8SubProg pl).CodeLoaded (stripExecOutside (keepR_fromUtf8 pl) u.mem) :=
      fromUtf8SubProg_codeLoaded_stripExecOutside (hCL u hInvU)
    have hLrOut : keepR_fromUtf8 pl (u.readReg64 .lr) = false :=
      fromUtf8GhostHookK_keepLr_false_of_noException hnoex
    obtain ⟨hvis, hfr_fu⟩ :=
      fromUtf8GhostHookK_visitedIn
        (keep := keepR_fromUtf8 pl)
        (P_run := emptyStdProg)
        (P_sub := fromUtf8SubProg pl)
        (pl := pl)
        hpl
        emptyStdProg_svc_eq
        (fromUtf8SubProg_svc pl)
        (fun pc _ => emptyStdProg_externAt pc)
        (fromUtf8SubProg_externAt_none pl)
        (fromUtf8SubProg_hasWords pl)
        (hRo u hfr hInvU)
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC pl.base) (fromUtf8GhostK pl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_fromUtf8 pl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc_eq.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC pl.base = u :=
      setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu,
      hInvKeep u (fromUtf8GhostK pl u) hInvU hkf (emptyFromUtf8GhostHookK_fs (keepR_fromUtf8 pl) pl u)⟩

/-- Guard-strengthening adapter on `GhostRowReplayOn` (for `ExtraListReplaysOn` when `guardOf sym`
    implies `entryGuard`). -/
theorem ghostRowReplayOn_of_guard_imp
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {sym : String} {entryGuard guard' : State → Prop} {f : State → State}
    (hRow : GhostRowReplayOn mpl mmpl InvS EG sym entryGuard f)
    (hImp : ∀ s0 : State, guard' s0 → entryGuard s0) :
    GhostRowReplayOn mpl mmpl InvS EG sym guard' f where
  preserves_execFrozen := hRow.preserves_execFrozen
  replay_at_stub := fun W s0 sf hG hRet hNoEx hNHalt =>
    hRow.replay_at_stub W s0 sf (hImp s0 hG) hRet hNoEx hNHalt

/-- Full per-row `GhostRowOk` bundle (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) for `lsFromUtf8Sym`. -/
theorem fromUtf8Ghost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (pl : Obj.Placement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : fromUtf8Block.Placeable pl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsFromUtf8Sym = pl.base)
    (hCL : ∀ u : State, InvS u → (fromUtf8SubProg pl).CodeLoaded u.mem)
    (hRo : ∀ u : State, ExecFrozen u.mem → InvS u →
      RoDataAt u.mem (pl.ρ coreUtf8CharWidthSym) corePlacedData1)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsFromUtf8Sym) = some (fromUtf8Ghost pl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_fromUtf8 pl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_fromUtf8 pl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsFromUtf8Sym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl InvS EG lsFromUtf8Sym (fromUtf8EntryGuard mpl) (fromUtf8Ghost pl) :=
  ⟨fromUtf8Ghost_rowSpecOk hpl,
   fromUtf8Ghost_rowReplayOn mpl mmpl pl InvS EG hpl hTargetEq hCL hRo hInvKeep hGhostAt
     hRealHullNoExt hGhostNoExtNe⟩

/-- `MultiPlacement`-indexed full `GhostRowOk` bundle for `fromUtf8MplGhost`. -/
theorem fromUtf8MplGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (tbl : BitVec 64)
    (relax1 : Nat → Bool := fun _ => false)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : fromUtf8Block.Placeable (fromUtf8MplPlacement mpl tbl relax1))
    (hCL : ∀ u : State, InvS u → (fromUtf8SubProg (fromUtf8MplPlacement mpl tbl relax1)).CodeLoaded u.mem)
    (hRo : ∀ u : State, ExecFrozen u.mem → InvS u → RoDataAt u.mem tbl corePlacedData1)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsFromUtf8Sym) =
          some (fromUtf8MplGhost mpl mmpl tbl relax1))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_fromUtf8Mpl mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_fromUtf8Mpl mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsFromUtf8Sym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl InvS EG lsFromUtf8Sym (fromUtf8EntryGuard mpl)
      (fromUtf8MplGhost mpl mmpl tbl relax1) :=
  ⟨fromUtf8MplGhost_rowSpecOk mpl mmpl tbl relax1 hpl,
   fromUtf8MplGhost_rowReplayOn mpl mmpl tbl relax1 InvS EG hpl hCL hRo hInvKeep hGhostAt
     hRealHullNoExt hGhostNoExtNe⟩

/-! ## 5. Per-Arm & Singleton `ExtraEntryGuard` Helpers (`ccard_recipe.md` §2.1, `N3`) -/

/-- Per-arm `lsFromUtf8Sym` discharge for any `guardOf : String → State → Prop` agreeing with
    `fromUtf8EntryGuard mpl` on `lsFromUtf8Sym`. -/
theorem extraEntryGuard_fromUtf8_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf lsFromUtf8Sym s0 ↔ fromUtf8EntryGuard mpl s0)
    (hGuard : fromUtf8EntryGuard mpl s0) :
    guardOf lsFromUtf8Sym s0 :=
  hGuardEq.mpr hGuard

/-- Table-level `ExtraEntryGuard guardOf g s0` discharge when `g.extra` carries the singleton
    `lsFromUtf8Sym` row `[(lsFromUtf8Sym, fRow)]` (`N3`: 1-row helper; multi-row C2 tables assemble
    `ExtraListEntryGuard` from `extraEntryGuard_fromUtf8_arm`). -/
theorem extraEntryGuard_singleton_fromUtf8
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {fRow : State → State} {s0 : State}
    (hg : g.extra = [(lsFromUtf8Sym, fRow)])
    (hGuardEq : guardOf lsFromUtf8Sym s0 ↔ fromUtf8EntryGuard mpl s0)
    (hGuard : fromUtf8EntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 := by
  intro sym f _ hLook
  rw [hg] at hLook
  simp only [List.lookup] at hLook
  by_cases hSym : (sym == lsFromUtf8Sym) = true
  · have hEq : sym = lsFromUtf8Sym := eq_of_beq hSym
    subst hEq
    exact hGuardEq.mpr hGuard
  · simp [hSym] at hLook

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays
