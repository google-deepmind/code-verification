/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrapBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemmoveRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Card CC-MEMMOVE (`memmove`) — `"memmove"` `CliGhostHooks.extra` Specs, `GhostRowSpecOk`, `GhostRowReplayOn`, & `GhostRowOk` (`HooksDehook.MemmoveExtraReplays`)

Cutover-2 `c`-card assembly for the `libc.a` `"memmove"` row over the `239`-word (`956` B)
`.text.b_pre` hull `bPreHullWords` (`memcpy` at `m := resolve mpl "memcpy"`, 1-word `0#32` pad at
`m + 396`, `memset` at `m + 400`, `memmove` at `m + 660`), leaving the GO'd
`HooksDehook.MemmoveGhostReplays` module completely untouched:

1. **`.text.b_pre` Hull Carrier, `keepR_memmove`, `W`-Independent `memmoveGhost`, & `GhostRowSpecOk` (`§1`–`§2`):**
   - Defines `memcpyEntry mpl := libsignalSessionLib.resolve mpl "memcpy"`,
     `memmoveEntry mpl := libsignalSessionLib.resolve mpl "memmove"`,
     `keepR_memmove mpl := keepBPreHull (memcpyEntry mpl)`,
     `memmoveHullWords mpl := bPreHullWords (memcpyEntry mpl) (libsignalSessionLib.resolve mpl) bPrePadWord`,
     `memmoveSubProg mpl := pureWordsProg (memcpyEntry mpl) (memmoveHullWords mpl)`, and
     `memmoveGhost mpl _mmpl := f3EmptyMemmoveGhostHook (keepR_memmove mpl) (memmoveSubProg mpl)
       (memcpyEntry mpl + bPreMemmoveByteOff)` (`W`-free: `P_real := emptyStdProg`,
       `fallback := hookMemmove`, definitionally equal to `f3PureMemmoveGhostHook`).
   - Proves **unconditional** (`0` layout or memory premises) `memmoveGhost_vmPreserved`,
     `memmoveGhost_allocCallPreserved`, `memmoveGhost_fs`, `memmoveGhost_fsT`, all `#1348`
     `*BoundedSpec` `HookOk` arms (`libcMemmoveBoundedSpec`, `sessionMemmoveBoundedSpec`,
     `sessionMemmoveBoundedBudgetSpec`, `withVmPreserved`, and `withAlloc`),
     `memmoveGhost_memmoveRowSpec`, and **`memmoveGhost_rowSpecOk`**
     (`GhostRowSpecOk "memmove" (memmoveGhost mpl mmpl)` against the `CC-ROWSPEC` narrowed
     `MemmoveRowSpec`).
2. **3-Entry `.text.b_pre` Hull & Interior-`TrapHook` `GhostRowReplayOn` & `GhostRowOk` (`§3`):**
   - Proves `memmoveGhost_rowReplayOn`, `memmoveGhost_rowOk`,
     `memmoveGhost_rowReplayOn_of_interior`, and `memmoveGhost_rowOk_of_interior` over arbitrary
     `InvS : State → Prop` using L3-d `MemmoveLrTrap`'s `hother`-free 3-entry `.text.b_pre` hull
     (`["memmove", "memcpy", "memset"]`) `C4`+`F1`+`H1` closed-`lr` trap
     (`bPreHull_keepLr_false_after_hook_of_codeLoaded_u` + `bPreHull_reg_ext_forall_of_entries`),
     matching verbatim the premise shapes of `Lib2LayoutFacts.lean @ a230f2671b:392-402, :355-362`
     (`f3RowSyms_ghostProg617_externAt_none_of_ne_entries` and `f3RxSeg_ghostProg617_externAt_entry`),
     plus the `K`-narrowed spare `memmoveGhostK_rowReplayOn`.

## Scope Disclosures (`REV-PILOT` N1–N3 + `L3-d`)
- **N1 (post-Cutover-2 only):** `hRealHullNoExt` (and `hRealRxNoExt` in `ElfMemmoveEntryGuard`)
  requires `"memmove"` (alongside Stage A `"memcpy"` / `"memset"`) to be removed from
  `cliHookTablePlaced` (`C2ExternTableFacts.realRxNoExtern`, `Lib2LayoutFacts.lean @ a230f2671b:317`,
  discharged by `rfl_kernel` at C2 rebase). On pre-cutover `train`, `"memmove"` is still hooked on
  `P_real`, so the replay arm is usable only post-Cutover-2.
- **N2 (`K` replay has no spec partner):** `memmoveGhostK_rowReplayOn` is honest, but no
  `GhostRowSpecOk "memmove" (memmoveGhostK …)` exists because `*BoundedSpec.pre` has no
  `lr ∉ keepR_memmove` conjunct while `memmoveGhostK` raises `.Exception` when
  `lr ∈ keepR_memmove`. The usable `ExtraListOk` / `GhostRowOk` route for `"memmove"` is the
  guarded `memmoveGhost` + `memmoveEntryGuard`; `memmoveGhostK` replays are spares only.
- **N3 (singleton helper covers 1 row):** `ElfMemmoveEntryGuard.extraEntryGuard_singleton_memmove`
  covers `g.extra = [("memmove", memmoveGhost mpl mmpl)]` only. At Cutover 2, the multi-row
  `g.extra` table assembles `ExtraListEntryGuard` from per-arm `extraEntryGuard_memmove_arm`
  helpers across all active rows.
- **L3-d (`hother`-free multi-ghost route vs. single-stub `MemmoveGhostReplays`):** The earlier
  GO'd `MemmoveGhostReplays` single-stub packagers retain single-stub `hother`, whereas
  `MemmoveExtraReplays` and `ElfMemmoveEntryGuard` build strictly on L3-d `MemmoveLrTrap`'s
  `hother`-free 3-entry (`["memmove", "memcpy", "memset"]`) `C4`+`F1`+`H1` corollaries.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
  (libcMemmoveBoundedSpec sessionMemmoveBoundedBudgetSpec sessionMemmoveBoundedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (
  GhostRowOk GhostRowReplayOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode (
  bPreHullWords bPreHullWords_length bPreMemmoveByteOff bPrePadWord
  masterMemmoveSpec memmoveSpecK pureWordsProg_bPreHull_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost (
  keepBPreHull keepBPreHull_memmoveEntry
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostK (
  f3EmptyMemmoveGhostHook f3EmptyMemmoveGhostHookK
  f3EmptyMemmoveGhostHook_allocCallPreserved
  f3EmptyMemmoveGhostHook_fs f3EmptyMemmoveGhostHook_fsT
  f3EmptyMemmoveGhostHook_libcBounded_budget_ok f3EmptyMemmoveGhostHook_libcBounded_ok
  f3EmptyMemmoveGhostHook_libcBounded_withAlloc_ok
  f3EmptyMemmoveGhostHook_master_ok
  f3EmptyMemmoveGhostHook_sessionBoundedBudget_ok
  f3EmptyMemmoveGhostHook_sessionBoundedBudget_withAlloc_ok
  f3EmptyMemmoveGhostHook_sessionBounded_ok
  f3EmptyMemmoveGhostHook_sessionBounded_withAlloc_ok
  f3EmptyMemmoveGhostHook_vmPreserved
  f3EmptyMemmoveGhostHookK_fs f3EmptyMemmoveGhostHookK_fsT
  f3EmptyMemmoveGhostHookK_masterK_ok f3EmptyMemmoveGhostHookK_vmPreserved
  f3PureMemmoveGhostHook f3PureMemmoveGhostHookK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostReplays (
  f3EmptyMemmoveGhostHook_visitedIn f3EmptyMemmoveGhostHookK_visitedIn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrap (
  bPreHull_keepLr_false_after_hook_of_codeLoaded_u bPreHull_reg_ext_forall_of_entries
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrapBase (
  MemmoveEntryGuard bPreHullByteLen codeLoaded_of_stripExecOutside
  trapHook_f3EmptyMemmoveGhostHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (
  TrapHook codeLoaded_stripExecOutside_of_keep
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (
  ExtraRowSpec GhostRowSpecOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemmoveRowSpec (
  MemmoveRowSpec
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_steps_lift_of_visitedIn_noExtern
)

/-! ## 1. `.text.b_pre` Hull Carrier, `keepR_memmove`, & `W`-Independent `memmoveGhost` -/

/-- Base address of the `956` B `.text.b_pre` hull (`libsignalSessionLib.resolve mpl "memcpy"`). -/
@[expose] def memcpyEntry (mpl : Obj.MultiPlacement) : BitVec 64 :=
  libsignalSessionLib.resolve mpl "memcpy"

/-- Resolved `"memmove"` symbol address (`= memcpyEntry mpl + bPreMemmoveByteOff` on C2 `2C`). -/
@[expose] def memmoveEntry (mpl : Obj.MultiPlacement) : BitVec 64 :=
  libsignalSessionLib.resolve mpl "memmove"

/-- `956` B (`239`-word) `.text.b_pre` hull code-region predicate `[memcpyEntry mpl, +956)`. -/
@[expose] def keepR_memmove (mpl : Obj.MultiPlacement) : BitVec 64 → Bool :=
  keepBPreHull (memcpyEntry mpl)

/-- `239`-word `.text.b_pre` hull word list patched against `libsignalSessionLib.resolve mpl`. -/
@[expose] def memmoveHullWords (mpl : Obj.MultiPlacement) : List (BitVec 32) :=
  bPreHullWords (memcpyEntry mpl) (libsignalSessionLib.resolve mpl) bPrePadWord

/-- Pure `239`-word `.text.b_pre` sub-program anchored at `memcpyEntry mpl`. -/
@[expose] def memmoveSubProg (mpl : Obj.MultiPlacement) : Program :=
  pureWordsProg (memcpyEntry mpl) (memmoveHullWords mpl)

theorem memmoveHullWords_length (mpl : Obj.MultiPlacement) :
    (memmoveHullWords mpl).length = 239 :=
  bPreHullWords_length (memcpyEntry mpl) (libsignalSessionLib.resolve mpl) bPrePadWord

theorem memmoveSubProg_base (mpl : Obj.MultiPlacement) :
    (memmoveSubProg mpl).base = memcpyEntry mpl := by
  dsimp only [memmoveSubProg, pureWordsProg, Program.ofWords]

theorem memmoveSubProg_svc (mpl : Obj.MultiPlacement) :
    (memmoveSubProg mpl).svc = Syscall.standard := by
  dsimp only [memmoveSubProg, pureWordsProg, Program.ofWords]

theorem memmoveSubProg_externAt_none (mpl : Obj.MultiPlacement) (pc : BitVec 64) :
    (memmoveSubProg mpl).externAt? pc = none :=
  pureWordsProg_externAt_none (memcpyEntry mpl) (memmoveHullWords mpl) pc

theorem memmoveSubProg_code_length (mpl : Obj.MultiPlacement) :
    (memmoveSubProg mpl).code.length = bPreHullByteLen := by
  have hwlen := memmoveHullWords_length mpl
  change ((memmoveHullWords mpl).flatMap Program.wordToBytesLE).length = 956
  have hflat : ∀ ws : List (BitVec 32), (ws.flatMap Program.wordToBytesLE).length = 4 * ws.length := by
    intro ws
    induction ws with
    | nil => rfl
    | cons _ tl ih =>
      simp [Program.wordToBytesLE, ih]
      omega
  rw [hflat, hwlen]

theorem memmoveSubProg_hasWords (mpl : Obj.MultiPlacement) :
    (memmoveSubProg mpl).hasWords (memcpyEntry mpl) (memmoveHullWords mpl) :=
  pureWordsProg_bPreHull_hasWords (memcpyEntry mpl) (libsignalSessionLib.resolve mpl) bPrePadWord

theorem resolve_memcpy_eq_memcpyEntry (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl "memcpy" = memcpyEntry mpl := by
  dsimp only [memcpyEntry]

theorem keepR_memmove_target (mpl : Obj.MultiPlacement) :
    keepR_memmove mpl (memcpyEntry mpl + bPreMemmoveByteOff) = true :=
  keepBPreHull_memmoveEntry (memcpyEntry mpl)

theorem keepR_memmove_entry {mpl : Obj.MultiPlacement}
    (hMemmoveOff : memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff) :
    keepR_memmove mpl (memmoveEntry mpl) = true := by
  rw [hMemmoveOff]
  exact keepR_memmove_target mpl

theorem keepR_memmove_of_code_offset {mpl : Obj.MultiPlacement} {i : Nat}
    (hi : i < (memmoveSubProg mpl).code.length) :
    keepR_memmove mpl ((memmoveSubProg mpl).base + BitVec.ofNat 64 i) = true := by
  rw [memmoveSubProg_code_length] at hi
  rw [memmoveSubProg_base]
  dsimp only [keepR_memmove, keepBPreHull, TrapSafeWords.keepBlock, bPreHullByteLen] at hi ⊢
  have hsub : (memcpyEntry mpl + BitVec.ofNat 64 i) - memcpyEntry mpl = BitVec.ofNat 64 i := by
    bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact decide_eq_true hi

theorem memmoveSubProg_codeLoaded_stripExecOutside {mpl : Obj.MultiPlacement} {m : Memory}
    (hCL : (memmoveSubProg mpl).CodeLoaded m) :
    (memmoveSubProg mpl).CodeLoaded (stripExecOutside (keepR_memmove mpl) m) :=
  codeLoaded_stripExecOutside_of_keep (fun _ hi => keepR_memmove_of_code_offset hi) hCL

theorem memmoveSubProg_codeLoaded_of_stripExecOutside {mpl : Obj.MultiPlacement} {m : Memory}
    (hCL : (memmoveSubProg mpl).CodeLoaded (stripExecOutside (keepR_memmove mpl) m)) :
    (memmoveSubProg mpl).CodeLoaded m :=
  codeLoaded_of_stripExecOutside hCL

theorem memmoveSubProg_codeLoaded_stripExecOutside_iff (mpl : Obj.MultiPlacement) (m : Memory) :
    (memmoveSubProg mpl).CodeLoaded (stripExecOutside (keepR_memmove mpl) m) ↔
      (memmoveSubProg mpl).CodeLoaded m :=
  ⟨memmoveSubProg_codeLoaded_of_stripExecOutside, memmoveSubProg_codeLoaded_stripExecOutside⟩

/-- Canonical `W`-independent ghost `"memmove"` hook for `CliGhostHooks.extra`. -/
@[expose] noncomputable def memmoveGhost (mpl _mmpl : Obj.MultiPlacement) : State → State :=
  f3EmptyMemmoveGhostHook (keepR_memmove mpl) (memmoveSubProg mpl)
    (memcpyEntry mpl + bPreMemmoveByteOff)

/-- `K`-narrowed companion ghost `"memmove"` hook (`lr ∉ keepR_memmove` enforced in `pre`). -/
@[expose] noncomputable def memmoveGhostK (mpl _mmpl : Obj.MultiPlacement) : State → State :=
  f3EmptyMemmoveGhostHookK (keepR_memmove mpl) (memmoveSubProg mpl)
    (memcpyEntry mpl + bPreMemmoveByteOff)

theorem memmoveGhost_eq_f3Pure (mpl mmpl : Obj.MultiPlacement) :
    memmoveGhost mpl mmpl =
      f3PureMemmoveGhostHook (keepR_memmove mpl) (memcpyEntry mpl)
        (libsignalSessionLib.resolve mpl) bPrePadWord := by
  dsimp only [memmoveGhost, f3PureMemmoveGhostHook, memmoveSubProg, memmoveHullWords]

theorem memmoveGhostK_eq_f3Pure (mpl mmpl : Obj.MultiPlacement) :
    memmoveGhostK mpl mmpl =
      f3PureMemmoveGhostHookK (keepR_memmove mpl) (memcpyEntry mpl)
        (libsignalSessionLib.resolve mpl) bPrePadWord := by
  dsimp only [memmoveGhostK, f3PureMemmoveGhostHookK, memmoveSubProg, memmoveHullWords]

/-- Entry-state `lr` guard for `memmoveGhost` on Block `617`: `s0.lr` is outside the `956` B
    `.text.b_pre` hull and unequal to the `"memmove"` entry (`rfl`-matching
    `MemmoveLrTrapBase.MemmoveEntryGuard` and `Lib2LayoutFacts.f3BatchLEntryGuard_of_startupLr`). -/
@[expose] def memmoveEntryGuard (mpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  keepR_memmove mpl (s0.readReg64 .lr) = false ∧
    s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl "memmove"

theorem memmoveEntryGuard_iff (mpl : Obj.MultiPlacement) (s0 : State) :
    memmoveEntryGuard mpl s0 ↔
      (keepR_memmove mpl (s0.readReg64 .lr) = false ∧
        s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl "memmove") :=
  Iff.rfl

theorem memmoveEntryGuard_eq_base (mpl : Obj.MultiPlacement) (s0 : State) :
    memmoveEntryGuard mpl s0 = MemmoveEntryGuard (memcpyEntry mpl) (memmoveEntry mpl) s0 := by
  dsimp only [memmoveEntryGuard, MemmoveEntryGuard, keepR_memmove, memmoveEntry]

theorem memmoveEntryGuard_of_keepR_false {mpl : Obj.MultiPlacement} {s0 : State}
    (hMemmoveOff : memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff)
    (h : keepR_memmove mpl (s0.readReg64 .lr) = false) :
    memmoveEntryGuard mpl s0 := by
  refine ⟨h, fun hEq => ?_⟩
  have hIn : keepR_memmove mpl (s0.readReg64 .lr) = true := by
    rw [hEq]
    exact keepR_memmove_entry hMemmoveOff
  cases h.symm.trans hIn

/-! ## 2. Unconditional `#1348` Bounded `HookOk` Suite (`0` Layout or Memory Premises) -/

theorem memmoveGhost_fs (mpl mmpl : Obj.MultiPlacement) (s : State) :
    (memmoveGhost mpl mmpl s).fs = s.fs :=
  f3EmptyMemmoveGhostHook_fs (keepR_memmove mpl) (memmoveSubProg mpl)
    (memcpyEntry mpl + bPreMemmoveByteOff) s

theorem memmoveGhost_fsT (mpl mmpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (memmoveGhost mpl mmpl) :=
  f3EmptyMemmoveGhostHook_fsT (keepR_memmove mpl) (memmoveSubProg mpl)
    (memcpyEntry mpl + bPreMemmoveByteOff)

theorem memmoveGhostK_fs (mpl mmpl : Obj.MultiPlacement) (s : State) :
    (memmoveGhostK mpl mmpl s).fs = s.fs :=
  f3EmptyMemmoveGhostHookK_fs (keepR_memmove mpl) (memmoveSubProg mpl)
    (memcpyEntry mpl + bPreMemmoveByteOff) s

theorem memmoveGhostK_fsT (mpl mmpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (memmoveGhostK mpl mmpl) :=
  f3EmptyMemmoveGhostHookK_fsT (keepR_memmove mpl) (memmoveSubProg mpl)
    (memcpyEntry mpl + bPreMemmoveByteOff)

theorem memmoveGhost_vmPreserved (mpl mmpl : Obj.MultiPlacement) (s : State) :
    VmPreserved s (memmoveGhost mpl mmpl s) :=
  f3EmptyMemmoveGhostHook_vmPreserved (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl) s

theorem memmoveGhostK_vmPreserved (mpl mmpl : Obj.MultiPlacement) (s : State) :
    VmPreserved s (memmoveGhostK mpl mmpl s) :=
  f3EmptyMemmoveGhostHookK_vmPreserved (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl) s

theorem memmoveGhost_allocCallPreserved (mpl mmpl : Obj.MultiPlacement) (s : State) :
    AllocCallPreserved s (memmoveGhost mpl mmpl s) :=
  f3EmptyMemmoveGhostHook_allocCallPreserved (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl) s

theorem memmoveGhost_master_ok (mpl mmpl : Obj.MultiPlacement) :
    HookOk (memmoveGhost mpl mmpl) masterMemmoveSpec :=
  f3EmptyMemmoveGhostHook_master_ok (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl)

theorem memmoveGhostK_masterK_ok (mpl mmpl : Obj.MultiPlacement) :
    HookOk (memmoveGhostK mpl mmpl) (memmoveSpecK (keepR_memmove mpl) masterMemmoveSpec) :=
  f3EmptyMemmoveGhostHookK_masterK_ok (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl)

theorem memmoveGhost_libcBounded_ok (mpl mmpl : Obj.MultiPlacement) (stk : Nat) :
    HookOk (memmoveGhost mpl mmpl) (libcMemmoveBoundedSpec stk) :=
  f3EmptyMemmoveGhostHook_libcBounded_ok (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl) stk

theorem memmoveGhost_libcBounded_budget_ok (mpl mmpl : Obj.MultiPlacement) (stk : Nat) :
    HookOk (memmoveGhost mpl mmpl) (withVmPreserved (libcMemmoveBoundedSpec stk)) :=
  f3EmptyMemmoveGhostHook_libcBounded_budget_ok (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl) stk

theorem memmoveGhost_libcBounded_withAlloc_ok (mpl mmpl : Obj.MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk (memmoveGhost mpl mmpl) (withAlloc A lim (libcMemmoveBoundedSpec stk)) :=
  f3EmptyMemmoveGhostHook_libcBounded_withAlloc_ok (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl) A lim stk

theorem memmoveGhost_sessionBounded_ok (mpl mmpl : Obj.MultiPlacement) (stk : Nat) :
    HookOk (memmoveGhost mpl mmpl) (sessionMemmoveBoundedSpec stk) :=
  f3EmptyMemmoveGhostHook_sessionBounded_ok (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl) stk

theorem memmoveGhost_sessionBoundedBudget_ok (mpl mmpl : Obj.MultiPlacement) (stk : Nat) :
    HookOk (memmoveGhost mpl mmpl) (sessionMemmoveBoundedBudgetSpec stk) :=
  f3EmptyMemmoveGhostHook_sessionBoundedBudget_ok (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl) stk

theorem memmoveGhost_sessionBounded_withAlloc_ok (mpl mmpl : Obj.MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk (memmoveGhost mpl mmpl) (withAlloc A lim (sessionMemmoveBoundedSpec stk)) :=
  f3EmptyMemmoveGhostHook_sessionBounded_withAlloc_ok (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl) A lim stk

theorem memmoveGhost_sessionBoundedBudget_withAlloc_ok (mpl mmpl : Obj.MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk (memmoveGhost mpl mmpl) (withAlloc A lim (sessionMemmoveBoundedBudgetSpec stk)) :=
  f3EmptyMemmoveGhostHook_sessionBoundedBudget_withAlloc_ok (memmoveSubProg_svc mpl)
    (memmoveSubProg_externAt_none mpl) (memmoveSubProg_hasWords mpl)
    (resolve_memcpy_eq_memcpyEntry mpl) A lim stk

theorem memmoveGhost_memmoveRowSpec (mpl mmpl : Obj.MultiPlacement) :
    MemmoveRowSpec (memmoveGhost mpl mmpl) :=
  MemmoveRowSpec.of_vm
    (memmoveGhost_libcBounded_ok mpl mmpl)
    (memmoveGhost_sessionBounded_ok mpl mmpl)
    (memmoveGhost_vmPreserved mpl mmpl)
    (memmoveGhost_allocCallPreserved mpl mmpl)

/-- Complete `GhostRowSpecOk "memmove" (memmoveGhost mpl mmpl)` (`0` layout or memory premises). -/
theorem memmoveGhost_rowSpecOk [LibsignalPlacement] (mpl mmpl : Obj.MultiPlacement) :
    GhostRowSpecOk "memmove" (memmoveGhost mpl mmpl) where
  fs_eq := memmoveGhost_fs mpl mmpl
  fsT := memmoveGhost_fsT mpl mmpl
  rowSpec := by
    change ExtraRowSpec "memmove" (memmoveGhost mpl mmpl)
    simpa [ExtraRowSpec] using memmoveGhost_memmoveRowSpec mpl mmpl

/-! ## 3. `ExecFrozen` Preservation, 3-Entry `.text.b_pre` `GhostRowReplayOn`, `GhostRowOk`, & `K` Spare -/

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (h : u.pc = pc) :
    u.setPC pc = u := by
  cases u
  simp_all [State.setPC]

private theorem realProg617_svc (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard :=
  rfl

private theorem emptyStdProg_svc : emptyStdProg.svc = Syscall.standard :=
  rfl

private theorem emptyStdProg_externAt (pc : BitVec 64) :
    emptyStdProg.externAt? pc = none :=
  rfl

theorem memmoveGhost_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (memmoveGhost mpl mmpl u).mem :=
  hfr.of_perm_eq (memmoveGhost_vmPreserved mpl mmpl u).2.2.1

theorem memmoveGhostK_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (memmoveGhostK mpl mmpl u).mem :=
  hfr.of_perm_eq (memmoveGhostK_vmPreserved mpl mmpl u).2.2.1

/-- Generic-`InvS` `GhostRowReplayOn` for `memmoveGhost` over the 3-entry `.text.b_pre` hull
    (`["memmove", "memcpy", "memset"]`), consuming L3-d's `hother`-free corollaries and matching
    verbatim the 3-entry premise shapes of `Lib2LayoutFacts.lean @ a230f2671b:392-402, :355-362`:
    - `hGhostOffEntries`: `f3RowSyms_ghostProg617_externAt_none_of_ne_entries`
    - `hGhostEntry`: `f3RxSeg_ghostProg617_externAt_entry`
    - `hMemmoveExt`, `hMemcpyTrap`, `hMemsetTrap`: per-entry `TrapHook` dispatch on `EG W`. -/
theorem memmoveGhost_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hMemmoveOff : memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff)
    (hCL : ∀ u : State, InvS u → (memmoveSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostOffEntries : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map (libsignalSessionLib.resolve mpl) →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none)
    (hGhostEntry : ∀ (W : CliHooks) {sym : String},
      sym ∈ ["memmove", "memcpy", "memset"] →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl sym) = EG W sym)
    (hMemmoveExt : ∀ W : CliHooks,
      EG W "memmove" = none ∨ EG W "memmove" = some (memmoveGhost mpl mmpl))
    (hMemcpyTrap : ∀ (W : CliHooks) (f : State → State),
      EG W "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ (W : CliHooks) (f : State → State),
      EG W "memset" = some f → ∀ L, TrapHook L f) :
    GhostRowReplayOn mpl mmpl InvS EG "memmove" (memmoveEntryGuard mpl)
      (memmoveGhost mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨memmoveGhost_preserves_execFrozen mpl mmpl hfr,
     memmoveGhost_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    right
    refine ⟨hRealHullNoExt W (keepR_memmove_entry hMemmoveOff), ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (memmoveSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hRegExt :=
      bPreHull_reg_ext_forall_of_entries
        (m := memcpyEntry mpl)
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (resolve := libsignalSessionLib.resolve mpl)
        (extOf := EG W)
        (fun hkp hnotin => hGhostOffEntries W hkp hnotin)
        (fun hsym => hGhostEntry W hsym)
        (fun f hf _ hL => by
          rcases hMemmoveExt W with hn | hs
          · rw [hn] at hf
            cases hf
          · rw [hs] at hf
            have hfeq : f = memmoveGhost mpl mmpl := (Option.some.inj hf).symm
            rw [hfeq]
            exact trapHook_f3EmptyMemmoveGhostHook (memmoveSubProg mpl)
              (memcpyEntry mpl + bPreMemmoveByteOff) hL)
        (hMemcpyTrap W)
        (hMemsetTrap W)
    have hLrOut : keepR_memmove mpl (u.readReg64 .lr) = false :=
      bPreHull_keepLr_false_after_hook_of_codeLoaded_u
        (memmoveSubProg_hasWords mpl)
        (resolve_memcpy_eq_memcpyEntry mpl)
        hRegExt
        (fun _ hL => trapHook_f3EmptyMemmoveGhostHook (memmoveSubProg mpl)
          (memcpyEntry mpl + bPreMemmoveByteOff) hL)
        hEntry.1
        hRetPc
        hNoExSf
        hNotHaltSf
        u
        hStepsAfter
        hrun
        hCodeU
        hkf
    have hCodeStrip :
        (memmoveSubProg mpl).CodeLoaded (stripExecOutside (keepR_memmove mpl) u.mem) :=
      memmoveSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨_, _, hfr_fu, hfs_fu, hvis⟩ :=
      f3EmptyMemmoveGhostHook_visitedIn
        (keepR := keepR_memmove mpl)
        (P_sub := memmoveSubProg mpl)
        (m := memcpyEntry mpl)
        (resolve := libsignalSessionLib.resolve mpl)
        (padWord := bPrePadWord)
        (memmoveSubProg_svc mpl)
        (memmoveSubProg_externAt_none mpl)
        (memmoveSubProg_hasWords mpl)
        (resolve_memcpy_eq_memcpyEntry mpl)
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (memcpyEntry mpl + bPreMemmoveByteOff))
          (memmoveGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hpc_target : u.pc = memcpyEntry mpl + bPreMemmoveByteOff := by
      have hpc' : u.pc = memmoveEntry mpl := hpc
      exact hpc'.trans hMemmoveOff
    rw [setPC_eq_self_of_pc_eq hpc_target] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (memmoveGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- Full per-row bundle `GhostRowOk` (`GhostRowSpecOk ∧ GhostRowReplayOn`) for `"memmove"` over
    the 3-entry `.text.b_pre` hull (`["memmove", "memcpy", "memset"]`). -/
theorem memmoveGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hMemmoveOff : memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff)
    (hCL : ∀ u : State, InvS u → (memmoveSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostOffEntries : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map (libsignalSessionLib.resolve mpl) →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none)
    (hGhostEntry : ∀ (W : CliHooks) {sym : String},
      sym ∈ ["memmove", "memcpy", "memset"] →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl sym) = EG W sym)
    (hMemmoveExt : ∀ W : CliHooks,
      EG W "memmove" = none ∨ EG W "memmove" = some (memmoveGhost mpl mmpl))
    (hMemcpyTrap : ∀ (W : CliHooks) (f : State → State),
      EG W "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ (W : CliHooks) (f : State → State),
      EG W "memset" = some f → ∀ L, TrapHook L f) :
    GhostRowOk mpl mmpl InvS EG "memmove" (memmoveEntryGuard mpl) (memmoveGhost mpl mmpl) :=
  ⟨memmoveGhost_rowSpecOk mpl mmpl,
   memmoveGhost_rowReplayOn mpl mmpl InvS EG hMemmoveOff hCL hInvKeep hRealHullNoExt
     hGhostOffEntries hGhostEntry hMemmoveExt hMemcpyTrap hMemsetTrap⟩

/-- Entry-excluded interior-`TrapHook` variant of `memmoveGhost_rowReplayOn` (matching
    `BcmpGhostReplays.bcmpGhost_rowReplayOn_of_interior` /
    `StrlenGhostReplays.strlenGhost_rowReplayOn_of_interior`). -/
theorem memmoveGhost_rowReplayOn_of_interior
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hMemmoveOff : memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff)
    (hCL : ∀ u : State, InvS u → (memmoveSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "memmove") =
        some (memmoveGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hInteriorGhost : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "memmove" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ g, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some g ∧
          ∀ L : BitVec 64, keepR_memmove mpl L = true → TrapHook L g) :
    GhostRowReplayOn mpl mmpl InvS EG "memmove" (memmoveEntryGuard mpl)
      (memmoveGhost mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨memmoveGhost_preserves_execFrozen mpl mmpl hfr,
     memmoveGhost_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    have hRegExt : ∀ L : BitVec 64, keepR_memmove mpl L = true →
        ∀ pc : BitVec 64, keepR_memmove mpl pc = true →
          (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
            ∃ g, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some g ∧ TrapHook L g := by
      intro L hL pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl "memmove"
      · rw [hEq]
        exact Or.inr ⟨memmoveGhost mpl mmpl, hGhostAt W,
          trapHook_f3EmptyMemmoveGhostHook (memmoveSubProg mpl)
            (memcpyEntry mpl + bPreMemmoveByteOff) hL⟩
      · rcases hInteriorGhost W hk hEq with hNone | ⟨gStub, hSome, hTrap⟩
        · exact Or.inl hNone
        · exact Or.inr ⟨gStub, hSome, hTrap L hL⟩
    right
    refine ⟨hRealHullNoExt W (keepR_memmove_entry hMemmoveOff), ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (memmoveSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hLrOut : keepR_memmove mpl (u.readReg64 .lr) = false :=
      bPreHull_keepLr_false_after_hook_of_codeLoaded_u
        (memmoveSubProg_hasWords mpl)
        (resolve_memcpy_eq_memcpyEntry mpl)
        hRegExt
        (fun _ hL => trapHook_f3EmptyMemmoveGhostHook (memmoveSubProg mpl)
          (memcpyEntry mpl + bPreMemmoveByteOff) hL)
        hEntry.1
        hRetPc
        hNoExSf
        hNotHaltSf
        u
        hStepsAfter
        hrun
        hCodeU
        hkf
    have hCodeStrip :
        (memmoveSubProg mpl).CodeLoaded (stripExecOutside (keepR_memmove mpl) u.mem) :=
      memmoveSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨_, _, hfr_fu, hfs_fu, hvis⟩ :=
      f3EmptyMemmoveGhostHook_visitedIn
        (keepR := keepR_memmove mpl)
        (P_sub := memmoveSubProg mpl)
        (m := memcpyEntry mpl)
        (resolve := libsignalSessionLib.resolve mpl)
        (padWord := bPrePadWord)
        (memmoveSubProg_svc mpl)
        (memmoveSubProg_externAt_none mpl)
        (memmoveSubProg_hasWords mpl)
        (resolve_memcpy_eq_memcpyEntry mpl)
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (memcpyEntry mpl + bPreMemmoveByteOff))
          (memmoveGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hpc_target : u.pc = memcpyEntry mpl + bPreMemmoveByteOff := by
      have hpc' : u.pc = memmoveEntry mpl := hpc
      exact hpc'.trans hMemmoveOff
    rw [setPC_eq_self_of_pc_eq hpc_target] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (memmoveGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- Entry-excluded interior-`TrapHook` variant of `memmoveGhost_rowOk`. -/
theorem memmoveGhost_rowOk_of_interior [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hMemmoveOff : memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff)
    (hCL : ∀ u : State, InvS u → (memmoveSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "memmove") =
        some (memmoveGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hInteriorGhost : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "memmove" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ g, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some g ∧
          ∀ L : BitVec 64, keepR_memmove mpl L = true → TrapHook L g) :
    GhostRowOk mpl mmpl InvS EG "memmove" (memmoveEntryGuard mpl) (memmoveGhost mpl mmpl) :=
  ⟨memmoveGhost_rowSpecOk mpl mmpl,
   memmoveGhost_rowReplayOn_of_interior mpl mmpl InvS EG hMemmoveOff hCL hInvKeep hGhostAt
     hRealHullNoExt hInteriorGhost⟩

/-- `K`-narrowed `memmoveGhostK` spare `GhostRowReplayOn` (`entryGuard := fun _ => True`). -/
theorem memmoveGhostK_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hMemmoveOff : memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff)
    (hCL : ∀ u : State, InvS u → (memmoveSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG "memmove" (fun _ => True) (memmoveGhostK mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨memmoveGhostK_preserves_execFrozen mpl mmpl hfr,
     memmoveGhostK_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealHullNoExt W (keepR_memmove_entry hMemmoveOff), ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hCodeStrip :
        (memmoveSubProg mpl).CodeLoaded (stripExecOutside (keepR_memmove mpl) u.mem) :=
      memmoveSubProg_codeLoaded_stripExecOutside (hCL u hInvU)
    obtain ⟨_, _, hfr_fu, hfs_fu, hvis⟩ :=
      f3EmptyMemmoveGhostHookK_visitedIn
        (keepR := keepR_memmove mpl)
        (P_sub := memmoveSubProg mpl)
        (m := memcpyEntry mpl)
        (resolve := libsignalSessionLib.resolve mpl)
        (padWord := bPrePadWord)
        (memmoveSubProg_svc mpl)
        (memmoveSubProg_externAt_none mpl)
        (memmoveSubProg_hasWords mpl)
        (resolve_memcpy_eq_memcpyEntry mpl)
        hrun
        hnoex
        hfr
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (memcpyEntry mpl + bPreMemmoveByteOff))
          (memmoveGhostK mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hpc_target : u.pc = memcpyEntry mpl + bPreMemmoveByteOff := by
      have hpc' : u.pc = memmoveEntry mpl := hpc
      exact hpc'.trans hMemmoveOff
    rw [setPC_eq_self_of_pc_eq hpc_target] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (memmoveGhostK mpl mmpl u) hInvU hkf hfs_fu⟩

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

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays
