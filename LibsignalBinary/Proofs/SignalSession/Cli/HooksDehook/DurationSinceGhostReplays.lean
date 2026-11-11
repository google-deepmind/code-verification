/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.RustStd.TimeDurationSince -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Card `CC-R0` (Row 2) — `duration_since` Route-`R0` `GhostRowReplayOn` (`HooksDehook.DurationSinceGhostReplays`)

Cutover-2 `c`-card for `lsDurationSinceSym` (`<std::time::SystemTime>::duration_since`) on the
Route-`R0` (`WithLsRet.withLsRet` / `LsRetAddr624`) `.text.lib2` track:

1. **Row Anchor & `W`-Independent Ghost (`keepR_durationSince`, `durationSinceSubProg`, `durationSinceGhost`):**
   - `durationSinceSubProg timeMpl := durationSinceHullProg timeMpl` (`80` words = `320` B
     contiguous hull at `timeMpl.base 0`: `Timespec::sub_timespec` `60` words at `+0` followed by
     `SystemTime::duration_since` `20` words at `+240`).
   - `durationSinceGhost timeMpl` wraps `DurationSinceGhostLs.f3EmptyDurationSinceHullGhostHookLs`
     (`P_real := emptyStdProg`, `roTableGuard` on `timePlacedData0`, `fallback := durationSinceExactHook`),
     so it has **zero `W : CliHooks` dependence**.
2. **State Preservation & `withLsRet` Consumer `HookOk` Arms:**
   - Unconditional (`0` layout premises) `durationSinceGhost_fs`, `durationSinceGhost_fsT`, and
     `durationSinceGhost_preserves_execFrozen`.
   - Under `hpl : timeMultiLib.Placeable timeMpl` and
     `hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen`, `durationSinceGhost_vmPreserved`
     and `withLsRet` consumer `HookOk` arms matching `DurationSinceRowSpec` (`Slots.durationSinceBoundedSpec`
     and bounded-stack `208 ≤ stk ≤ 2 ^ 64` `Slots.durationSinceEpochAtSpec`, plain,
     `withVmPreserved`, and `withAlloc`).
3. **Generic-`InvS` `GhostRowReplayOn` (`entryGuard := fun _ => True`, `F1` + `H1` compliant):**
   - `hCL` and `hRo` extract `(durationSinceSubProg timeMpl).CodeLoaded u.mem` and
     `RoDataAt u.mem (timeMpl.ρ timeRodataCst16Sym) timePlacedData0` at each intermediate call
     state `u` from `InvS u` (**H1**; never `s0.mem`).
   - `hRealHullNoExt` requires `externAt? pc = none` on `keepR_durationSince timeMpl pc = true`
     **only** on the de-hooked real program `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`
     (**F1**; zero `P_ghost` hull premise).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.RustStd (timeMultiLib timePlacedData0 timeRodataCst16Sym)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced durationSinceExactHook libsignalSessionLib
   lsDurationSinceSym lsFromUtf8Sym lsMemrchrSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC)
open CryptoVerification.SignalSession.Cli.Slots (durationSinceEpochAtSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen keepFsTrace linkedCallHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode
  (durationSinceExactHook_vm durationSinceHullProg durationSinceHullProg_externAt_none
   durationSinceHullProg_hasWords_durationSince durationSinceHullProg_hasWords_subTimespec
   durationSinceHullProg_svc durationSinceHullWords_length)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhost
  (durationSinceGhostFnLs durationSinceGhostFnLs_fs durationSinceGhostFnLs_fsT
   durationSinceGhostFnLs_keepLr_false_of_noException durationSinceGhostFnLs_vmPreserved
   durationSinceHullGhostFnLs durationSinceHullGhostFnLs_masterLs_ok hookOk_congr
   hookOk_withLsRet_durationSinceBounded_of_master hookOk_withLsRet_durationSinceEpochAt_of_master
   masterDurationSinceLs_outcome_setPC masterDurationSinceLs_pre_setPC
   specPreservesFsTrace_masterDurationSinceLs specStripSInvariant_masterDurationSinceLs
   subroutine_ok_masterDurationSinceLs_of_hasWords subTimespecByteLen withLsRet_withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (ExtraEntryGuard GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG
  (ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis linkedCallHookG roDataAt_of_keepsFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (emptyStdProg emptyStdProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords
  (codeLoaded_stripExecOutside_of_keep)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowSpec GhostRowSpecOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.DurationSinceRowSpec
  (DurationSinceRowSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_steps_lift_of_visitedIn_noExtern)

/-! ## 1. Row Anchor Definitions & `CodeLoaded` `stripExecOutside` Equivalence -/

/-- Byte length (`320` B = `80` words) of `sub_timespec` (`240` B) ++ `duration_since` (`80` B). -/
@[expose] def durationSinceHullByteLen : Nat := 320

/-- Kept-region byte predicate `[timeMpl.base 0, timeMpl.base 0 + 320)` covering the contiguous
    `sub_timespec ++ duration_since` `.text.lib2` hull. -/
@[expose] def keepR_durationSince (timeMpl : Obj.MultiPlacement) (pc : BitVec 64) : Bool :=
  decide ((pc - timeMpl.base 0).toNat < durationSinceHullByteLen)

theorem keepR_durationSince_entry (timeMpl : Obj.MultiPlacement) :
    keepR_durationSince timeMpl (timeMpl.base 0 + subTimespecByteLen) = true := by
  unfold keepR_durationSince durationSinceHullByteLen subTimespecByteLen
  have hsub : timeMpl.base 0 + 240#64 - timeMpl.base 0 = 240#64 := by bv_omega
  rw [hsub]
  decide

/-- Pure `80`-word (`320`-byte) sub-program holding `durationSinceHullWords timeMpl` at
    `timeMpl.base 0`. -/
@[expose] def durationSinceSubProg (timeMpl : Obj.MultiPlacement) : Program :=
  durationSinceHullProg timeMpl

theorem durationSinceSubProg_base (timeMpl : Obj.MultiPlacement) :
    (durationSinceSubProg timeMpl).base = timeMpl.base 0 := rfl

theorem durationSinceSubProg_code_length (timeMpl : Obj.MultiPlacement) :
    (durationSinceSubProg timeMpl).code.length = durationSinceHullByteLen := by
  unfold durationSinceSubProg durationSinceHullProg durationSinceHullByteLen
    pureWordsProg Program.ofWords
  rw [Program.length_flatMap_wordToBytesLE, durationSinceHullWords_length]

theorem keepR_durationSince_of_code_offset (timeMpl : Obj.MultiPlacement) {off : Nat}
    (hoff : off < (durationSinceSubProg timeMpl).code.length) :
    keepR_durationSince timeMpl ((durationSinceSubProg timeMpl).base + BitVec.ofNat 64 off) =
      true := by
  rw [durationSinceSubProg_code_length] at hoff
  rw [durationSinceSubProg_base]
  unfold keepR_durationSince
  have hsub : timeMpl.base 0 + BitVec.ofNat 64 off - timeMpl.base 0 = BitVec.ofNat 64 off := by
    bv_omega
  have hoff_lt : off < 2 ^ 64 := by
    have hb : durationSinceHullByteLen = 320 := rfl
    omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]
  exact decide_eq_true hoff

theorem durationSinceSubProg_codeLoaded_stripExecOutside {timeMpl : Obj.MultiPlacement}
    {mem : Memory}
    (hL : (durationSinceSubProg timeMpl).CodeLoaded mem) :
    (durationSinceSubProg timeMpl).CodeLoaded
      (stripExecOutside (keepR_durationSince timeMpl) mem) :=
  codeLoaded_stripExecOutside_of_keep
    (fun _ hoff => keepR_durationSince_of_code_offset timeMpl hoff) hL

theorem durationSinceSubProg_codeLoaded_of_stripExecOutside {timeMpl : Obj.MultiPlacement}
    {mem : Memory}
    (hL : (durationSinceSubProg timeMpl).CodeLoaded
      (stripExecOutside (keepR_durationSince timeMpl) mem)) :
    (durationSinceSubProg timeMpl).CodeLoaded mem := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hk : keepR_durationSince timeMpl
      ((durationSinceSubProg timeMpl).base + BitVec.ofNat 64 i) = true :=
    keepR_durationSince_of_code_offset timeMpl hi
  have hbyte := hL.byte_eq i hi
  have hperm := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [ProofLib.strip_read8] at hbyte
  rw [ProofLib.strip_perm_of_keep hk] at hperm
  rw [ProofLib.strip_isLazyFree] at hlf
  exact ⟨hbyte, hperm, hlf⟩

theorem durationSinceSubProg_codeLoaded_stripExecOutside_iff {timeMpl : Obj.MultiPlacement}
    {mem : Memory} :
    (durationSinceSubProg timeMpl).CodeLoaded
        (stripExecOutside (keepR_durationSince timeMpl) mem) ↔
      (durationSinceSubProg timeMpl).CodeLoaded mem :=
  ⟨durationSinceSubProg_codeLoaded_of_stripExecOutside,
   durationSinceSubProg_codeLoaded_stripExecOutside⟩

/-- Route-`R0` (`withLsRet`) `W`-independent ghost hook for `lsDurationSinceSym`. -/
@[expose] noncomputable def durationSinceGhost [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement) : State → State :=
  durationSinceHullGhostFnLs (keepR_durationSince timeMpl) emptyStdProg timeMpl (timeMpl.base 0)

/-- Block-`617` entry-state guard for Route-`R0` `lsDurationSinceSym` (`True`: `LsRetAddr624` is
    extracted directly from non-`.Exception` at each call step). -/
@[expose] def durationSinceEntryGuard (_mpl : Obj.MultiPlacement) (_s0 : State) : Prop :=
  True

/-! ## 2. State Preservation & `withLsRet` Consumer `HookOk` Arms -/

theorem durationSinceGhost_fs [LibsignalPlacement] (timeMpl : Obj.MultiPlacement) (s : State) :
    (durationSinceGhost timeMpl s).fs = s.fs :=
  durationSinceGhostFnLs_fs (timeMpl.ρ timeRodataCst16Sym)
    (keepR_durationSince timeMpl) emptyStdProg (durationSinceHullProg timeMpl)
    (timeMpl.base 0 + subTimespecByteLen) s

theorem durationSinceGhost_fsT [LibsignalPlacement] (timeMpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (durationSinceGhost timeMpl) :=
  durationSinceGhostFnLs_fsT (timeMpl.ρ timeRodataCst16Sym)
    (keepR_durationSince timeMpl) emptyStdProg (durationSinceHullProg timeMpl)
    (timeMpl.base 0 + subTimespecByteLen)

theorem durationSinceGhost_vmPreserved [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen)
    (s : State) :
    VmPreserved s (durationSinceGhost timeMpl s) := by
  unfold durationSinceGhost durationSinceHullGhostFnLs
  rw [← hb1]
  exact durationSinceGhostFnLs_vmPreserved hpl emptyStdProg_svc
    (durationSinceHullProg_svc timeMpl) (fun _ _ => rfl)
    (durationSinceHullProg_externAt_none timeMpl)
    (durationSinceHullProg_hasWords_subTimespec timeMpl)
    (hb1 ▸ durationSinceHullProg_hasWords_durationSince timeMpl) s

theorem durationSinceGhost_masterLs_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen) :
    HookOk (durationSinceGhost timeMpl)
      (withLsRet LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode.masterDurationSinceSpec) :=
  durationSinceHullGhostFnLs_masterLs_ok (timeMpl.base 0) hpl rfl hb1 emptyStdProg_svc
    (fun _ _ => rfl)

theorem durationSinceGhost_bounded_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen) :
    HookOk (durationSinceGhost timeMpl)
      (withLsRet CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec) :=
  hookOk_congr (rfl : withLsRet _ = withLsRet _)
    (hookOk_withLsRet_durationSinceBounded_of_master
      (durationSinceGhost_masterLs_ok timeMpl hpl hb1))

theorem durationSinceGhost_bounded_withVmPreserved_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen) :
    HookOk (durationSinceGhost timeMpl)
      (withVmPreserved
        (withLsRet CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec)) :=
  hookOk_withVmPreserved (durationSinceGhost_bounded_ok timeMpl hpl hb1)
    (durationSinceGhost_vmPreserved timeMpl hpl hb1)

theorem durationSinceGhost_bounded_withAlloc_ls_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (durationSinceGhost timeMpl)
      (withAlloc A lim
        (withLsRet CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec)) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (durationSinceGhost_bounded_withVmPreserved_ok timeMpl hpl hb1)

theorem durationSinceGhost_bounded_withAlloc_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (durationSinceGhost timeMpl)
      (withLsRet
        (withAlloc A lim CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec)) := by
  rw [withLsRet_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (hookOk_withVmPreserved (durationSinceGhost_bounded_ok timeMpl hpl hb1)
      (durationSinceGhost_vmPreserved timeMpl hpl hb1))

theorem durationSinceGhost_epochAt_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen)
    (stk : Nat) (hlo : 208 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (durationSinceGhost timeMpl) (withLsRet (durationSinceEpochAtSpec stk)) :=
  hookOk_congr (rfl : withLsRet _ = withLsRet _)
    (hookOk_withLsRet_durationSinceEpochAt_of_master
      (durationSinceGhost_masterLs_ok timeMpl hpl hb1) ⟨hlo, hhi⟩)

theorem durationSinceGhost_epochAt_withVmPreserved_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen)
    (stk : Nat) (hlo : 208 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (durationSinceGhost timeMpl)
      (withVmPreserved (withLsRet (durationSinceEpochAtSpec stk))) :=
  hookOk_withVmPreserved (durationSinceGhost_epochAt_ok timeMpl hpl hb1 stk hlo hhi)
    (durationSinceGhost_vmPreserved timeMpl hpl hb1)

theorem durationSinceGhost_epochAt_withAlloc_ls_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 208 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (durationSinceGhost timeMpl)
      (withAlloc A lim (withLsRet (durationSinceEpochAtSpec stk))) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (durationSinceGhost_epochAt_withVmPreserved_ok timeMpl hpl hb1 stk hlo hhi)

theorem durationSinceGhost_epochAt_withAlloc_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 208 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (durationSinceGhost timeMpl)
      (withLsRet (withAlloc A lim (durationSinceEpochAtSpec stk))) := by
  rw [withLsRet_withAlloc]
  exact hookOk_withAlloc_of_withVmPreserved A lim
    (hookOk_withVmPreserved (durationSinceGhost_epochAt_ok timeMpl hpl hb1 stk hlo hhi)
      (durationSinceGhost_vmPreserved timeMpl hpl hb1))

/-! ## 3. `ExecFrozen` Preservation & Generic-`InvS` `GhostRowReplayOn` -/

private theorem linkedCallHook_preserves_execFrozen {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hfb : ∀ s : State, ExecFrozen s.mem → ExecFrozen (fallback s).mem)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem := by
  classical
  unfold linkedCallHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
    · change ExecFrozen (fallback u).mem
      exact hfb u hfr
  · exact hfr

private theorem linkedCallHookG_preserves_execFrozen {α : Type}
    {Guard : State → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hfb : ∀ s : State, ExecFrozen s.mem → ExecFrozen (fallback s).mem)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback u).mem := by
  classical
  unfold linkedCallHookG
  split
  · exact linkedCallHook_preserves_execFrozen hfb hfr
  · split
    · change ExecFrozen (fallback u).mem
      exact hfb u hfr
    · exact hfr

theorem durationSinceGhost_preserves_execFrozen [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (durationSinceGhost timeMpl u).mem := by
  unfold durationSinceGhost durationSinceHullGhostFnLs durationSinceGhostFnLs
  exact linkedCallHookG_preserves_execFrozen
    (fun s hs => ExecFrozen.of_perm_eq hs (durationSinceExactHook_vm s).perm_eq) hfr

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u
  dsimp only [State.setPC] at hpc ⊢
  subst hpc
  rfl

private theorem realProg617_svc (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard :=
  rfl

private theorem emptyStdProg_externAt (pc : BitVec 64) :
    emptyStdProg.externAt? pc = none :=
  rfl

/-- Behind-stub (`StubReachesTargetOn`) `GhostRowReplayOn` for `lsDurationSinceSym` (`entryGuard :=
    fun _ => True`, `F1` + `H1` compliant). -/
theorem durationSinceGhost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl timeMpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen)
    (hCL : ∀ u : State, InvS u → (durationSinceSubProg timeMpl).CodeLoaded u.mem)
    (hRo : ∀ u : State, InvS u →
      RoDataAt u.mem (timeMpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_durationSince timeMpl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_durationSince timeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsDurationSinceSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn
        (fun m => (durationSinceSubProg timeMpl).CodeLoaded m ∧
          RoDataAt m (timeMpl.ρ timeRodataCst16Sym) timePlacedData0)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsDurationSinceSym)
        (timeMpl.base 0 + subTimespecByteLen)) :
    GhostRowReplayOn mpl mmpl InvS EG lsDurationSinceSym (fun _ => True)
      (durationSinceGhost timeMpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨durationSinceGhost_preserves_execFrozen timeMpl hfr,
     durationSinceGhost_fs timeMpl u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    have hStub1 :
        StubReachesTargetOn
          (fun m => (durationSinceSubProg timeMpl).CodeLoaded m ∧
            RoDataAt m (timeMpl.ρ timeRodataCst16Sym) timePlacedData0)
          (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (libsignalSessionLib.resolve mpl lsDurationSinceSym)
          (timeMpl.base 1) := by
      rw [hb1]
      exact hStub W
    have hRep :=
      ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis
        (InvMem := fun m => (durationSinceSubProg timeMpl).CodeLoaded m ∧
          RoDataAt m (timeMpl.ρ timeRodataCst16Sym) timePlacedData0)
        (keep := keepR_durationSince timeMpl)
        (P_run := emptyStdProg)
        (P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (P_sub := durationSinceSubProg timeMpl)
        (stubPc := libsignalSessionLib.resolve mpl lsDurationSinceSym)
        (entryTarget := timeMpl.base 1)
        (tbl := timeMpl.ρ timeRodataCst16Sym)
        (bytes := timePlacedData0)
        (fallback := durationSinceExactHook)
        emptyStdProg_svc
        (durationSinceHullProg_svc timeMpl)
        (fun pc _ => emptyStdProg_externAt pc)
        (durationSinceHullProg_externAt_none timeMpl)
        (hRealStubNone W)
        hStub1
        (fun _ _ _ _ _ hvis =>
          h2fsgen_steps_lift_of_visitedIn_noExtern
            (D := keepR_durationSince timeMpl)
            (P1 := emptyStdProg)
            (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
            (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
            (fun pc _ => emptyStdProg_externAt pc)
            (fun _ hk => hRealHullNoExt W hk)
            hvis)
        (fun _ _ hInvM => durationSinceSubProg_codeLoaded_stripExecOutside hInvM.1)
        (fun _ _ hInvM hkf =>
          ⟨hInvM.1.of_keepsFrozen hkf, roDataAt_of_keepsFrozen hInvM.2 hkf⟩)
        (fun _ _ hInvM => hInvM.2)
        (subroutine_ok_masterDurationSinceLs_of_hasWords hpl
          (durationSinceHullProg_svc timeMpl)
          (durationSinceHullProg_externAt_none timeMpl)
          (durationSinceHullProg_hasWords_subTimespec timeMpl)
          (hb1 ▸ durationSinceHullProg_hasWords_durationSince timeMpl))
        (specStripSInvariant_masterDurationSinceLs (keepR_durationSince timeMpl))
        specPreservesFsTrace_masterDurationSinceLs
        masterDurationSinceLs_pre_setPC
        masterDurationSinceLs_outcome_setPC
    refine ⟨hRep.1, ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hnoex1 :
        ∀ msg,
          (durationSinceGhostFnLs (timeMpl.ρ timeRodataCst16Sym) (keepR_durationSince timeMpl)
            emptyStdProg (durationSinceSubProg timeMpl) (timeMpl.base 1) u).status ≠
            .Exception msg := by
      rw [hb1]
      exact hnoex
    have hlr : keepR_durationSince timeMpl (u.readReg64 .lr) = false :=
      durationSinceGhostFnLs_keepLr_false_of_noException hKeep hnoex1
    obtain ⟨hSteps1, hfr1, _⟩ :=
      hRep.2 u hpc hrun hnoex1 hfr hlr ⟨hCL u hInvU, hRo u hInvU⟩
    have hEqGhost :
        linkedCallHookG
          (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG.roTableGuard
            (timeMpl.ρ timeRodataCst16Sym) timePlacedData0)
          (keepR_durationSince timeMpl) emptyStdProg (durationSinceSubProg timeMpl)
          (timeMpl.base 1)
          (withLsRet LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode.masterDurationSinceSpec)
          durationSinceExactHook u = durationSinceGhost timeMpl u := by
      change durationSinceGhostFnLs (timeMpl.ρ timeRodataCst16Sym) (keepR_durationSince timeMpl)
        emptyStdProg (durationSinceHullProg timeMpl) (timeMpl.base 1) u =
        durationSinceGhostFnLs (timeMpl.ρ timeRodataCst16Sym) (keepR_durationSince timeMpl)
          emptyStdProg (durationSinceHullProg timeMpl) (timeMpl.base 0 + subTimespecByteLen) u
      rw [hb1]
    rw [hEqGhost] at hSteps1 hfr1
    exact ⟨hSteps1, hfr1,
      hInvKeep u (durationSinceGhost timeMpl u) hInvU hkf (durationSinceGhost_fs timeMpl u)⟩

/-- **Artifact 2a (`CC-R0`, Row 2) — Direct `.text.lib2` `GhostRowReplayOn` for `lsDurationSinceSym`:**
    Route `R0` (`entryGuard := fun _ => True`), discharging `hRealStubNone` and `hStub` directly
    from `hTargetEq : libsignalSessionLib.resolve mpl lsDurationSinceSym =
    timeMpl.base 0 + subTimespecByteLen` (`F1` + `H1` compliant). -/
theorem durationSinceGhost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl timeMpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen)
    (hTargetEq : libsignalSessionLib.resolve mpl lsDurationSinceSym =
      timeMpl.base 0 + subTimespecByteLen)
    (hCL : ∀ u : State, InvS u → (durationSinceSubProg timeMpl).CodeLoaded u.mem)
    (hRo : ∀ u : State, InvS u →
      RoDataAt u.mem (timeMpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_durationSince timeMpl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_durationSince timeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsDurationSinceSym (fun _ => True)
      (durationSinceGhost timeMpl) :=
  durationSinceGhost_rowReplayOn_of_stub mpl mmpl timeMpl InvS EG hpl hb1 hCL hRo hInvKeep
    hKeep hRealHullNoExt
    (fun W => by rw [hTargetEq]; exact hRealHullNoExt W (keepR_durationSince_entry timeMpl))
    (fun _ u hpc _ _ _ => by
      rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)]
      exact Steps.refl _)

/-! ## 4. `DurationSinceRowSpec`, `GhostRowSpecOk`, `GhostRowOk` & `ExtraEntryGuard` Helpers -/

/-- `DurationSinceRowSpec` (`withLsRet` outermost) for `durationSinceGhost timeMpl`. -/
theorem durationSinceGhost_durationSinceRowSpec [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen) :
    DurationSinceRowSpec (durationSinceGhost timeMpl) :=
  DurationSinceRowSpec.of_ls_vm
    (durationSinceGhost_bounded_ok timeMpl hpl hb1)
    (fun stk hlo hhi => durationSinceGhost_epochAt_ok timeMpl hpl hb1 stk hlo hhi)
    (durationSinceGhost_vmPreserved timeMpl hpl hb1)

/-- **Artifact 1 (`CC-R0`, Row 2):** `GhostRowSpecOk lsDurationSinceSym (durationSinceGhost timeMpl)`
    under `timeMultiLib.Placeable timeMpl` and `timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen`. -/
theorem durationSinceGhost_rowSpecOk [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen) :
    GhostRowSpecOk lsDurationSinceSym (durationSinceGhost timeMpl) where
  fs_eq := durationSinceGhost_fs timeMpl
  fsT := durationSinceGhost_fsT timeMpl
  rowSpec := by
    unfold ExtraRowSpec
    have hd1 : (lsDurationSinceSym == "bcmp") = false := by decide
    have hd2 : (lsDurationSinceSym == "strlen") = false := by decide
    have hd3 : (lsDurationSinceSym == "memmove") = false := by decide
    have hd4 : (lsDurationSinceSym == lsFromUtf8Sym) = false := by decide
    have hd5 : (lsDurationSinceSym == lsMemrchrSym) = false := by decide
    have hd6 : (lsDurationSinceSym == lsDurationSinceSym) = true := by decide
    simp only [hd1, hd2, hd3, hd4, hd5, hd6, Bool.false_eq_true, ↓reduceIte]
    exact durationSinceGhost_durationSinceRowSpec timeMpl hpl hb1

/-- Behind-stub `GhostRowOk` bundle (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) for `lsDurationSinceSym`. -/
theorem durationSinceGhost_rowOk_of_stub [LibsignalPlacement]
    (mpl mmpl timeMpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen)
    (hCL : ∀ u : State, InvS u → (durationSinceSubProg timeMpl).CodeLoaded u.mem)
    (hRo : ∀ u : State, InvS u →
      RoDataAt u.mem (timeMpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_durationSince timeMpl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_durationSince timeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsDurationSinceSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn
        (fun m =>
          (durationSinceSubProg timeMpl).CodeLoaded m ∧
            RoDataAt m (timeMpl.ρ timeRodataCst16Sym) timePlacedData0)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsDurationSinceSym)
        (timeMpl.base 0 + subTimespecByteLen)) :
    GhostRowOk mpl mmpl InvS EG lsDurationSinceSym (fun _ => True)
      (durationSinceGhost timeMpl) :=
  ⟨durationSinceGhost_rowSpecOk timeMpl hpl hb1,
   durationSinceGhost_rowReplayOn_of_stub mpl mmpl timeMpl InvS EG hpl hb1 hCL hRo hInvKeep
     hKeep hRealHullNoExt hRealStubNone hStub⟩

/-- **Full per-row `GhostRowOk` bundle (`GhostRowSpecOk` ∧ `GhostRowReplayOn`)** for
    `lsDurationSinceSym` (`entryGuard := fun _ => True`). -/
theorem durationSinceGhost_rowOk [LibsignalPlacement]
    (mpl mmpl timeMpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : timeMultiLib.Placeable timeMpl)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen)
    (hTargetEq : libsignalSessionLib.resolve mpl lsDurationSinceSym =
      timeMpl.base 0 + subTimespecByteLen)
    (hCL : ∀ u : State, InvS u → (durationSinceSubProg timeMpl).CodeLoaded u.mem)
    (hRo : ∀ u : State, InvS u →
      RoDataAt u.mem (timeMpl.ρ timeRodataCst16Sym) timePlacedData0)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_durationSince timeMpl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_durationSince timeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl InvS EG lsDurationSinceSym (fun _ => True)
      (durationSinceGhost timeMpl) :=
  ⟨durationSinceGhost_rowSpecOk timeMpl hpl hb1,
   durationSinceGhost_rowReplayOn mpl mmpl timeMpl InvS EG hpl hb1 hTargetEq hCL hRo hInvKeep
     hKeep hRealHullNoExt⟩

theorem extraEntryGuard_durationSince_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf lsDurationSinceSym s0 ↔ durationSinceEntryGuard mpl s0) :
    guardOf lsDurationSinceSym s0 :=
  hGuardEq.mpr trivial

theorem extraEntryGuard_singleton_durationSince [LibsignalPlacement]
    {mpl timeMpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hg : g.extra = [(lsDurationSinceSym, durationSinceGhost timeMpl)])
    (hGuardEq : guardOf lsDurationSinceSym s0 ↔ durationSinceEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 := by
  intro sym _ _ hLook
  rw [hg] at hLook
  simp only [List.lookup] at hLook
  by_cases hSym : (sym == lsDurationSinceSym) = true
  · have hEq := eq_of_beq hSym
    subst hEq
    exact hGuardEq.mpr trivial
  · simp [hSym] at hLook

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostReplays
