/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import

/-!
# Card `CC-R0` (Row 3) — `time add` Route-`R0` + `K4` `GhostRowReplayOn` (`HooksDehook.TimeAddGhostReplays`)

Cutover-2 `c`-card for `lsTimeAddSym` (`<std::time::SystemTime as Add<Duration>>::add`) on the
Route-`R0` (`WithLsRet.withLsRet` / `LsRetAddr624`) + `K4` panic-extern strip `.text.lib2` track:

1. **Row Anchor & `W`-Independent Ghost (`keepR_timeAdd`, `timeAddSubProg`, `timeAddGhost`):**
   - `timeAddPanicExterns` maps `rustTimeExpectFailedSym` (`core::option::expect_failed`) to
     `some Rust.panicked` and every other symbol to `none`.
   - `timeAddSubProg timeMpl := timeAddBlk2Prog timeMpl timeAddPanicExterns` (`24` words = `96` B
     at `timeMpl.base 2`, with `timeMultiLib.fnAddr timeMpl timeAddSym = timeMpl.base 2`).
   - `timeAddGhost timeMpl` wraps `TimeAddPanicGhostK.timeAddGhostHookExternOnlyLsRet`
     (`externOnlyStdProg`, `fallback := CryptoVerification.E2E.timeAddHook`), so it has **zero
     `W : CliHooks` dependence**.
2. **State Preservation & `withLsRet` Consumer `HookOk` Arms:**
   - Unconditional (`0` layout premises) `timeAddGhost_fs`, `timeAddGhost_fsT`, and
     `timeAddGhost_preserves_execFrozen`.
   - Under `hpl : timeMultiLib.Placeable timeMpl`,
     `hkeep_stub : keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false`, and
     `hlr_ne_stub : ∀ lr, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl`,
     `timeAddGhost_vmPreserved` and `withLsRet` consumer `HookOk` arms matching `TimeAddRowSpec`
     (`LibsignalPublicApi.timeAddSpec`, `withVmPreserved` / `timeAddBudgetSpec`, `withAlloc`, and
     `E2E.HooksE.timeAddSpec`).
3. **Generic-`InvS` `GhostRowReplayOn` (`entryGuard := fun _ => True`, `F1` + `H1` compliant):**
   - `hCL` extracts `(timeAddSubProg timeMpl).CodeLoaded u.mem` at each intermediate call state `u`
     from `InvS u` (**H1**; never `s0.mem`).
   - `hRealHullNoExt` requires `externAt? pc = none` on `keepR_timeAdd timeMpl pc = true` **only**
     on the de-hooked real program `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`, and
     `hPanReal` witnesses `externAt? (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked` on
     `P_real` (**F1**; zero `P_ghost` hull premise).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open VerifiedLibraries.RustStd (rustTimeExpectFailedSym timeAddSym timeMultiLib)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced libsignalSessionLib
   lsDurationSinceSym lsFromUtf8Sym lsMemrchrSym lsTimeAddSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.Fine (timeAddHook_vmPreserved)
open LibsignalBinary.Heap.SpecBudget (timeAddBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen linkedCallHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (ExtraEntryGuard GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhost
  (codeLoaded_stripExecOutside_timeAddBlk2 keepCoversTimeAddBlk2_keepTimeAddBlk2
   keepTimeAddBlk2 timeAddBlk2Prog timeAddBlk2Prog_base timeAddBlk2Prog_code_length
   timeAddEntryAddr_eq_base2 timeAddExpectFailedStubPc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhostK
  (timeAddGhostHookExternOnly_eq timeAddGhostHookExternOnly_fs timeAddGhostHookExternOnly_fsT
   timeAddGhostHookExternOnly_vmPreserved timeAddGhostHookExternOnlyLsRet
   timeAddGhostHookExternOnlyLsRet_e2eTimeAddSpec_ok
   timeAddGhostHookExternOnlyLsRet_replaysOn
   timeAddGhostHookExternOnlyLsRet_timeAddBudgetSpec_ok
   timeAddGhostHookExternOnlyLsRet_timeAddSpec_ok
   timeAddGhostHookExternOnlyLsRet_timeAddSpec_withAlloc_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowSpec GhostRowSpecOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.TimeAddRowSpec
  (TimeAddRowSpec)

/-! ## 1. Row Anchor Definitions & `CodeLoaded` `stripExecOutside` Equivalence -/

/-- Closed `W`-independent panic-extern map for `timeMultiLib` block `2` (`SystemTime::add`):
    maps `rustTimeExpectFailedSym` (`core::option::expect_failed`) to `some Rust.panicked`. -/
@[expose] def timeAddPanicExterns (sym : String) : Option (State → State) :=
  if sym == rustTimeExpectFailedSym then some Rust.panicked else none

theorem timeAddPanicExterns_expectFailed :
    timeAddPanicExterns rustTimeExpectFailedSym = some Rust.panicked := by
  simp [timeAddPanicExterns]

/-- Kept-region byte predicate `[timeMpl.base 2, timeMpl.base 2 + 96)` retaining the `24`-word
    (`96`-byte) `SystemTime::add` `.text.lib2` block. -/
@[expose] def keepR_timeAdd (timeMpl : Obj.MultiPlacement) (pc : BitVec 64) : Bool :=
  keepTimeAddBlk2 timeMpl pc

theorem keepR_timeAdd_entry (timeMpl : Obj.MultiPlacement) :
    keepR_timeAdd timeMpl (timeMultiLib.fnAddr timeMpl timeAddSym) = true := by
  rw [timeAddEntryAddr_eq_base2]
  simpa [keepR_timeAdd] using keepCoversTimeAddBlk2_keepTimeAddBlk2 timeMpl 0 (by decide)

/-- `24`-word (`96`-byte) `timeMultiLib` block-`2` sub-program paired with `timeAddPanicExterns`. -/
@[expose] def timeAddSubProg (timeMpl : Obj.MultiPlacement) : Program :=
  timeAddBlk2Prog timeMpl timeAddPanicExterns

theorem timeAddSubProg_base (timeMpl : Obj.MultiPlacement) :
    (timeAddSubProg timeMpl).base = timeMpl.base 2 :=
  timeAddBlk2Prog_base timeMpl timeAddPanicExterns

theorem timeAddSubProg_code_length (timeMpl : Obj.MultiPlacement) :
    (timeAddSubProg timeMpl).code.length = 96 :=
  timeAddBlk2Prog_code_length timeMpl timeAddPanicExterns

theorem timeAddSubProg_codeLoaded_stripExecOutside {timeMpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (timeAddSubProg timeMpl).CodeLoaded mem) :
    (timeAddSubProg timeMpl).CodeLoaded (stripExecOutside (keepR_timeAdd timeMpl) mem) :=
  codeLoaded_stripExecOutside_timeAddBlk2 (keepCoversTimeAddBlk2_keepTimeAddBlk2 timeMpl) hL

theorem timeAddSubProg_codeLoaded_of_stripExecOutside {timeMpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (timeAddSubProg timeMpl).CodeLoaded (stripExecOutside (keepR_timeAdd timeMpl) mem)) :
    (timeAddSubProg timeMpl).CodeLoaded mem := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hi96 : i < 96 := by
    rw [timeAddSubProg_code_length] at hi
    exact hi
  have hk : keepR_timeAdd timeMpl ((timeAddSubProg timeMpl).base + BitVec.ofNat 64 i) = true := by
    rw [timeAddSubProg_base]
    exact keepCoversTimeAddBlk2_keepTimeAddBlk2 timeMpl i hi96
  have hbyte := hL.byte_eq i hi
  have hperm := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [ProofLib.strip_read8] at hbyte
  rw [ProofLib.strip_perm_of_keep hk] at hperm
  rw [ProofLib.strip_isLazyFree] at hlf
  exact ⟨hbyte, hperm, hlf⟩

theorem timeAddSubProg_codeLoaded_stripExecOutside_iff {timeMpl : Obj.MultiPlacement}
    {mem : Memory} :
    (timeAddSubProg timeMpl).CodeLoaded (stripExecOutside (keepR_timeAdd timeMpl) mem) ↔
      (timeAddSubProg timeMpl).CodeLoaded mem :=
  ⟨timeAddSubProg_codeLoaded_of_stripExecOutside, timeAddSubProg_codeLoaded_stripExecOutside⟩

/-- Route-`R0` + `K4` (`withLsRet` + `externOnlyStdProg`) `W`-independent ghost hook for
    `lsTimeAddSym`. -/
@[expose] noncomputable def timeAddGhost [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement) : State → State :=
  timeAddGhostHookExternOnlyLsRet (keepR_timeAdd timeMpl) timeMpl timeAddPanicExterns

/-- Block-`617` entry-state guard for Route-`R0` `lsTimeAddSym` (`True`: `LsRetAddr624` is
    extracted directly from non-`.Exception` at each call step). -/
@[expose] def timeAddEntryGuard (_mpl : Obj.MultiPlacement) (_s0 : State) : Prop :=
  True

/-! ## 2. State Preservation & `withLsRet` Consumer `HookOk` Arms -/

theorem timeAddGhost_fs [LibsignalPlacement] (timeMpl : Obj.MultiPlacement) (s : State) :
    (timeAddGhost timeMpl s).fs = s.fs :=
  timeAddGhostHookExternOnly_fs LsRetAddr624 (keepR_timeAdd timeMpl) timeMpl timeAddPanicExterns s

theorem timeAddGhost_fsT [LibsignalPlacement] (timeMpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (timeAddGhost timeMpl) :=
  timeAddGhostHookExternOnly_fsT LsRetAddr624 (keepR_timeAdd timeMpl) timeMpl timeAddPanicExterns

theorem timeAddGhost_vmPreserved [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hkeep_stub : keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (s : State) :
    VmPreserved s (timeAddGhost timeMpl s) :=
  timeAddGhostHookExternOnly_vmPreserved hpl hkeep_stub timeAddPanicExterns_expectFailed
    hlr_ne_stub s

theorem timeAddGhost_timeAddSpec_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hkeep_stub : keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    HookOk (timeAddGhost timeMpl)
      (withLsRet CryptoVerification.LibsignalPublicApi.timeAddSpec) :=
  timeAddGhostHookExternOnlyLsRet_timeAddSpec_ok hpl hkeep_stub
    timeAddPanicExterns_expectFailed hlr_ne_stub

theorem timeAddGhost_timeAddSpec_withVmPreserved_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hkeep_stub : keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    HookOk (timeAddGhost timeMpl)
      (withVmPreserved (withLsRet CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  hookOk_withVmPreserved
    (timeAddGhost_timeAddSpec_ok timeMpl hpl hkeep_stub hlr_ne_stub)
    (timeAddGhost_vmPreserved timeMpl hpl hkeep_stub hlr_ne_stub)

theorem timeAddGhost_timeAddSpec_withAlloc_ls_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hkeep_stub : keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (timeAddGhost timeMpl)
      (withAlloc A lim (withLsRet CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (timeAddGhost_timeAddSpec_withVmPreserved_ok timeMpl hpl hkeep_stub hlr_ne_stub)

theorem timeAddGhost_timeAddBudgetSpec_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hkeep_stub : keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    HookOk (timeAddGhost timeMpl) (withLsRet timeAddBudgetSpec) :=
  timeAddGhostHookExternOnlyLsRet_timeAddBudgetSpec_ok hpl hkeep_stub
    timeAddPanicExterns_expectFailed hlr_ne_stub

theorem timeAddGhost_timeAddSpec_withAlloc_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hkeep_stub : keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (timeAddGhost timeMpl)
      (withLsRet (withAlloc A lim CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  timeAddGhostHookExternOnlyLsRet_timeAddSpec_withAlloc_ok hpl hkeep_stub
    timeAddPanicExterns_expectFailed hlr_ne_stub A lim

theorem timeAddGhost_e2eTimeAddSpec_ok [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hkeep_stub : keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    HookOk (timeAddGhost timeMpl) (withLsRet CryptoVerification.E2E.HooksE.timeAddSpec) :=
  timeAddGhostHookExternOnlyLsRet_e2eTimeAddSpec_ok hpl hkeep_stub
    timeAddPanicExterns_expectFailed hlr_ne_stub

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

theorem timeAddGhost_preserves_execFrozen [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (timeAddGhost timeMpl u).mem := by
  unfold timeAddGhost timeAddGhostHookExternOnlyLsRet
  rw [timeAddGhostHookExternOnly_eq]
  exact linkedCallHook_preserves_execFrozen
    (fun s hs => ExecFrozen.of_perm_eq hs (timeAddHook_vmPreserved s).perm_eq) hfr

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u
  dsimp only [State.setPC] at hpc ⊢
  subst hpc
  rfl

private theorem realProg617_svc (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard :=
  rfl

/-- Behind-stub (`StubReachesTargetOn`) `GhostRowReplayOn` for `lsTimeAddSym` (`entryGuard :=
    fun _ => True`, `F1` + `H1` compliant). -/
theorem timeAddGhost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl timeMpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : timeMultiLib.Placeable timeMpl)
    (hCL : ∀ u : State, InvS u → (timeAddSubProg timeMpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_timeAdd timeMpl lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_timeAdd timeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsTimeAddSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn
        (fun m => (timeAddSubProg timeMpl).CodeLoaded m)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsTimeAddSym)
        (timeMultiLib.fnAddr timeMpl timeAddSym)) :
    GhostRowReplayOn mpl mmpl InvS EG lsTimeAddSym (fun _ => True)
      (timeAddGhost timeMpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨timeAddGhost_preserves_execFrozen timeMpl hfr,
     timeAddGhost_fs timeMpl u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    have hRep :=
      timeAddGhostHookExternOnlyLsRet_replaysOn
        (InvMem := fun m => (timeAddSubProg timeMpl).CodeLoaded m)
        (keep := keepR_timeAdd timeMpl)
        (P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (stubPc := libsignalSessionLib.resolve mpl lsTimeAddSym)
        (timeMpl := timeMpl)
        (externs := timeAddPanicExterns)
        hpl
        (realProg617_svc mpl mmpl W)
        (fun _ hk => hRealHullNoExt W hk)
        timeAddPanicExterns_expectFailed
        (hPanReal W)
        hKeep
        hlr_ne_stub
        (hRealStubNone W)
        (hStub W)
        (fun _ _ hInvM => timeAddSubProg_codeLoaded_stripExecOutside hInvM)
        (fun _ _ hInvM hkf => hInvM.of_keepsFrozen hkf)
    refine ⟨hRep.1, ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    obtain ⟨hSteps, hfr_fu, _, hfs_fu⟩ := hRep.2 u hpc hrun hnoex hfr (hCL u hInvU)
    exact ⟨hSteps, hfr_fu, hInvKeep u (timeAddGhost timeMpl u) hInvU hkf hfs_fu⟩

/-- **Artifact 2a (`CC-R0`, Row 3) — Direct `.text.lib2` `GhostRowReplayOn` for `lsTimeAddSym`:**
    Route `R0` + `K4` (`entryGuard := fun _ => True`), discharging `hRealStubNone` and `hStub`
    directly from `hTargetEq : libsignalSessionLib.resolve mpl lsTimeAddSym =
    timeMultiLib.fnAddr timeMpl timeAddSym` (`F1` + `H1` compliant). -/
theorem timeAddGhost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl timeMpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : timeMultiLib.Placeable timeMpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsTimeAddSym =
      timeMultiLib.fnAddr timeMpl timeAddSym)
    (hCL : ∀ u : State, InvS u → (timeAddSubProg timeMpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_timeAdd timeMpl lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_timeAdd timeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked) :
    GhostRowReplayOn mpl mmpl InvS EG lsTimeAddSym (fun _ => True)
      (timeAddGhost timeMpl) :=
  timeAddGhost_rowReplayOn_of_stub mpl mmpl timeMpl InvS EG hpl hCL hInvKeep hKeep
    hlr_ne_stub hRealHullNoExt hPanReal
    (fun W => by rw [hTargetEq]; exact hRealHullNoExt W (keepR_timeAdd_entry timeMpl))
    (fun _ u hpc _ _ _ => by
      rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)]
      exact Steps.refl _)

/-! ## 4. `TimeAddRowSpec`, `GhostRowSpecOk`, `GhostRowOk` & `ExtraEntryGuard` Helpers -/

/-- `TimeAddRowSpec` (`withLsRet` outermost) for `timeAddGhost timeMpl`. -/
theorem timeAddGhost_timeAddRowSpec [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hkeep_stub : keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    TimeAddRowSpec (timeAddGhost timeMpl) :=
  TimeAddRowSpec.of_ls_vm
    (timeAddGhost_timeAddSpec_ok timeMpl hpl hkeep_stub hlr_ne_stub)
    (timeAddGhost_vmPreserved timeMpl hpl hkeep_stub hlr_ne_stub)

/-- **Artifact 1 (`CC-R0`, Row 3):** `GhostRowSpecOk lsTimeAddSym (timeAddGhost timeMpl)` under
    `timeMultiLib.Placeable timeMpl`, `keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) =
    false`, and `∀ lr, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl`. -/
theorem timeAddGhost_rowSpecOk [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hpl : timeMultiLib.Placeable timeMpl)
    (hkeep_stub : keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl) :
    GhostRowSpecOk lsTimeAddSym (timeAddGhost timeMpl) where
  fs_eq := timeAddGhost_fs timeMpl
  fsT := timeAddGhost_fsT timeMpl
  rowSpec := by
    unfold ExtraRowSpec
    have hd1 : (lsTimeAddSym == "bcmp") = false := by decide
    have hd2 : (lsTimeAddSym == "strlen") = false := by decide
    have hd3 : (lsTimeAddSym == "memmove") = false := by decide
    have hd4 : (lsTimeAddSym == lsFromUtf8Sym) = false := by decide
    have hd5 : (lsTimeAddSym == lsMemrchrSym) = false := by decide
    have hd6 : (lsTimeAddSym == lsDurationSinceSym) = false := by decide
    have hd7 : (lsTimeAddSym == lsTimeAddSym) = true := by decide
    simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, Bool.false_eq_true, ↓reduceIte]
    exact timeAddGhost_timeAddRowSpec timeMpl hpl hkeep_stub hlr_ne_stub

private noncomputable def dummyCliHooks : CliHooks := by
  classical
  exact {
    C := {
      F := fun s _ => s
      E := fun _ b => b
      D := fun _ b => b
      X := fun k _ => k
      pubKey := fun k => k
    }
    Q := {
      F512 := fun s _ => s
      montToEd := fun _ _ => none
      compress := fun _ => List.Vector.replicate 32 0#8
      edNeg := fun p => p
      isTorsionFree := fun _ => false
      dsmb := fun _ p _ => p
      scalarMod := fun s => s
      scalarWide := fun _ => List.Vector.replicate 32 0#8
      encaps := fun pk c => (pk, c)
      decaps := fun _ _ => List.Vector.replicate 32 0#8
      K := {
        keyPair := fun _ => List.Vector.replicate 2400 0#8
        encaps1 := fun _ _ => none
        encaps2 := fun _ _ => List.Vector.replicate 128 0#8
        decaps := fun _ _ _ => List.Vector.replicate 32 0#8
        validPk := fun _ _ => false
      }
    }
  }

private theorem keepR_timeAdd_expectFailed_false
    {mpl mmpl timeMpl : Obj.MultiPlacement}
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_timeAdd timeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked) :
    keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false := by
  cases hk : keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl)
  · rfl
  · have hnone := hRealHullNoExt dummyCliHooks hk
    rw [hPanReal dummyCliHooks] at hnone
    cases hnone

/-- Behind-stub `GhostRowOk` bundle (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) for `lsTimeAddSym`,
    deriving `keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false` from
    `hRealHullNoExt` + `hPanReal` (`TimeAddPanicGhostK.lean:539`). -/
theorem timeAddGhost_rowOk_of_stub [LibsignalPlacement]
    (mpl mmpl timeMpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : timeMultiLib.Placeable timeMpl)
    (hCL : ∀ u : State, InvS u → (timeAddSubProg timeMpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_timeAdd timeMpl lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_timeAdd timeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsTimeAddSym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn
        (fun m => (timeAddSubProg timeMpl).CodeLoaded m)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsTimeAddSym)
        (timeMultiLib.fnAddr timeMpl timeAddSym)) :
    GhostRowOk mpl mmpl InvS EG lsTimeAddSym (fun _ => True)
      (timeAddGhost timeMpl) :=
  ⟨timeAddGhost_rowSpecOk timeMpl hpl
     (keepR_timeAdd_expectFailed_false hRealHullNoExt hPanReal) hlr_ne_stub,
   timeAddGhost_rowReplayOn_of_stub mpl mmpl timeMpl InvS EG hpl hCL hInvKeep hKeep
     hlr_ne_stub hRealHullNoExt hPanReal hRealStubNone hStub⟩

/-- **Full per-row `GhostRowOk` bundle (`GhostRowSpecOk` ∧ `GhostRowReplayOn`)** for `lsTimeAddSym`
    (`entryGuard := fun _ => True`), deriving `hkeep_stub` from `hRealHullNoExt` + `hPanReal`. -/
theorem timeAddGhost_rowOk [LibsignalPlacement]
    (mpl mmpl timeMpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : timeMultiLib.Placeable timeMpl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsTimeAddSym =
      timeMultiLib.fnAddr timeMpl timeAddSym)
    (hCL : ∀ u : State, InvS u → (timeAddSubProg timeMpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_timeAdd timeMpl lr = false)
    (hlr_ne_stub : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_timeAdd timeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hPanReal : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked) :
    GhostRowOk mpl mmpl InvS EG lsTimeAddSym (fun _ => True)
      (timeAddGhost timeMpl) :=
  ⟨timeAddGhost_rowSpecOk timeMpl hpl
     (keepR_timeAdd_expectFailed_false hRealHullNoExt hPanReal) hlr_ne_stub,
   timeAddGhost_rowReplayOn mpl mmpl timeMpl InvS EG hpl hTargetEq hCL hInvKeep hKeep
     hlr_ne_stub hRealHullNoExt hPanReal⟩

theorem extraEntryGuard_timeAdd_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf lsTimeAddSym s0 ↔ timeAddEntryGuard mpl s0) :
    guardOf lsTimeAddSym s0 :=
  hGuardEq.mpr trivial

theorem extraEntryGuard_singleton_timeAdd [LibsignalPlacement]
    {mpl timeMpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hg : g.extra = [(lsTimeAddSym, timeAddGhost timeMpl)])
    (hGuardEq : guardOf lsTimeAddSym s0 ↔ timeAddEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 := by
  intro sym _ _ hLook
  rw [hg] at hLook
  simp only [List.lookup] at hLook
  by_cases hSym : (sym == lsTimeAddSym) = true
  · have hEq := eq_of_beq hSym
    subst hEq
    exact hGuardEq.mpr trivial
  · simp [hSym] at hLook

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays
