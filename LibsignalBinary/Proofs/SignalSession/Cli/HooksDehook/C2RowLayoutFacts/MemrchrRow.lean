/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.F3LayoutData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrExtraReplays -- proof-setup: allow-public-import

/-!
# Cutover-2 (`C2`) `memrchr` `.text.lib2` Per-Row `GhostRowOk` Glue (`C2RowLayoutFacts.MemrchrRow`)

Discharges the per-row `GhostRowOk` obligations at the Cutover-2 placement (`mpl := lsmpl`) for
Route-`R0` (`withLsRet`) `lsMemrchrSym` (`MemrchrExtraReplays.memrchrGhost_rowOk`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MemrchrRow

open Arm64 Arm64.Obj
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession (CliHooks cliElfBytes libsignalSessionLib lsMemrchrSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (StdMainEntryLr)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_keepLib2Text_of_sub_lt c2_realHullNoExt_of_keepLib2Text checkProgCodeSubslice
   f3CodeInv_and_fs_keepsFrozen f3CodeInv_codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (ExtraEntryGuard GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrExtraReplays
  (extraEntryGuard_memrchr_arm extraEntryGuard_singleton_memrchr keepR_memrchr
   keepR_memrchr_entry memrchrEntryGuard memrchrGhost memrchrGhost_rowOk
   memrchrHullByteLen memrchrSubProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3LsRetAddr624_rxRegion_guard keepLib2Text)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2Lib2TextHi c2Lib2TextLo c2MemrchrAddr)

/-! ## 1. Hull Inclusion & Caller `LsRetAddr624` Guard -/

/-- `keepR_memrchr mpl` (`[resolve mpl lsMemrchrSym, resolve mpl lsMemrchrSym + 260)`) lies inside
    `.text.lib2` (`keepLib2Text`) at the Cutover-2 placement. -/
theorem keepR_memrchr_sub_keepLib2Text {mpl : Obj.MultiPlacement}
    (hResMemrchr : libsignalSessionLib.resolve mpl lsMemrchrSym = c2MemrchrAddr) :
    ∀ pc : BitVec 64, keepR_memrchr mpl pc = true → keepLib2Text pc = true := by
  intro pc hkeep
  unfold keepR_memrchr at hkeep
  rw [hResMemrchr, decide_eq_true_eq] at hkeep
  exact c2_keepLib2Text_of_sub_lt hkeep
    (by decide : c2Lib2TextLo.toNat ≤ c2MemrchrAddr.toNat)
    (by decide : c2MemrchrAddr.toNat + memrchrHullByteLen ≤ c2Lib2TextHi.toNat)

/-- Every crate return address `LsRetAddr624 lr` lies outside `keepR_memrchr lsmpl` at Cutover-2. -/
theorem c2_memrchr_hKeep [LibsignalPlacement]
    (hResMemrchr : libsignalSessionLib.resolve lsmpl lsMemrchrSym = c2MemrchrAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_memrchr lsmpl lr = false :=
  fun _ hRet =>
    (f3LsRetAddr624_rxRegion_guard hLs hRet
      (Or.inr (keepR_memrchr_sub_keepLib2Text hResMemrchr _ (keepR_memrchr_entry lsmpl)))
      (fun pc hpc => Or.inr (keepR_memrchr_sub_keepLib2Text hResMemrchr pc hpc))).1

/-! ## 2. Per-Row `GhostRowOk` Glue (`mpl := lsmpl`, Single `LinkedAt`) -/

private theorem ghostRowReplayOn_of_guard_imp
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {sym : String} {entryGuard guard' : State → Prop} {f : State → State}
    (hRow : GhostRowReplayOn mpl mmpl InvS EG sym entryGuard f)
    (hImp : ∀ s0 : State, guard' s0 → entryGuard s0) :
    GhostRowReplayOn mpl mmpl InvS EG sym guard' f where
  preserves_execFrozen := hRow.preserves_execFrozen
  replay_at_stub := fun W s0 sf hG hRet hNoEx hNHalt =>
    hRow.replay_at_stub W s0 sf (hImp s0 hG) hRet hNoEx hNHalt

/-- Cutover-2 `GhostRowOk` discharge for Route-`R0` `lsMemrchrSym` at `mpl := lsmpl`
    (`MemrchrExtraReplays.memrchrGhost_rowOk`), polymorphic in `EG` with a single `LinkedAt`
    hypothesis `hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl`. -/
theorem c2_memrchrGhost_rowOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hRxMemrchr : checkProgCodeSubslice f3TrialRxProg (memrchrSubProg lsmpl) = true)
    (hResMemrchr : libsignalSessionLib.resolve lsmpl lsMemrchrSym = c2MemrchrAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      EG
      lsMemrchrSym
      (memrchrEntryGuard lsmpl)
      (memrchrGhost lsmpl mmpl) :=
  memrchrGhost_rowOk lsmpl mmpl
    (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
    EG
    (f3CodeInv_codeLoaded_of_checkProgCodeSubslice hRxMemrchr)
    (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
    (c2_memrchr_hKeep hResMemrchr hLs)
    (c2_realHullNoExt_of_keepLib2Text hExt (keepR_memrchr_sub_keepLib2Text hResMemrchr))

/-- `guardOf`-adapted `GhostRowOk` for `lsMemrchrSym` at `mpl := lsmpl`. -/
theorem c2_memrchrGhost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hGuard : ∀ s0 : State, guardOf lsMemrchrSym s0 → memrchrEntryGuard lsmpl s0)
    (hExt : C2ExternTableFacts lsmpl)
    (hRxMemrchr : checkProgCodeSubslice f3TrialRxProg (memrchrSubProg lsmpl) = true)
    (hResMemrchr : libsignalSessionLib.resolve lsmpl lsMemrchrSym = c2MemrchrAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      EG
      lsMemrchrSym
      (guardOf lsMemrchrSym)
      (memrchrGhost lsmpl mmpl) := by
  have hRow := c2_memrchrGhost_rowOk mmpl PredFs EG hExt hRxMemrchr hResMemrchr hLs
  exact ⟨hRow.1, ghostRowReplayOn_of_guard_imp hRow.2 hGuard⟩

/-! ## 3. Startup Entry-Guard Dischargers -/

/-- Trivial startup `StdMainEntryLr` discharge of `memrchrEntryGuard mpl s0` (`True`). -/
theorem c2MemrchrEntryGuard_of_stdMainEntryLr
    {mpl : Obj.MultiPlacement} {s0 : State}
    (_hlr : StdMainEntryLr f3StdLayout s0) :
    memrchrEntryGuard mpl s0 :=
  trivial

/-- Per-arm `lsMemrchrSym` `ExtraEntryGuard` discharge at Cutover-2. -/
theorem c2_extraEntryGuard_memrchr_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf lsMemrchrSym s0 ↔ memrchrEntryGuard mpl s0) :
    guardOf lsMemrchrSym s0 :=
  extraEntryGuard_memrchr_arm hGuardEq

/-- Singleton `g.extra = [(lsMemrchrSym, memrchrGhost mpl mmpl)]` `ExtraEntryGuard` discharge. -/
theorem c2_extraEntryGuard_singleton_memrchr [LibsignalPlacement]
    {mpl mmpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hg : g.extra = [(lsMemrchrSym, memrchrGhost mpl mmpl)])
    (hGuardEq : guardOf lsMemrchrSym s0 ↔ memrchrEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 :=
  extraEntryGuard_singleton_memrchr hg hGuardEq

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MemrchrRow
