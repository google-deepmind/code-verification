/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Dalek -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays -- proof-setup: allow-public-import

/-!
# Cutover-2 (`C2`) Dalek `.text.lib2` Per-Row `GhostRowOk` Glue (`C2RowLayoutFacts.DalekRows`)

Discharges the per-row `GhostRowOk` obligations at the Cutover-2 placement for the three Dalek
`.text.lib2` rows (`lsBlackBoxSym`, `lsSharedSecretDropSym`, `lsStaticSecretDropSym`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DalekRows

open Arm64 Arm64.Obj ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib lsBlackBoxSym
   lsSharedSecretDropSym lsStaticSecretDropSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays
  (blackBoxEntryGuard blackBoxGhost blackBoxGhost_rowOk blackBoxSubProg
   ghostRowReplayOn_of_guard_imp keepR_blackBox)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxLrTrap (keepBlackBox)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Dalek
  (keepR_blackBox_sub_keepLib2Text keepR_sharedSecretDrop_sub_keepLib2Text
   keepR_staticSecretDrop_sub_keepLib2Text)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_ghostAt_of_extraLookup c2_realHullNoExt_of_keepLib2Text checkProgCodeSubslice
   f3CodeInv_and_fs_keepsFrozen f3CodeInv_codeLoaded_of_checkProgCodeSubslice
   resolve_c2RxSym_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays
  (keepR_sharedSecretDrop sharedSecretDropEntryGuard sharedSecretDropGhost
   sharedSecretDropGhost_rowOk sharedSecretDropHullBase sharedSecretDropSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays
  (keepR_staticSecretDrop staticSecretDropEntryGuard staticSecretDropGhost
   staticSecretDropGhost_rowOk staticSecretDropSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost (sharedSecretDropEntryOff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap
  (keepSharedSecretDropHull keepStaticSecretDrop)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced (cliElfMultiPlacement)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3Row_ghostProg617_externAt_none_of_ne_entry keepLib2Text_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BlackBoxAddr c2RxDehookedSyms c2SharedSecretDropAddr c2StaticSecretDropAddr)

/-! ## 1. `black_box` (`lsBlackBoxSym`) -/

private theorem lsBlackBoxSym_mem_c2RxDehookedSyms :
    lsBlackBoxSym ∈ c2RxDehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

private theorem c2RxOther_outside_blackBox :
    ((c2RxDehookedSyms.filter (· != lsBlackBoxSym)).all
      (fun s => !(keepBlackBox c2BlackBoxAddr (cliElfMultiPlacement.ρ s)))) = true := by
  rfl_kernel

theorem c2_blackBox_hGhostNoExtNe
    {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (hResBlackBox : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (EG : CliHooks → String → Option (State → State)) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_blackBox mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsBlackBoxSym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none := by
  intro W pc hkeep hne
  refine f3Row_ghostProg617_externAt_none_of_ne_entry hExt EG W
    (fun q hq => keepLib2Text_sub_rxProg (keepR_blackBox_sub_keepLib2Text hResBlackBox q hq))
    (fun s hs hs_ne => Or.inl ?_) hkeep hne
  have hfilt : s ∈ c2RxDehookedSyms.filter (· != lsBlackBoxSym) :=
    List.mem_filter.mpr ⟨hs, bne_iff_ne.mpr hs_ne⟩
  have hout := List.all_eq_true.mp c2RxOther_outside_blackBox s hfilt
  simp only [Bool.not_eq_true'] at hout
  dsimp only [keepR_blackBox]
  rw [hResBlackBox, resolve_c2RxSym_eq_cliElf_rho hLs hs]
  exact hout

/-- Cutover-2 `GhostRowOk` discharge for `lsBlackBoxSym` (`BlackBoxGhostReplays.blackBoxGhost_rowOk`). -/
theorem c2_blackBoxGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsBlackBoxSym = some (blackBoxGhost mpl mmpl))
    (hExt : C2ExternTableFacts mpl)
    (hRxBlackBox : checkProgCodeSubslice f3TrialRxProg (blackBoxSubProg mpl) = true)
    (hResBlackBox : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsBlackBoxSym
      (blackBoxEntryGuard mpl)
      (blackBoxGhost mpl mmpl) :=
  blackBoxGhost_rowOk mpl mmpl
    (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    (f3CodeInv_codeLoaded_of_checkProgCodeSubslice hRxBlackBox)
    (f3CodeInv_and_fs_keepsFrozen mpl mmpl PredFs)
    (c2_ghostAt_of_extraLookup hExt g extra lsBlackBoxSym_mem_c2RxDehookedSyms (by decide) hLook)
    (c2_realHullNoExt_of_keepLib2Text hExt (keepR_blackBox_sub_keepLib2Text hResBlackBox))
    (c2_blackBox_hGhostNoExtNe hExt hResBlackBox hLs _)

/-- `guardOf`-adapted `GhostRowOk` for `lsBlackBoxSym`. -/
theorem c2_blackBoxGhost_rowOk_guardOf [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsBlackBoxSym = some (blackBoxGhost mpl mmpl))
    (hGuard : ∀ s0 : State, guardOf lsBlackBoxSym s0 → blackBoxEntryGuard mpl s0)
    (hExt : C2ExternTableFacts mpl)
    (hRxBlackBox : checkProgCodeSubslice f3TrialRxProg (blackBoxSubProg mpl) = true)
    (hResBlackBox : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsBlackBoxSym
      (guardOf lsBlackBoxSym)
      (blackBoxGhost mpl mmpl) := by
  have hRow := c2_blackBoxGhost_rowOk mpl mmpl PredFs g extra hLook hExt hRxBlackBox hResBlackBox hLs
  exact ⟨hRow.1, ghostRowReplayOn_of_guard_imp hRow.2 hGuard⟩

/-! ## 2. `SharedSecret::drop` (`lsSharedSecretDropSym`) -/

private theorem lsSharedSecretDropSym_mem_c2RxDehookedSyms :
    lsSharedSecretDropSym ∈ c2RxDehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

private theorem c2RxOther_outside_sharedSecretDrop :
    ((c2RxDehookedSyms.filter (· != lsSharedSecretDropSym)).all
      (fun s => !(keepSharedSecretDropHull (c2SharedSecretDropAddr - sharedSecretDropEntryOff)
        (cliElfMultiPlacement.ρ s)))) = true := by
  rfl_kernel

theorem c2_sharedSecretDrop_hGhostNoExtNe
    {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (hResSharedDrop : libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (EG : CliHooks → String → Option (State → State)) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_sharedSecretDrop mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsSharedSecretDropSym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none := by
  intro W pc hkeep hne
  refine f3Row_ghostProg617_externAt_none_of_ne_entry hExt EG W
    (fun q hq => keepLib2Text_sub_rxProg (keepR_sharedSecretDrop_sub_keepLib2Text hResSharedDrop q hq))
    (fun s hs hs_ne => Or.inl ?_) hkeep hne
  have hfilt : s ∈ c2RxDehookedSyms.filter (· != lsSharedSecretDropSym) :=
    List.mem_filter.mpr ⟨hs, bne_iff_ne.mpr hs_ne⟩
  have hout := List.all_eq_true.mp c2RxOther_outside_sharedSecretDrop s hfilt
  simp only [Bool.not_eq_true'] at hout
  dsimp only [keepR_sharedSecretDrop, sharedSecretDropHullBase]
  rw [hResSharedDrop, resolve_c2RxSym_eq_cliElf_rho hLs hs]
  exact hout

/-- Cutover-2 `GhostRowOk` discharge for `lsSharedSecretDropSym`
    (`SharedSecretDropGhostReplays.sharedSecretDropGhost_rowOk`). -/
theorem c2_sharedSecretDropGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsSharedSecretDropSym = some (sharedSecretDropGhost mpl mmpl))
    (hExt : C2ExternTableFacts mpl)
    (hRxSharedDrop : checkProgCodeSubslice f3TrialRxProg (sharedSecretDropSubProg mpl) = true)
    (hResSharedDrop : libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsSharedSecretDropSym
      (sharedSecretDropEntryGuard mpl)
      (sharedSecretDropGhost mpl mmpl) :=
  sharedSecretDropGhost_rowOk mpl mmpl
    (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    (f3CodeInv_codeLoaded_of_checkProgCodeSubslice hRxSharedDrop)
    (f3CodeInv_and_fs_keepsFrozen mpl mmpl PredFs)
    (c2_ghostAt_of_extraLookup hExt g extra lsSharedSecretDropSym_mem_c2RxDehookedSyms
      (by decide) hLook)
    (c2_realHullNoExt_of_keepLib2Text hExt
      (keepR_sharedSecretDrop_sub_keepLib2Text hResSharedDrop))
    (c2_sharedSecretDrop_hGhostNoExtNe hExt hResSharedDrop hLs _)

/-- `guardOf`-adapted `GhostRowOk` for `lsSharedSecretDropSym`. -/
theorem c2_sharedSecretDropGhost_rowOk_guardOf [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsSharedSecretDropSym = some (sharedSecretDropGhost mpl mmpl))
    (hGuard : ∀ s0 : State, guardOf lsSharedSecretDropSym s0 → sharedSecretDropEntryGuard mpl s0)
    (hExt : C2ExternTableFacts mpl)
    (hRxSharedDrop : checkProgCodeSubslice f3TrialRxProg (sharedSecretDropSubProg mpl) = true)
    (hResSharedDrop : libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsSharedSecretDropSym
      (guardOf lsSharedSecretDropSym)
      (sharedSecretDropGhost mpl mmpl) := by
  have hRow := c2_sharedSecretDropGhost_rowOk mpl mmpl PredFs g extra hLook hExt
    hRxSharedDrop hResSharedDrop hLs
  exact ⟨hRow.1, ghostRowReplayOn_of_guard_imp hRow.2 hGuard⟩

/-! ## 3. `StaticSecret::drop` (`lsStaticSecretDropSym`) -/

private theorem lsStaticSecretDropSym_mem_c2RxDehookedSyms :
    lsStaticSecretDropSym ∈ c2RxDehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

private theorem c2RxOther_outside_staticSecretDrop :
    ((c2RxDehookedSyms.filter (· != lsStaticSecretDropSym)).all
      (fun s => !(keepStaticSecretDrop c2StaticSecretDropAddr
        (cliElfMultiPlacement.ρ s)))) = true := by
  rfl_kernel

theorem c2_staticSecretDrop_hGhostNoExtNe
    {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (hResStaticDrop : libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (EG : CliHooks → String → Option (State → State)) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_staticSecretDrop mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsStaticSecretDropSym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none := by
  intro W pc hkeep hne
  refine f3Row_ghostProg617_externAt_none_of_ne_entry hExt EG W
    (fun q hq => keepLib2Text_sub_rxProg (keepR_staticSecretDrop_sub_keepLib2Text hResStaticDrop q hq))
    (fun s hs hs_ne => Or.inl ?_) hkeep hne
  have hfilt : s ∈ c2RxDehookedSyms.filter (· != lsStaticSecretDropSym) :=
    List.mem_filter.mpr ⟨hs, bne_iff_ne.mpr hs_ne⟩
  have hout := List.all_eq_true.mp c2RxOther_outside_staticSecretDrop s hfilt
  simp only [Bool.not_eq_true'] at hout
  dsimp only [keepR_staticSecretDrop]
  rw [hResStaticDrop, resolve_c2RxSym_eq_cliElf_rho hLs hs]
  exact hout

/-- Cutover-2 `GhostRowOk` discharge for `lsStaticSecretDropSym`
    (`StaticSecretDropGhostReplays.staticSecretDropGhost_rowOk`). -/
theorem c2_staticSecretDropGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsStaticSecretDropSym = some (staticSecretDropGhost mpl mmpl))
    (hExt : C2ExternTableFacts mpl)
    (hRxStaticDrop : checkProgCodeSubslice f3TrialRxProg (staticSecretDropSubProg mpl) = true)
    (hResStaticDrop : libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsStaticSecretDropSym
      (staticSecretDropEntryGuard mpl)
      (staticSecretDropGhost mpl mmpl) :=
  staticSecretDropGhost_rowOk mpl mmpl
    (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    (f3CodeInv_codeLoaded_of_checkProgCodeSubslice hRxStaticDrop)
    (f3CodeInv_and_fs_keepsFrozen mpl mmpl PredFs)
    (c2_ghostAt_of_extraLookup hExt g extra lsStaticSecretDropSym_mem_c2RxDehookedSyms
      (by decide) hLook)
    (c2_realHullNoExt_of_keepLib2Text hExt
      (keepR_staticSecretDrop_sub_keepLib2Text hResStaticDrop))
    (c2_staticSecretDrop_hGhostNoExtNe hExt hResStaticDrop hLs _)

/-- `guardOf`-adapted `GhostRowOk` for `lsStaticSecretDropSym`. -/
theorem c2_staticSecretDropGhost_rowOk_guardOf [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsStaticSecretDropSym = some (staticSecretDropGhost mpl mmpl))
    (hGuard : ∀ s0 : State, guardOf lsStaticSecretDropSym s0 → staticSecretDropEntryGuard mpl s0)
    (hExt : C2ExternTableFacts mpl)
    (hRxStaticDrop : checkProgCodeSubslice f3TrialRxProg (staticSecretDropSubProg mpl) = true)
    (hResStaticDrop : libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsStaticSecretDropSym
      (guardOf lsStaticSecretDropSym)
      (staticSecretDropGhost mpl mmpl) := by
  have hRow := c2_staticSecretDropGhost_rowOk mpl mmpl PredFs g extra hLook hExt
    hRxStaticDrop hResStaticDrop hLs
  exact ⟨hRow.1, ghostRowReplayOn_of_guard_imp hRow.2 hGuard⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DalekRows
