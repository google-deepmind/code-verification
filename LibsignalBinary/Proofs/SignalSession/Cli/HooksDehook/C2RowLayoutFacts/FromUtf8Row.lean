/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8 -- proof-setup: allow-public-import
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Cutover-2 (`C2`) Full `GhostRowOk` Discharge for `core::str::converts::from_utf8` (`C2RowLayoutFacts.FromUtf8Row`)

**Checked by Lean. Untrusted (`Role::Proof`).**

Supplies the full per-row `GhostRowOk` (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) theorem
`c2_fromUtf8MplGhost_rowOk` for `lsFromUtf8Sym` consumed by `ExtraOk` / `ExtraListOk`
(`ExtraGhostReplay.lean:376-386, 437-456`) and `CliGhostA0Hooks.extraOk`
(`CliHookSatPlaced.lean:385`, `ExtraGhostSpecs.lean:313-321`), building directly on
`C2RowLayoutFacts.FromUtf8` in the lightweight `HooksDehook` + `Lib2LayoutFacts` import cone
(`0` `CliStrictPlaced2` / `Cli.Main` imports):

1. **Consumer conclusions (`§3`):**
   - `c2_fromUtf8MplGhost_rowOk`: `GhostRowOk mpl mmpl (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
     (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')) lsFromUtf8Sym
     (fromUtf8EntryGuard mpl) (fromUtf8MplGhost mpl mmpl c2FromUtf8TableAddr)`;
   - `c2_fromUtf8MplGhost_rowOk_guardOf`: `guardOf`-adapted form for `ExtraListReplaysOn`;
   - `c2_fromUtf8MplGhost_rowOk_startupLr`: `guardOf`-adapted form discharging `fromUtf8EntryGuard mpl`
     directly via `FromUtf8.c2FromUtf8EntryGuard_of_resolve` from `s0.readReg64 .lr = f3StartupLrVal`
     (`= f3StdLayout.libcStartMainStage2Addr + 56#64`, definitionally equal to `StdMainEntryLr f3StdLayout s0`);
   - `c2FromUtf8EntryGuard_of_stage2Lr` / `f3FromUtf8EntryGuard_of_stage2Lr`: direct stage2+56 (`lr`)
     corollaries matching `StdMainEntryLr f3StdLayout s0`.
2. **Internal premise discharges (`§2`, `0` hex literals):**
   - `hpl`: `FromUtf8.c2_fromUtf8Block_placeable_unrelaxed hLs hRes`;
   - `hTargetEq`: `rfl`;
   - `hCL`: `c2_fromUtf8_hCL` (`codeLoaded_of_checkProgCodeSubslice` from `(hInv u hu).rxCode` +
     `hRxUtf8` + `hRes`);
   - `hRo`: `FromUtf8.c2_fromUtf8_hRo_of_f3CodeInv hRoSlice hLs` (keyed to `c2FromUtf8TableAddr`);
   - `hInvKeep`: unconditional via `StartupStatics.F3CodeInv.of_keepsFrozen` + `v.fs = u.fs`;
   - `hGhostAt`: `c2_fromUtf8_hGhostAt` (`f3RxSeg_ghostProg617_externAt_entry` +
     `cliGhostExternsWithExtra_extra_some`);
   - `hRealHullNoExt`: `c2_fromUtf8_hRealHullNoExt` (`f3RxSeg_realProg617_externAt_none` +
     `keepLib2Text_sub_rxProg` + `FromUtf8.keepR_fromUtf8Mpl_sub_keepLib2Text`);
   - `hGhostNoExtNe`: standalone `c2_fromUtf8_hGhostNoExtNe_of_linkedAt`
     (`f3Row_ghostProg617_externAt_none_of_ne_entry` + interned extern `ρ` lookup on
     `cliElfMultiPlacement` over generated `c2RxDehookedSyms`, holding both pre-T4 and post-T4
     with `0` extra `C2ResolveFacts` premises).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8Row

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib lsFromUtf8Sym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliGhostExternsWithExtra cliGhostExternsWithExtra_extra_some)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock (fromUtf8Placement)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Ghost (keepFromUtf8Block)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays
  (fromUtf8EntryGuard fromUtf8MplGhost fromUtf8MplGhost_rowOk fromUtf8MplPlacement fromUtf8SubProg
   ghostRowReplayOn_of_guard_imp keepR_fromUtf8Mpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8
  (c2FromUtf8EntryGuard_of_resolve c2_fromUtf8Block_placeable_unrelaxed
   c2_fromUtf8_hRo_of_f3CodeInv f3FromUtf8EntryGuard_of_startupLr
   keepR_fromUtf8Mpl_sub_keepLib2Text)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (lsPlacedStubPairs lsPlacedStubPairs_eq ls_idsOk ls_sharedExterns_lt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElf_linkedAt_unique lsInternedMultiLib lsSharedExterns
   ls_names_nodup ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts C2RoSliceFacts f3Row_ghostProg617_externAt_none_of_ne_entry
   f3RxSeg_ghostProg617_externAt_entry f3RxSeg_realProg617_externAt_none f3StartupLrVal
   keepLib2Text_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FromUtf8Addr c2FromUtf8TableAddr c2RxDehookedSyms)

/-! ## 1. `hInvKeep` & Fast Interned Extern `ρ` Lookup on `c2RxDehookedSyms` -/

-- DUP(RowCommon): unconditional `hInvKeep` on `F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs`
private theorem f3CodeInv_and_fs_hInvKeep (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop) :
    ∀ u v : State, (F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs) →
      u.mem.KeepsFrozen v.mem → v.fs = u.fs →
      (F3CodeInv mpl mmpl v.mem ∧ PredFs v.fs) := by
  intro _ _ ⟨hmem, hfs⟩ hkf hvfs
  exact ⟨hmem.of_keepsFrozen hkf, hvfs ▸ hfs⟩

-- Fast interned-ID `resolve = cliElfMultiPlacement.ρ` on the 19 symbols in `c2RxDehookedSyms`
-- (via `ElfCodeMatchesData.lsPlacedStubPairs`, never unpacking `GeneratedLean.libsignalSessionExterns`).
private def findStubPosAux (target : String) : List (String × BitVec 64) → Nat → Nat
  | [], acc => acc
  | (nm, _) :: rest, acc =>
    if nm == target then acc else findStubPosAux target rest (acc + 1)

private noncomputable def checkC2RxExternSym (s : String) : Bool :=
  let pos := findStubPosAux s lsPlacedStubPairs 0
  let idx := lsSharedExterns.getD pos 0
  let pair := lsPlacedStubPairs.getD pos ("", 0#64)
  Nat.blt pos lsSharedExterns.length &&
  (pair.1 == s) &&
  (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none)

set_option maxRecDepth 400000 in
private theorem c2RxDehookedSyms_extern_ok :
    c2RxDehookedSyms.all checkC2RxExternSym = true := by
  rfl_kernel

private theorem resolve_c2RxSym_eq_cliElf_rho {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s : String} (hs : s ∈ c2RxDehookedSyms) :
    libsignalSessionLib.resolve mpl s = cliElfMultiPlacement.ρ s := by
  have hchk := List.all_eq_true.mp c2RxDehookedSyms_extern_ok s hs
  unfold checkC2RxExternSym at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨hpos_lt, hpair_fst⟩, hblk_none⟩
  set pos := findStubPosAux s lsPlacedStubPairs 0
  set idx := lsSharedExterns.getD pos 0
  have hidx_eq : idx = lsSharedExterns[pos]'hpos_lt :=
    Obj.Interned.getD_of_lt hpos_lt
  have hidx_lt : idx < lsInternedMultiLib.names.length := by
    have hmem_ext : idx ∈ lsSharedExterns := by
      rw [hidx_eq]
      exact List.getElem_mem hpos_lt
    exact Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hmem_ext)
  have hname_eq : lsInternedMultiLib.names.getD idx "" = s := by
    have hplen : pos < lsPlacedStubPairs.length := by
      rw [lsPlacedStubPairs_eq, List.length_map]
      exact hpos_lt
    have hpair :
        lsPlacedStubPairs.getD pos ("", 0#64) =
          (lsInternedMultiLib.names.getD idx "",
            LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsSymAddrs.getD
              idx 0#64) := by
      rw [Obj.Interned.getD_of_lt hplen]
      simp only [lsPlacedStubPairs_eq, List.getElem_map, ← hidx_eq]
    exact (congrArg Prod.fst hpair).symm.trans hpair_fst
  have hs_mem : s ∈ lsInternedMultiLib.names := by
    rw [← hname_eq, Obj.Interned.getD_of_lt hidx_lt]
    exact List.getElem_mem hidx_lt
  have hnone : Obj.lookupBlockSym s libsignalSessionLib.blocks = none := by
    rw [← hname_eq, ls_toMultiPlacedLib_eq,
      Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hidx_lt]
    exact hblk_none
  have huniq := (cliElf_linkedAt_unique hLs).2.1 s hs_mem
  have hres_rho : libsignalSessionLib.resolve cliElfMultiPlacement s = cliElfMultiPlacement.ρ s := by
    unfold MultiPlacedLib.resolve
    rw [hnone]
  exact huniq.trans hres_rho

/-! ## 2. Per-Premise C2 `from_utf8` Discharges (`hCL`, `hRealHullNoExt`, `hGhostNoExtNe`, `hGhostAt`) -/

private theorem keepR_fromUtf8Mpl_sub_rxProg {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr)
    (pc : BitVec 64) (h : keepR_fromUtf8Mpl mpl pc = true) :
    progKeep f3TrialRxProg pc = true :=
  keepLib2Text_sub_rxProg (keepR_fromUtf8Mpl_sub_keepLib2Text hLs hRes pc h)

theorem lsFromUtf8Sym_mem_c2RxDehookedSyms :
    lsFromUtf8Sym ∈ c2RxDehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

/-- Every symbol in generated `c2RxDehookedSyms` other than `lsFromUtf8Sym` resolves under
    `cliElfMultiPlacement.ρ` outside `keepFromUtf8Block c2FromUtf8Addr` (holds by `rfl_kernel`
    both pre-T4 and post-T4). -/
private theorem c2RxOther_outside_fromUtf8Hull :
    ((c2RxDehookedSyms.filter (· != lsFromUtf8Sym)).all fun s =>
      !(keepFromUtf8Block c2FromUtf8Addr (cliElfMultiPlacement.ρ s))) = true := by
  rfl_kernel

/-- Exact `hCL` premise of `fromUtf8MplGhost_rowOk` at `c2FromUtf8TableAddr` from `F3CodeInv`,
    `hRes`, and `hRxUtf8`. -/
theorem c2_fromUtf8_hCL
    (hRxUtf8 : checkProgCodeSubslice f3TrialRxProg
      (fromUtf8SubProg (fromUtf8Placement c2FromUtf8Addr c2FromUtf8TableAddr)) = true)
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u →
      (fromUtf8SubProg (fromUtf8MplPlacement mpl c2FromUtf8TableAddr)).CodeLoaded u.mem := by
  intro u hu
  unfold fromUtf8MplPlacement
  rw [hRes]
  exact codeLoaded_of_checkProgCodeSubslice (hInv u hu).rxCode hRxUtf8

/-- Exact `hRealHullNoExt` premise of `fromUtf8MplGhost_rowOk` from `LinkedAt cliElfBytes mpl`,
    `C2ExternTableFacts mpl`, and `hRes`. -/
theorem c2_fromUtf8_hRealHullNoExt {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_fromUtf8Mpl mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  fun W {_} hkeep =>
    f3RxSeg_realProg617_externAt_none hExt W (keepR_fromUtf8Mpl_sub_rxProg hLs hRes _ hkeep)

/-- Standalone `hGhostNoExtNe` discharge for `fromUtf8MplGhost_rowOk` (`cliElf_linkedAt_unique` +
    `rfl_kernel` over generated `c2RxDehookedSyms`; `0` extra `C2ResolveFacts` premises). -/
theorem c2_fromUtf8_hGhostNoExtNe_of_linkedAt {mpl : Obj.MultiPlacement}
    (EG : CliHooks → String → Option (State → State))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_fromUtf8Mpl mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsFromUtf8Sym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none := by
  intro W pc hkeep hne
  refine f3Row_ghostProg617_externAt_none_of_ne_entry hExt EG W
    (keepR_fromUtf8Mpl_sub_rxProg hLs hRes) ?_ hkeep hne
  intro s hs hs_ne
  left
  dsimp only [keepR_fromUtf8Mpl]
  rw [hRes, resolve_c2RxSym_eq_cliElf_rho hLs hs]
  have hmem_filt : s ∈ c2RxDehookedSyms.filter (· != lsFromUtf8Sym) := by
    rw [List.mem_filter]
    exact ⟨hs, bne_iff_ne.mpr hs_ne⟩
  have hnot := List.all_eq_true.mp c2RxOther_outside_fromUtf8Hull s hmem_filt
  simpa using hnot

/-- Exact `hGhostAt` premise of `fromUtf8MplGhost_rowOk` for `EG := fun W' =>
    cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')` under `hLook`. -/
theorem c2_fromUtf8_hGhostAt {mpl mmpl : Obj.MultiPlacement}
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hExt : C2ExternTableFacts mpl)
    (hLook : extra.lookup lsFromUtf8Sym =
      some (fromUtf8MplGhost mpl mmpl c2FromUtf8TableAddr)) :
    ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsFromUtf8Sym) =
          some (fromUtf8MplGhost mpl mmpl c2FromUtf8TableAddr) := by
  intro W
  rw [f3RxSeg_ghostProg617_externAt_entry hExt _ W lsFromUtf8Sym_mem_c2RxDehookedSyms]
  exact cliGhostExternsWithExtra_extra_some g extra (cliExternsPlaced mmpl W) hLook
    (by decide +kernel)

/-! ## 3. Full Cutover-2 `GhostRowOk` & Startup Entry-Guard Discharges -/

/-- **Primary Cutover-2 `GhostRowOk` discharge for `lsFromUtf8Sym`:** matches `ExtraOk` /
    `ExtraListOk` (`ExtraGhostReplay.lean:376-386, 437-456`) and `CliGhostA0Hooks.extraOk`
    (`CliHookSatPlaced.lean:385`, `ExtraGhostSpecs.lean:313-321`) directly at
    `InvS := fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs` and
    `EG := fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')`. -/
theorem c2_fromUtf8MplGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsFromUtf8Sym =
      some (fromUtf8MplGhost mpl mmpl c2FromUtf8TableAddr))
    (hRoSlice : C2RoSliceFacts)
    (hExt : C2ExternTableFacts mpl)
    (hRxUtf8 : checkProgCodeSubslice f3TrialRxProg
      (fromUtf8SubProg (fromUtf8Placement c2FromUtf8Addr c2FromUtf8TableAddr)) = true)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsFromUtf8Sym
      (fromUtf8EntryGuard mpl)
      (fromUtf8MplGhost mpl mmpl c2FromUtf8TableAddr) :=
  fromUtf8MplGhost_rowOk mpl mmpl c2FromUtf8TableAddr (fun _ => false)
    (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    (c2_fromUtf8Block_placeable_unrelaxed hLs hRes)
    (c2_fromUtf8_hCL hRxUtf8 hRes (fun _ h => h.1))
    (c2_fromUtf8_hRo_of_f3CodeInv hRoSlice hLs (fun _ h => h.1))
    (f3CodeInv_and_fs_hInvKeep mpl mmpl PredFs)
    (c2_fromUtf8_hGhostAt g extra hExt hLook)
    (c2_fromUtf8_hRealHullNoExt hLs hExt hRes)
    (c2_fromUtf8_hGhostNoExtNe_of_linkedAt
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')) hLs hExt hRes)

/-- `guardOf`-adapted `GhostRowOk` for direct arm dispatch in `ExtraListReplaysOn` / `ExtraListOk`
    (`ExtraGhostReplay.lean:380-386`) when `guardOf lsFromUtf8Sym` implies `fromUtf8EntryGuard mpl`. -/
theorem c2_fromUtf8MplGhost_rowOk_guardOf [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsFromUtf8Sym =
      some (fromUtf8MplGhost mpl mmpl c2FromUtf8TableAddr))
    (hGuard : ∀ s0 : State, guardOf lsFromUtf8Sym s0 → fromUtf8EntryGuard mpl s0)
    (hRoSlice : C2RoSliceFacts)
    (hExt : C2ExternTableFacts mpl)
    (hRxUtf8 : checkProgCodeSubslice f3TrialRxProg
      (fromUtf8SubProg (fromUtf8Placement c2FromUtf8Addr c2FromUtf8TableAddr)) = true)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsFromUtf8Sym
      (guardOf lsFromUtf8Sym)
      (fromUtf8MplGhost mpl mmpl c2FromUtf8TableAddr) := by
  have hRow := c2_fromUtf8MplGhost_rowOk mpl mmpl PredFs g extra hLook
    hRoSlice hExt hRxUtf8 hRes hLs
  exact ⟨hRow.1, ghostRowReplayOn_of_guard_imp hRow.2 hGuard⟩

/-- `guardOf`-adapted `GhostRowOk` discharging `fromUtf8EntryGuard mpl` directly via
    `FromUtf8.c2FromUtf8EntryGuard_of_resolve` from `s0.readReg64 .lr = f3StartupLrVal`
    (`= f3StdLayout.libcStartMainStage2Addr + 56#64`, definitionally equal to
    `StdMainEntryLr f3StdLayout s0`). -/
theorem c2_fromUtf8MplGhost_rowOk_startupLr [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsFromUtf8Sym =
      some (fromUtf8MplGhost mpl mmpl c2FromUtf8TableAddr))
    (hGuardLr : ∀ s0 : State, guardOf lsFromUtf8Sym s0 → s0.readReg64 .lr = f3StartupLrVal)
    (hRoSlice : C2RoSliceFacts)
    (hExt : C2ExternTableFacts mpl)
    (hRxUtf8 : checkProgCodeSubslice f3TrialRxProg
      (fromUtf8SubProg (fromUtf8Placement c2FromUtf8Addr c2FromUtf8TableAddr)) = true)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsFromUtf8Sym
      (guardOf lsFromUtf8Sym)
      (fromUtf8MplGhost mpl mmpl c2FromUtf8TableAddr) :=
  c2_fromUtf8MplGhost_rowOk_guardOf mpl mmpl PredFs guardOf g extra hLook
    (fun s0 hg => c2FromUtf8EntryGuard_of_resolve hLs hRes (hGuardLr s0 hg))
    hRoSlice hExt hRxUtf8 hRes hLs

/-- Block-`617` startup `stage2 + 56` (`StdMainEntryLr f3StdLayout s0`) discharge of
    `fromUtf8EntryGuard mpl s0` routing directly through `FromUtf8.c2FromUtf8EntryGuard_of_resolve`
    without importing `CliStrictPlaced2`. -/
theorem c2FromUtf8EntryGuard_of_stage2Lr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr)
    {s0 : State} (hlr : s0.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64) :
    fromUtf8EntryGuard mpl s0 :=
  c2FromUtf8EntryGuard_of_resolve hLs hRes hlr

/-- Block-`617` startup `stage2 + 56` (`StdMainEntryLr f3StdLayout s0`) discharge of
    `fromUtf8EntryGuard mpl s0` routing through `FromUtf8.f3FromUtf8EntryGuard_of_startupLr`
    without importing `CliStrictPlaced2`. -/
theorem f3FromUtf8EntryGuard_of_stage2Lr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr)
    {s0 : State} (hlr : s0.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64) :
    fromUtf8EntryGuard mpl s0 :=
  f3FromUtf8EntryGuard_of_startupLr hLs hExt hRes hlr

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8Row
