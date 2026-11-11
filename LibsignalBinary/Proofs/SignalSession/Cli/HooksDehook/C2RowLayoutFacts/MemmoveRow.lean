/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Cutover-2 (`C2`) Full `GhostRowOk` Discharge for `"memmove"` (`C2RowLayoutFacts.MemmoveRow`)

**Checked by Lean. Untrusted (`Role::Proof`).**

Supplies the full Cutover-2 per-row `GhostRowOk` (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) theorem
`c2_memmoveGhost_rowOk` (plus `c2_memmoveGhost_rowOk_guardOf`, `c2MemmoveEntryGuard_of_stdMainEntryLr`,
and `f3MemmoveEntryGuard_c2_of_stdMainEntryLr`) for `"memmove"` over the `956` B `.text.b_pre` hull
(`["memmove", "memcpy", "memset"]`), discharging `MemmoveExtraReplays.memmoveGhost_rowOk`
(`MemmoveExtraReplays.lean:546`) with zero hex literals:

1. **`"memcpy"` / `"memset"` Resolution from `LinkedAt` Alone (`§1`):**
   - Both `"memcpy"` and `"memset"` are already at their final `.text.b_pre` addresses
     (`wp4MemcpyRealAddr` / `wp4MemsetRealAddr`) in `cliElfMultiPlacement.ρ` pre-T4 as well as
     post-T4. Via `RowCommon.resolve_c2RxSym_eq_cliElf_rho`,
     `libsignalSessionLib.resolve mpl "memcpy"` and `libsignalSessionLib.resolve mpl "memset"` are
     resolved from `hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl` alone (`0` `hResMemcpy` /
     `hResMemset` premises), discharging `hMemmoveOff`
     (`memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff`) from `hLs` + `hResMemmove`.
2. **`.text.b_pre` Hull Inclusion & `hGhostOffEntries` (`§2`):**
   - `keepR_memmove_sub_keepTextBPre` embeds `keepR_memmove mpl` into `keepTextBPre` (and hence
     `progKeep f3TrialRxProg`) from `hLs` alone, discharging `hRealHullNoExt`.
   - `c2_memmove_hGhostOffEntries_of_linkedAt` discharges `hGhostOffEntries` via
     `Lib2LayoutFacts.f3RowSyms_ghostProg617_externAt_none_of_ne_entries` (`rowSyms :=
     ["memmove", "memcpy", "memset"]`), `RowCommon.resolve_c2RxSym_eq_cliElf_rho`, and `rfl_kernel`
     over the generated `c2RxDehookedSyms`.
3. **Named `g.memcpy` / `g.memset` `TrapHook` & `cliExternsPlaced = none` via `hExt` (`§3`):**
   - On the `none` branch (`ElfSlicesPqOomH2KHooks.h2k_ghFixedK`, closed by `Or.inl rfl`),
     `cliExternsPlaced mmpl W' "memcpy" = none` and `cliExternsPlaced mmpl W' "memset" = none` are
     derived directly from `hExt : C2ExternTableFacts mpl` by equating
     `hExt.ghostRxEntry (cliExternsPlaced mmpl) W'` with `hExt.realRxNoExtern mmpl W'` on
     `keepTextBPre_sub_rxProg` (valid both pre-T4 and post-T4, never relying on `rfl` on the
     pre-T4 37-row `cliExternsPlaced`).
   - On the narrow Stage-A `R1` branch (`Or.inr rfl`, consumer-justified by
     `NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow_master_ok` at `NarrowF3R1Witness.lean:213` and
     `NarrowF3R1Witness.f3EmptyMemsetGhostHookNarrow_master_ok` at `NarrowF3R1Witness.lean:149`),
     universal-`L` `TrapHook L` holds via `MemmoveLrTrapBase.trapHook_f3EmptyMemcpyGhostHook`
     (`MemmoveLrTrapBase.lean:759`) and `MemmoveLrTrapBase.trapHook_f3EmptyMemsetGhostHook`
     (`MemmoveLrTrapBase.lean:825`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MemmoveRow

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib lsMemcpySym lsMemsetSym
   lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli
   lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (StdMainEntryLr)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_keepTextBPre_of_sub_lt f3CodeInv_and_fs_keepsFrozen resolve_c2RxSym_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode
  (mallocngBlockProg20_externAt_none mallocngBlockProg20_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode (bPreMemmoveByteOff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays
  (ghostRowReplayOn_of_guard_imp keepR_memmove memcpyEntry memmoveEntry memmoveEntryGuard
   memmoveEntryGuard_iff memmoveGhost memmoveGhost_rowOk memmoveSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost (keepBPreHull)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrapBase
  (trapHook_f3EmptyMemcpyGhostHook trapHook_f3EmptyMemsetGhostHook)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode
  (mallocngBlockProg21_externAt_none mallocngBlockProg21_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
  (f3EmptyMemcpyGhostHookNarrow f3EmptyMemsetGhostHookNarrow)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (TrapHook)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliGhostExternsWithExtra cliGhostExternsWithExtra_extra_some)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3BatchLEntryGuard_of_startupLr f3BatchL_dehookedSym_in_keepTextBPre
   f3RowSyms_ghostProg617_externAt_none_of_ne_entries f3RxSeg_realProg617_externAt_none
   keepTextBPre keepTextBPre_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced (cliElfMultiPlacement)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BatchLDehookedSyms c2MemmoveAddr c2RxDehookedSyms wp4MemcpyRealAddr wp4MemsetRealAddr)

/-! ## 1. `c2RxDehookedSyms` Interned `ρ` Resolution & `"memcpy"` / `"memset"` / `hMemmoveOff` -/

theorem memmove_mem_c2RxDehookedSyms : "memmove" ∈ c2RxDehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

theorem memcpy_mem_c2RxDehookedSyms : "memcpy" ∈ c2RxDehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

theorem memset_mem_c2RxDehookedSyms : "memset" ∈ c2RxDehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

theorem memmove_mem_c2BatchLDehookedSyms : "memmove" ∈ c2BatchLDehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

/-- `"memcpy"` is already at its final `.text.b_pre` address `wp4MemcpyRealAddr` in
    `cliElfMultiPlacement.ρ` both pre-T4 and post-T4 (`0` `hResMemcpy` premise needed). -/
theorem resolve_memcpy_eq_wp4MemcpyRealAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl "memcpy" = wp4MemcpyRealAddr := by
  rw [resolve_c2RxSym_eq_cliElf_rho hLs memcpy_mem_c2RxDehookedSyms]
  exact decide_eq_true_eq.mp (by rfl_kernel)

/-- `"memset"` is already at its final `.text.b_pre` address `wp4MemsetRealAddr` in
    `cliElfMultiPlacement.ρ` both pre-T4 and post-T4 (`0` `hResMemset` premise needed). -/
theorem resolve_memset_eq_wp4MemsetRealAddr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl "memset" = wp4MemsetRealAddr := by
  rw [resolve_c2RxSym_eq_cliElf_rho hLs memset_mem_c2RxDehookedSyms]
  exact decide_eq_true_eq.mp (by rfl_kernel)

/-- Exact `hMemmoveOff` premise of `MemmoveExtraReplays.memmoveGhost_rowOk` from `hLs` and
    `hResMemmove : libsignalSessionLib.resolve mpl "memmove" = c2MemmoveAddr`. -/
theorem c2_memmove_hMemmoveOff {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hResMemmove : libsignalSessionLib.resolve mpl "memmove" = c2MemmoveAddr) :
    memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff := by
  unfold memmoveEntry memcpyEntry
  rw [hResMemmove, resolve_memcpy_eq_wp4MemcpyRealAddr hLs]
  exact decide_eq_true_eq.mp (by rfl_kernel)

/-! ## 2. `.text.b_pre` Hull Inclusion, `hCL`, `hRealHullNoExt`, `hGhostEntry`, & `hGhostOffEntries` -/

/-- Hull inclusion `keepR_memmove mpl ⊆ keepTextBPre` from `LinkedAt cliElfBytes mpl` alone. -/
theorem keepR_memmove_sub_keepTextBPre {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {pc : BitVec 64} (hk : keepR_memmove mpl pc = true) :
    keepTextBPre pc = true := by
  unfold keepR_memmove keepBPreHull at hk
  rw [memcpyEntry, resolve_memcpy_eq_wp4MemcpyRealAddr hLs, decide_eq_true_eq] at hk
  exact c2_keepTextBPre_of_sub_lt hk
    (decide_eq_true_eq.mp (by rfl_kernel))
    (decide_eq_true_eq.mp (by rfl_kernel))

/-- Hull inclusion `keepR_memmove mpl ⊆ progKeep f3TrialRxProg` from `LinkedAt cliElfBytes mpl`. -/
theorem keepR_memmove_sub_rxProg {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {pc : BitVec 64} (hk : keepR_memmove mpl pc = true) :
    progKeep f3TrialRxProg pc = true :=
  keepTextBPre_sub_rxProg (keepR_memmove_sub_keepTextBPre hLs hk)

/-- Exact `hCL` premise of `memmoveGhost_rowOk` via `CodeSubslice.checkProgCodeSubslice`. -/
theorem c2_memmove_hCL {mpl mmpl : Obj.MultiPlacement}
    (hRxMemmove : checkProgCodeSubslice f3TrialRxProg (memmoveSubProg mpl) = true)
    {InvS : State → Prop}
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u → (memmoveSubProg mpl).CodeLoaded u.mem :=
  fun u hu => codeLoaded_of_checkProgCodeSubslice (hInv u hu).rxCode hRxMemmove

/-- Exact `hRealHullNoExt` premise of `memmoveGhost_rowOk` from `LinkedAt` and `C2ExternTableFacts`. -/
theorem c2_memmove_hRealHullNoExt {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  fun W {_} hk => f3RxSeg_realProg617_externAt_none hExt W (keepR_memmove_sub_rxProg hLs hk)

/-- Exact `hGhostEntry` premise of `memmoveGhost_rowOk` over `["memmove", "memcpy", "memset"]`. -/
theorem c2_memmove_hGhostEntry {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (EG : CliHooks → String → Option (State → State)) :
    ∀ (W : CliHooks) {sym : String},
      sym ∈ ["memmove", "memcpy", "memset"] →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl sym) =
        EG W sym := by
  intro W sym hsym
  have hrx : sym ∈ c2RxDehookedSyms := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsym
    rcases hsym with rfl | rfl | rfl
    · exact memmove_mem_c2RxDehookedSyms
    · exact memcpy_mem_c2RxDehookedSyms
    · exact memset_mem_c2RxDehookedSyms
  exact hExt.ghostRxEntry EG W hrx

/-- Every symbol in generated `c2RxDehookedSyms` outside `["memmove", "memcpy", "memset"]` resolves
    under `cliElfMultiPlacement.ρ` outside `keepBPreHull wp4MemcpyRealAddr` (verified by
    `rfl_kernel` both pre-T4 and post-T4). -/
private theorem c2RxOther_outside_memmoveHull :
    ((c2RxDehookedSyms.filter (fun s => !(["memmove", "memcpy", "memset"].contains s))).all
      (fun s => !(keepBPreHull wp4MemcpyRealAddr (cliElfMultiPlacement.ρ s)))) = true := by
  rfl_kernel

/-- Exact `hGhostOffEntries` premise of `memmoveGhost_rowOk` (`cliElf_linkedAt_unique` +
    `rfl_kernel` over generated `c2RxDehookedSyms`; `0` extra `C2ResolveFacts` premises). -/
theorem c2_memmove_hGhostOffEntries_of_linkedAt {mpl : Obj.MultiPlacement}
    (EG : CliHooks → String → Option (State → State))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map (libsignalSessionLib.resolve mpl) →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none := by
  intro W pc hkeep hnotin
  refine f3RowSyms_ghostProg617_externAt_none_of_ne_entries hExt EG W
    (fun _ hk => keepR_memmove_sub_rxProg hLs hk) ?_ hkeep hnotin
  intro s hs hs_notin
  left
  have hcontains_false : (["memmove", "memcpy", "memset"].contains s) = false := by
    cases hc : ["memmove", "memcpy", "memset"].contains s
    · rfl
    · exact False.elim (hs_notin (List.contains_iff_mem.mp hc))
  have hmem_filt :
      s ∈ c2RxDehookedSyms.filter (fun x => !(["memmove", "memcpy", "memset"].contains x)) :=
    List.mem_filter.mpr ⟨hs, by rw [hcontains_false]; rfl⟩
  have hnot := List.all_eq_true.mp c2RxOther_outside_memmoveHull s hmem_filt
  dsimp only [keepR_memmove, memcpyEntry]
  rw [resolve_memcpy_eq_wp4MemcpyRealAddr hLs, resolve_c2RxSym_eq_cliElf_rho hLs hs]
  simpa using hnot

/-! ## 3. `cliExternsPlaced = none` via `hExt` & `TrapHook L` on `g.memcpy` / `g.memset` -/

/-- Derive `cliExternsPlaced mmpl W "memcpy" = none` directly from `hExt : C2ExternTableFacts mpl`
    and `hLs : LinkedAt cliElfBytes mpl` by equating `hExt.ghostRxEntry (cliExternsPlaced mmpl) W`
    with `hExt.realRxNoExtern mmpl W` on `keepTextBPre_sub_rxProg` (never unfolding the pre-T4
    37-row `cliExternsPlaced` definition). -/
theorem c2_cliExternsPlaced_memcpy_none {mpl : Obj.MultiPlacement} (mmpl : Obj.MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) (W : CliHooks) :
    cliExternsPlaced mmpl W "memcpy" = none := by
  have hEntry := hExt.ghostRxEntry (cliExternsPlaced mmpl) W memcpy_mem_c2RxDehookedSyms
  have hInBPre : keepTextBPre (libsignalSessionLib.resolve mpl "memcpy") = true := by
    rw [resolve_memcpy_eq_wp4MemcpyRealAddr hLs]
    exact decide_eq_true_eq.mp (by rfl_kernel)
  have hReal := hExt.realRxNoExtern mmpl W (keepTextBPre_sub_rxProg hInBPre)
  exact hEntry.symm.trans hReal

/-- Derive `cliExternsPlaced mmpl W "memset" = none` directly from `hExt : C2ExternTableFacts mpl`
    and `hLs : LinkedAt cliElfBytes mpl` by equating `hExt.ghostRxEntry (cliExternsPlaced mmpl) W`
    with `hExt.realRxNoExtern mmpl W` on `keepTextBPre_sub_rxProg`. -/
theorem c2_cliExternsPlaced_memset_none {mpl : Obj.MultiPlacement} (mmpl : Obj.MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) (W : CliHooks) :
    cliExternsPlaced mmpl W "memset" = none := by
  have hEntry := hExt.ghostRxEntry (cliExternsPlaced mmpl) W memset_mem_c2RxDehookedSyms
  have hInBPre : keepTextBPre (libsignalSessionLib.resolve mpl "memset") = true := by
    rw [resolve_memset_eq_wp4MemsetRealAddr hLs]
    exact decide_eq_true_eq.mp (by rfl_kernel)
  have hReal := hExt.realRxNoExtern mmpl W (keepTextBPre_sub_rxProg hInBPre)
  exact hEntry.symm.trans hReal

private theorem cliGhostExternsWithExtra_memcpy (g : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State)) :
    cliGhostExternsWithExtra g extra baseExt "memcpy" =
      match g.memcpy with | some f => some f | none => baseExt "memcpy" := by
  unfold cliGhostExternsWithExtra
  have h1 : ("memcpy" == lsRustAllocSymCli) = false := by decide
  have h2 : ("memcpy" == lsRustDeallocSymCli) = false := by decide
  have h3 : ("memcpy" == lsRustReallocSymCli) = false := by decide
  have h4 : ("memcpy" == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : ("memcpy" == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : ("memcpy" == lsStringCloneSym) = false := by decide
  have h7 : ("memcpy" == lsReadFileSym) = false := by decide
  have h8 : ("memcpy" == lsReadStdinSym) = false := by decide
  have h9 : ("memcpy" == lsMemsetSym) = false := by decide
  have h10 : ("memcpy" == lsMemcpySym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Bool.false_eq_true, ↓reduceIte]
  cases g.memcpy <;> rfl

private theorem cliGhostExternsWithExtra_memset (g : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State)) :
    cliGhostExternsWithExtra g extra baseExt "memset" =
      match g.memset with | some f => some f | none => baseExt "memset" := by
  unfold cliGhostExternsWithExtra
  have h1 : ("memset" == lsRustAllocSymCli) = false := by decide
  have h2 : ("memset" == lsRustDeallocSymCli) = false := by decide
  have h3 : ("memset" == lsRustReallocSymCli) = false := by decide
  have h4 : ("memset" == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : ("memset" == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : ("memset" == lsStringCloneSym) = false := by decide
  have h7 : ("memset" == lsReadFileSym) = false := by decide
  have h8 : ("memset" == lsReadStdinSym) = false := by decide
  have h9 : ("memset" == lsMemsetSym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, Bool.false_eq_true, ↓reduceIte]
  cases g.memset <;> rfl

/-- Universal-`L` `TrapHook L` for `f3EmptyMemcpyGhostHookNarrow mmpl` via
    `MemmoveLrTrapBase.trapHook_f3EmptyMemcpyGhostHook` (`MemmoveLrTrapBase.lean:759`). -/
theorem trapHook_f3EmptyMemcpyGhostHookNarrow (mmpl : Obj.MultiPlacement) (L : BitVec 64) :
    TrapHook L (f3EmptyMemcpyGhostHookNarrow mmpl) := by
  unfold f3EmptyMemcpyGhostHookNarrow
  exact trapHook_f3EmptyMemcpyGhostHook
    (show (mallocngBlockProg mmpl 20 Syscall.standard).svc = Syscall.standard from rfl)
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)
    L

/-- Universal-`L` `TrapHook L` for `f3EmptyMemsetGhostHookNarrow mmpl` via
    `MemmoveLrTrapBase.trapHook_f3EmptyMemsetGhostHook` (`MemmoveLrTrapBase.lean:825`). -/
theorem trapHook_f3EmptyMemsetGhostHookNarrow (mmpl : Obj.MultiPlacement) (L : BitVec 64) :
    TrapHook L (f3EmptyMemsetGhostHookNarrow mmpl) := by
  unfold f3EmptyMemsetGhostHookNarrow
  exact trapHook_f3EmptyMemsetGhostHook
    (show (mallocngBlockProg mmpl 21 Syscall.standard).svc = Syscall.standard from rfl)
    (mallocngBlockProg21_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg21_hasWords mmpl Syscall.standard)
    L

/-- Exact `hMemcpyTrap` premise of `memmoveGhost_rowOk` under
    `hGMemcpy : g.memcpy = none ∨ g.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl)`. -/
theorem c2_memmove_hMemcpyTrap {mpl mmpl : Obj.MultiPlacement}
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hGMemcpy : g.memcpy = none ∨ g.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) :
    ∀ (W : CliHooks) (f : State → State),
      cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W) "memcpy" = some f →
      ∀ L : BitVec 64, TrapHook L f := by
  intro W f hSome L
  rw [cliGhostExternsWithExtra_memcpy] at hSome
  rcases hGMemcpy with hNone | hNarrow
  · rw [hNone, c2_cliExternsPlaced_memcpy_none mmpl hLs hExt W] at hSome
    cases hSome
  · rw [hNarrow] at hSome
    cases hSome
    exact trapHook_f3EmptyMemcpyGhostHookNarrow mmpl L

/-- Exact `hMemsetTrap` premise of `memmoveGhost_rowOk` under
    `hGMemset : g.memset = none ∨ g.memset = some (f3EmptyMemsetGhostHookNarrow mmpl)`. -/
theorem c2_memmove_hMemsetTrap {mpl mmpl : Obj.MultiPlacement}
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hGMemset : g.memset = none ∨ g.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl) :
    ∀ (W : CliHooks) (f : State → State),
      cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W) "memset" = some f →
      ∀ L : BitVec 64, TrapHook L f := by
  intro W f hSome L
  rw [cliGhostExternsWithExtra_memset] at hSome
  rcases hGMemset with hNone | hNarrow
  · rw [hNone, c2_cliExternsPlaced_memset_none mmpl hLs hExt W] at hSome
    cases hSome
  · rw [hNarrow] at hSome
    cases hSome
    exact trapHook_f3EmptyMemsetGhostHookNarrow mmpl L

/-- Exact `hMemmoveExt` premise of `memmoveGhost_rowOk` from `hLook`. -/
theorem c2_memmove_hMemmoveExt {mpl mmpl : Obj.MultiPlacement}
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "memmove" = some (memmoveGhost mpl mmpl)) :
    ∀ W : CliHooks,
      cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W) "memmove" = none ∨
        cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W) "memmove" =
          some (memmoveGhost mpl mmpl) :=
  fun W => Or.inr (cliGhostExternsWithExtra_extra_some g extra (cliExternsPlaced mmpl W) hLook
    (by decide +kernel))

/-! ## 4. Full Cutover-2 `GhostRowOk` & Block-`617` Startup Entry-Guard Discharges -/

/-- **Primary Cutover-2 `GhostRowOk` discharge for `"memmove"`**
    (`MemmoveExtraReplays.memmoveGhost_rowOk`, `MemmoveExtraReplays.lean:546`), instantiating
    cleanly at `mpl := lsmpl` with a single `hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl`.

    **GK6c `hGMemcpy` / `hGMemset` & `cliExternsPlaced` notes:**
    - (a) Concrete `g` closing terms:
      * Stage-B `H2K` (`ElfSlicesPqOomH2KHooks.h2k_ghFixedK`, `g.memcpy = none`,
        `g.memset = none`): close `hGMemcpy` and `hGMemset` by `Or.inl rfl`.
      * Stage-A `R1` (`ElfSlicesPqOomPlacedInst.hole2_ghFixed`, installing
        `f3EmptyMemcpyGhostHookNarrow mmpl` and `f3EmptyMemsetGhostHookNarrow mmpl`): close
        `hGMemcpy` and `hGMemset` by `Or.inr rfl`.
    - (b) Stage-A `R1` narrow-hook consumer & `TrapHook` justifications:
      * Consumer `HookOk` contracts: `NarrowF3R1Witness.f3EmptyMemcpyGhostHookNarrow_master_ok`
        (`NarrowF3R1Witness.lean:213`) and
        `NarrowF3R1Witness.f3EmptyMemsetGhostHookNarrow_master_ok` (`NarrowF3R1Witness.lean:149`).
      * Universal-`L` `TrapHook L` contracts: `MemmoveLrTrapBase.trapHook_f3EmptyMemcpyGhostHook`
        (`MemmoveLrTrapBase.lean:759`) and `MemmoveLrTrapBase.trapHook_f3EmptyMemsetGhostHook`
        (`MemmoveLrTrapBase.lean:825`).
    - (c) Base-table `cliExternsPlaced mmpl W' "memcpy" = none` and
      `cliExternsPlaced mmpl W' "memset" = none` (`c2_cliExternsPlaced_memcpy_none` /
      `c2_cliExternsPlaced_memset_none`): derived from `hExt : C2ExternTableFacts mpl` (and `hLs`)
      by equating `hExt.ghostRxEntry (cliExternsPlaced mmpl) W'` with
      `hExt.realRxNoExtern mmpl W'` on `keepTextBPre_sub_rxProg` (reflecting that `"memcpy"` and
      `"memset"` are dehooked in C2's 27-row table, never unfolding pre-T4's 37-row table). -/
theorem c2_memmoveGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "memmove" = some (memmoveGhost mpl mmpl))
    (hGMemcpy : g.memcpy = none ∨ g.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : g.memset = none ∨ g.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hExt : C2ExternTableFacts mpl)
    (hRxMemmove : checkProgCodeSubslice f3TrialRxProg (memmoveSubProg mpl) = true)
    (hResMemmove : libsignalSessionLib.resolve mpl "memmove" = c2MemmoveAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "memmove"
      (memmoveEntryGuard mpl)
      (memmoveGhost mpl mmpl) :=
  memmoveGhost_rowOk mpl mmpl
    (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    (c2_memmove_hMemmoveOff hLs hResMemmove)
    (c2_memmove_hCL hRxMemmove (fun _ h => h.1))
    (f3CodeInv_and_fs_keepsFrozen mpl mmpl PredFs)
    (c2_memmove_hRealHullNoExt hLs hExt)
    (c2_memmove_hGhostOffEntries_of_linkedAt
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')) hLs hExt)
    (c2_memmove_hGhostEntry hExt
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')))
    (c2_memmove_hMemmoveExt g extra hLook)
    (c2_memmove_hMemcpyTrap g extra hGMemcpy hLs hExt)
    (c2_memmove_hMemsetTrap g extra hGMemset hLs hExt)

/-- `guardOf`-adapted `GhostRowOk` for direct `"memmove"` arm dispatch in `ExtraListReplaysOn` /
    `ExtraListOk` (`ExtraGhostReplay.lean:380-386`) when `guardOf "memmove"` implies
    `memmoveEntryGuard mpl`. -/
theorem c2_memmoveGhost_rowOk_guardOf [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "memmove" = some (memmoveGhost mpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "memmove" s0 → memmoveEntryGuard mpl s0)
    (hGMemcpy : g.memcpy = none ∨ g.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : g.memset = none ∨ g.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hExt : C2ExternTableFacts mpl)
    (hRxMemmove : checkProgCodeSubslice f3TrialRxProg (memmoveSubProg mpl) = true)
    (hResMemmove : libsignalSessionLib.resolve mpl "memmove" = c2MemmoveAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "memmove"
      (guardOf "memmove")
      (memmoveGhost mpl mmpl) := by
  have hRow := c2_memmoveGhost_rowOk mpl mmpl PredFs g extra hLook hGMemcpy hGMemset
    hExt hRxMemmove hResMemmove hLs
  exact ⟨hRow.1, ghostRowReplayOn_of_guard_imp hRow.2 hGuard⟩

/-- Block-`617` startup `StdMainEntryLr f3StdLayout s0` discharge of `memmoveEntryGuard mpl s0`
    from `hLs` and `hResMemmove : libsignalSessionLib.resolve mpl "memmove" = c2MemmoveAddr`
    (routing through `Lib2LayoutFacts.f3BatchLEntryGuard_of_startupLr`). -/
theorem c2MemmoveEntryGuard_of_stdMainEntryLr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hResMemmove : libsignalSessionLib.resolve mpl "memmove" = c2MemmoveAddr)
    {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    memmoveEntryGuard mpl s0 := by
  have hSymIn : keepTextBPre (libsignalSessionLib.resolve mpl "memmove") = true := by
    rw [hResMemmove]
    exact decide_eq_true_eq.mp (by rfl_kernel)
  exact (memmoveEntryGuard_iff mpl s0).mpr
    (f3BatchLEntryGuard_of_startupLr hlr hSymIn (fun _ hk => keepR_memmove_sub_keepTextBPre hLs hk))

/-- Block-`617` startup `StdMainEntryLr f3StdLayout s0` discharge of `memmoveEntryGuard mpl s0`
    from `hLs` and `hExt : C2ExternTableFacts mpl` (via `f3BatchL_dehookedSym_in_keepTextBPre`). -/
theorem f3MemmoveEntryGuard_c2_of_stdMainEntryLr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    memmoveEntryGuard mpl s0 :=
  (memmoveEntryGuard_iff mpl s0).mpr
    (f3BatchLEntryGuard_of_startupLr hlr
      (f3BatchL_dehookedSym_in_keepTextBPre hExt memmove_mem_c2BatchLDehookedSyms)
      (fun _ hk => keepR_memmove_sub_keepTextBPre hLs hk))

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MemmoveRow
