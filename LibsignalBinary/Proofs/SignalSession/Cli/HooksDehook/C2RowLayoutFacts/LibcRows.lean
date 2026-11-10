/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.F3LayoutData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfBcmpEntryGuard -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStrlenEntryGuard -- proof-setup: allow-public-import
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Cutover-2 (`C2`) `.text.b_pre` `"strlen"` & `"bcmp"` Full `GhostRowOk` Glue (`C2RowLayoutFacts.LibcRows`)

**Checked by Lean. Untrusted (`Role::Proof`).**

Supplies the full Cutover-2 per-row `GhostRowOk` (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) and
Block-`617` startup `StdMainEntryLr` entry-guard discharges for the `.text.b_pre` libc rows
`"strlen"` (`StrlenGhostReplays`, `ElfStrlenEntryGuard`) and `"bcmp"` (`BcmpGhostReplays`,
`ElfBcmpEntryGuard`), consumed by `ExtraOk` / `ExtraListOk` (`ExtraGhostReplay.lean:376-386,
437-456`) and `CliGhostA0Hooks.extraOk` (`CliHookSatPlaced.lean:385`,
`ExtraGhostSpecs.lean:313-321`) with zero hex literals:

1. **`"strlen"` (`§1`):**
   - `c2_strlenGhost_rowOk` and `c2_strlenGhost_rowOk_guardOf` (single `LinkedAt`, polymorphic
     `[LibsignalPlacement]`, instantiating cleanly at `mpl := lsmpl`);
   - `c2_strlen_hGhostNoExtNe_of_linkedAt` (`RowCommon.resolve_c2RxSym_eq_cliElf_rho` + `rfl_kernel`
     over generated `c2RxDehookedSyms`; `0` extra `C2ResolveFacts` premises);
   - `c2StrlenEntryGuard_of_stdMainEntryLr`, `c2_extraEntryGuard_strlen_arm`, and
     `c2_extraEntryGuard_singleton_strlen` (via `ElfStrlenEntryGuard`).
2. **`"bcmp"` (`§2`):**
   - `c2_bcmpGhost_rowOk` and `c2_bcmpGhost_rowOk_guardOf` (single `LinkedAt`, polymorphic
     `[LibsignalPlacement]`, instantiating cleanly at `mpl := lsmpl`);
   - `c2_bcmp_hGhostNoExtNe_of_linkedAt` (`RowCommon.resolve_c2RxSym_eq_cliElf_rho` + `rfl_kernel`
     over generated `c2RxDehookedSyms`; `0` extra `C2ResolveFacts` premises);
   - `c2BcmpEntryGuard_of_stdMainEntryLr`, `c2_extraEntryGuard_bcmp_arm`, and
     `c2_extraEntryGuard_singleton_bcmp` (via `ElfBcmpEntryGuard`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcRows

open Arm64 Arm64.Obj Arm64.Process ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (StdMainEntryLr)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode (memcmpByteLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays
  (bcmpEntryGuard bcmpGhost bcmpGhost_rowOk bcmpHullBase bcmpSubProg keepR_bcmp)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap
  (bcmpHullByteLen keepBcmpHull keepBcmpHull_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (c2_ghostAt_of_extraLookup c2_keepTextBPre_of_sub_lt c2_realHullNoExt_of_keepTextBPre
   f3CodeInv_and_fs_keepsFrozen f3CodeInv_codeLoaded_of_checkProgCodeSubslice
   resolve_c2RxSym_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (ExtraEntryGuard GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost
  (keepStrlenRange strlenByteLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays
  (ghostRowReplayOn_of_guard_imp keepR_strlen strlenEntry strlenEntryGuard strlenGhost
   strlenGhost_rowOk strlenSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenLrTrap (keepStrlenRange_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfBcmpEntryGuard
  (extraEntryGuard_bcmp_arm extraEntryGuard_singleton_bcmp f3BcmpEntryGuard_of_stdMainEntryLr)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced (cliElfMultiPlacement)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3Row_ghostProg617_externAt_none_of_ne_entry keepTextBPre
   keepTextBPre_startupLr_false keepTextBPre_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStrlenEntryGuard
  (extraEntryGuard_singleton_strlen extraEntryGuard_strlen_arm f3StrlenEntryGuard_of_stdMainEntryLr)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BcmpAddr c2RxDehookedSyms c2StrlenAddr c2TextBPreHi c2TextBPreLo)

/-! ## 1. `"strlen"` (`StrlenGhostReplays` + `ElfStrlenEntryGuard`) -/

theorem strlen_mem_c2RxDehookedSyms :
    "strlen" ∈ c2RxDehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

/-- `keepR_strlen mpl` (`[resolve mpl "strlen", resolve mpl "strlen" + 88)`) lies inside
    `.text.b_pre` (`keepTextBPre`) at the Cutover-2 placement. -/
theorem keepR_strlen_sub_keepTextBPre {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl "strlen" = c2StrlenAddr) :
    ∀ pc : BitVec 64, keepR_strlen mpl pc = true → keepTextBPre pc = true := by
  intro pc hkeep
  dsimp only [keepR_strlen, strlenEntry] at hkeep
  rw [hRes, keepStrlenRange_iff] at hkeep
  exact c2_keepTextBPre_of_sub_lt hkeep
    (decide_eq_true_eq.mp (by rfl_kernel))
    (decide_eq_true_eq.mp (by rfl_kernel))

private theorem c2RxOther_outside_strlen :
    ((c2RxDehookedSyms.filter (· != "strlen")).all
      (fun s => !(keepStrlenRange c2StrlenAddr (cliElfMultiPlacement.ρ s)))) = true := by
  rfl_kernel

/-- Standalone `hGhostNoExtNe` discharge for `"strlen"` (`cliElf_linkedAt_unique` + `rfl_kernel`
    over generated `c2RxDehookedSyms`; `0` extra `C2ResolveFacts` premises). -/
theorem c2_strlen_hGhostNoExtNe_of_linkedAt
    {mpl : Obj.MultiPlacement}
    (EG : CliHooks → String → Option (State → State))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl "strlen" = c2StrlenAddr) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_strlen mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "strlen" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none := by
  intro W pc hkeep hne
  refine f3Row_ghostProg617_externAt_none_of_ne_entry hExt EG W
    (fun q hq => keepTextBPre_sub_rxProg (keepR_strlen_sub_keepTextBPre hRes q hq))
    (fun s hs hs_ne => Or.inl ?_) hkeep hne
  have hfilt : s ∈ c2RxDehookedSyms.filter (· != "strlen") :=
    List.mem_filter.mpr ⟨hs, bne_iff_ne.mpr hs_ne⟩
  have hout := List.all_eq_true.mp c2RxOther_outside_strlen s hfilt
  simp only [Bool.not_eq_true'] at hout
  dsimp only [keepR_strlen, strlenEntry]
  rw [hRes, resolve_c2RxSym_eq_cliElf_rho hLs hs]
  exact hout

/-- **Primary Cutover-2 `GhostRowOk` discharge for `"strlen"`**
    (`StrlenGhostReplays.strlenGhost_rowOk`). -/
theorem c2_strlenGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "strlen" = some (strlenGhost mpl mmpl))
    (hExt : C2ExternTableFacts mpl)
    (hRx : checkProgCodeSubslice f3TrialRxProg (strlenSubProg mpl) = true)
    (hRes : libsignalSessionLib.resolve mpl "strlen" = c2StrlenAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "strlen"
      (strlenEntryGuard mpl)
      (strlenGhost mpl mmpl) :=
  strlenGhost_rowOk mpl mmpl
    (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    (f3CodeInv_codeLoaded_of_checkProgCodeSubslice hRx)
    (f3CodeInv_and_fs_keepsFrozen mpl mmpl PredFs)
    (c2_ghostAt_of_extraLookup hExt g extra strlen_mem_c2RxDehookedSyms (by decide +kernel) hLook)
    (c2_realHullNoExt_of_keepTextBPre hExt (keepR_strlen_sub_keepTextBPre hRes))
    (c2_strlen_hGhostNoExtNe_of_linkedAt _ hLs hExt hRes)

/-- `guardOf`-adapted `GhostRowOk` for `"strlen"`. -/
theorem c2_strlenGhost_rowOk_guardOf [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "strlen" = some (strlenGhost mpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "strlen" s0 → strlenEntryGuard mpl s0)
    (hExt : C2ExternTableFacts mpl)
    (hRx : checkProgCodeSubslice f3TrialRxProg (strlenSubProg mpl) = true)
    (hRes : libsignalSessionLib.resolve mpl "strlen" = c2StrlenAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "strlen"
      (guardOf "strlen")
      (strlenGhost mpl mmpl) := by
  have hRow := c2_strlenGhost_rowOk mpl mmpl PredFs g extra hLook hExt hRx hRes hLs
  exact ⟨hRow.1, ghostRowReplayOn_of_guard_imp hRow.2 hGuard⟩

/-- Block-`617` startup `StdMainEntryLr f3StdLayout s0` discharge of `strlenEntryGuard mpl s0`
    from `hRes` (routing through `ElfStrlenEntryGuard.f3StrlenEntryGuard_of_stdMainEntryLr`). -/
theorem c2StrlenEntryGuard_of_stdMainEntryLr
    {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl "strlen" = c2StrlenAddr)
    {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    strlenEntryGuard mpl s0 :=
  f3StrlenEntryGuard_of_stdMainEntryLr keepTextBPre hlr
    keepTextBPre_startupLr_false
    (by rw [hRes]; exact decide_eq_true_eq.mp (by rfl_kernel))
    (keepR_strlen_sub_keepTextBPre hRes)

/-- Per-arm `"strlen"` `ExtraEntryGuard` discharge at Cutover-2. -/
theorem c2_extraEntryGuard_strlen_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hRes : libsignalSessionLib.resolve mpl "strlen" = c2StrlenAddr)
    (hlr : StdMainEntryLr f3StdLayout s0)
    (hGuardEq : guardOf "strlen" s0 ↔ strlenEntryGuard mpl s0) :
    guardOf "strlen" s0 :=
  extraEntryGuard_strlen_arm hGuardEq (c2StrlenEntryGuard_of_stdMainEntryLr hRes hlr)

/-- Singleton `g.extra = [("strlen", strlenGhost mpl mmpl)]` `ExtraEntryGuard` discharge. -/
theorem c2_extraEntryGuard_singleton_strlen
    {mpl mmpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hRes : libsignalSessionLib.resolve mpl "strlen" = c2StrlenAddr)
    (hlr : StdMainEntryLr f3StdLayout s0)
    (hg : g.extra = [("strlen", strlenGhost mpl mmpl)])
    (hGuardEq : guardOf "strlen" s0 ↔ strlenEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 :=
  extraEntryGuard_singleton_strlen hg hGuardEq
    (c2StrlenEntryGuard_of_stdMainEntryLr hRes hlr)

/-! ## 2. `"bcmp"` (`BcmpGhostReplays` + `ElfBcmpEntryGuard`) -/

theorem bcmp_mem_c2RxDehookedSyms :
    "bcmp" ∈ c2RxDehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

/-- `keepR_bcmp mpl` (`[resolve mpl "bcmp" - 52, resolve mpl "bcmp" + 4)`) lies inside
    `.text.b_pre` (`keepTextBPre`) at the Cutover-2 placement. -/
theorem keepR_bcmp_sub_keepTextBPre {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl "bcmp" = c2BcmpAddr) :
    ∀ pc : BitVec 64, keepR_bcmp mpl pc = true → keepTextBPre pc = true := by
  intro pc hkeep
  dsimp only [keepR_bcmp, bcmpHullBase] at hkeep
  rw [hRes, keepBcmpHull_iff] at hkeep
  exact c2_keepTextBPre_of_sub_lt hkeep
    (decide_eq_true_eq.mp (by rfl_kernel))
    (decide_eq_true_eq.mp (by rfl_kernel))

private theorem c2RxOther_outside_bcmp :
    ((c2RxDehookedSyms.filter (· != "bcmp")).all
      (fun s => !(keepBcmpHull (c2BcmpAddr - memcmpByteLen) (cliElfMultiPlacement.ρ s)))) = true := by
  rfl_kernel

/-- Standalone `hGhostNoExtNe` discharge for `"bcmp"` (`cliElf_linkedAt_unique` + `rfl_kernel`
    over generated `c2RxDehookedSyms`; `0` extra `C2ResolveFacts` premises). -/
theorem c2_bcmp_hGhostNoExtNe_of_linkedAt
    {mpl : Obj.MultiPlacement}
    (EG : CliHooks → String → Option (State → State))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl "bcmp" = c2BcmpAddr) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_bcmp mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "bcmp" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none := by
  intro W pc hkeep hne
  refine f3Row_ghostProg617_externAt_none_of_ne_entry hExt EG W
    (fun q hq => keepTextBPre_sub_rxProg (keepR_bcmp_sub_keepTextBPre hRes q hq))
    (fun s hs hs_ne => Or.inl ?_) hkeep hne
  have hfilt : s ∈ c2RxDehookedSyms.filter (· != "bcmp") :=
    List.mem_filter.mpr ⟨hs, bne_iff_ne.mpr hs_ne⟩
  have hout := List.all_eq_true.mp c2RxOther_outside_bcmp s hfilt
  simp only [Bool.not_eq_true'] at hout
  dsimp only [keepR_bcmp, bcmpHullBase]
  rw [hRes, resolve_c2RxSym_eq_cliElf_rho hLs hs]
  exact hout

/-- **Primary Cutover-2 `GhostRowOk` discharge for `"bcmp"`**
    (`BcmpGhostReplays.bcmpGhost_rowOk`). -/
theorem c2_bcmpGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "bcmp" = some (bcmpGhost mpl mmpl))
    (hExt : C2ExternTableFacts mpl)
    (hRx : checkProgCodeSubslice f3TrialRxProg (bcmpSubProg mpl) = true)
    (hRes : libsignalSessionLib.resolve mpl "bcmp" = c2BcmpAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "bcmp"
      (bcmpEntryGuard mpl)
      (bcmpGhost mpl mmpl) :=
  bcmpGhost_rowOk mpl mmpl
    (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    (f3CodeInv_codeLoaded_of_checkProgCodeSubslice hRx)
    (f3CodeInv_and_fs_keepsFrozen mpl mmpl PredFs)
    (c2_ghostAt_of_extraLookup hExt g extra bcmp_mem_c2RxDehookedSyms (by decide +kernel) hLook)
    (c2_realHullNoExt_of_keepTextBPre hExt (keepR_bcmp_sub_keepTextBPre hRes))
    (c2_bcmp_hGhostNoExtNe_of_linkedAt _ hLs hExt hRes)

/-- `guardOf`-adapted `GhostRowOk` for `"bcmp"`. -/
theorem c2_bcmpGhost_rowOk_guardOf [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "bcmp" = some (bcmpGhost mpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "bcmp" s0 → bcmpEntryGuard mpl s0)
    (hExt : C2ExternTableFacts mpl)
    (hRx : checkProgCodeSubslice f3TrialRxProg (bcmpSubProg mpl) = true)
    (hRes : libsignalSessionLib.resolve mpl "bcmp" = c2BcmpAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "bcmp"
      (guardOf "bcmp")
      (bcmpGhost mpl mmpl) := by
  have hRow := c2_bcmpGhost_rowOk mpl mmpl PredFs g extra hLook hExt hRx hRes hLs
  exact ⟨hRow.1, ghostRowReplayOn_of_guard_imp hRow.2 hGuard⟩

/-- Block-`617` startup `StdMainEntryLr f3StdLayout s0` discharge of `bcmpEntryGuard mpl s0`
    from `hRes` (routing through `ElfBcmpEntryGuard.f3BcmpEntryGuard_of_stdMainEntryLr`). -/
theorem c2BcmpEntryGuard_of_stdMainEntryLr
    {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl "bcmp" = c2BcmpAddr)
    {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    bcmpEntryGuard mpl s0 :=
  f3BcmpEntryGuard_of_stdMainEntryLr keepTextBPre hlr
    keepTextBPre_startupLr_false
    (by rw [hRes]; exact decide_eq_true_eq.mp (by rfl_kernel))
    (keepR_bcmp_sub_keepTextBPre hRes)

/-- Per-arm `"bcmp"` `ExtraEntryGuard` discharge at Cutover-2. -/
theorem c2_extraEntryGuard_bcmp_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hRes : libsignalSessionLib.resolve mpl "bcmp" = c2BcmpAddr)
    (hlr : StdMainEntryLr f3StdLayout s0)
    (hGuardEq : guardOf "bcmp" s0 ↔ bcmpEntryGuard mpl s0) :
    guardOf "bcmp" s0 :=
  extraEntryGuard_bcmp_arm hGuardEq (c2BcmpEntryGuard_of_stdMainEntryLr hRes hlr)

/-- Singleton `g.extra = [("bcmp", bcmpGhost mpl mmpl)]` `ExtraEntryGuard` discharge. -/
theorem c2_extraEntryGuard_singleton_bcmp
    {mpl mmpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hRes : libsignalSessionLib.resolve mpl "bcmp" = c2BcmpAddr)
    (hlr : StdMainEntryLr f3StdLayout s0)
    (hg : g.extra = [("bcmp", bcmpGhost mpl mmpl)])
    (hGuardEq : guardOf "bcmp" s0 ↔ bcmpEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 :=
  extraEntryGuard_singleton_bcmp hg hGuardEq
    (c2BcmpEntryGuard_of_stdMainEntryLr hRes hlr)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.LibcRows
