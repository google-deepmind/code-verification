/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl4 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Card `W-ADD` — `hPanReal` & `SystemTime::add` Cutover-2 (`C2`) Row Glue
(`HooksDehook.C2RowLayoutFacts.TimeAddPanic`)

**Checked by Lean. Untrusted (`Role::Proof`).**

Discharges GK6c §19(d) for the `<SystemTime as Add<Duration>>::add` (`lsTimeAddSym`) row from
`TimeAddGhostReplays` (`origin/hooks-prep/cc-r0`) at the shared Cutover-2 placement
`C2RowLayoutFacts.Time.c2TimeMpl`, with zero hex literals:

1. **Panic-Stub PC & `cliExternsPlaced` / `libsignalSessionExterns` Bridge (`§1–§2`):**
   - Reuses `C2RowLayoutFacts.Time.timeAddExpectFailedStubPc_eq_rho` and
     `c2TimeMpl_expectFailedStubPc_of_linkedAt` to connect `timeAddExpectFailedStubPc c2TimeMpl`
     (`rustTimeExpectFailedSym`, crate hash `Cs2kXlt…`) to
     `libsignalSessionLib.resolve mpl lsExpectFailedSymC2` (crate hash `Cskxt…`).
   - Proves `c2_timeAdd_hPanReal` with **`0` pending C2 hypotheses** (from
     `libsignalSessionLib.LinkedAt cliElfBytes mpl` alone) via interned `lookupBlockSymId`
     resolution, `ElfCodeMatchesData.ls_block617_externs_eq`, and
     `ElfPlaced.cliElf_externs_nodup_of_linkedAt`.
2. **Generic Add-Row Premise Reductions (`§3`):**
   - Layout-generic reductions for `hTargetEq`, `hkeep_stub`, `hlr_ne_stub`, `hKeep`,
     `hRealHullNoExt`, and `hCL` (via `C2RowLayoutFacts.CodeSubslice.checkProgCodeSubslice`).
3. **Concrete Cutover-2 (`c2TimeMpl`) Row Theorems (`§4`):**
   - `c2_timeAddGhost_rowSpecOk`: unconditional wrt C2 bundles (takes only
     `libsignalSessionLib.LinkedAt cliElfBytes lsmpl`).
   - `c2_timeAddGhost_rowOk_extra`, `c2_timeAddGhost_rowOk_guardOf`,
     `c2_timeAddGhost_rowOk_lsmpl_extra`, `c2_timeAddGhost_rowOk_lsmpl_guardOf` (specialized to
     `EG := fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')` and
     `InvS := fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs` for direct `ExtraOk` consumption),
     plus `EG`-polymorphic `c2_timeAddGhost_rowOk*`: discharges `hpl`, `hPanReal`, `hCL`, `hKeep`,
     `hlr_ne_stub`, `hRealHullNoExt`, `hTargetEq`, and `hInvKeep` internally, leaving only
     `hExt : C2ExternTableFacts mpl`,
     `hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true` (which also
     kernel-pins `.rodata..Lanon.678` at `add+0x4c/+0x50` `adrp + add` and the `bl` to
     `expect_failed` at `add+0x5c`),
     `hResAdd : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr`, and `LinkedAt`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open VerifiedLibraries.RustStd (rustTimeExpectFailedSym timeAddSym timeMultiLib)
open CryptoVerification (LibsignalPlacement libsignalSessionExterns lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced isCliPanicSymbolPlaced libsignalSessionLib lsTimeAddSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time
  (c2_f3CodeInv_and_fs_hInvKeep c2_f3CodeInv_hInvKeep c2_timeAdd_hCL c2TimeMpl c2TimeMpl_base2
   c2TimeMpl_expectFailedStubPc c2TimeMpl_expectFailedStubPc_of_linkedAt c2TimeMpl_fnAddr_timeAdd
   c2TimeMpl_placeable timeAddExpectFailedStubPc_eq_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays
  (keepR_timeAdd timeAddEntryGuard timeAddGhost timeAddGhost_rowOk timeAddGhost_rowReplayOn
   timeAddGhost_rowSpecOk timeAddSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhost
  (keepTimeAddBlk2 timeAddEntryAddr_eq_base2 timeAddExpectFailedStubPc)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable GhostRowSpecOk cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (ls_block617_externs_eq ls_idsOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3LsRetAddr624_lt_firstExternStub f3LsRetAddr624_ne_panicStubs
   f3RxSeg_realProg617_externAt_none keepLib2Text keepLib2Text_sub_rxProg lsExpectFailedSymC2)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElf_externs_nodup_of_linkedAt lsInternedMultiLib lsSharedExterns
   ls_names_nodup ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr c2Lib2TextLo c2TimeAddAddr)

/-! ## 1. CLI `expect_failed` Symbol (`lsExpectFailedSymC2`) & `cliExternsPlaced` Membership -/

theorem isCliPanicSymbolPlaced_lsExpectFailedSymC2 :
    isCliPanicSymbolPlaced lsExpectFailedSymC2 = true := by
  decide

theorem cliExternsPlaced_lsExpectFailedSymC2 (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsExpectFailedSymC2 = some Rust.panicked := by
  unfold cliExternsPlaced
  rw [isCliPanicSymbolPlaced_lsExpectFailedSymC2]
  rfl

theorem lsExpectFailedSymC2_mem_libsignalSessionExterns :
    lsExpectFailedSymC2 ∈ libsignalSessionExterns := by
  decide

/-! ## 2. Block-`617` `externAt?` & Generic `hPanReal` Discharge -/

private theorem findSome?_eq_none_of_forall_ne {α β γ : Type} [BEq β] [LawfulBEq β]
    {xs : List α} {f : α → β} (g : α → Option γ) {v : β}
    (hne : ∀ e ∈ xs, f e ≠ v) :
    (xs.findSome? fun e => if f e == v then g e else none) = none := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have ha : (f a == v) = false := beq_eq_false_iff_ne.mpr (hne a (.head _))
    simp only [List.findSome?_cons, ha, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun e he => hne e (.tail _ he))

private theorem findSome?_eq_of_nodup_map {α β γ : Type} [BEq β] [LawfulBEq β]
    {xs : List α} {f : α → β} (g : α → Option γ) {x : α}
    (hMem : x ∈ xs) (hNodup : (xs.map f).Nodup) :
    (xs.findSome? fun e => if f e == f x then g e else none) = g x := by
  induction xs with
  | nil => cases hMem
  | cons a rest ih =>
    rw [List.map_cons, List.nodup_cons] at hNodup
    rcases hNodup with ⟨ha_not_mem, hrest_nd⟩
    by_cases hax : f a == f x
    · have heq_fa : f a = f x := beq_iff_eq.mp hax
      rcases List.mem_cons.mp hMem with rfl | hx_rest
      · simp only [List.findSome?_cons, beq_self_eq_true, ↓reduceIte]
        have htail :
            (rest.findSome? fun e => if f e == f x then g e else none) = none :=
          findSome?_eq_none_of_forall_ne g fun e he hfe =>
            ha_not_mem (hfe ▸ List.mem_map_of_mem he)
        cases g x <;> simp [htail]
      · exact absurd (heq_fa ▸ List.mem_map_of_mem hx_rest) ha_not_mem
    · simp only [Bool.not_eq_true] at hax
      rcases List.mem_cons.mp hMem with rfl | hx_rest
      · simp at hax
      · simp only [List.findSome?_cons, hax, Bool.false_eq_true, ↓reduceIte]
        exact ih hx_rest hrest_nd

/-- Characterize `(cliProgExtPlacedAt mpl ext 617 W).externAt? pc` via `findSome?` over
    `(libsignalSessionLib.blockLib 617).text.externs` and `libsignalSessionLib.resolve mpl`. -/
theorem externAt?_cliProgExtPlacedAt_617
    (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State))
    (W : CliHooks) (pc : BitVec 64) :
    (cliProgExtPlacedAt mpl ext 617 W).externAt? pc =
      (libsignalSessionLib.blockLib 617).text.externs.findSome? fun e =>
        if libsignalSessionLib.resolve mpl e == pc then ext W e else none := by
  have key : ∀ (b : BitVec 64) (e : String),
      ((libsignalSessionLib.resolve mpl e - b).toNat == (pc - b).toNat) =
        (libsignalSessionLib.resolve mpl e == pc) := by
    intro b e
    cases h : libsignalSessionLib.resolve mpl e == pc with
    | true =>
      have heq := beq_iff_eq.mp h
      subst heq
      simp
    | false =>
      rw [beq_eq_false_iff_ne] at h ⊢
      intro hnat
      apply h
      have hbv := BitVec.eq_of_toNat_eq hnat
      have : (libsignalSessionLib.resolve mpl e - b) + b = (pc - b) + b := congrArg (· + b) hbv
      simpa [BitVec.sub_add_cancel] using this
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  dsimp only [cliProgExtPlacedAt, MultiPlacedLib.blockProgram, Obj.PlacedLib.program,
    MultiPlacedLib.blockPlacement, Program.externAt?, Program.hookAtOff?]
  simp only [ite_self, h0, Option.or_none, List.findSome?_map, Function.comp_def, key]

/-- Lookup `(cliProgExtPlacedAt mpl ext 617 W).externAt?` at `libsignalSessionLib.resolve mpl sym`
    under pairwise distinctness of block `617`'s resolved extern addresses. -/
theorem externAt?_cliProgExtPlacedAt_617_of_nodup_resolve
    {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)}
    {sym : String}
    (hMem : sym ∈ (libsignalSessionLib.blockLib 617).text.externs)
    (hNodup : ((libsignalSessionLib.blockLib 617).text.externs.map
      (libsignalSessionLib.resolve mpl)).Nodup)
    (W : CliHooks) :
    (cliProgExtPlacedAt mpl ext 617 W).externAt?
      (libsignalSessionLib.resolve mpl sym) = ext W sym := by
  rw [externAt?_cliProgExtPlacedAt_617]
  exact findSome?_eq_of_nodup_map (ext W) hMem hNodup

/-- **Generic `hPanReal` discharge (form 1 — resolved block-`617` extern `Nodup`):**
    Matches the `hPanReal` premise of `timeAddGhost_rowReplayOn` (`TimeAddGhostReplays.lean:362`)
    and `timeAddGhost_rowOk` (`TimeAddGhostReplays.lean:514`) verbatim. -/
theorem timeAdd_hPanReal_of_nodup_resolve
    (mpl mmpl timeMpl : Obj.MultiPlacement)
    (hStubEq : timeAddExpectFailedStubPc timeMpl =
      libsignalSessionLib.resolve mpl lsExpectFailedSymC2)
    (hMem : lsExpectFailedSymC2 ∈ (libsignalSessionLib.blockLib 617).text.externs)
    (hNodup : ((libsignalSessionLib.blockLib 617).text.externs.map
      (libsignalSessionLib.resolve mpl)).Nodup) :
    ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked := by
  intro W
  rw [hStubEq,
    externAt?_cliProgExtPlacedAt_617_of_nodup_resolve hMem hNodup,
    cliExternsPlaced_lsExpectFailedSymC2]

/-- **Generic `hPanReal` discharge (form 2 — `libsignalSessionExterns` + `mpl.ρ` `Nodup`):**
    Plugs directly into `ElfPlaced.cliElf_externs_nodup_of_linkedAt` and
    `ElfCodeMatchesData.ls_block617_externs_eq` without re-evaluating block `617` in the kernel. -/
theorem timeAdd_hPanReal_of_externs_eq_nodup_rho
    (mpl mmpl timeMpl : Obj.MultiPlacement)
    (hStubEq : timeAddExpectFailedStubPc timeMpl =
      libsignalSessionLib.resolve mpl lsExpectFailedSymC2)
    (hExt617 : (libsignalSessionLib.blockLib 617).text.externs = libsignalSessionExterns)
    (hResolveEqRho : ∀ e ∈ libsignalSessionExterns,
      libsignalSessionLib.resolve mpl e = mpl.ρ e)
    (hNodupRho : (libsignalSessionExterns.map mpl.ρ).Nodup) :
    ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked := by
  have hMem : lsExpectFailedSymC2 ∈ (libsignalSessionLib.blockLib 617).text.externs := by
    rw [hExt617]
    exact lsExpectFailedSymC2_mem_libsignalSessionExterns
  have hMapEq :
      (libsignalSessionLib.blockLib 617).text.externs.map (libsignalSessionLib.resolve mpl) =
        libsignalSessionExterns.map mpl.ρ := by
    rw [hExt617]
    exact List.map_congr_left hResolveEqRho
  have hNodup :
      ((libsignalSessionLib.blockLib 617).text.externs.map
        (libsignalSessionLib.resolve mpl)).Nodup := by
    rwa [hMapEq]
  exact timeAdd_hPanReal_of_nodup_resolve mpl mmpl timeMpl hStubEq hMem hNodup

set_option maxRecDepth 4000000 in
private theorem ls_sharedExterns_lookupId_ok :
    libsignalSessionExterns =
        lsSharedExterns.map (fun idx => lsInternedMultiLib.names.getD idx "") ∧
      (lsSharedExterns.all fun idx =>
        Nat.blt idx lsInternedMultiLib.names.length &&
          (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none)) = true := by
  exact ⟨by rfl_kernel, by rfl_kernel⟩

theorem ls_block617_externs_eq_libsignalSessionExterns :
    (libsignalSessionLib.blockLib 617).text.externs = libsignalSessionExterns := by
  rw [ls_block617_externs_eq, ← ls_sharedExterns_lookupId_ok.1]

/-- Every extern in `libsignalSessionExterns` is absent from `libsignalSessionLib.blocks`, so
    `libsignalSessionLib.resolve mpl e = mpl.ρ e` for all `mpl` (proved via interned integer IDs). -/
theorem libsignalSessionExterns_resolve_eq_rho (mpl : Obj.MultiPlacement) :
    ∀ e ∈ libsignalSessionExterns, libsignalSessionLib.resolve mpl e = mpl.ρ e := by
  intro e he
  rw [ls_sharedExterns_lookupId_ok.1, List.mem_map] at he
  rcases he with ⟨idx, hidx, rfl⟩
  have hall := List.all_eq_true.mp ls_sharedExterns_lookupId_ok.2 idx hidx
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hall
  have hnone :
      Obj.lookupBlockSym (lsInternedMultiLib.names.getD idx "") libsignalSessionLib.blocks =
        none := by
    rw [ls_toMultiPlacedLib_eq,
      Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hall.1]
    exact hall.2
  unfold MultiPlacedLib.resolve
  rw [hnone]

/-- **Generic `hPanReal` discharge from `LinkedAt cliElfBytes mpl`:** for any `timeMpl` whose
    `timeAddExpectFailedStubPc` equals `libsignalSessionLib.resolve mpl lsExpectFailedSymC2`. -/
theorem timeAdd_hPanReal_of_linkedAt
    {mpl : Obj.MultiPlacement} (mmpl timeMpl : Obj.MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hStubEq : timeAddExpectFailedStubPc timeMpl =
      libsignalSessionLib.resolve mpl lsExpectFailedSymC2) :
    ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (timeAddExpectFailedStubPc timeMpl) = some Rust.panicked :=
  timeAdd_hPanReal_of_externs_eq_nodup_rho mpl mmpl timeMpl hStubEq
    ls_block617_externs_eq_libsignalSessionExterns
    (libsignalSessionExterns_resolve_eq_rho mpl)
    (cliElf_externs_nodup_of_linkedAt hLs)

/-! ## 3. Generic Add-Row Premise Reductions (`hTargetEq`, `hCL`, `hkeep_stub`, `hlr_ne_stub`, `hKeep`, `hRealHullNoExt`) -/

/-- **Generic `hTargetEq` discharge:** matches `TimeAddGhostReplays.lean:353, 505` verbatim. -/
theorem timeAdd_hTargetEq_of_base2
    {mpl timeMpl : Obj.MultiPlacement}
    (hBase2 : libsignalSessionLib.resolve mpl lsTimeAddSym = timeMpl.base 2) :
    libsignalSessionLib.resolve mpl lsTimeAddSym =
      timeMultiLib.fnAddr timeMpl timeAddSym := by
  rw [timeAddEntryAddr_eq_base2]
  exact hBase2

/-- **Generic `hCL` discharge via `checkProgCodeSubslice`:** matches
    `TimeAddGhostReplays.lean:355, 507` verbatim. -/
theorem timeAdd_hCL_of_checkProgCodeSubslice
    {rxProg : Program} {timeMpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hChk : checkProgCodeSubslice rxProg (timeAddSubProg timeMpl) = true)
    (hInvRx : ∀ u : State, InvS u → rxProg.CodeLoaded u.mem) :
    ∀ u : State, InvS u → (timeAddSubProg timeMpl).CodeLoaded u.mem :=
  fun u hu => codeLoaded_of_checkProgCodeSubslice (hInvRx u hu) hChk

/-- Generic interval inclusion for `keepR_timeAdd timeMpl` (`96` bytes at `timeMpl.base 2`). -/
theorem keepR_timeAdd_sub_interval {timeMpl : Obj.MultiPlacement}
    {lo hi pc : BitVec 64}
    (hlo : lo.toNat ≤ (timeMpl.base 2).toNat)
    (hhi : (timeMpl.base 2).toNat + 96 ≤ hi.toNat)
    (hk : keepR_timeAdd timeMpl pc = true) :
    decide (lo.toNat ≤ pc.toNat ∧ pc.toNat < hi.toNat) = true := by
  unfold keepR_timeAdd keepTimeAddBlk2 at hk
  rw [decide_eq_true_eq] at hk ⊢
  have htop : hi.toNat < 2 ^ 64 := BitVec.isLt hi
  generalize hd : pc - timeMpl.base 2 = d at hk
  have hpc_eq : pc = timeMpl.base 2 + d := by subst hd; bv_omega
  have htoNat : pc.toNat = (timeMpl.base 2).toNat + d.toNat := by
    rw [hpc_eq, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **Generic `hkeep_stub` discharge:** matches `TimeAddGhostReplays.lean:380, 393` verbatim when
    `timeAddExpectFailedStubPc timeMpl` sits strictly below `timeMpl.base 2`. -/
theorem timeAdd_hkeep_stub_of_lt_base2
    {timeMpl : Obj.MultiPlacement}
    (hNoWrap : (timeMpl.base 2).toNat + 96 ≤ 2 ^ 64)
    (hLt : (timeAddExpectFailedStubPc timeMpl).toNat < (timeMpl.base 2).toNat) :
    keepR_timeAdd timeMpl (timeAddExpectFailedStubPc timeMpl) = false := by
  unfold keepR_timeAdd keepTimeAddBlk2
  rw [decide_eq_false_iff_not]
  bv_omega

/-- **Generic `hlr_ne_stub` discharge (via stub equality):** matches
    `TimeAddGhostReplays.lean:358, 394, 510` verbatim. -/
theorem timeAdd_hlr_ne_stub_of_stubEq [LibsignalPlacement]
    {timeMpl : Obj.MultiPlacement} {stubPc : BitVec 64}
    (hStubEq : timeAddExpectFailedStubPc timeMpl = stubPc)
    (hNe : ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ stubPc) :
    ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc timeMpl := by
  intro lr hlr
  rw [hStubEq]
  exact hNe lr hlr

/-- **Generic `hKeep` discharge (subset form):** matches `TimeAddGhostReplays.lean:357, 509`
    verbatim. -/
theorem timeAdd_hKeep_of_subset [LibsignalPlacement]
    {timeMpl : Obj.MultiPlacement} {keepCover : BitVec 64 → Bool}
    (hSub : ∀ pc : BitVec 64, keepR_timeAdd timeMpl pc = true → keepCover pc = true)
    (hCoverFalse : ∀ lr : BitVec 64, LsRetAddr624 lr → keepCover lr = false) :
    ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_timeAdd timeMpl lr = false := by
  intro lr hlr
  cases hk : keepR_timeAdd timeMpl lr
  · rfl
  · cases (hCoverFalse lr hlr).symm.trans (hSub lr hk)

/-- **Generic `hRealHullNoExt` discharge (subset form):** matches `TimeAddGhostReplays.lean:359, 511`
    verbatim. -/
theorem timeAdd_hRealHullNoExt_of_subset
    {mpl mmpl timeMpl : Obj.MultiPlacement}
    {keepCover : BitVec 64 → Bool}
    (hSub : ∀ pc : BitVec 64, keepR_timeAdd timeMpl pc = true → keepCover pc = true)
    (hNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepCover pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_timeAdd timeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  fun W {_} hk => hNoExt W (hSub _ hk)

/-! ## 4. Concrete Cutover-2 (`c2TimeMpl`) Premise Discharges & Row Theorems -/

/-- **Cutover-2 `hPanReal` at `c2TimeMpl` (`0` pending C2 hypotheses):**
    Matches `TimeAddGhostReplays.lean:362, 514` verbatim for any `mpl` satisfying
    `libsignalSessionLib.LinkedAt cliElfBytes mpl` (valid both pre-T4 and post-T4). -/
theorem c2_timeAdd_hPanReal {mpl : Obj.MultiPlacement} (mmpl : Obj.MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (timeAddExpectFailedStubPc c2TimeMpl) = some Rust.panicked :=
  timeAdd_hPanReal_of_linkedAt mmpl c2TimeMpl hLs
    (c2TimeMpl_expectFailedStubPc_of_linkedAt hLs)

/-- Fast `ρ`-projection of `timeAddExpectFailedStubPc c2TimeMpl` avoiding 624-block string lookup. -/
theorem c2TimeMpl_expectFailedStubPc_eq_cliElf_rho :
    timeAddExpectFailedStubPc c2TimeMpl =
      cliElfMultiPlacement.ρ lsExpectFailedSymC2 :=
  c2TimeMpl_expectFailedStubPc.trans
    (libsignalSessionExterns_resolve_eq_rho cliElfMultiPlacement
      lsExpectFailedSymC2 lsExpectFailedSymC2_mem_libsignalSessionExterns)

/-- **Cutover-2 `hkeep_stub` at `c2TimeMpl` (`0` pending hypotheses):**
    Matches `TimeAddGhostReplays.lean:380, 393` verbatim. -/
theorem c2_timeAdd_hkeep_stub :
    keepR_timeAdd c2TimeMpl (timeAddExpectFailedStubPc c2TimeMpl) = false := by
  apply timeAdd_hkeep_stub_of_lt_base2
  · rw [c2TimeMpl_base2]
    exact decide_eq_true_eq.mp (by rfl_kernel)
  · rw [c2TimeMpl_base2, c2TimeMpl_expectFailedStubPc_eq_cliElf_rho]
    exact decide_eq_true_eq.mp (by rfl_kernel)

/-- **Cutover-2 `hlr_ne_stub` at `c2TimeMpl` (`0` pending C2 hypotheses):**
    Matches `TimeAddGhostReplays.lean:358, 394, 510` verbatim. -/
theorem c2_timeAdd_hlr_ne_stub [LibsignalPlacement]
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    ∀ lr : BitVec 64, LsRetAddr624 lr → lr ≠ timeAddExpectFailedStubPc c2TimeMpl :=
  timeAdd_hlr_ne_stub_of_stubEq
    (c2TimeMpl_expectFailedStubPc_of_linkedAt hLsLsmpl)
    (fun _ hRet => (f3LsRetAddr624_ne_panicStubs hLsLsmpl hRet).1)

/-- **Cutover-2 `GhostRowSpecOk` for `lsTimeAddSym` at `c2TimeMpl` (`0` pending C2 hypotheses):**
    Discharges `TimeAddGhostReplays.timeAddGhost_rowSpecOk` (`TimeAddGhostReplays.lean:390`). -/
theorem c2_timeAddGhost_rowSpecOk [LibsignalPlacement]
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowSpecOk lsTimeAddSym (timeAddGhost c2TimeMpl) :=
  timeAddGhost_rowSpecOk c2TimeMpl
    c2TimeMpl_placeable
    c2_timeAdd_hkeep_stub
    (c2_timeAdd_hlr_ne_stub hLsLsmpl)

/-- **Cutover-2 `hTargetEq` at `c2TimeMpl`:** matches `TimeAddGhostReplays.lean:353, 505` verbatim
    from `hResAdd : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr`
    (`c2TimeMpl.base 2 = c2TimeAddAddr` by `rfl`). -/
theorem c2_timeAdd_hTargetEq {mpl : Obj.MultiPlacement}
    (hResAdd : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr) :
    libsignalSessionLib.resolve mpl lsTimeAddSym =
      timeMultiLib.fnAddr c2TimeMpl timeAddSym := by
  rw [c2TimeMpl_fnAddr_timeAdd]
  exact hResAdd

/-- Unconditional hull inclusion `keepR_timeAdd c2TimeMpl ⊆ keepLib2Text`. -/
theorem keepR_timeAdd_c2_sub_keepLib2Text {pc : BitVec 64}
    (h : keepR_timeAdd c2TimeMpl pc = true) :
    keepLib2Text pc = true := by
  refine keepR_timeAdd_sub_interval ?_ ?_ h
  · rw [c2TimeMpl_base2]
    exact decide_eq_true_eq.mp (by rfl_kernel)
  · rw [c2TimeMpl_base2]
    exact decide_eq_true_eq.mp (by rfl_kernel)

/-- Unconditional hull inclusion `keepR_timeAdd c2TimeMpl ⊆ progKeep f3TrialRxProg`. -/
theorem keepR_timeAdd_c2_sub_rxProg {pc : BitVec 64}
    (h : keepR_timeAdd c2TimeMpl pc = true) :
    progKeep f3TrialRxProg pc = true :=
  keepLib2Text_sub_rxProg (keepR_timeAdd_c2_sub_keepLib2Text h)

/-- **Cutover-2 `hKeep` at `c2TimeMpl` (`0` pending C2 hypotheses):**
    Matches `TimeAddGhostReplays.lean:357, 509` verbatim. -/
theorem c2_timeAdd_hKeep [LibsignalPlacement]
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_timeAdd c2TimeMpl lr = false := by
  intro lr hRet
  have hlt := f3LsRetAddr624_lt_firstExternStub hLsLsmpl hRet
  have hlo : c2FirstExternStubAddr.toNat ≤ c2Lib2TextLo.toNat :=
    decide_eq_true_eq.mp (by rfl_kernel)
  cases hk : keepR_timeAdd c2TimeMpl lr
  · rfl
  · have hlib2 := keepR_timeAdd_c2_sub_keepLib2Text hk
    unfold keepLib2Text at hlib2
    rw [decide_eq_true_eq] at hlib2
    omega

/-- **Cutover-2 `hRealHullNoExt` at `c2TimeMpl`:** matches `TimeAddGhostReplays.lean:359, 511`
    verbatim from `C2ExternTableFacts mpl`. -/
theorem c2_timeAdd_hRealHullNoExt {mpl mmpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_timeAdd c2TimeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  fun W {_} hkeep =>
    f3RxSeg_realProg617_externAt_none hExt W (keepR_timeAdd_c2_sub_rxProg hkeep)

/-- Combined Cutover-2 `GhostRowReplayOn` discharge for `lsTimeAddSym` at `c2TimeMpl` for any
    `KeepsFrozen`/`fs`-stable `InvS` projecting to `F3CodeInv mpl mmpl u.mem`. -/
theorem c2_timeAddGhost_rowReplayOn_of_inv [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts mpl)
    (hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true)
    (hResAdd : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v) :
    GhostRowReplayOn mpl mmpl InvS EG lsTimeAddSym (fun _ => True)
      (timeAddGhost c2TimeMpl) :=
  timeAddGhost_rowReplayOn mpl mmpl c2TimeMpl InvS EG
    c2TimeMpl_placeable
    (c2_timeAdd_hTargetEq hResAdd)
    (c2_timeAdd_hCL hRxAdd hInv)
    hInvKeep
    (c2_timeAdd_hKeep hLsLsmpl)
    (c2_timeAdd_hlr_ne_stub hLsLsmpl)
    (c2_timeAdd_hRealHullNoExt hExt)
    (c2_timeAdd_hPanReal mmpl hLs)

/-- Combined Cutover-2 `GhostRowOk` discharge for `lsTimeAddSym` at `c2TimeMpl` for any
    `KeepsFrozen`/`fs`-stable `InvS` projecting to `F3CodeInv mpl mmpl u.mem`. -/
theorem c2_timeAddGhost_rowOk_of_inv [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts mpl)
    (hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true)
    (hResAdd : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v) :
    GhostRowOk mpl mmpl InvS EG lsTimeAddSym (fun _ => True)
      (timeAddGhost c2TimeMpl) :=
  timeAddGhost_rowOk mpl mmpl c2TimeMpl InvS EG
    c2TimeMpl_placeable
    (c2_timeAdd_hTargetEq hResAdd)
    (c2_timeAdd_hCL hRxAdd hInv)
    hInvKeep
    (c2_timeAdd_hKeep hLsLsmpl)
    (c2_timeAdd_hlr_ne_stub hLsLsmpl)
    (c2_timeAdd_hRealHullNoExt hExt)
    (c2_timeAdd_hPanReal mmpl hLs)

/-- Combined Cutover-2 `GhostRowOk` discharge for `lsTimeAddSym` at `c2TimeMpl` for
    `InvS := fun u => F3CodeInv mpl mmpl u.mem`. -/
theorem c2_timeAddGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts mpl)
    (hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true)
    (hResAdd : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk mpl mmpl (fun u => F3CodeInv mpl mmpl u.mem) EG lsTimeAddSym
      (fun _ => True) (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk_of_inv mpl mmpl (fun u => F3CodeInv mpl mmpl u.mem) EG
    hExt hRxAdd hResAdd hLs hLsLsmpl
    (fun _ h => h)
    (c2_f3CodeInv_hInvKeep mpl mmpl)

/-- Combined Cutover-2 `GhostRowOk` discharge for `lsTimeAddSym` at `c2TimeMpl` for
    `InvS := fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs`
    (matching `ExtraGhostReplay.ExtraOk` / `block617TransferFixedG_of_extraRow`). -/
theorem c2_timeAddGhost_rowOk_and_fs [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts mpl)
    (hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true)
    (hResAdd : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk mpl mmpl (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs) EG lsTimeAddSym
      (fun _ => True) (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk_of_inv mpl mmpl
    (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs) EG
    hExt hRxAdd hResAdd hLs hLsLsmpl
    (fun _ h => h.1)
    (c2_f3CodeInv_and_fs_hInvKeep mpl mmpl PredFs)

/-- Single-placement (`mpl := lsmpl`) specialization of `c2_timeAddGhost_rowOk_and_fs` taking a
    single `hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl`. -/
theorem c2_timeAddGhost_rowOk_lsmpl_and_fs [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true)
    (hResAdd : libsignalSessionLib.resolve lsmpl lsTimeAddSym = c2TimeAddAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsTimeAddSym
      (fun _ => True) (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk_and_fs lsmpl mmpl PredFs EG hExt hRxAdd hResAdd hLs hLs

/-- `GhostRowReplayOn` projection of `c2_timeAddGhost_rowOk_lsmpl_and_fs` for direct
    `ExtraListReplaysOn` / `block617TransferFixedG_of_extraRow` consumption. -/
theorem c2_timeAddGhost_rowReplayOn_lsmpl_and_fs [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true)
    (hResAdd : libsignalSessionLib.resolve lsmpl lsTimeAddSym = c2TimeAddAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowReplayOn lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsTimeAddSym (fun _ => True) (timeAddGhost c2TimeMpl) :=
  (c2_timeAddGhost_rowOk_lsmpl_and_fs mmpl PredFs EG hExt hRxAdd hResAdd hLs).2

private theorem ghostRowReplayOn_of_true_guard
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {sym : String} {f : State → State}
    (entryGuard : State → Prop)
    (h : GhostRowReplayOn mpl mmpl InvS EG sym (fun _ => True) f) :
    GhostRowReplayOn mpl mmpl InvS EG sym entryGuard f :=
  ⟨h.preserves_execFrozen, fun W s0 sf _ => h.replay_at_stub W s0 sf trivial⟩

/-- **Primary `ExtraOk`-shaped Cutover-2 `GhostRowOk` discharge for `lsTimeAddSym`:**
    Matches `ExtraOk` / `ExtraListOk` (`ExtraGhostReplay.lean:376-386, 437-456`) directly at
    `InvS := fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs`,
    `EG := fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')`, and
    `entryGuard := timeAddEntryGuard mpl` (`0` `hLook` or `C2RoSliceFacts` premises needed because
    `timeAddGhost` is Route-`R0` + `K4` `linkedCallHook`, and `.rodata..Lanon.678` at
    `add+0x4c/+0x50` `adrp + add` is kernel-pinned directly by `hRxAdd`). -/
theorem c2_timeAddGhost_rowOk_extra [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hExt : C2ExternTableFacts mpl)
    (hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true)
    (hResAdd : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsTimeAddSym
      (timeAddEntryGuard mpl)
      (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk_and_fs mpl mmpl PredFs
    (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
    hExt hRxAdd hResAdd hLs hLsLsmpl

/-- `guardOf`-specialized `GhostRowOk` for direct arm dispatch in `ExtraListReplaysOn` /
    `ExtraListOk` (`ExtraGhostReplay.lean:380-386`) for arbitrary `guardOf : String → State → Prop`
    (`0` `hGuard` premise required because `timeAddEntryGuard mpl` is `True`). -/
theorem c2_timeAddGhost_rowOk_guardOf [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hExt : C2ExternTableFacts mpl)
    (hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true)
    (hResAdd : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk mpl mmpl
      (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsTimeAddSym
      (guardOf lsTimeAddSym)
      (timeAddGhost c2TimeMpl) := by
  have hRow := c2_timeAddGhost_rowOk_extra mpl mmpl PredFs g extra
    hExt hRxAdd hResAdd hLs hLsLsmpl
  exact ⟨hRow.1, ghostRowReplayOn_of_true_guard (guardOf lsTimeAddSym) hRow.2⟩

/-- Single-placement (`mpl := lsmpl`) `ExtraOk`-shaped `GhostRowOk` for `lsTimeAddSym` taking a
    single `hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl`. -/
theorem c2_timeAddGhost_rowOk_lsmpl_extra [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hExt : C2ExternTableFacts lsmpl)
    (hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true)
    (hResAdd : libsignalSessionLib.resolve lsmpl lsTimeAddSym = c2TimeAddAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsTimeAddSym
      (timeAddEntryGuard lsmpl)
      (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk_extra lsmpl mmpl PredFs g extra hExt hRxAdd hResAdd hLs hLs

/-- Single-placement (`mpl := lsmpl`) `guardOf`-specialized `GhostRowOk` for `lsTimeAddSym` taking a
    single `hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl`. -/
theorem c2_timeAddGhost_rowOk_lsmpl_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hExt : C2ExternTableFacts lsmpl)
    (hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true)
    (hResAdd : libsignalSessionLib.resolve lsmpl lsTimeAddSym = c2TimeAddAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsTimeAddSym
      (guardOf lsTimeAddSym)
      (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk_guardOf lsmpl mmpl PredFs guardOf g extra hExt hRxAdd hResAdd hLs hLs

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
