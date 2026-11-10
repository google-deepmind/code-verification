/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import

/-!
# Shared Cutover-2 (`C2`) Premise Dischargers (`C2RowLayoutFacts.RowCommon`)

Generic layout-independent dischargers shared across per-row C2 `GhostRowOk` glue modules:
1. `checkProgCodeSubslice` and `codeLoaded_of_checkProgCodeSubslice` /
   `f3CodeInv_codeLoaded_of_checkProgCodeSubslice` (`hCL`).
2. `f3CodeInv_and_fs_keepsFrozen` (`hInvKeep` on `fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs`).
3. `c2_ghostAt_of_extraLookup` (`hGhostAt` on `cliGhostExternsWithExtra` via
   `C2ExternTableFacts.ghostRxEntry`).
4. `c2_realHullNoExt_of_keepLib2Text` / `c2_realHullNoExt_of_keepTextBPre` (`hRealHullNoExt`).
5. `c2_keepLib2Text_of_sub_lt` / `c2_keepTextBPre_of_sub_lt` (interval hull inclusions).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon

open Arm64 Arm64.Obj Arm64.Process ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionExterns)
open CryptoVerification.SignalSession (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice rxSubslice_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (ls_idsOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElf_linkedAt_unique lsInternedMultiLib lsSharedExterns
   ls_names_nodup ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliExtraGhostSyms cliGhostExternsWithExtra cliGhostExternsWithExtra_extra_some)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3RxSeg_ghostProg617_externAt_entry f3RxSeg_realProg617_externAt_none
   keepLib2Text keepLib2Text_sub_rxProg keepTextBPre keepTextBPre_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2Lib2TextHi c2Lib2TextLo c2RxDehookedSyms c2TextBPreHi c2TextBPreLo)

/-! ## 1. `hCL` Dischargers (via `C2RowLayoutFacts.CodeSubslice`) -/

export LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice rxSubslice_of_checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)

/-- Discharge `hCL` on `InvS := fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs` from
    `checkProgCodeSubslice f3TrialRxProg subProg = true`. -/
theorem f3CodeInv_codeLoaded_of_checkProgCodeSubslice
    {mpl mmpl : Obj.MultiPlacement} {PredFs : FsState → Prop} {subProg : Program}
    (hSub : checkProgCodeSubslice f3TrialRxProg subProg = true) :
    ∀ u : State, (F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs) → subProg.CodeLoaded u.mem :=
  fun _ ⟨hCode, _⟩ => codeLoaded_of_checkProgCodeSubslice hCode.rxCode hSub

/-- Pure-memory `hCL` companion on `InvS := fun u => F3CodeInv mpl mmpl u.mem`. -/
theorem f3CodeInv_memOnly_codeLoaded_of_checkProgCodeSubslice
    {mpl mmpl : Obj.MultiPlacement} {subProg : Program}
    (hSub : checkProgCodeSubslice f3TrialRxProg subProg = true) :
    ∀ u : State, F3CodeInv mpl mmpl u.mem → subProg.CodeLoaded u.mem :=
  fun _ hCode => codeLoaded_of_checkProgCodeSubslice hCode.rxCode hSub

/-! ## 2. `hInvKeep` Dischargers on `F3CodeInv ∧ PredFs` and `F3CodeInv` -/

/-- Unconditional `KeepsFrozen` + `fs`-preservation lift for
    `fun u : State => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs`. -/
theorem f3CodeInv_and_fs_keepsFrozen
    (mpl mmpl : Obj.MultiPlacement) (PredFs : FsState → Prop) :
    ∀ u v : State,
      (F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs) →
      u.mem.KeepsFrozen v.mem →
      v.fs = u.fs →
      (F3CodeInv mpl mmpl v.mem ∧ PredFs v.fs) :=
  fun _ _ ⟨hCode, hFs⟩ hkf hfs => ⟨F3CodeInv.of_keepsFrozen hCode hkf, hfs ▸ hFs⟩

/-- Unconditional `KeepsFrozen` lift for `fun u : State => F3CodeInv mpl mmpl u.mem`. -/
theorem f3CodeInv_memOnly_keepsFrozen
    (mpl mmpl : Obj.MultiPlacement) :
    ∀ u v : State,
      F3CodeInv mpl mmpl u.mem →
      u.mem.KeepsFrozen v.mem →
      v.fs = u.fs →
      F3CodeInv mpl mmpl v.mem :=
  fun _ _ hCode hkf _ => F3CodeInv.of_keepsFrozen hCode hkf

/-! ## 3. `hGhostAt` Discharger on `cliGhostExternsWithExtra` -/

/-- Discharge `hGhostAt` on `EG := fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')`
    from `C2ExternTableFacts mpl` and `extra.lookup sym = some f`. -/
theorem c2_ghostAt_of_extraLookup
    {mpl mmpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    {sym : String} {f : State → State}
    (hSymRx : sym ∈ c2RxDehookedSyms)
    (hSymDom : cliExtraGhostSyms.contains sym = true)
    (hLook : extra.lookup sym = some f) :
    ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')) 617 W).externAt?
          (libsignalSessionLib.resolve mpl sym) = some f := by
  intro W
  rw [f3RxSeg_ghostProg617_externAt_entry hExt _ W hSymRx]
  exact cliGhostExternsWithExtra_extra_some g extra (cliExternsPlaced mmpl W) hLook hSymDom

/-! ## 4. `hRealHullNoExt` Dischargers -/

/-- Discharge `hRealHullNoExt` for any `.text.lib2` hull `keepR ⊆ keepLib2Text`. -/
theorem c2_realHullNoExt_of_keepLib2Text
    {mpl mmpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    {keepR : BitVec 64 → Bool}
    (hSub : ∀ pc : BitVec 64, keepR pc = true → keepLib2Text pc = true) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  fun W {pc} hk =>
    f3RxSeg_realProg617_externAt_none hExt W (keepLib2Text_sub_rxProg (hSub pc hk))

/-- Discharge `hRealHullNoExt` for any `.text.b_pre` hull `keepR ⊆ keepTextBPre`. -/
theorem c2_realHullNoExt_of_keepTextBPre
    {mpl mmpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    {keepR : BitVec 64 → Bool}
    (hSub : ∀ pc : BitVec 64, keepR pc = true → keepTextBPre pc = true) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  fun W {pc} hk =>
    f3RxSeg_realProg617_externAt_none hExt W (keepTextBPre_sub_rxProg (hSub pc hk))

/-! ## 5. Interval Hull Inclusions into `keepLib2Text` and `keepTextBPre` -/

theorem c2_keepLib2Text_of_sub_lt {base pc : BitVec 64} {len : Nat}
    (hsub : (pc - base).toNat < len)
    (hlo : c2Lib2TextLo.toNat ≤ base.toNat)
    (hhi : base.toNat + len ≤ c2Lib2TextHi.toNat) :
    keepLib2Text pc = true := by
  unfold keepLib2Text
  rw [decide_eq_true_eq]
  have htop : c2Lib2TextHi.toNat < 2 ^ 64 := BitVec.isLt c2Lib2TextHi
  generalize hd : pc - base = d at hsub
  have hpc_eq : pc = base + d := by subst hd; bv_omega
  have htoNat : pc.toNat = base.toNat + d.toNat := by
    rw [hpc_eq, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

theorem c2_keepTextBPre_of_sub_lt {base pc : BitVec 64} {len : Nat}
    (hsub : (pc - base).toNat < len)
    (hlo : c2TextBPreLo.toNat ≤ base.toNat)
    (hhi : base.toNat + len ≤ c2TextBPreHi.toNat) :
    keepTextBPre pc = true := by
  unfold keepTextBPre
  rw [decide_eq_true_eq]
  have htop : c2TextBPreHi.toNat < 2 ^ 64 := BitVec.isLt c2TextBPreHi
  generalize hd : pc - base = d at hsub
  have hpc_eq : pc = base + d := by subst hd; bv_omega
  have htoNat : pc.toNat = base.toNat + d.toNat := by
    rw [hpc_eq, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## 6. Fast Interned-ID `resolve = cliElfMultiPlacement.ρ` on `c2RxDehookedSyms` -/

set_option maxRecDepth 4000000 in
private theorem ls_sharedExterns_lookupId_ok :
    libsignalSessionExterns =
        lsSharedExterns.map (fun idx => lsInternedMultiLib.names.getD idx "") ∧
      (lsSharedExterns.all fun idx =>
        Nat.blt idx lsInternedMultiLib.names.length &&
          (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none)) = true :=
  ⟨by rfl_kernel, by rfl_kernel⟩

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

private theorem c2RxDehookedSyms_sub_externs_and_names :
    (c2RxDehookedSyms.all fun s =>
      libsignalSessionExterns.contains s && lsInternedMultiLib.names.contains s) = true := by
  rfl_kernel

/-- Any `s ∈ c2RxDehookedSyms` resolves under `hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl`
    to `cliElfMultiPlacement.ρ s`. -/
theorem resolve_c2RxSym_eq_cliElf_rho {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s : String} (hs : s ∈ c2RxDehookedSyms) :
    libsignalSessionLib.resolve mpl s = cliElfMultiPlacement.ρ s := by
  have hboth := List.all_eq_true.mp c2RxDehookedSyms_sub_externs_and_names s hs
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hboth
  have huniq := (cliElf_linkedAt_unique hLs).2.1 s hboth.2
  exact huniq.trans (libsignalSessionExterns_resolve_eq_rho cliElfMultiPlacement s hboth.1)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
