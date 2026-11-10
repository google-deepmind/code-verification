/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection

/-!
# Order-Independent Multi-Block Placement Combiner for Stock Mutant `mallocngLib`

In the stock `ld.lld` link (`stock_c2.ld`), `mallocngMultiL` blocks `20` (`memcpy`) and `21`
(`memset`) are placed in `.text.b_pre` ahead of blocks `0..19` in `.text`, so `mly.bases` are not
monotonically increasing by block index. `checkMultiMetaCoreAnyOrderB` and
`checkMultiSplitAnyOrder_spec` mirror `ElfMallocngPlaced` by falling back from `rangesSorted` to
pairwise `checkRangesDisjoint`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpecAnyOrder

open Arm64 Arm64.Obj Arm64.Obj.Interned Arm64.Process
open ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection

/-- Like `Obj.Interned.checkMultiMetaCoreFastB`, but falls back from `rangesSorted` to pairwise
    `checkRangesDisjoint` when blocks are laid out out-of-index-order in the stock `ld.lld` ELF. -/
def checkMultiMetaCoreAnyOrderB (ML : Obj.Interned.MultiLib)
    (mly : Obj.Interned.MultiLayout) (nameChars : List (List Char)) : Bool :=
  Nat.blt mly.bases.length 1048576 &&
  Nat.blt mly.addrs.length 1048576 &&
  Nat.blt mly.relax.length 1048576 &&
  Nat.blt mly.b2b.length 1048576 &&
  Nat.blt nameChars.length 1048576 &&
  Obj.Interned.namesNodup nameChars &&
  Obj.Interned.multiIdsOkFast ML &&
  Obj.Interned.withVecTree 0#64 mly.bases fun tBase =>
  Obj.Interned.withVecTree 0#64 mly.addrs fun tAddr =>
  Obj.Interned.withNat ML.names.length fun nNames =>
  match Obj.Interned.insertAllBlocks 0 ML.blocks (Obj.Interned.mkNoneTree 20 nNames) with
  | none => false
  | some tSym =>
    match Obj.Interned.insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => false
    | some _ =>
      Obj.Interned.blockSymsMatchTree ML tBase tAddr &&
      Obj.Interned.textPlaceableTreeMulti ML tBase tAddr &&
      (rangesSorted (Obj.Interned.blockRanges tBase 0 ML.blocks) ||
        Obj.allIdx (fun i b1 =>
          Obj.allIdx (fun j b2 =>
            !Nat.blt i j ||
              checkRangesDisjoint (mly.bases.getD i 0#64).toNat b1.code.length
                (mly.bases.getD j 0#64).toNat b2.code.length)
            0 ML.blocks) 0 ML.blocks)

/-- Combines order-independent metadata, data-walk, and text-walk checks into
    `Placeable ∧ InElf ∧ DataDisjoint`. -/
theorem checkMultiSplitAnyOrder_spec {lib : Obj.MultiPlacedLib}
    {ML : Obj.Interned.MultiLib} {mly : Obj.Interned.MultiLayout}
    {nameChars : List (List Char)} {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    (hlib : lib = ML.toMultiPlacedLib)
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (hcore : checkMultiMetaCoreAnyOrderB ML mly nameChars = true)
    (hdata : Obj.Interned.checkMultiMetaDataFastB ML mly = true)
    (hexp : Obj.Interned.checkMultiMetaExportsFastB ML mly nameChars symChars = true)
    (hdwalk : Obj.Interned.checkMultiDataWalkFastB ML mly img = true)
    (htwalk : Obj.Interned.checkMultiTextWalkFastB ML mly img = true) :
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl ∧ lib.DataDisjoint mpl := by
  subst hlib
  unfold checkMultiMetaCoreAnyOrderB at hcore
  unfold Obj.Interned.checkMultiMetaDataFastB at hdata
  unfold Obj.Interned.checkMultiMetaExportsFastB at hexp
  unfold Obj.Interned.checkMultiDataWalkFastB at hdwalk
  unfold Obj.Interned.checkMultiTextWalkFastB at htwalk
  simp only [withVecTree_eq, withRegionsWithLen_eq, buildEncSymTable_eq, withNat_eq,
    multiIdsOkFast_eq, Bool.and_eq_true, Nat.blt_eq] at hcore hdata hexp hdwalk htwalk
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, ha⟩, hrx⟩, hb2b⟩, hnc⟩, hnn⟩, hids⟩, hrest⟩ := hcore
  cases hsym : insertAllBlocks 0 ML.blocks (mkNoneTree 20 ML.names.length) with
  | none => rw [hsym] at hrest; nomatch hrest
  | some tSym =>
    rw [hsym] at hrest hexp
    dsimp only at hrest hexp
    cases hdsym : insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => rw [hdsym] at hrest; nomatch hrest
    | some tSymData =>
      rw [hdsym] at hrest
      dsimp only at hrest
      simp only [Bool.and_eq_true] at hrest
      obtain ⟨⟨hmatch, htp⟩, hdisj_or⟩ := hrest
      have hdisj' : Obj.allIdx (fun i b1 =>
          Obj.allIdx (fun j b2 =>
            !Nat.blt i j ||
              checkRangesDisjoint (mly.bases.getD i 0#64).toNat b1.code.length
                (mly.bases.getD j 0#64).toNat b2.code.length)
            0 ML.blocks) 0 ML.blocks = true := by
        rw [Bool.or_eq_true] at hdisj_or
        rcases hdisj_or with hsorted | hpw
        · exact blocksDisjoint_of_rangesSorted hb hsorted
        · exact hpw
      obtain ⟨hnd_syms, _, hget_sym⟩ := insertAllBlocks_spec 0 ML.blocks _ tSym hsym
      obtain ⟨hnd_data_raw, hnone_data_raw, _⟩ :=
        insertBlockSyms_spec 0 (ML.data.map fun d => (d.sym, 0)) tSym tSymData hdsym
      have hmap_data : ((ML.data.map fun d => (d.sym, 0)).map (·.1)) = ML.data.map (·.sym) := by
        simp [List.map_map, Function.comp_def]
      rw [hmap_data] at hnd_data_raw hnone_data_raw
      have hlookup : ∀ q, tSym.getD none q = lookupBlockSymId q ML.blocks := by
        intro q
        rw [hget_sym q, getD_mkNoneTree]
        rfl
      rw [blockSymsMatchTree_eq ML mly hb ha] at hmatch
      rw [textPlaceableTreeMulti_eq ML mly hb ha] at htp
      have hnd_b : natNodupFast ((ML.blocks.flatMap (·.symbols)).map (·.1)) = true := by
        simp [natNodupFast, natNodup_of_nodup hnd_syms]
      have hdp' := dataPlaceableTreeMulti_imp ML mly ha hnd_data_raw hdata.1
      have hdnone' : (ML.data.all fun d => (lookupBlockSymId d.sym ML.blocks).isNone) = true := by
        rw [List.all_eq_true]
        intro d hd
        have hnone := hnone_data_raw d.sym (List.mem_map_of_mem hd)
        rw [hlookup d.sym] at hnone
        simp [hnone]
      rw [multiTextWalkTree_eq ML mly hb ha hrx hb2b] at htwalk
      rw [dataWalkTreeMulti_eq ML mly ha] at hdwalk
      rw [multiExportsOkTree_eq ML mly nameChars _ tSym hb hnc hlookup] at hexp
      have hddisj' := multiDataDisjointTree_imp ha hdata.2
      have hmp : multiPlaceableB ML mly = true := by
        simp only [multiPlaceableB, Bool.and_eq_true]
        exact ⟨⟨⟨⟨htp, (Bool.or_eq_true _ _).mpr (Or.inr hdisj')⟩, hnd_b⟩, hdp'⟩, hdnone'⟩
      apply checkMultiDisjoint_spec hnames hsyms
      simp only [checkMultiDisjoint, checkMulti, Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨hnn, hids⟩, hmatch⟩, hmp⟩, htwalk⟩, hdwalk⟩, hexp⟩, hddisj'⟩

end Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpecAnyOrder
