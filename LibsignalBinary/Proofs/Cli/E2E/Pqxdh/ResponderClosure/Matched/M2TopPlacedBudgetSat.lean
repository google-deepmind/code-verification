/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2OkPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import ProofLib.SepLogic.WPp

/-!
# `HookSat`-Backed Budget-Threaded Top-Level Stage P2 Matched-Session Contract

Additive `HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat` sibling of
`LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget` on Block `518`
(`lsProg_518 (Rust.withPanics ext)`). Carves `80` B (`publicKeyEqMemBudgetSpec16`) out of
`stackAt sp rootStack` (`262144` B), keeping all outer theorem conclusions identical to
`M2TopPlacedBudget`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudgetSat

noncomputable section

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (IdentityKey PublicKey SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  LibsignalPlacement lsBlackBoxU8Sym lsLogFilterAddr ls_subroutine_ok_of_block lsmpl lsρ
  withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (remoteIdentityOkAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalPublicApiRepr (
  RecordGhost apiDecResultAt sessionRecordAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved decryptPrekeySavedRegsAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  SepWPp.weaken_frame entails_replace_sub eq_of_sep_emp
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open scoped CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel stackAt_split_of_le
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  chunks32At coro_2a0_split32_placed memRegion_32_eq_chunks32 memRegion_34_split_24_10
  memRegion_34_split_32_2 memRegion_920_6_join memRegion_920_6_split memRegion_a90_48_join_10_38
  memRegion_a90_48_split_10_38 mismatchRemoteIkStrPlaced pack16LE pack32LE pack64LE
  pointsToBytes_32_eq_chunks32 prevSessionsEmptyAt processPrekeyActive10At_eq_placed
  publicKey_beq_false_of_ne_placed rem34_bytes_entails_memRegion34 remoteIdentityOkAt_none_eq
  remoteIdentityOkAt_some_eq
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  publicKeySerializeSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (
  blackBoxSpecSat publicKeyEqMemBudgetSpec16 publicKeyEqMemSpec16
  publicKey_eq_mem_placed_vm_ok_16_sat
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudget (
  StageP2MatchedBridgeEnv stageP2MatchedBridgeEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedBudgetSat (
  stageP2_matched_0868_to_094c_placed_sat
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2OkPlacedBudget (
  bind_sepWPp_nopanic_state p2_seg_094c_ok_placed_wp p2_seg_094c_ok_vm_placed_wp
  p2_seg_1064_none_placed_wp p2_seg_1064_some_load_vm_placed_wp
  p2_seg_1094_some_store_vm_placed_wp p2_seg_10cc_mismatch_placed_wp
  sepWPp_frame_pool_drop_vm sepWPp_lift_qp stageP2_matched_ok_10cc_to_1778_vm_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2PlacedBudget (
  bind_sepWP_lscro_steps_m2_placed call_lscro_nopanic_m2_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget (
  strToOwnedEvents strToOwnedLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlacedBudget (
  StageP2MismatchTailEnv stageP2MismatchTailPostAtPlaced stageP2MismatchTailPrePlaced
  stageP2_matched_mismatch_tail_exists_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudget (
  StageP2MatchedEnv StageP2MatchedMismatchEnv
  fitsEnv_publicKeySerialize_of_matchedEnv fitsEvents_mismatchTail_of_matchedEnv
  stageP2MatchedMatchPrePlaced stageP2MatchedMismatchEnv_of_tail
  stageP2MatchedMismatchPostPlaced stageP2MatchedPrePlaced
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

private theorem stack_root_to_pkEq16_mem_placed (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - 80) ∗
      memRegion (sp - 80#64) 80 := by
  rw [stackAt_split_of_le sp rootStack 80 (by decide) hn]

private theorem sepWPp_ret_frame_nopanic {prog : Program} {ret : BitVec 64} {s : State}
    {P P_stage F : SepProp} {Q_stage Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog ret s P_stage Q_stage (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hret : ∀ sf P_f, Steps prog s sf → sf.pc = ret → sf.status = .Running →
      Q_stage sf P_f → Q sf (P_f ∗ F)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hqf⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f ∗ F, hmf, hret sf P_f hsteps hpcf hrunf hqf⟩⟩
  · exact False.elim hpan
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Remote-identity `Some ik` check (`+0x094c → +0x10cc`) under `HookSat` -/

set_option maxHeartbeats 1200000 in
/-- `HookSat`-backed sibling of `M2OkPlacedBudget.stageP2_matched_094c_some_to_10cc_vm_placed`. -/
theorem stageP2_matched_094c_some_to_10cc_vm_placed_sat [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h_bb : HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat)
    (s : State)
    (sp coroPtr outPtr msgPtr : BitVec 64)
    (remIdKey ik : IdentityKey)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x10cc#64) s
      (remoteIdentityOkAt (sp + 0x3e0#64) (some ik) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       memRegion (sp + 0x920#64) 6 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       stackAt sp rootStack)
      (fun s4 P_f =>
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 34 ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          memRegion (sp + 0x920#64) 6 ∗
          memRegion (sp + 0xa90#64) 48 ∗
          stackAt sp rootStack) ∧
        VmPreserved s s4 ∧
        (s4.sp = sp ∧
         s4.trace = s.trace ∧
         s4.readReg64 .x0 = (if remIdKey.publicKey == ik.publicKey then 1#64 else 0#64) ∧
         s4.readReg64 .x19 = coroPtr ∧
         s4.readReg64 .x25 = sp + 0x210#64 ∧
         s4.readReg64 .x26 = outPtr ∧
         s4.readReg64 .x28 = sp + 0xa90#64 ∧
         s4.readReg64 .x29 = s.readReg64 .x29 ∧
         calleeSavedVRegs s4 = calleeSavedVRegs s ∧
         LibsignalCodeRoLoaded lsmpl s4.mem))
      (fun _ _ => False) := by
  have hroot_le : rootStack ≤ 2 ^ 64 := Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  let bs := ik.publicKey.bytes.toList
  have hbs_len : bs.length = 32 := ik.publicKey.bytes.property
  let w0 := pack32LE (bs.take 4)
  let h1 := pack16LE ((bs.drop 4).take 2)
  let q2 := pack64LE ((bs.drop 6).take 8)
  let q3 := pack64LE ((bs.drop 14).take 8)
  let q4 := pack64LE ((bs.drop 22).take 8)
  let h5 := pack16LE (bs.drop 30)
  conv => arg 4; rw [remoteIdentityOkAt_some_eq sp ik,
      show ik.publicKey.bytes.toList = bs from rfl,
      pointsToBytes_32_eq_chunks32 (sp + 0x3e2#64) bs hbs_len,
      memRegion_920_6_split sp, memRegion_a90_48_split_10_38 sp]
  dsimp only [chunks32At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  sep_norm
  refine SepWPp.exists_elim fun u_920 => SepWPp.exists_elim fun u_924 =>
    SepWPp.exists_elim fun u_a90 => SepWPp.exists_elim fun u_a98 => ?_
  have h094c := p2_seg_094c_ok_vm_placed_wp ext s coroPtr outPtr hpc hrun hsp_align hx19
  rw [hsp_eq] at h094c
  refine bind_sepWP_lscro_steps_m2_placed hcro h094c (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 ⟨hvm1, hregs1⟩ => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx19_1, hx21_1, _, _, hx25_1, hx26_1, _, hx28_1, hx29_1, _⟩
  have hsp1 : s1.sp = sp := hsp1_s
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1, ← hsp_eq]; exact hsp_align
  have hx21_1' : s1.readReg64 .x21 = s1.sp + 0x370#64 := by rw [hsp1]; exact hx21_1.trans hx21
  have h1064 := p2_seg_1064_some_load_vm_placed_wp ext s1 coroPtr q2 q3 q4 u_a90
    w0 u_920 h1 h5 u_924 u_a98 hpc1 hrun1 hsp1_align hx19_1 hx21_1'
  rw [hsp1] at h1064
  refine bind_sepWP_lscro_steps_m2_placed hcro1 h1064 (by sep_focus)
    fun s2 _ hpc2 hrun2 hcro2 ⟨hvm2, hregs2⟩ => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, hvregs2, hx8_2, hx9_2, hx19_2, hx21_2, hx25_2, hx26_2, _, hx28_2, hx29_2, _⟩
  have hsp2 : s2.sp = sp := hsp2_1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  have hx21_2' : s2.readReg64 .x21 = s2.sp + 0x370#64 := by rw [hsp2]; exact hx21_2
  have hrepack34 :
      ((sp + 0x3e0#64) ↦₈ 0#8) ∗ ((sp + 0x3e1#64) ↦₈ 1#8) ∗
        chunks32At (sp + 0x3e2#64) w0 h1 q2 q3 q4 h5 ⊢
        memRegion (sp + 0x3e0#64) 32 ∗ memRegion (sp + 0x400#64) 2 := by
    rw [← memRegion_34_split_32_2 sp]
    exact rem34_bytes_entails_memRegion34 sp 0#8 1#8 w0 h1 q2 q3 q4 h5
  dsimp only [chunks32At] at hrepack34
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack34
  refine SepWPp.weaken_frame hrepack34 (by sep_focus) ?_
  conv => arg 4; rw [memRegion_32_eq_chunks32 (sp + 0x3e0#64)]
  dsimp only [chunks32At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  sep_norm
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
    SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun d5 => ?_
  have h1094 := p2_seg_1094_some_store_vm_placed_wp ext s2 coroPtr msgPtr q2 q3 q4 d2 d3 d4
    w0 d0 h1 h5 d1 d5 hpc2 hrun2 hsp2_align hx8_2 hx9_2 hx19_2 hx21_2'
  rw [hsp2] at h1094
  refine bind_sepWP_lscro_steps_m2_placed hcro2 h1094 (by sep_focus)
    fun s3 _ hpc3 hrun3 hcro3 ⟨hvm3, hregs3⟩ => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hvregs3, hx0_3, hx1_3, hx19_3, _, hx25_3, hx26_3, _, hx28_3, hx29_3, hx30_3⟩
  have hsp3 : s3.sp = sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by
    simpa only [State.spAligned, hsp3, ← hsp_eq] using hsp_align
  have hfold_bs :
      ((sp + 0x3e0#64) ↦₃₂ w0) ∗ ((sp + 0x3e4#64) ↦₁₆ h1) ∗
      ((sp + 0x3e6#64) ↦₆₄ q2) ∗ ((sp + 0x3ee#64) ↦₆₄ q3) ∗
      ((sp + 0x3f6#64) ↦₆₄ q4) ∗ ((sp + 0x3fe#64) ↦₁₆ h5) =
      ((sp + 0x3e0#64) ↦ₛ ik.publicKey.bytes.toList) := by
    rw [show ik.publicKey.bytes.toList = bs from rfl,
        pointsToBytes_32_eq_chunks32 (sp + 0x3e0#64) bs hbs_len]
    dsimp only [chunks32At, w0, h1, q2, q3, q4, h5]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hfold_bs) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_pkEq16_mem_placed sp hroot_le)) (by sep_focus) ?_
  have hpkeq := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := lsProg_518 (Rust.withPanics ext))
      (j := 212) (entry := lsmpl.base 212)
      (publicKey_eq_mem_placed_vm_ok_16_sat h_bb)
      (by decide))
  refine call_lscro_nopanic_m2_placed
    (spec := publicKeyEqMemBudgetSpec16)
    (x := (msgPtr + 0xc8#64, remIdKey.publicKey, sp + 0x3e0#64, ik.publicKey, sp))
    (T := ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
      ((sp + 0x3e0#64) ↦ₛ ik.publicKey.bytes.toList) ∗
      memRegion (sp - 80#64) 80)
    hcro3 hpkeq hpc3 hrun3 hsp3_al hx30_3
    (by dsimp only [publicKeyEqMemBudgetSpec16, withVmPreserved, publicKeyEqMemSpec16])
    (And.intro hx0_3 (And.intro hx1_3 hsp3)) (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  dsimp only [publicKeyEqMemBudgetSpec16, withVmPreserved, publicKeyEqMemSpec16]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hvm4 => SepWPp.pure_elim fun ⟨hx0_4, htr4_3⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_pkEq16_mem_placed sp hroot_le).symm) (by sep_focus) ?_
  rcases hcs4 with ⟨hx19_cs4, _, _, _, _, _, hx25_cs4, hx26_cs4, _, hx28_cs4, hx29_cs4, hvregs_cs4⟩
  refine SepWPp.done hpc4 hrun4 ⟨?_, hvm1.trans (hvm2.trans (hvm3.trans hvm4)),
    hsp4_3.trans hsp3,
    htr4_3.trans (htr3_2.trans (htr2_1.trans htr1_s)),
    hx0_4, hx19_cs4.trans hx19_3,
    hx25_cs4.trans (hx25_3.trans (hx25_2.trans (hx25_1.trans hx25))),
    hx26_cs4.trans (hx26_3.trans (hx26_2.trans hx26_1)),
    hx28_cs4.trans (hx28_3.trans (hx28_2.trans (hx28_1.trans hx28))),
    hx29_cs4.trans (hx29_3.trans (hx29_2.trans hx29_1)),
    hvregs_cs4.trans (congrArg VRegFile.calleeSaved (hvregs3.trans (hvregs2.trans hvregs1))),
    hcro4⟩
  have hbs34 :
      ((sp + 0x3e0#64) ↦ₛ ik.publicKey.bytes.toList) ∗ memRegion (sp + 0x400#64) 2 ⊢
        memRegion (sp + 0x3e0#64) 34 := by
    rw [memRegion_34_split_32_2 sp]
    refine sepConj_mono_left ?_
    simpa only [hbs_len] using ProofLib.pointsToBytes_entails_memRegion (sp + 0x3e0#64) bs
  refine Entails.trans (entails_replace_sub hbs34 (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub (memRegion_920_6_join sp w0 h1) (by sep_focus) rfl) ?_
  exact entails_replace_sub (memRegion_a90_48_join_10_38 sp q4 h5) (by sep_focus)
    (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- `HookSat`-backed sibling of `M2OkPlacedBudget.stageP2_matched_094c_some_to_10cc_placed`. -/
theorem stageP2_matched_094c_some_to_10cc_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (h_bb : HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat)
    (st : M.σ) (s : State)
    (sp coroPtr outPtr msgPtr : BitVec 64)
    (remIdKey ik : IdentityKey)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x10cc#64) s
      (remoteIdentityOkAt (sp + 0x3e0#64) (some ik) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       memRegion (sp + 0x920#64) 6 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       A.pool lim st s ∗
       stackAt sp rootStack)
      (fun s4 P_f =>
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 34 ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          memRegion (sp + 0x920#64) 6 ∗
          memRegion (sp + 0xa90#64) 48 ∗
          A.pool lim st s4 ∗
          stackAt sp rootStack) ∧
        s4.sp = sp ∧
        s4.trace = s.trace ∧
        s4.readReg64 .x0 = (if remIdKey.publicKey == ik.publicKey then 1#64 else 0#64) ∧
        s4.readReg64 .x19 = coroPtr ∧
        s4.readReg64 .x25 = sp + 0x210#64 ∧
        s4.readReg64 .x26 = outPtr ∧
        s4.readReg64 .x28 = sp + 0xa90#64 ∧
        s4.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s4 = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl s4.mem)
      Qp := by
  have hvm := sepWPp_frame_pool_drop_vm A lim st (Qp := Qp)
    (stageP2_matched_094c_some_to_10cc_vm_placed_sat h_bb s sp coroPtr outPtr msgPtr
      remIdKey ik hcro hsp_eq hsp_root hpc hrun hsp_align hx19 hx21 hx25 hx28)
  intro R hm hL
  obtain ⟨s4, hsteps, ⟨hpc4, hrun4, P_f, hm4, hent, hregs⟩ | hrest⟩ :=
    hvm R (Arm64.Satisfies.mono (sepConj_mono_left (Entails.of_eq (by sep_ac_rfl))) hm) hL
  · refine ⟨s4, hsteps, Or.inl ⟨hpc4, hrun4, P_f, hm4, ?_, hregs⟩⟩
    exact Entails.trans hent (Entails.of_eq (by sep_ac_rfl))
  · exact ⟨s4, hsteps, Or.inr hrest⟩

/-! ## Remote-identity match branch (`+0x094c → +0x1778`) under `HookSat` -/

set_option maxHeartbeats 1200000 in
/-- `HookSat`-backed sibling of `M2OkPlacedBudget.stageP2_matched_094c_match_vm_placed`. -/
theorem stageP2_matched_094c_match_vm_placed_sat [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_bb : HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat)
    (s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388
      u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_4f2 b_390 b_3ac : BitVec 8)
    (remIdKey : IdentityKey)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hrem_eq : recSt.remoteIdentity = some remIdKey)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x1778#64) s
      (remoteIdentityOkAt (sp + 0x3e0#64) recSt.remoteIdentity ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
       ((sp + 0x80#64) ↦₆₄ u_80) ∗
       ((sp + 0x88#64) ↦₆₄ u_88) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₃₂ u_b8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
       ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗
       ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
       ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
       ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
       memRegion (sp + 0x920#64) 6 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ opkHi : BitVec 32, ∃∗ kyberPacked : BitVec 64,
            memRegion (sp + 0x3e0#64) 34 ∗
            sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
            ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
            ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
            ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
            cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
            ((coroPtr + 0x29c#64) ↦₃₂ opkHi) ∗
            ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗
            ((coroPtr + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
            ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
            ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
            ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
            ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
            ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((sp + 0x90#64) ↦₆₄ v_388) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
            ((sp + 0xa8#64) ↦₆₄ v_330) ∗
            ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
            ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
            ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
            ((sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
            ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
            ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
            ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
            ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            memRegion (sp + 0x920#64) 6 ∗
            memRegion (sp + 0xa90#64) 48 ∗
            stackAt sp rootStack) ∧
        VmPreserved s sf ∧
        (sf.sp = sp ∧
         sf.trace = s.trace ∧
         sf.readReg64 .x19 = coroPtr ∧
         sf.readReg64 .x27 = sp + 0x370#64 ∧
         sf.readReg64 .x29 = s.readReg64 .x29 ∧
         calleeSavedVRegs sf = calleeSavedVRegs s ∧
         LibsignalCodeRoLoaded lsmpl sf.mem))
      (fun _ _ => False) := by
  conv =>
    arg 4
    rw [hrem_eq]
  have hchk := stageP2_matched_094c_some_to_10cc_vm_placed_sat h_bb s sp coroPtr outPtr msgPtr
    remIdKey remIdKey hcro hsp_eq hsp_root hpc hrun hsp_align hx19 hx21 hx25 hx28
  refine bind_sepWPp_nopanic_state hchk (by sep_focus)
    fun s1 _ hpc1 hrun1 ⟨hvm1, hsp1, htr1, hx0_1, hx19_1, _, hx26_1, _, hx29_1, hvregs1, hcro1⟩ => ?_
  have hx0_one : s1.readReg64 .x0 = 1#64 := by
    simpa [beq_self_eq_true] using hx0_1
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1, ← hsp_eq]; exact hsp_align
  have htail := stageP2_matched_ok_10cc_to_1778_vm_placed (A := A) (ext := ext)
    s1 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388
    u_80 u_88 u_90 (coroPtr + 0x4f2#64) u_a8 u_b0 v_d0
    u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
    u_2a8 u_b8 msgVerByte b_4f2 b_390 b_3ac
    recG recSt hcro1 hsp1 hsp_root hpc1 hrun1 hsp1_align hx0_one hx19_1 hx26_1
  refine bind_sepWPp_nopanic_state htail (by sep_focus)
    fun sf _ hpcf hrunf ⟨hvm2, hspf, htrf, hx19_f, hx27_f, hx29_f, hvregsf_1, hcrof⟩ => ?_
  refine SepWPp.done hpcf hrunf
    ⟨?_, hvm1.trans hvm2,
     hspf, htrf.trans htr1, hx19_f, hx27_f, hx29_f.trans hx29_1, hvregsf_1.trans hvregs1, hcrof⟩
  sep_norm
  refine Entails.sepExists_elim fun opkHi => Entails.sepExists_right opkHi ?_
  refine Entails.sepExists_elim fun kyberPacked => Entails.sepExists_right kyberPacked ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- `HookSat`-backed sibling of `M2OkPlacedBudget.stageP2_matched_094c_match_placed`. -/
theorem stageP2_matched_094c_match_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (h_bb : HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat)
    (st : M.σ) (s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388
      u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_4f2 b_390 b_3ac : BitVec 8)
    (remIdKey : IdentityKey)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hrem_eq : recSt.remoteIdentity = some remIdKey)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x1778#64) s
      (remoteIdentityOkAt (sp + 0x3e0#64) recSt.remoteIdentity ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
       ((sp + 0x80#64) ↦₆₄ u_80) ∗
       ((sp + 0x88#64) ↦₆₄ u_88) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₃₂ u_b8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
       ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗
       ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
       ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
       ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
       memRegion (sp + 0x920#64) 6 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       A.pool lim st s ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ opkHi : BitVec 32, ∃∗ kyberPacked : BitVec 64,
            memRegion (sp + 0x3e0#64) 34 ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
            ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
            ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
            ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
            cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
            ((coroPtr + 0x29c#64) ↦₃₂ opkHi) ∗
            ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗
            ((coroPtr + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
            ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
            ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
            ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
            ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
            ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((sp + 0x90#64) ↦₆₄ v_388) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
            ((sp + 0xa8#64) ↦₆₄ v_330) ∗
            ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
            ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
            ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
            ((sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
            ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
            ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
            ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
            ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            memRegion (sp + 0x920#64) 6 ∗
            memRegion (sp + 0xa90#64) 48 ∗
            A.pool lim st sf ∗
            stackAt sp rootStack) ∧
        sf.sp = sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x27 = sp + 0x370#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hvm := sepWPp_frame_pool_drop_vm A lim st (Qp := Qp)
    (stageP2_matched_094c_match_vm_placed_sat (A := A.repAlloc) (ext := ext)
      h_bb s sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388
      u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
      u_2a8 u_b8 msgVerByte b_4f2 b_390 b_3ac remIdKey recG recSt hrem_eq
      hcro hsp_eq hsp_root hpc hrun hsp_align hx19 hx21 hx25 hx28)
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hent, hregs⟩ | hrest⟩ :=
    hvm R (Arm64.Satisfies.mono (sepConj_mono_left (Entails.of_eq (by sep_ac_rfl))) hm) hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ?_, hregs⟩⟩
    refine Entails.trans hent ?_
    sep_norm
    refine Entails.sepExists_elim fun opkHi => Entails.sepExists_right opkHi ?_
    refine Entails.sepExists_elim fun kyberPacked => Entails.sepExists_right kyberPacked ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · exact ⟨sf, hsteps, Or.inr hrest⟩

/-! ## Remote-identity mismatch branch (`+0x094c → s0.readReg64 .x30`) under `HookSat` -/

set_option maxHeartbeats 1200000 in
/-- `HookSat`-backed sibling of `M2TopPlacedBudget.stageP2_matched_094c_mismatch_exists_placed`. -/
theorem stageP2_matched_094c_mismatch_exists_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (h_bb : HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr msgPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (remIdKey : IdentityKey)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hrem_ne : recSt.remoteIdentity ≠ some remIdKey)
    (hfits : FitsEvents M lim st (strToOwnedEvents mismatchRemoteIkStrPlaced))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (remoteIdentityOkAt (sp + 0x3e0#64) recSt.remoteIdentity ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x920#64) 6 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       memRegion outPtr 48 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, StageP2MismatchTailEnv evs ∧
          (P_f ⊢
            memRegion (sp + 0x3e0#64) 34 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
            ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
            cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
            memRegion (sp + 0x370#64) 36 ∗
            memRegion (sp + 0x920#64) 6 ∗
            memRegion (sp + 0xa90#64) 48 ∗
            apiDecResultAt A.repAlloc outPtr
              (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt sp rootStack)) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  apply sepWPp_lift_qp
  cases hrem : recSt.remoteIdentity with
  | none =>
    conv =>
      arg 4
      rw [remoteIdentityOkAt_none_eq sp, memRegion_32_eq_chunks32 (sp + 0x3e2#64),
          memRegion_920_6_split sp, memRegion_a90_48_split_10_38 sp]
    dsimp only [chunks32At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    sep_norm
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun h1 =>
      SepWPp.exists_elim fun q2 => SepWPp.exists_elim fun q3 =>
      SepWPp.exists_elim fun q4 => SepWPp.exists_elim fun h5 =>
      SepWPp.exists_elim fun u_920 => SepWPp.exists_elim fun u_924 =>
      SepWPp.exists_elim fun u_a90 => SepWPp.exists_elim fun u_a98 => ?_
    have h094c := p2_seg_094c_ok_placed_wp (A := A) (lim := lim) ext st s coroPtr outPtr
      hpc hrun hsp_align hx19
    rw [hsp_eq] at h094c
    refine bind_sepWP_lscro_steps_m2_placed hcro h094c (by sep_focus)
      fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx19_1, hx21_1, _, _, hx25_1, hx26_1, _, hx28_1, _, _⟩
    have hsp1 : s1.sp = sp := hsp1_s
    have hx21_1' : s1.readReg64 .x21 = s1.sp + 0x370#64 := by rw [hsp1]; exact hx21_1.trans hx21
    have h1064 := p2_seg_1064_none_placed_wp (A := A) (lim := lim) ext st s1 coroPtr q2 q3 q4 u_a90
      w0 u_920 h1 h5 u_924 u_a98 hpc1 hrun1 (by rw [hsp1, ← hsp_eq]; exact hsp_align) hx19_1 hx21_1'
    rw [hsp1] at h1064
    refine bind_sepWP_lscro_steps_m2_placed hcro1 h1064 (by sep_focus)
      fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2_1, htr2_1, hvregs2, hx19_2, hx25_2, hx26_2, _, hx28_2, _, _⟩
    have hsp2 : s2.sp = sp := hsp2_1
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    have htr2_s : s2.trace = s.trace := htr2_1.trans htr1_s
    have hx25_2' : s2.readReg64 .x25 = sp + 0x210#64 := hx25_2.trans (hx25_1.trans hx25)
    have hx26_2' : s2.readReg64 .x26 = outPtr := hx26_2.trans hx26_1
    have hx28_2' : s2.readReg64 .x28 = sp + 0xa90#64 := hx28_2.trans (hx28_1.trans hx28)
    have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      congrArg VRegFile.calleeSaved (hvregs2.trans hvregs1)
    have hrem34 := rem34_bytes_entails_memRegion34 sp 0#8 0#8 w0 h1 q2 q3 q4 h5
    dsimp only [chunks32At] at hrem34
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrem34
    refine SepWPp.weaken_frame hrem34 (by sep_focus) ?_
    refine SepWPp.weaken_frame (memRegion_920_6_join sp w0 h1) (by sep_focus) ?_
    refine SepWPp.weaken_frame (memRegion_a90_48_join_10_38 sp q4 h5) (by sep_focus) ?_
    conv => arg 4; rw [memRegion_34_split_24_10 sp]
    simp only [sepConj_assoc]
    have htail := stageP2_matched_mismatch_tail_exists_placed (Qp := fun _ _ => False)
      hto hdealloc hdrop_ss st s0 s2 sp coroPtr outPtr u_a8 u_d0 b_4f2 b_390 b_2c0 g recG recSt
      hfits hcro2 hsp2 hsp_root hpc2 hrun2 hsp2_align hx19_2 hx25_2' hx26_2' hx28_2'
    refine sepWPp_ret_frame_nopanic htail
      (by unfold stageP2MismatchTailPrePlaced; sep_focus)
      fun sf P_tail _ _ _ ⟨⟨evs, henv, hent_tail⟩, hspf, htrf_2, hcsf, hvregsf_2, hcrof⟩ => ?_
    refine ⟨⟨evs, henv, ?_⟩, hspf, htrf_2.trans htr2_s, hcsf, hvregsf_2.trans hvregs2_s, hcrof⟩
    unfold stageP2MismatchTailPostAtPlaced at hent_tail
    refine Entails.trans (sepConj_mono_left hent_tail) ?_
    have hjoin34 : memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 10 ⊢
        memRegion (sp + 0x3e0#64) 34 :=
      Entails.of_eq (memRegion_34_split_24_10 sp).symm
    exact entails_replace_sub hjoin34 (by sep_focus) (by sep_ac_rfl)
  | some ik =>
    have hne_ik : some ik ≠ some remIdKey := by rw [← hrem]; exact hrem_ne
    have hchk := stageP2_matched_094c_some_to_10cc_placed_sat (A := A) (lim := lim)
      (Qp := fun _ _ => False)
      h_bb st s sp coroPtr outPtr msgPtr remIdKey ik hcro hsp_eq hsp_root hpc hrun hsp_align
      hx19 hx21 hx25 hx28
    refine bind_sepWPp_nopanic_state hchk (by sep_focus)
      fun s1 _ hpc1 hrun1 ⟨hsp1, htr1_s, hx0_1, hx19_1, hx25_1, hx26_1, hx28_1, _, hvregs1, hcro1⟩ => ?_
    have hx0_zero : s1.readReg64 .x0 = 0#64 := by
      simpa [publicKey_beq_false_of_ne_placed hne_ik] using hx0_1
    have h10cc := p2_seg_10cc_mismatch_placed_wp (A := A) (lim := lim) ext st s1 coroPtr
      hpc1 hrun1 hx0_zero hx19_1
    refine bind_sepWP_lscro_steps_m2_placed hcro1 h10cc (by sep_focus)
      fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2_1, htr2_1, hvregs2, hx19_2, hx25_2, hx26_2, _, hx28_2, _, _⟩
    have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    have htr2_s : s2.trace = s.trace := htr2_1.trans htr1_s
    have hx25_2' : s2.readReg64 .x25 = sp + 0x210#64 := hx25_2.trans hx25_1
    have hx26_2' : s2.readReg64 .x26 = outPtr := hx26_2.trans hx26_1
    have hx28_2' : s2.readReg64 .x28 = sp + 0xa90#64 := hx28_2.trans hx28_1
    have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      (congrArg VRegFile.calleeSaved hvregs2).trans hvregs1
    conv => arg 4; rw [memRegion_34_split_24_10 sp]
    simp only [sepConj_assoc]
    have htail := stageP2_matched_mismatch_tail_exists_placed (Qp := fun _ _ => False)
      hto hdealloc hdrop_ss st s0 s2 sp coroPtr outPtr u_a8 u_d0 b_4f2 b_390 b_2c0 g recG recSt
      hfits hcro2 hsp2 hsp_root hpc2 hrun2 hsp2_align hx19_2 hx25_2' hx26_2' hx28_2'
    refine sepWPp_ret_frame_nopanic htail
      (by unfold stageP2MismatchTailPrePlaced; sep_focus)
      fun sf P_tail _ _ _ ⟨⟨evs, henv, hent_tail⟩, hspf, htrf_2, hcsf, hvregsf_2, hcrof⟩ => ?_
    refine ⟨⟨evs, henv, ?_⟩, hspf, htrf_2.trans htr2_s, hcsf, hvregsf_2.trans hvregs2_s, hcrof⟩
    unfold stageP2MismatchTailPostAtPlaced at hent_tail
    refine Entails.trans (sepConj_mono_left hent_tail) ?_
    have hjoin34 : memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 10 ⊢
        memRegion (sp + 0x3e0#64) 34 :=
      Entails.of_eq (memRegion_34_split_24_10 sp).symm
    exact entails_replace_sub hjoin34 (by sep_focus) (by sep_ac_rfl)

/-! ## Top-level budget-threaded Stage P2 matched-session contract under `HookSat` -/

set_option maxHeartbeats 1200000 in
/-- `HookSat`-backed sibling of `M2TopPlacedBudget.stageP2_matched_ok_placed`. -/
theorem stageP2_matched_ok_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A lim)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustCliDeallocBudgetSpec M A lim))
    (h_bb : HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st : M.σ) (s0 s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
      v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac : BitVec 8)
    (baseKey : PublicKey) (remIdKey : IdentityKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (F : SepProp)
    (hcur : r.currentSession = some sess)
    (hver : sess.state.version = outerVerByte.zeroExtend 32)
    (halice : sess.aliceBaseKey = baseKey.serialize)
    (hfits : FitsEnv M lim st (StageP2MatchedEnv sess remIdKey))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64)
    (hmismatch : sess.state.remoteIdentity ≠ some remIdKey →
      ∀ (evs : List AllocEvent),
        StageP2MatchedMismatchEnv evs →
        ∀ (sf : State) (Pf : SepProp),
          sf.pc = s0.readReg64 .x30 →
          sf.status = .Running →
          Steps (lsProg_518 (Rust.withPanics ext)) s sf →
          sf.sp = sp + 0xcd0#64 →
          sf.trace = s.trace →
          ClosureCalleeSaved s0 sf →
          calleeSavedVRegs sf = calleeSavedVRegs s →
          LibsignalCodeRoLoaded lsmpl sf.mem →
          (Pf ⊢ stageP2MatchedMismatchPostPlaced A lim (M.stepEvents evs st) s0 sf sp coroPtr outPtr
            msgPtr remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt v_330 v_388 u_80 u_88 u_90 u_b0
            u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
            u_2a8 u_b8 outerVerByte innerVerByte b_3ac baseKey remIdKey F) →
          Q sf Pf)
    (hmatch : sess.state.remoteIdentity = some remIdKey →
      ∀ (evs : List AllocEvent),
        StageP2MatchedBridgeEnv evs →
        ∀ (s2 : State) (recG : SessionGhost) (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
          g.cur = some recG →
          SessionExtraRel recG sess →
          Steps (lsProg_518 (Rust.withPanics ext)) s s2 →
          s2.pc = (blkPl_518).base + 0x1778#64 →
          s2.status = .Running →
          s2.sp = sp →
          (s2.sp &&& 15#64 == 0#64) = true →
          s2.trace = s.trace →
          s2.readReg64 .x19 = coroPtr →
          s2.readReg64 .x27 = sp + 0x370#64 →
          s2.readReg64 .x29 = sp + 0xc70#64 →
          calleeSavedVRegs s2 = calleeSavedVRegs s →
          LibsignalCodeRoLoaded lsmpl s2.mem →
          SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
            (stageP2MatchedMatchPrePlaced A lim (M.stepEvents evs st) s0 s2 sp coroPtr outPtr msgPtr
              remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt v_330 v_388 v_d0
              opkHi kyberPreKeyId signedPreKeyId outerVerByte innerVerByte b_2c0
              baseKey remIdKey g recG sess.state F)
            Q Qp) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP2MatchedPrePlaced A lim st s0 s sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
        v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
        u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
        u_2a8 u_b8 outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac
        baseKey remIdKey g r F)
      Q Qp := by
  dsimp only [stageP2MatchedPrePlaced, stageP2MatchedMismatchPostPlaced,
    stageP2MatchedMatchPrePlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedPrePlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedMismatchPostPlaced,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2MatchedMatchPrePlaced]
    at hmismatch hmatch ⊢
  have hpre_eq :
      sessionRecordAt (A.atState lim st s) (coroPtr + 0xe0#64) g r =
        sessionRecordAt A.repAlloc (coroPtr + 0xe0#64) g r := rfl
  have hpool_s : (A.atState lim st s).pool = A.pool lim st s := rfl
  rw [hpre_eq, hpool_s]
  have hpre := stageP2_matched_0868_to_094c_placed_sat (Qp := fun _ _ => False)
    hser hdealloc h_bb st s sp coroPtr msgPtr
    remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt outerVerByte b_4f1 baseKey
    g r sess hcur hver halice (fitsEnv_publicKeySerialize_of_matchedEnv hfits)
    hcro hsp_eq hsp_root hpc hrun hsp_align
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28 hx29
  refine bind_sepWPp_nopanic_state hpre (by sep_focus)
    fun sm hsteps01 hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hspm, htrm, hx19m, hx21m, hx25m, hx28m, hx29m, hvregsm, hcrom⟩
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by rw [hspm, ← hsp_eq]; exact hsp_align
  let st_br := M.stepEvents stageP2MatchedBridgeEvents st
  sep_norm
  refine SepWPp.exists_elim fun recG => SepWPp.pure_elim fun ⟨hgc, hextra⟩ => ?_
  by_cases hrem : sess.state.remoteIdentity = some remIdKey
  · conv =>
      arg 4
      rw [processPrekeyActive10At_eq_placed]
    simp only [sepConj_assoc]
    have hm := stageP2_matched_094c_match_placed_sat (A := A) (lim := lim) (Qp := fun _ _ => False)
      h_bb st_br sm sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388
      u_80 u_88 u_90 u_a8 u_b0 v_d0 u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
      u_2a8 u_b8 innerVerByte b_4f2 b_390 b_3ac remIdKey recG sess.state hrem
      hcrom hspm hsp_root hpcm hrunm hspm_align hx19m hx21m hx25m hx28m
    refine bind_sepWPp_nopanic_state hm (by sep_focus)
      fun s2 hsteps12 hpc2 hrun2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx27_2, hx29_2, hvregs2, hcro2⟩
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    sep_norm
    refine SepWPp.exists_elim fun opkHi => SepWPp.exists_elim fun kyberPacked => ?_
    have hgoal := hmatch hrem stageP2MatchedBridgeEvents rfl s2 recG opkHi
      (kyberPacked.extractLsb' 0 32) (kyberPacked.extractLsb' 32 32)
      hgc hextra (hsteps01.trans hsteps12) hpc2 hrun2 hsp2 hsp2_align
      (htr2.trans htrm) hx19_2 hx27_2 (hx29_2.trans hx29m) (hvregs2.trans hvregsm) hcro2
    refine fun R hmR hL => hgoal R (Arm64.Satisfies.mono (sepConj_mono_left ?_) hmR) hL
    have hprev2 :
        prevSessionsEmptyAt (A.atState lim st_br s2) coroPtr g =
          prevSessionsEmptyAt A.repAlloc coroPtr g := rfl
    have hss2 :
        sessionStateAt (A.atState lim st_br s2) (coroPtr + 0xf8#64) recG sess.state =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG sess.state := rfl
    have hpool2 : (A.atState lim st_br s2).pool = A.pool lim st_br s2 := rfl
    rw [hprev2, hss2, hpool2, coro_2a0_split32_placed coroPtr kyberPacked,
      processPrekeyActive10At_eq_placed]
    simp only [sepConj_assoc]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
  · conv =>
      arg 4
      rw [processPrekeyActive10At_eq_placed]
    simp only [sepConj_assoc]
    have hmm := stageP2_matched_094c_mismatch_exists_placed_sat (A := A) (lim := lim)
      (Qp := fun _ _ => False) hto hdealloc h_bb hdrop_ss st_br s0 sm
      sp coroPtr outPtr msgPtr u_a8 v_d0 b_4f2 b_390 b_2c0 remIdKey g recG sess.state
      hrem (fitsEvents_mismatchTail_of_matchedEnv hrem hfits)
      hcrom hspm hsp_root hpcm hrunm hspm_align hx19m hx21m hx25m hx28m
    refine sepWPp_ret_frame_nopanic hmm (by sep_focus)
      fun sf P_mis hsteps1f hpcf hrunf ⟨⟨evs_tail, htail, hent_mis⟩, hspf, htrf, hcsf, hvregsf, hcrof⟩ => ?_
    refine hmismatch hrem (stageP2MatchedBridgeEvents ++ evs_tail)
      (stageP2MatchedMismatchEnv_of_tail htail) sf _ hpcf hrunf
      (hsteps01.trans hsteps1f) hspf (htrf.trans htrm) hcsf (hvregsf.trans hvregsm) hcrof ?_
    refine Entails.trans (sepConj_mono_left hent_mis) ?_
    let st_exit := M.stepEvents (stageP2MatchedBridgeEvents ++ evs_tail) st
    have hstep_eq : M.stepEvents evs_tail st_br = st_exit :=
      (M.stepEvents_append stageP2MatchedBridgeEvents evs_tail st).symm
    have hdec_eq :
        apiDecResultAt (A.atState lim st_exit sf) outPtr
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) =
          apiDecResultAt A.repAlloc outPtr
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) := rfl
    have hpoolf : (A.atState lim st_exit sf).pool = A.pool lim st_exit sf := rfl
    rw [hstep_eq, hdec_eq, hpoolf, processPrekeyActive10At_eq_placed]
    simp only [sepConj_assoc]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev stageP2_matched_ok_framed_placed_sat := @stageP2_matched_ok_placed_sat

end

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedBudgetSat
