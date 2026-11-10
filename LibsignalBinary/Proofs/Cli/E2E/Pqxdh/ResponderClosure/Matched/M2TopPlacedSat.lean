/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2OkPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import ProofLib.SepLogic.WPp

/-!
# `HookSat`-Backed Top-Level Stage P2 Matched-Session Contract (`Matched/M2TopPlacedSat`)

Additive `HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat` sibling of
`CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP2_matched_ok_framed_placed`
(`M2TopPlaced.lean`) on Block `518`. Carves `80` B (`publicKeyEqMemSpec16`) out of
`stackAt sp rootStack` (`262144` B), keeping all outer theorem conclusions identical to
`M2TopPlaced`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedSat

noncomputable section

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (IdentityKey PublicKey SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (
  LibsignalPlacement lsBlackBoxU8Sym lsLogFilterAddr ls_subroutine_ok_of_block lsmpl lsρ
  withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc rustDeallocSpec)
open CryptoVerification.LibsignalTripleRatchet (publicKeySerializeSpec rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  dropSessionStructureLocal2Spec
)
open CryptoVerification.LibsignalTripleRatchet.Getters (remoteIdentityOkAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost sessionStateAt)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost apiDecResultAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved PanicOomProp SepWPp.bind_sepWPp_steps_frame SepWPp.weaken_frame
  decryptPrekeySavedRegsAt processPrekeyActive10At
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  entails_replace_sub eq_of_sep_emp
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open scoped CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  SessionExtraRel stackAt_split_of_le
)
open scoped CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  bind_sepWP_lscro_steps_m2_placed
  call_lscro_nopanic_m2_placed chunks32At coro_2a0_split32_placed
  memRegion_32_eq_chunks32_placed memRegion_34_split_24_10_placed memRegion_34_split_32_2_placed
  memRegion_920_6_join_placed memRegion_920_6_split_placed memRegion_a90_48_join_10_38_placed
  memRegion_a90_48_split_10_38_placed p2_seg_094c_ok_placed_wp p2_seg_1064_none_placed_wp
  p2_seg_1064_some_load_placed_wp p2_seg_1094_some_store_placed_wp p2_seg_10cc_mismatch_placed_wp
  pack16LE pack32LE pack64LE panicOomProp_frame_placed pointsToBytes_32_eq_chunks32
  prevSessionsEmptyAt processPrekeyActive10At_eq publicKey_beq_false_of_ne_placed
  rem34_bytes_entails_memRegion34_placed remoteIdentityOkAt_none_eq_placed
  remoteIdentityOkAt_some_eq_placed stageP2MatchedMatchPrePlaced stageP2MatchedMismatchPostPlaced
  stageP2MatchedPrePlaced stageP2_matched_mismatch_tail_placed
  stageP2_matched_ok_10cc_to_1778_placed strToOwnedLocal2Spec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (
  blackBoxSpecSat publicKeyEqMemSpec16 publicKey_eq_mem_placed_ok_16_sat
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2BridgePlacedSat (
  stageP2_matched_0868_to_094c_placed_sat
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

private theorem bind_sepWPp_steps_frame_panicF_placed [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P F P_stage P_stage_post F_inner : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf (Pf ∗ F))
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = (P_stage ∗ F) ∗ F_inner)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post ∗ (F_inner ∗ F)) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hP_re : P = P_stage ∗ (F_inner ∗ F) := by
    rw [hP]; sep_ac_rfl
  rw [hP_re, sepConj_assoc P_stage (F_inner ∗ F) R] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hp, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage ((F_inner ∗ F) ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post ∗ (F_inner ∗ F)) ∗ R := by
      rw [sepConj_assoc P_stage_post (F_inner ∗ F) R]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc P_m (F_inner ∗ F) R, ← sepConj_assoc P_m F_inner F] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hp, (P_m ∗ F_inner) ∗ F, hmm,
      hpan sm (P_m ∗ F_inner) (panicOomProp_frame_placed F_inner hpanm)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1200000 in
/-- `HookSat`-backed sibling of `M2OkPlaced.stageP2_matched_094c_some_to_10cc_placed`. -/
theorem stageP2_matched_094c_some_to_10cc_placed_sat [LibsignalPlacement]
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
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
  have hroot_le : rootStack ≤ 2 ^ 64 := Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  let bs := ik.publicKey.bytes.toList
  have hbs_len : bs.length = 32 := ik.publicKey.bytes.property
  let w0 := pack32LE (bs.take 4)
  let h1 := pack16LE ((bs.drop 4).take 2)
  let q2 := pack64LE ((bs.drop 6).take 8)
  let q3 := pack64LE ((bs.drop 14).take 8)
  let q4 := pack64LE ((bs.drop 22).take 8)
  let h5 := pack16LE (bs.drop 30)
  conv => arg 4; rw [remoteIdentityOkAt_some_eq_placed sp ik,
      show ik.publicKey.bytes.toList = bs from rfl,
      pointsToBytes_32_eq_chunks32 (sp + 0x3e2#64) bs hbs_len,
      memRegion_920_6_split_placed sp, memRegion_a90_48_split_10_38_placed sp]
  dsimp only [chunks32At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  sep_norm
  refine SepWPp.exists_elim fun u_920 => SepWPp.exists_elim fun u_924 =>
    SepWPp.exists_elim fun u_a90 => SepWPp.exists_elim fun u_a98 => ?_
  have h094c := p2_seg_094c_ok_placed_wp ext s coroPtr outPtr hpc hrun hsp_align hx19
  rw [hsp_eq] at h094c
  refine bind_sepWP_lscro_steps_m2_placed hcro h094c (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx19_1, hx21_1, _, _, hx25_1, hx26_1, _, hx28_1, hx29_1, _⟩
  have hsp1 : s1.sp = sp := hsp1_s
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1, ← hsp_eq]; exact hsp_align
  have hx21_1' : s1.readReg64 .x21 = s1.sp + 0x370#64 := by rw [hsp1]; exact hx21_1.trans hx21
  have h1064 := p2_seg_1064_some_load_placed_wp ext s1 coroPtr q2 q3 q4 u_a90
    w0 u_920 h1 h5 u_924 u_a98 hpc1 hrun1 hsp1_align hx19_1 hx21_1'
  rw [hsp1] at h1064
  refine bind_sepWP_lscro_steps_m2_placed hcro1 h1064 (by sep_focus)
    fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, hvregs2, hx8_2, hx9_2, hx19_2, hx21_2, hx25_2, hx26_2, _, hx28_2, hx29_2, _⟩
  have hsp2 : s2.sp = sp := hsp2_1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  have hx21_2' : s2.readReg64 .x21 = s2.sp + 0x370#64 := by rw [hsp2]; exact hx21_2
  have hrepack34 :
      ((sp + 0x3e0#64) ↦₈ 0#8) ∗ ((sp + 0x3e1#64) ↦₈ 1#8) ∗
        chunks32At (sp + 0x3e2#64) w0 h1 q2 q3 q4 h5 ⊢
        memRegion (sp + 0x3e0#64) 32 ∗ memRegion (sp + 0x400#64) 2 := by
    rw [← memRegion_34_split_32_2_placed sp]
    exact rem34_bytes_entails_memRegion34_placed sp 0#8 1#8 w0 h1 q2 q3 q4 h5
  dsimp only [chunks32At] at hrepack34
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack34
  refine SepWPp.weaken_frame hrepack34 (by sep_focus) ?_
  conv => arg 4; rw [memRegion_32_eq_chunks32_placed (sp + 0x3e0#64)]
  dsimp only [chunks32At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  sep_norm
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
    SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun d5 => ?_
  have h1094 := p2_seg_1094_some_store_placed_wp ext s2 coroPtr msgPtr q2 q3 q4 d2 d3 d4
    w0 d0 h1 h5 d1 d5 hpc2 hrun2 hsp2_align hx8_2 hx9_2 hx19_2 hx21_2'
  rw [hsp2] at h1094
  refine bind_sepWP_lscro_steps_m2_placed hcro2 h1094 (by sep_focus)
    fun s3 _ hpc3 hrun3 hcro3 hregs3 => ?_
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
      (publicKey_eq_mem_placed_ok_16_sat h_bb)
      (by decide))
  refine call_lscro_nopanic_m2_placed
    (spec := publicKeyEqMemSpec16)
    (x := (msgPtr + 0xc8#64, remIdKey.publicKey, sp + 0x3e0#64, ik.publicKey, sp))
    (T := ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
      ((sp + 0x3e0#64) ↦ₛ ik.publicKey.bytes.toList) ∗
      memRegion (sp - 80#64) 80)
    hcro3 hpkeq hpc3 hrun3 hsp3_al hx30_3
    (by dsimp only [publicKeyEqMemSpec16])
    (And.intro hx0_3 (And.intro hx1_3 hsp3)) (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  dsimp only [publicKeyEqMemSpec16]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_4, htr4_3⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_pkEq16_mem_placed sp hroot_le).symm) (by sep_focus) ?_
  rcases hcs4 with ⟨hx19_cs4, _, _, _, _, _, hx25_cs4, hx26_cs4, _, hx28_cs4, hx29_cs4, hvregs_cs4⟩
  refine SepWPp.done hpc4 hrun4 ⟨?_, hsp4_3.trans hsp3,
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
    rw [memRegion_34_split_32_2_placed sp]
    refine sepConj_mono_left ?_
    simpa only [hbs_len] using ProofLib.pointsToBytes_entails_memRegion (sp + 0x3e0#64) bs
  refine Entails.trans (entails_replace_sub hbs34 (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub (memRegion_920_6_join_placed sp w0 h1) (by sep_focus) rfl) ?_
  exact entails_replace_sub (memRegion_a90_48_join_10_38_placed sp q4 h5) (by sep_focus)
    (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- `HookSat`-backed sibling of `M2OkPlaced.stageP2_matched_094c_match_placed`. -/
theorem stageP2_matched_094c_match_placed_sat [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {s0 : State}
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
        sf.sp = sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x27 = sp + 0x370#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      (PanicOomProp s0) := by
  conv =>
    arg 4
    rw [hrem_eq]
  have hchk := stageP2_matched_094c_some_to_10cc_placed_sat
    (Qp := PanicOomProp s0) h_bb s sp coroPtr outPtr msgPtr
    remIdKey remIdKey hcro hsp_eq hsp_root hpc hrun hsp_align hx19 hx21 hx25 hx28
  refine SepWPp.bind_sepWPp_steps_frame hchk (by sep_focus)
    fun s1 _ hpc1 hrun1 ⟨hsp1, htr1, hx0_1, hx19_1, _, hx26_1, _, hx29_1, hvregs1, hcro1⟩ => ?_
  have hx0_one : s1.readReg64 .x0 = 1#64 := by
    simpa [beq_self_eq_true] using hx0_1
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1, ← hsp_eq]; exact hsp_align
  have htail := stageP2_matched_ok_10cc_to_1778_placed (A := A) (ext := ext)
    (Qp := PanicOomProp s0) s1 sp coroPtr outPtr msgPtr
    remoteAddrPtr localAddrPtr v_330 v_388 u_80 u_88 u_90 (coroPtr + 0x4f2#64) u_a8 u_b0 v_d0
    u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 u_2a8 u_b8 msgVerByte b_4f2 b_390 b_3ac
    recG recSt hcro1 hsp1 hsp_root hpc1 hrun1 hsp1_align hx0_one hx19_1 hx26_1
  refine SepWPp.bind_sepWPp_steps_frame htail (by sep_focus)
    fun sf _ hpcf hrunf ⟨hspf, htrf, hx19_f, hx27_f, hx29_f, hvregsf_1, hcrof⟩ => ?_
  refine SepWPp.done hpcf hrunf
    ⟨?_, hspf, htrf.trans htr1, hx19_f, hx27_f, hx29_f.trans hx29_1, hvregsf_1.trans hvregs1, hcrof⟩
  sep_norm
  refine Entails.sepExists_elim fun opkHi => Entails.sepExists_right opkHi ?_
  refine Entails.sepExists_elim fun kyberPacked => Entails.sepExists_right kyberPacked ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- `HookSat`-backed sibling of `M2TopPlaced.stageP2_matched_094c_mismatch_placed`. -/
theorem stageP2_matched_094c_mismatch_placed_sat [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (h_bb : HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State)
    (sp coroPtr outPtr msgPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (remIdKey : IdentityKey)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hrem_ne : recSt.remoteIdentity ≠ some remIdKey)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
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
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
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
       A.pool ∗
       stackAt sp rootStack)
      (fun sf P_f =>
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
          apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp rootStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      (PanicOomProp s0) := by
  cases hrem : recSt.remoteIdentity with
  | none =>
    conv =>
      arg 4
      rw [remoteIdentityOkAt_none_eq_placed sp, memRegion_32_eq_chunks32_placed (sp + 0x3e2#64),
          memRegion_920_6_split_placed sp, memRegion_a90_48_split_10_38_placed sp]
    dsimp only [chunks32At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    sep_norm
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun h1 =>
      SepWPp.exists_elim fun q2 => SepWPp.exists_elim fun q3 =>
      SepWPp.exists_elim fun q4 => SepWPp.exists_elim fun h5 =>
      SepWPp.exists_elim fun u_920 => SepWPp.exists_elim fun u_924 =>
      SepWPp.exists_elim fun u_a90 => SepWPp.exists_elim fun u_a98 => ?_
    have h094c := p2_seg_094c_ok_placed_wp ext s coroPtr outPtr hpc hrun hsp_align hx19
    rw [hsp_eq] at h094c
    refine bind_sepWP_lscro_steps_m2_placed hcro h094c (by sep_focus)
      fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx19_1, hx21_1, _, _, hx25_1, hx26_1, _, hx28_1, _, _⟩
    have hsp1 : s1.sp = sp := hsp1_s
    have hx21_1' : s1.readReg64 .x21 = s1.sp + 0x370#64 := by rw [hsp1]; exact hx21_1.trans hx21
    have h1064 := p2_seg_1064_none_placed_wp ext s1 coroPtr q2 q3 q4 u_a90
      w0 u_920 h1 h5 u_924 u_a98 hpc1 hrun1 (by rw [hsp1, ← hsp_eq]; exact hsp_align) hx19_1 hx21_1'
    rw [hsp1] at h1064
    refine bind_sepWP_lscro_steps_m2_placed hcro1 h1064 (by sep_focus)
      fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2_1, htr2_1, hvregs2, hx19_2, hx25_2, hx26_2, _, hx28_2, _, _⟩
    have hsp2 : s2.sp = sp := hsp2_1
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    have htr2_s : s2.trace = s.trace := htr2_1.trans htr1_s
    have htr2 : s0.trace <+: s2.trace := by rw [htr2_s]; exact htr
    have hx25_2' : s2.readReg64 .x25 = sp + 0x210#64 := hx25_2.trans (hx25_1.trans hx25)
    have hx26_2' : s2.readReg64 .x26 = outPtr := hx26_2.trans hx26_1
    have hx28_2' : s2.readReg64 .x28 = sp + 0xa90#64 := hx28_2.trans (hx28_1.trans hx28)
    have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      congrArg VRegFile.calleeSaved (hvregs2.trans hvregs1)
    have hrem34 := rem34_bytes_entails_memRegion34_placed sp 0#8 0#8 w0 h1 q2 q3 q4 h5
    dsimp only [chunks32At] at hrem34
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrem34
    refine SepWPp.weaken_frame hrem34 (by sep_focus) ?_
    refine SepWPp.weaken_frame (memRegion_920_6_join_placed sp w0 h1) (by sep_focus) ?_
    refine SepWPp.weaken_frame (memRegion_a90_48_join_10_38_placed sp q4 h5) (by sep_focus) ?_
    conv => arg 4; rw [memRegion_34_split_24_10_placed sp]
    simp only [sepConj_assoc]
    have htail := stageP2_matched_mismatch_tail_placed hto hdealloc hdrop_ss s0 s2 sp coroPtr outPtr
      u_a8 u_d0 b_4f2 b_390 b_2c0 g recG recSt hcro2 htr2 hsp2 hsp_root hpc2 hrun2
      hsp2_align hx19_2 hx25_2' hx26_2' hx28_2'
    refine SepWPp.bind_sepWPp_steps_frame htail (by sep_focus)
      fun sf _ hpcf hrunf ⟨hspf, htrf_2, hcsf, hvregsf_2, hcrof⟩ => ?_
    refine SepWPp.done hpcf hrunf
      ⟨?_, hspf, htrf_2.trans htr2_s, hcsf, hvregsf_2.trans hvregs2_s, hcrof⟩
    have hjoin34 : memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 10 ⊢
        memRegion (sp + 0x3e0#64) 34 :=
      Entails.of_eq (memRegion_34_split_24_10_placed sp).symm
    exact entails_replace_sub hjoin34 (by sep_focus) (eq_of_sep_emp (by sep_focus))
  | some ik =>
    have hne_ik : some ik ≠ some remIdKey := by rw [← hrem]; exact hrem_ne
    have hchk := stageP2_matched_094c_some_to_10cc_placed_sat (Qp := PanicOomProp s0)
      h_bb s sp coroPtr outPtr msgPtr remIdKey ik hcro hsp_eq hsp_root hpc hrun hsp_align
      hx19 hx21 hx25 hx28
    refine SepWPp.bind_sepWPp_steps_frame hchk (by sep_focus)
      fun s1 _ hpc1 hrun1 ⟨hsp1, htr1_s, hx0_1, hx19_1, hx25_1, hx26_1, hx28_1, _, hvregs1, hcro1⟩ => ?_
    have hx0_zero : s1.readReg64 .x0 = 0#64 := by
      simpa [publicKey_beq_false_of_ne_placed hne_ik] using hx0_1
    have h10cc := p2_seg_10cc_mismatch_placed_wp ext s1 coroPtr hpc1 hrun1 hx0_zero hx19_1
    refine bind_sepWP_lscro_steps_m2_placed hcro1 h10cc (by sep_focus)
      fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2_1, htr2_1, hvregs2, hx19_2, hx25_2, hx26_2, _, hx28_2, _, _⟩
    have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    have htr2_s : s2.trace = s.trace := htr2_1.trans htr1_s
    have htr2 : s0.trace <+: s2.trace := by rw [htr2_s]; exact htr
    have hx25_2' : s2.readReg64 .x25 = sp + 0x210#64 := hx25_2.trans hx25_1
    have hx26_2' : s2.readReg64 .x26 = outPtr := hx26_2.trans hx26_1
    have hx28_2' : s2.readReg64 .x28 = sp + 0xa90#64 := hx28_2.trans hx28_1
    have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
      (congrArg VRegFile.calleeSaved hvregs2).trans hvregs1
    conv => arg 4; rw [memRegion_34_split_24_10_placed sp]
    simp only [sepConj_assoc]
    have htail := stageP2_matched_mismatch_tail_placed hto hdealloc hdrop_ss s0 s2 sp coroPtr outPtr
      u_a8 u_d0 b_4f2 b_390 b_2c0 g recG recSt hcro2 htr2 hsp2 hsp_root hpc2 hrun2
      hsp2_align hx19_2 hx25_2' hx26_2' hx28_2'
    refine SepWPp.bind_sepWPp_steps_frame htail (by sep_focus)
      fun sf _ hpcf hrunf ⟨hspf, htrf_2, hcsf, hvregsf_2, hcrof⟩ => ?_
    refine SepWPp.done hpcf hrunf
      ⟨?_, hspf, htrf_2.trans htr2_s, hcsf, hvregsf_2.trans hvregs2_s, hcrof⟩
    have hjoin34 : memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 10 ⊢
        memRegion (sp + 0x3e0#64) 34 :=
      Entails.of_eq (memRegion_34_split_24_10_placed sp).symm
    exact entails_replace_sub hjoin34 (by sep_focus) (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- `HookSat`-backed sibling of `M2TopPlaced.stageP2_matched_ok_framed_placed`. -/
theorem stageP2_matched_ok_framed_placed_sat [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (h_bb : HookSat (Rust.withPanics ext) lsBlackBoxU8Sym blackBoxSpecSat)
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State)
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
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
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
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf (Pf ∗ F))
    (hmismatch : sess.state.remoteIdentity ≠ some remIdKey →
      ∀ (sf : State) (Pf : SepProp),
        sf.pc = s0.readReg64 .x30 →
        sf.status = .Running →
        Steps (lsProg_518 (Rust.withPanics ext)) s sf →
        sf.sp = sp + 0xcd0#64 →
        sf.trace = s.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        LibsignalCodeRoLoaded lsmpl sf.mem →
        (Pf ⊢ stageP2MatchedMismatchPostPlaced A s0 sp coroPtr outPtr msgPtr
          remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
          kyberStorePtr kyberStoreVt v_330 v_388 u_80 u_88 u_90 u_b0
          u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
          u_2a8 u_b8 outerVerByte innerVerByte b_3ac baseKey remIdKey F) →
        Q sf Pf)
    (hmatch : sess.state.remoteIdentity = some remIdKey →
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
          (stageP2MatchedMatchPrePlaced A s0 sp coroPtr outPtr msgPtr
            remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt v_330 v_388 v_d0
            opkHi kyberPreKeyId signedPreKeyId outerVerByte innerVerByte b_2c0
            baseKey remIdKey g recG sess.state F)
          Q Qp) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stageP2MatchedPrePlaced A s0 sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
        v_330 v_388 u_80 u_88 u_90 u_a8 u_b0 v_d0
        u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
        u_2a8 u_b8 outerVerByte innerVerByte b_4f1 b_4f2 b_390 b_2c0 b_3ac
        baseKey remIdKey g r F)
      Q Qp := by
  dsimp only [stageP2MatchedPrePlaced, stageP2MatchedMismatchPostPlaced, stageP2MatchedMatchPrePlaced]
    at hmismatch hmatch ⊢
  have hpre := stageP2_matched_0868_to_094c_placed_sat hser hdealloc h_bb s0 s sp coroPtr msgPtr
    remoteAddrPtr localAddrPtr idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt outerVerByte b_4f1 baseKey
    g r sess hcur hver halice hcro htr hsp_eq hsp_root hpc hrun hsp_align
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28 hx29
  refine bind_sepWPp_steps_frame_panicF_placed hpan hpre (by sep_focus)
    fun sm hsteps01 hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hspm, htrm, hx19m, hx21m, hx25m, hx28m, hx29m, hvregsm, hcrom⟩
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by rw [hspm, ← hsp_eq]; exact hsp_align
  have htr0m : s0.trace <+: sm.trace := by rw [htrm]; exact htr
  sep_norm
  refine SepWPp.exists_elim fun recG => SepWPp.pure_elim fun ⟨hgc, hextra⟩ => ?_
  by_cases hrem : sess.state.remoteIdentity = some remIdKey
  · conv =>
      arg 4
      rw [processPrekeyActive10At_eq]
    simp only [sepConj_assoc]
    have hm := stageP2_matched_094c_match_placed_sat (A := A) (s0 := s0)
      h_bb sm sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388
      u_80 u_88 u_90 u_a8 u_b0 v_d0 u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
      u_2a8 u_b8 innerVerByte b_4f2 b_390 b_3ac remIdKey recG sess.state hrem
      hcrom hspm hsp_root hpcm hrunm hspm_align hx19m hx21m hx25m hx28m
    refine bind_sepWPp_steps_frame_panicF_placed hpan hm (by sep_focus)
      fun s2 hsteps12 hpc2 hrun2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx27_2, hx29_2, hvregs2, hcro2⟩
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
    sep_norm
    refine SepWPp.exists_elim fun opkHi => SepWPp.exists_elim fun kyberPacked => ?_
    have hgoal := hmatch hrem s2 recG opkHi
      (kyberPacked.extractLsb' 0 32) (kyberPacked.extractLsb' 32 32)
      hgc hextra (hsteps01.trans hsteps12) hpc2 hrun2 hsp2 hsp2_align
      (htr2.trans htrm) hx19_2 hx27_2 (hx29_2.trans hx29m) (hvregs2.trans hvregsm) hcro2
    refine fun R hmR hL => hgoal R (Arm64.Satisfies.mono (sepConj_mono_left ?_) hmR) hL
    rw [coro_2a0_split32_placed coroPtr kyberPacked, processPrekeyActive10At_eq]
    simp only [sepConj_assoc]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
  · conv =>
      arg 4
      rw [processPrekeyActive10At_eq]
    simp only [sepConj_assoc]
    have hmm := stageP2_matched_094c_mismatch_placed_sat hto hdealloc h_bb hdrop_ss s0 sm
      sp coroPtr outPtr msgPtr u_a8 v_d0 b_4f2 b_390 b_2c0 remIdKey g recG sess.state
      hrem hcrom htr0m hspm hsp_root hpcm hrunm hspm_align hx19m hx21m hx25m hx28m
    refine bind_sepWPp_steps_frame_panicF_placed hpan hmm (by sep_focus)
      fun sf hsteps1f hpcf hrunf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hcsf, hvregsf, hcrof⟩
    refine SepWPp.done hpcf hrunf (hmismatch hrem sf _ hpcf hrunf
      (hsteps01.trans hsteps1f) hspf (htrf.trans htrm) hcsf (hvregsf.trans hvregsm) hcrof ?_)
    rw [processPrekeyActive10At_eq]
    simp only [sepConj_assoc]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TopPlacedSat
