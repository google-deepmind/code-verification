/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedASat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain

/-!
# `HookSat`-backed `black_box` Sibling of `VerifySignaturePlacedA` Segments 2 and 3a

Proves `verifySig_seg2_1569_placed_sat`, `verifySig_seg2_33_placed_sat`, and
`verifySig_seg3a_placed_sat` for unmutated Block `204` (`verify_signature_for_multipart_message`)
under `[LibsignalPlacement]` and `VerifySignaturePlacedHooks'Sat P H`, completing the Segment 2–3
`HookSat` siblings alongside `VerifySignaturePlacedASat.verifySig_seg3b_placed_sat`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped CryptoVerification.E2E.Pqxdh.Shared

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedA2Sat

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPC_204 blkPl_204 ls_hook_ok_any)
open CryptoVerification.E2E.Pqxdh.Shared
  (and64_mask255_ite_1_0 blockBuf_tail32_pack blockBuf_tail32_unpack bv_add_neg64 bv_sub_sub_lit
   bytesToBv8 bytesToBv8_append cell_split7 cells_10_merge cells_16_merge csinc_eq_zero32_ite_1_0
   exists_pad97_cells exists_unpack64_of_length_64 exists_unpack64_revWords64_of_length_64 first7
   first7_pack fitBv8 fitBv8_64_sha512CompressOutBytes pqxdhHookStack
   readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre revWords64 revWords64_length sha512CompressOutBytes
   sha512CompressOutBytes_length sp_setMem_setPC_pre sp_setPC_pre)
open LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedASat
  (VerifySignaturePlacedHooks'Sat)
open SignalPqxdh (Bytes Primitives encodeBitLen128BE encodeBitLen64BE)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64

private theorem calleeSavedVRegs_setPC_pre_placed (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := calleeSavedVRegs_setPC s pc

private theorem calleeSavedVRegs_setMem_setPC_pre_placed (s : State) (m : Memory) (pc : BitVec 64) :
    calleeSavedVRegs ((s.setMem m).setPC pc) = calleeSavedVRegs s := by
  rw [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem]

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  calleeSavedVRegs_setPC_pre_placed calleeSavedVRegs_setMem_setPC_pre_placed

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  and64_mask255_ite_1_0 csinc_eq_zero32_ite_1_0

set_option maxHeartbeats 1600000 in
public theorem verifySig_seg2_1569_placed_sat [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hH : VerifySignaturePlacedHooks'Sat P H)
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 1569) (_hst0 : st0.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 320#64)
    (hsp : s.sp = fsp) (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = 1#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H)
      ((blkPl_204).base + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (m.drop 1472)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗
          ((fsp + 688#64) ↦ₛ bytesToBv8
            (sha512CompressOutBytes P (sha512CompressOutBytes P st0 (pre64 ++ m.take 64))
              ((m.drop 64).take 1408))) ∗
          ((fsp + 752#64) ↦₆₄ 12#64) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmemcpy := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.memcpy
  have hsha := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.sha512Compress
  clear hH
  have hlen_m64_bv : (bytesToBv8 (m.take 64)).length = 64 := by simp [bytesToBv8, hm]
  have hlen_m1408 : ((m.drop 64).take 1408).length = 128 * 11 := by simp [hm]
  have hlen_m1408_bv : (bytesToBv8 ((m.drop 64).take 1408)).length = 1408 := by
    simp [bytesToBv8, hm]
  have hlen_m97_bv : (bytesToBv8 (m.drop 1472)).length = 97 := by simp [bytesToBv8, hm]
  have hlen_pre_bv : (bytesToBv8 pre64).length = 64 := by simp [bytesToBv8, hpre64]
  have hlen_blk0 : (pre64 ++ m.take 64).length = 128 * 1 := by simp [hpre64, hm]
  have hlen_blk0_bv : (bytesToBv8 (pre64 ++ m.take 64)).length = 128 := by
    simp [bytesToBv8, hpre64, hm]
  have hst1_len : (sha512CompressOutBytes P st0 (pre64 ++ m.take 64)).length = 64 :=
    sha512CompressOutBytes_length P _ _
  have hm_split : msgPtr ↦ₛ bytesToBv8 m =
      ((msgPtr ↦ₛ bytesToBv8 (m.take 64)) ∗
       ((msgPtr + 64#64) ↦ₛ bytesToBv8 ((m.drop 64).take 1408)) ∗
       ((msgPtr + 1472#64) ↦ₛ bytesToBv8 (m.drop 1472))) := by
    have h1 : m = m.take 64 ++ ((m.drop 64).take 1408 ++ m.drop 1472) := by
      have ha : (m.drop 64).take 1408 ++ m.drop 1472 = m.drop 64 := by
        rw [show (1472 : Nat) = 64 + 1408 from rfl, ← List.drop_drop, List.take_append_drop]
      rw [ha, List.take_append_drop]
    conv => lhs; rw [h1, bytesToBv8_append, bytesToBv8_append]
    rw [pointsToBytes_append, pointsToBytes_append, hlen_m64_bv, hlen_m1408_bv]
    have h64 : BitVec.ofNat 64 64 = 64#64 := rfl
    have h1408 : 64#64 + BitVec.ofNat 64 1408 = 1472#64 := rfl
    rw [h64, BitVec.add_assoc, h1408]
  have hbuf64_in : memRegion (fsp + 624#64) 63 ∗ ((fsp + 687#64) ↦₈ 64#8) ⊢
      memRegion (fsp + 624#64) (bytesToBv8 (m.take 64)).length := by
    rw [hlen_m64_bv, ProofLib.memRegion_split' (b := fsp + 624#64) (n := 63) (k := 1)
      (b' := fsp + 687#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
    exact sepConj_mono_right (Entails.sepExists_intro 64#8)
  have hbuf128_weaken : ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m.take 64)) ⊢
      memRegion (fsp + 560#64) (bytesToBv8 (m.drop 1472)).length ∗ memRegion (fsp + 657#64) 30 ∗
      (∃∗ b687 : BitVec 8, (fsp + 687#64) ↦₈ b687) := by
    refine Entails.trans (Q := memRegion (fsp + 560#64) 128) ?_ (Entails.of_eq ?_)
    · rw [← hlen_blk0_bv]; exact pointsToBytes_entails_memRegion _ _
    · rw [hlen_m97_bv, ProofLib.memRegion_split' (b := fsp + 560#64) (n := 97) (k := 31)
        (b' := fsp + 657#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 657#64) (n := 30) (k := 1)
        (b' := fsp + 687#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hm_split) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf64_in) (by sep_frame)
  wp_call hmemcpy ⟨fsp + 624#64, msgPtr, bytesToBv8 (m.take 64)⟩
  have hmerge128 :
      ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ ((fsp + 624#64) ↦ₛ bytesToBv8 (m.take 64)) =
        ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m.take 64)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hlen_pre_bv, BitVec.add_assoc]
    rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge128) (by sep_frame)
  wp_steps
  wp_call hsha ⟨fsp + 688#64, st0, fsp + 560#64, pre64 ++ m.take 64, 1⟩
  rw [fitBv8_64_sha512CompressOutBytes]
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf128_weaken) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  wp_steps
  wp_call hsha ⟨fsp + 688#64, sha512CompressOutBytes P st0 (pre64 ++ m.take 64), msgPtr + 64#64,
    (m.drop 64).take 1408, 11⟩
  rw [fitBv8_64_sha512CompressOutBytes]
  wp_steps
  wp_call hmemcpy ⟨fsp + 560#64, msgPtr + 1472#64, bytesToBv8 (m.drop 1472)⟩
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hm_split.symm) (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by rw [hsp_sf_1, hsp_sf, hsp]; sep_ac_rfl), by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal⟩

set_option maxHeartbeats 1600000 in
public theorem verifySig_seg2_33_placed_sat [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hH : VerifySignaturePlacedHooks'Sat P H)
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 33) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 320#64)
    (hsp : s.sp = fsp) (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = 1#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H)
      ((blkPl_204).base + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗
          ((fsp + 752#64) ↦₆₄ 0#64) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmemcpy := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.memcpy
  clear hH
  have hlen_pre_bv : (bytesToBv8 pre64).length = 64 := by simp [bytesToBv8, hpre64]
  have hlen_m_bv : (bytesToBv8 m).length = 33 := by simp [bytesToBv8, hm]
  have hbuf63_split : memRegion (fsp + 624#64) 63 =
      memRegion (fsp + 624#64) (bytesToBv8 m).length ∗ memRegion (fsp + 657#64) 30 := by
    rw [hlen_m_bv]
    exact ProofLib.memRegion_split' (b := fsp + 624#64) (n := 33) (k := 30) (b' := fsp + 657#64)
      rfl (by bv_omega) (by decide)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hbuf63_split) (by sep_frame)
  wp_steps
  wp_call hmemcpy ⟨fsp + 624#64, msgPtr, bytesToBv8 m⟩
  have hmerge97 :
      ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ ((fsp + 624#64) ↦ₛ bytesToBv8 m) =
        ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hlen_pre_bv, BitVec.add_assoc]
    rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge97) (by sep_frame)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by sep_ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 2400000 in
/-- Segment 3a of Block `204` (`+548 .. +992`, SHA-512 final padding & `from_bytes_mod_order_wide`)
    under `[LibsignalPlacement]` and `VerifySignaturePlacedHooks'Sat P H`. -/
public theorem verifySig_seg3a_placed_sat [LibsignalPlacement]
    (P : Primitives) (H : LibsignalHooks) (hH : VerifySignaturePlacedHooks'Sat P H)
    (s : State) (fsp : BitVec 64) (tail97 st : Bytes) (blkCnt : BitVec 64) (L : Nat)
    (Frame : SepProp) (htail97 : tail97.length = 97) (hst : st.length = 64)
    (hblkL : (blkCnt = 0#64 ∧ L = 97) ∨ (blkCnt = 12#64 ∧ L = 1633))
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 548#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H)
      ((blkPl_204).base + 992#64) s
      (((fsp + 560#64) ↦ₛ bytesToBv8 tail97) ∗ memRegion (fsp + 657#64) 30 ∗
       ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st) ∗ ((fsp + 752#64) ↦₆₄ blkCnt) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ memRegion (fsp + 768#64) 32 ∗ cells (fsp + 800#64) 16 ∗
       cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ cells (fsp + 560#64) 16 ∗ cells (fsp + 688#64) 10 ∗
          ((fsp + 768#64) ↦ₛ fitBv8 32 (P.scalarFromWide (revWords64 (sha512CompressOutBytes P st
              (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L))))) ∗
          cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 992#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = fsp + 800#64 ∧ sm.readReg64 (.gpr 29#5) = fsp + 1152#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmemset := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.memset
  have hsha := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.sha512Compress
  have hwide := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hH.scalarWide
  clear hH
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, _p12, _p13, hp1, hp2, hp3⟩ :=
    exists_pad97_cells htail97
  have hst_bv : (bytesToBv8 st).length = 64 := by simp [bytesToBv8, hst]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hw_st⟩ := exists_unpack64_of_length_64 hst_bv
  cells_pre_unfold_fast
  wp_extract_exists
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hp1 (fsp + 560#64))) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hw_st (fsp + 688#64))) (by sep_frame)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply ProofLib.SepWP.replace_pre
    (hPQ := blockBuf_tail32_pack (fsp + 656#64) ((bytesToBv8 tail97).getD 96 0#8) 97#8)
    (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_left; intro b12
  apply SepWP.exists_left; intro b13
  apply SepWP.exists_left; intro b14
  apply SepWP.exists_left; intro b15
  apply SepWP.pure_elim; rintro ⟨hb12, hb15⟩
  wp_steps
  have hsp7 : ((fsp + 920#64) ↦₆₄ b15) =
      (((fsp + 920#64) ↦ₛ first7 b15) ∗ ((fsp + 927#64) ↦₈ 97#8)) := by
    rw [cell_split7 (fsp + 920#64) b15, hb15, BitVec.add_assoc]; rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsp7) (by sep_frame)
  wp_steps
  have hunpack32 := blockBuf_tail32_unpack (fsp + 896#64) b12 b13 b14 b15
    ((bytesToBv8 tail97).getD 96 0#8) 97#8 hb12
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hunpack32
  apply ProofLib.SepWP.replace_pre (hPQ := hunpack32) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  wp_steps
  wp_call hmemset (fsp + 898#64, 0#8, 30)
  have hp2_896 := hp2 (fsp + 896#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp2_896
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp2_896) (by sep_frame)
  wp_steps
  have hbithi : rev64 (BitVec.truncate 64 ((0#64 ++ blkCnt) >>> 54)) = 0#64 := by
    rcases hblkL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hbitlo : rev64 (blkCnt <<< 10 ||| 776#64) = rev64 (BitVec.ofNat 64 (8 * L)) := by
    rcases hblkL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hL_or : L = 97 ∨ L = 1633 := hblkL.imp And.right And.right
  have hp3_1008 := hp3 (fsp + 1008#64) hL_or
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp3_1008
  have hw_st_928 := (hw_st (fsp + 928#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hw_st_928
  wp_simp_pre_fast [hbithi, hbitlo]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp3_1008) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hw_st_928) (by sep_frame)
  have hpad_len :
      (tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L)).length = 128 := by
    simp [encodeBitLen128BE, encodeBitLen64BE, htail97]
  wp_call hsha ⟨fsp + 928#64, st, fsp + 1008#64, tail97 ++ [0x80] ++ List.replicate 14 0 ++
    encodeBitLen128BE L, 1⟩
  have hpad_norm :
      tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L) =
        tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L := by
    simp [List.append_assoc]
  wp_simp_pre_fast [fitBv8_64_sha512CompressOutBytes, hpad_norm]
  have hst_out_len :
      (sha512CompressOutBytes P st
        (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L)).length = 64 :=
    sha512CompressOutBytes_length P _ _
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, hu_st, hu_rev⟩ :=
    exists_unpack64_revWords64_of_length_64 hst_out_len
  have hu_st_928 := hu_st (fsp + 928#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu_st_928
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_st_928) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp3_1008.symm) (by sep_frame)
  have hsp7_920 := cell_split7 (fsp + 920#64) (rev64 (BitVec.ofNat 64 (8 * L)))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsp7_920
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsp7_920) (by sep_frame)
  wp_steps
  have hpk7_920 := first7_pack (fsp + 920#64) (rev64 (BitVec.ofNat 64 (8 * L))) 0#8
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpk7_920
  apply ProofLib.SepWP.replace_pre (hPQ := hpk7_920) (by sep_frame)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro _
  wp_steps
  have hu_rev_1008 := (hu_rev (fsp + 1008#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu_rev_1008
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_rev_1008) (by sep_frame)
  have hrev_len :
      (revWords64 (sha512CompressOutBytes P st
        (tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L)))).length = 64 :=
    revWords64_length (sha512CompressOutBytes_length P _ _)
  wp_call hwide ⟨fsp + 1008#64, revWords64 (sha512CompressOutBytes P st (tail97 ++ [0x80] ++
    List.replicate 14 0 ++ encodeBitLen128BE L)), fsp + 768#64⟩
  wp_simp_pre_fast [hpad_norm]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_rev_1008.symm) (by sep_frame)
  have hm560 := cells_16_merge (fsp + 560#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm560
  apply ProofLib.SepWP.replace_pre (hPQ := hm560) (by sep_frame)
  have hm688 := cells_10_merge (fsp + 688#64) w0 w1 w2 w3 w4 w5 w6 w7 blkCnt 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm688
  apply ProofLib.SepWP.replace_pre (hPQ := hm688) (by sep_frame)
  have hm800 := cells_16_merge (fsp + 800#64)
    0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm800
  apply ProofLib.SepWP.replace_pre (hPQ := hm800) (by sep_frame)
  have hm928 := cells_10_merge (fsp + 928#64) u0 u1 u2 u3 u4 u5 u6 u7 blkCnt 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm928
  apply ProofLib.SepWP.replace_pre (hPQ := hm928) (by sep_frame)
  have hm1008 := cells_16_merge (fsp + 1008#64)
    (rev64 u0) (rev64 u1) (rev64 u2) (rev64 u3) (rev64 u4) (rev64 u5) (rev64 u6) (rev64 u7)
    0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1008
  apply ProofLib.SepWP.replace_pre (hPQ := hm1008) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_1, hsp_sf, hsp]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by sep_ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

end LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedA2Sat
