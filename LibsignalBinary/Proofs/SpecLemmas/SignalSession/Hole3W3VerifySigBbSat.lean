/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import ProofLib.SepLogic.HeapIntro

/-!
# `HookOk` Elimination Helper for `blackBoxSpecSat` (`Hole3W3VerifySigBbSat`)

Provides `hookOk_blackBoxSpecSat_elim`, eliminating `HookOk f blackBoxSpecSat` on any `.Running`
state `s` with `s.spAligned = true` and `s.mem.RW (s.sp - 16#64) 16` into concrete state-level
postconditions (`KeepsFrozen`, `symtab`, `Returned`, `CallingConventionPreserved`, `VmPreserved`,
`x0 = (v.setWidth 8).zeroExtend 64`, `trace`, and `S2Frame s.mem (f s).mem [(s.sp - 16#64, 16)]`).

Used by `Hole3W3VerifySigAux` (`shadowBlackBox`, `hookOk_shadowBlackBox`, and
`shadowVsigHooks_findSome?_active`) so `w3m_verifySignature_vm_ok` discharges `lsBlackBoxU8Sym`
from `HookSat H lsBlackBoxU8Sym blackBoxSpecSat` without requiring `H lsBlackBoxU8Sym = some blackBoxHook`
or any extra `GhostRowSpecOk` field.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3VerifySigBbSat

open Arm64 ProofLib
open CryptoVerification.LibsignalTripleRatchet (blackBoxSpec withStack)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (S2Frame disjoint_fullComplementHeap fullComplementHeap matches_fullComplementHeap)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpec16 blackBoxSpecSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (isBlock_one_s2frame)

/-- Execute a `HookOk f blackBoxSpecSat` hook on a state `s` with `s.mem.RW (s.sp - 16#64) 16`,
yielding `KeepsFrozen`, `symtab`, `Returned`, `CallingConventionPreserved`, `VmPreserved`,
`s'.readReg64 .x0 = (v.setWidth 8).zeroExtend 64`, `s'.trace = s.trace`, and
`S2Frame s.mem s'.mem [(s.sp - 16#64, 16)]`. -/
public theorem hookOk_blackBoxSpecSat_elim {f : State → State}
    (hf : HookOk f blackBoxSpecSat)
    {s : State} {v : BitVec 64}
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = v)
    (hsp_al : s.spAligned = true)
    (hrw : s.mem.RW (s.sp - 16#64) 16) :
    let s' := f s
    s.mem.KeepsFrozen s'.mem ∧
    s'.symtab = s.symtab ∧
    Returned s s' ∧
    CallingConventionPreserved s s' ∧
    VmPreserved s s' ∧
    s'.readReg64 .x0 = (v.setWidth 8).zeroExtend 64 ∧
    s'.trace = s.trace ∧
    S2Frame s.mem s'.mem [(s.sp - 16#64, 16)] := by
  let dst := s.sp - 16#64
  have hb_pre := IsBlock.memRegion dst 16
  let hP : Heap := regionHeap dst 16 s.mem
  have hpP : (memRegion dst 16) hP := (hb_pre.iff hP).mpr ⟨s.mem, trivial, rfl⟩
  have hmP : hP.Matches s.mem := IsBlock.regionHeap_matches dst 16 s.mem hrw
  let R_comp : SepProp := ⟨fun h => h = fullComplementHeap hP s.mem⟩
  have hsep_pre : s.mem ⊨ memRegion dst 16 ∗ R_comp :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hpre_full : s.mem ⊨ blackBoxSpecSat.pre v s ∗ R_comp := by
    dsimp only [blackBoxSpecSat, blackBoxSpec16, withVmPreserved, withStack, blackBoxSpec, stackAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, hsep_pre⟩
  obtain ⟨hkf, hsym, hout⟩ := hf v R_comp s hrun hpre_full hsp_al
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [blackBoxSpecSat, blackBoxSpec16, withVmPreserved, withStack, blackBoxSpec, stackAt]
      at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hvm, hpost1⟩ := hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost1
    obtain ⟨⟨hx0', htr'⟩, hsep_post⟩ := hpost1
    have hpost_R : (f s).mem ⊨ R_comp ∗ memRegion dst 16 := by
      rwa [sepConj_comm] at hsep_post
    have hm_post : (fullComplementHeap hP s.mem).Matches (f s).mem := by
      obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
      cases hR_hc'
      exact Heap.Matches.of_union_left hmatch
    have hs2 : S2Frame s.mem (f s).mem [(dst, 16)] :=
      isBlock_one_s2frame hb_pre hb_pre hpP hmP hsep_post hm_post
    exact ⟨hkf, hsym, hret, hcc, hvm, hx0', htr', hs2⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3VerifySigBbSat
