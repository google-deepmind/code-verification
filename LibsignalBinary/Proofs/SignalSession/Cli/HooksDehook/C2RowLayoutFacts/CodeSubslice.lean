/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Invariant -- proof-setup: allow-public-import

/-!
# Linear `Program` Byte-Subslice Check & `CodeLoaded` Bridge (`C2RowLayoutFacts.CodeSubslice`)

**Checked by Lean. Untrusted (`Role::Proof`).**

Single canonical definition site for `checkProgCodeSubslice`, shared by `C2Lib2RxSliceFacts` and all
per-row Cutover-2 (`C2`) RX code-slice discharges (`Time`, `TimeAddPanic`, `FromUtf8Row`, and the
`RowCommon` rows):
- `checkProgCodeSubslice rxProg subProg` performs a single linear `O(off + subProg.code.length)`
  byte-subslice comparison `(rxProg.code.drop off).take subProg.code.length` together with 4-byte
  alignment and `2 ^ 64` no-wrap checks.
- `rxSubslice_of_checkProgCodeSubslice` extracts the alignment, no-wrap, and indexed byte-equality
  bundle consumed by `Lib2LayoutFacts.f3CodeInv_rxWords_codeLoaded_strip`.
- `codeLoaded_of_checkProgCodeSubslice` derives `subProg.CodeLoaded m` directly from
  `rxProg.CodeLoaded m` and `checkProgCodeSubslice rxProg subProg = true`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice

open Arm64 ProofLib

/-- Linear `O(off + subProg.code.length)` decidable byte-subslice witness certifying that
    `subProg.base` is 4-byte aligned, `[subProg.base, subProg.base + subProg.code.length)` does not
    wrap `2 ^ 64`, and `subProg.code` matches `rxProg.code` starting at byte offset
    `(subProg.base - rxProg.base).toNat`. -/
@[expose] def checkProgCodeSubslice (rxProg subProg : Program) : Bool :=
  let off := (subProg.base - rxProg.base).toNat
  Nat.beq (subProg.base.toNat % 4) 0 &&
  Nat.ble (subProg.base.toNat + subProg.code.length) (2 ^ 64) &&
  decide (rxProg.base + BitVec.ofNat 64 off = subProg.base) &&
  Nat.ble (off + subProg.code.length) rxProg.code.length &&
  (subProg.code == (rxProg.code.drop off).take subProg.code.length)

/-- Extract the exact alignment, no-wrap, and byte-subslice existential required by
    `Lib2LayoutFacts.f3CodeInv_rxWords_codeLoaded_strip` from a single `checkProgCodeSubslice`
    evaluation. -/
theorem rxSubslice_of_checkProgCodeSubslice {rxProg subProg : Program}
    (hchk : checkProgCodeSubslice rxProg subProg = true) :
    subProg.base.toNat % 4 = 0 ∧
      subProg.base.toNat + subProg.code.length ≤ 2 ^ 64 ∧
      (∀ (i : Nat) (hi : i < subProg.code.length),
        ∃ (j : Nat) (hj : j < rxProg.code.length),
          subProg.base + BitVec.ofNat 64 i = rxProg.base + BitVec.ofNat 64 j ∧
          subProg.code[i] = rxProg.code[j]) := by
  unfold checkProgCodeSubslice at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, decide_eq_true_eq, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨hAlign, hNoWrap⟩, hBaseEq⟩, hBound⟩, hCodeEq⟩
  refine ⟨hAlign, hNoWrap, fun i hi => ?_⟩
  let off := (subProg.base - rxProg.base).toNat
  have hj : off + i < rxProg.code.length := by omega
  refine ⟨off + i, hj, ?_, ?_⟩
  · have hofNat : BitVec.ofNat 64 (off + i) = BitVec.ofNat 64 off + BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        ← Nat.add_mod]
    rw [hofNat, ← BitVec.add_assoc, hBaseEq]
  · have hget? :
        subProg.code[i]? = ((rxProg.code.drop off).take subProg.code.length)[i]? :=
      congrArg (fun l => l[i]?) hCodeEq
    rw [List.getElem?_eq_getElem hi, List.getElem?_take_of_lt hi, List.getElem?_drop,
      List.getElem?_eq_getElem hj] at hget?
    exact Option.some.inj hget?

/-- Direct `subProg.CodeLoaded m` derivation from `rxProg.CodeLoaded m` and
    `checkProgCodeSubslice rxProg subProg = true` (independent of `subProg.externs`, covering both
    `durationSinceSubProg` and `timeAddSubProg`). -/
theorem codeLoaded_of_checkProgCodeSubslice {rxProg subProg : Program} {m : Memory}
    (hRx : rxProg.CodeLoaded m)
    (hchk : checkProgCodeSubslice rxProg subProg = true) :
    subProg.CodeLoaded m := by
  obtain ⟨hAlign, hNoWrap, hSub⟩ := rxSubslice_of_checkProgCodeSubslice hchk
  refine Program.CodeLoaded.intro hAlign hNoWrap fun i hi => ?_
  obtain ⟨j, hj, haddr_eq, hbyte_eq⟩ := hSub i hi
  rw [haddr_eq, hbyte_eq]
  exact ⟨hRx.byte_eq j hj, hRx.perm_eq j hj, hRx.isLazyFree_eq j hj⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
