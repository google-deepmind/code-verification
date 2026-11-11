/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudget

/-!
# Budget-Threaded Extended-Stack Wrapper for `<PolyDecoder as Decoder>::add_chunk`

Re-exports `addChunkSpecX_of_addChunkSpec` under `RustCliAllocBudget M`
for Block `419`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofXBudget

open Arm64 ProofLib
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (
  addChunkSpec addChunkSpecX
)

/-- `addChunkSpec M A lim` entails `addChunkSpecX M A lim` by framing the unused bottom stack region. -/
theorem addChunkSpecX_of_addChunkSpec {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok P addr (addChunkSpec M A lim)) :
    subroutine_ok P addr (addChunkSpecX M A lim) :=
  LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofPlacedBudget.addChunkSpecX_of_addChunkSpec h

end LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofXBudget
