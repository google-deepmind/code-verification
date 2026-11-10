/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget -- proof-setup: allow-public-import

/-!
# `bcmp` Consumer `HookOk` Row Arm (`ExtraRowSpecs.BcmpRowSpec`)

Row-owned consumer-contract leaf module for `"bcmp"` in `ExtraGhostSpecs.ExtraRowSpec`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BcmpRowSpec

open Arm64 ProofLib
open CryptoVerification.E2E.HooksE (bcmpVregsSpec)
open CryptoVerification.SignalSession.Cli (cliBcmpSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)

/-- `bcmp` consumer `HookOk` arm (`cliBcmpSpec` + `bcmpVregsSpec`, plain, `withVmPreserved`, and
    `withAlloc`; `e2eBcmpSpec` follows via `hookOk_bcmpSpec_of_vregs`). -/
@[expose] def BcmpRowSpec (f : State → State) : Prop :=
  HookOk f cliBcmpSpec ∧
  HookOk f (withVmPreserved cliBcmpSpec) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits),
    HookOk f (withAlloc A lim cliBcmpSpec)) ∧
  HookOk f bcmpVregsSpec ∧
  HookOk f (withVmPreserved bcmpVregsSpec) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits),
    HookOk f (withAlloc A lim bcmpVregsSpec))

theorem BcmpRowSpec.of_vm {f : State → State}
    (h1 : HookOk f cliBcmpSpec) (h2 : HookOk f bcmpVregsSpec)
    (hvm : ∀ s : State, VmPreserved s (f s)) : BcmpRowSpec f :=
  let h1v := hookOk_withVmPreserved h1 hvm
  let h2v := hookOk_withVmPreserved h2 hvm
  ⟨h1, h1v, fun A lim => hookOk_withAlloc_of_withVmPreserved A lim h1v,
   h2, h2v, fun A lim => hookOk_withAlloc_of_withVmPreserved A lim h2v⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BcmpRowSpec
