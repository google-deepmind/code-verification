/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import

/-!
# `<x25519_dalek::SharedSecret as Drop>::drop` Consumer `HookOk` Row Arm (`ExtraRowSpecs.SharedSecretDropRowSpec`)

Row-owned consumer-contract leaf module for `lsSharedSecretDropSym` in `ExtraGhostSpecs.ExtraRowSpec`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec

open Arm64 ProofLib
open CryptoVerification.LibsignalTripleRatchet (zeroizeSecretSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)

/-- `<x25519_dalek::SharedSecret as Drop>::drop` consumer `HookOk` arm (`zeroizeSecretSpec`,
    plain, `withVmPreserved`, and `withAlloc`). -/
@[expose] def SharedSecretDropRowSpec (f : State → State) : Prop :=
  HookOk f zeroizeSecretSpec ∧
  HookOk f (withVmPreserved zeroizeSecretSpec) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits),
    HookOk f (withAlloc A lim zeroizeSecretSpec))

theorem SharedSecretDropRowSpec.of_vm {f : State → State}
    (h1 : HookOk f zeroizeSecretSpec)
    (hvm : ∀ s : State, VmPreserved s (f s)) : SharedSecretDropRowSpec f :=
  let hv := hookOk_withVmPreserved h1 hvm
  ⟨h1, hv, fun A lim => hookOk_withAlloc_of_withVmPreserved A lim hv⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec
