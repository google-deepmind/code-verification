/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget -- proof-setup: allow-public-import

/-!
# `core::str::converts::from_utf8` Consumer `HookOk` Row Arm (`ExtraRowSpecs.FromUtf8RowSpec`)

Row-owned consumer-contract leaf module for `lsFromUtf8Sym` in `ExtraGhostSpecs.ExtraRowSpec`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FromUtf8RowSpec

open Arm64 ProofLib
open CryptoVerification.SignalSession.Cli.MainHops (fromUtf8AsciiSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (fromUtf8AsciiSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)

/-- `core::str::converts::from_utf8` consumer `HookOk` arm (`fromUtf8AsciiSpec` + RO twin,
    plain, `withVmPreserved`, and `withAlloc`). -/
@[expose] def FromUtf8RowSpec (f : State → State) : Prop :=
  (∀ stk : Nat, HookOk f (fromUtf8AsciiSpec stk)) ∧
  (∀ stk : Nat, HookOk f (withVmPreserved (fromUtf8AsciiSpec stk))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat),
    HookOk f (withAlloc A lim (fromUtf8AsciiSpec stk))) ∧
  (∀ stk : Nat, HookOk f (fromUtf8AsciiSpecRO stk)) ∧
  (∀ stk : Nat, HookOk f (withVmPreserved (fromUtf8AsciiSpecRO stk))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat),
    HookOk f (withAlloc A lim (fromUtf8AsciiSpecRO stk)))

theorem FromUtf8RowSpec.of_vm {f : State → State}
    (h1 : ∀ stk : Nat, HookOk f (fromUtf8AsciiSpec stk))
    (h2 : ∀ stk : Nat, HookOk f (fromUtf8AsciiSpecRO stk))
    (hvm : ∀ s : State, VmPreserved s (f s)) : FromUtf8RowSpec f :=
  ⟨h1,
   fun stk => hookOk_withVmPreserved (h1 stk) hvm,
   fun A lim stk => hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (h1 stk) hvm),
   h2,
   fun stk => hookOk_withVmPreserved (h2 stk) hvm,
   fun A lim stk => hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (h2 stk) hvm)⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FromUtf8RowSpec
