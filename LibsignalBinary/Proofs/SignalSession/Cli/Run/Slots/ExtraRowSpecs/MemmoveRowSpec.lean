/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import

/-!
# `memmove` Consumer `HookOk` Row Arm (`ExtraRowSpecs.MemmoveRowSpec`)

Row-owned consumer-contract leaf module for `"memmove"` in `ExtraGhostSpecs.ExtraRowSpec`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemmoveRowSpec

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
  (libcMemmoveBoundedSpec sessionMemmoveBoundedBudgetSpec sessionMemmoveBoundedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)

/-- `memmove` consumer `HookOk` arm narrowed to `#1348` `MemmoveArithBound`-guarded
    `libcMemmoveBoundedSpec` + `sessionMemmoveBoundedSpec` (plain, `withVmPreserved` /
    `sessionMemmoveBoundedBudgetSpec`, `withAlloc`, and `AllocCallPreserved`). -/
@[expose] def MemmoveRowSpec (f : State → State) : Prop :=
  (∀ stk : Nat, HookOk f (libcMemmoveBoundedSpec stk)) ∧
  (∀ stk : Nat, HookOk f (withVmPreserved (libcMemmoveBoundedSpec stk))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat),
    HookOk f (withAlloc A lim (libcMemmoveBoundedSpec stk))) ∧
  (∀ stk : Nat, HookOk f (sessionMemmoveBoundedSpec stk)) ∧
  (∀ stk : Nat, HookOk f (sessionMemmoveBoundedBudgetSpec stk)) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat),
    HookOk f (withAlloc A lim (sessionMemmoveBoundedSpec stk))) ∧
  (∀ s : State, AllocCallPreserved s (f s))

theorem MemmoveRowSpec.of_vm {f : State → State}
    (h1 : ∀ stk : Nat, HookOk f (libcMemmoveBoundedSpec stk))
    (h2 : ∀ stk : Nat, HookOk f (sessionMemmoveBoundedSpec stk))
    (hvm : ∀ s : State, VmPreserved s (f s))
    (hacp : ∀ s : State, AllocCallPreserved s (f s)) : MemmoveRowSpec f :=
  ⟨h1,
   fun stk => hookOk_withVmPreserved (h1 stk) hvm,
   fun A lim stk => hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (h1 stk) hvm),
   h2,
   fun stk => hookOk_withVmPreserved (h2 stk) hvm,
   fun A lim stk => hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (h2 stk) hvm),
   hacp⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemmoveRowSpec
