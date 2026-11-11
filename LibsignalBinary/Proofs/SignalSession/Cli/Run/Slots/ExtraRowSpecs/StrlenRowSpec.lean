/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.Libc.Strlen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget -- proof-setup: allow-public-import

/-!
# `strlen` Consumer `HookOk` Row Arm (`ExtraRowSpecs.StrlenRowSpec`)

Row-owned consumer-contract leaf module for `"strlen"` in `ExtraGhostSpecs.ExtraRowSpec`.

Narrowed to `HookDischarge.Libc.Strlen.withStrlenPadRO` (`musl` 88 B SWAR `strlen` on
`origin/stockhooks/train` `5e7c7addc7`); `withVmPreserved (withStrlenPadRO (strlenSpecRO stk))` is
definitionally (`rfl`) identical to `ArgvPad.strlenSpecROSat stk`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StrlenRowSpec

open Arm64 ProofLib
open CryptoVerification.SignalSession.Cli.MainHops (strlenSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (withStrlenPadRO)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (strlenSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)

/-- `strlen` consumer `HookOk` arm narrowed to SWAR-padded `withStrlenPadRO` (`strlenSpec` +
    `strlenSpecRO`, plain, `withVmPreserved` = `ArgvPad.strlenSpecROSat` by `rfl`, and `withAlloc`). -/
@[expose] def StrlenRowSpec (f : State → State) : Prop :=
  (∀ stk : Nat, HookOk f (withStrlenPadRO (strlenSpec stk))) ∧
  (∀ stk : Nat, HookOk f (withVmPreserved (withStrlenPadRO (strlenSpec stk)))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat),
    HookOk f (withAlloc A lim (withStrlenPadRO (strlenSpec stk)))) ∧
  (∀ stk : Nat, HookOk f (withStrlenPadRO (strlenSpecRO stk))) ∧
  (∀ stk : Nat, HookOk f (withVmPreserved (withStrlenPadRO (strlenSpecRO stk)))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat),
    HookOk f (withAlloc A lim (withStrlenPadRO (strlenSpecRO stk)))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat),
    HookOk f (withAlloc A lim (withVmPreserved (withStrlenPadRO (strlenSpecRO stk)))))

theorem StrlenRowSpec.of_vm {f : State → State}
    (h1 : ∀ stk : Nat, HookOk f (withStrlenPadRO (strlenSpec stk)))
    (h2 : ∀ stk : Nat, HookOk f (withStrlenPadRO (strlenSpecRO stk)))
    (hvm : ∀ s : State, VmPreserved s (f s)) : StrlenRowSpec f :=
  ⟨h1,
   fun stk => hookOk_withVmPreserved (h1 stk) hvm,
   fun A lim stk => hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (h1 stk) hvm),
   h2,
   fun stk => hookOk_withVmPreserved (h2 stk) hvm,
   fun A lim stk => hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (h2 stk) hvm),
   fun A lim stk => hookOk_withAlloc_withVmPreserved A lim (hookOk_withVmPreserved (h2 stk) hvm)⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StrlenRowSpec
