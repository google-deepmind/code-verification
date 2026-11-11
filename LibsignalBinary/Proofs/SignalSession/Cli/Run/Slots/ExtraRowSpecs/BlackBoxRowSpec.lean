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
# `core::hint::black_box<*const u8>` Consumer `HookOk` Row Arm (`ExtraRowSpecs.BlackBoxRowSpec`)

Row-owned consumer-contract leaf module for `lsBlackBoxSym` in `ExtraGhostSpecs.ExtraRowSpec`.
Uses bounded stack frames (`16 ≤ stk → stk ≤ 2 ^ 64`) matching `BlackBoxCode` (`0c1b7e2b2a`).
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BlackBoxRowSpec

open Arm64 ProofLib
open CryptoVerification.LibsignalTripleRatchet (blackBoxSpec withStack)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)

/-- `core::hint::black_box<*const u8>` (`lsBlackBoxSym`) consumer `HookOk` arm with bounded stack
    size `16 ≤ stk → stk ≤ 2 ^ 64` (plain, `withVmPreserved`, and `withAlloc`).
    Note: `CryptoVerification.LibsignalTripleRatchet.blackBoxSpec` and
    `CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec` have definitionally
    identical fields (`rfl` via `hookOk_congr`). -/
@[expose] def BlackBoxRowSpec (f : State → State) : Prop :=
  (∀ stk : Nat, 16 ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withStack blackBoxSpec stk)) ∧
  (∀ stk : Nat, 16 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withVmPreserved (withStack blackBoxSpec stk))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat),
    16 ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withAlloc A lim (withStack blackBoxSpec stk)))

theorem BlackBoxRowSpec.of_vm {f : State → State}
    (h1 : ∀ stk : Nat, 16 ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withStack blackBoxSpec stk))
    (hvm : ∀ s : State, VmPreserved s (f s)) : BlackBoxRowSpec f :=
  ⟨h1,
   fun stk hlo hhi => hookOk_withVmPreserved (h1 stk hlo hhi) hvm,
   fun A lim stk hlo hhi =>
     hookOk_withAlloc_of_withVmPreserved A lim (hookOk_withVmPreserved (h1 stk hlo hhi) hvm)⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BlackBoxRowSpec
