/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget -- proof-setup: allow-public-import

/-!
# `core::slice::memchr::memrchr` Consumer `HookOk` Row Arm (`ExtraRowSpecs.MemrchrRowSpec`)

Row-owned consumer-contract leaf module for `lsMemrchrSym` in `ExtraGhostSpecs.ExtraRowSpec`.
Uses bounded stack frames (`extHookStack ≤ stk → stk ≤ 2 ^ 64`) per `HOOKS-PREP` / `HOOKS-LEAD`
`03:43Z` decision (`stackAt_shrink` requirement on real-code lifts; instantiated at `extHookStack =
16384` by `decide`).
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemrchrRowSpec

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.Cli.MainHops (memrchrSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (hookOk_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (memrchrSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)

/-- `core::slice::memchr::memrchr` (`lsMemrchrSym`) consumer `HookOk` arm narrowed with outermost
    `withLsRet` and bounded stack `extHookStack ≤ stk → stk ≤ 2 ^ 64` (`MainHops.memrchrSpec` +
    `CalleesRO.memrchrSpecRO`, plain, `withVmPreserved`, and `withAlloc`). -/
@[expose] def MemrchrRowSpec [LibsignalPlacement] (f : State → State) : Prop :=
  (∀ stk : Nat, extHookStack ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withLsRet (memrchrSpec stk))) ∧
  (∀ stk : Nat, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (withVmPreserved (memrchrSpec stk)))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat),
    extHookStack ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withLsRet (withAlloc A lim (memrchrSpec stk)))) ∧
  (∀ stk : Nat, extHookStack ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withLsRet (memrchrSpecRO stk))) ∧
  (∀ stk : Nat, extHookStack ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (withVmPreserved (memrchrSpecRO stk)))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat),
    extHookStack ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withLsRet (withAlloc A lim (memrchrSpecRO stk))))

private theorem hookOk_withLsRet_withAlloc_of_ls [LibsignalPlacement] {α : Type}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {f : State → State} {spec : Spec α}
    (hh : HookOk f (withVmPreserved (withLsRet spec))) :
    HookOk f (withLsRet (withAlloc A lim spec)) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  exact hookOk_withAlloc_of_withVmPreserved A lim hh ⟨x, st⟩ R s0 hrun
    (by dsimp only [withLsRet, withAlloc] at hpre ⊢; simpa only [sepConj_assoc] using hpre) hsp

theorem MemrchrRowSpec.of_ls_vm [LibsignalPlacement] {f : State → State}
    (h1 : ∀ stk : Nat, extHookStack ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withLsRet (memrchrSpec stk)))
    (h2 : ∀ stk : Nat, extHookStack ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withLsRet (memrchrSpecRO stk)))
    (hvm : ∀ s : State, VmPreserved s (f s)) : MemrchrRowSpec f :=
  ⟨h1,
   fun stk hlo hhi => hookOk_withVmPreserved (h1 stk hlo hhi) hvm,
   fun A lim stk hlo hhi =>
     hookOk_withLsRet_withAlloc_of_ls A lim (hookOk_withVmPreserved (h1 stk hlo hhi) hvm),
   h2,
   fun stk hlo hhi => hookOk_withVmPreserved (h2 stk hlo hhi) hvm,
   fun A lim stk hlo hhi =>
     hookOk_withLsRet_withAlloc_of_ls A lim (hookOk_withVmPreserved (h2 stk hlo hhi) hvm)⟩

theorem MemrchrRowSpec.of_vm [LibsignalPlacement] {f : State → State}
    (h1 : ∀ stk : Nat, extHookStack ≤ stk → stk ≤ 2 ^ 64 → HookOk f (memrchrSpec stk))
    (h2 : ∀ stk : Nat, extHookStack ≤ stk → stk ≤ 2 ^ 64 → HookOk f (memrchrSpecRO stk))
    (hvm : ∀ s : State, VmPreserved s (f s)) : MemrchrRowSpec f :=
  MemrchrRowSpec.of_ls_vm
    (fun stk hlo hhi => hookOk_withLsRet (h1 stk hlo hhi))
    (fun stk hlo hhi => hookOk_withLsRet (h2 stk hlo hhi))
    hvm

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemrchrRowSpec
