/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat -- proof-setup: allow-public-import

/-!
# `SystemTime::duration_since` Consumer `HookOk` Row Arm (`ExtraRowSpecs.DurationSinceRowSpec`)

Row-owned consumer-contract leaf module for `lsDurationSinceSym` in `ExtraGhostSpecs.ExtraRowSpec`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.DurationSinceRowSpec

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession.Cli.Slots (durationSinceEpochAtSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (hookOk_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)

/-- `<std::time::SystemTime>::duration_since` consumer `HookOk` arm narrowed with outermost
    `withLsRet` (`Slots.durationSinceBoundedSpec` + bounded-stack `durationSinceEpochAtSpec stk`
    for `208 ≤ stk → stk ≤ 2 ^ 64`, plain, `withVmPreserved`, and `withAlloc`). -/
@[expose] def DurationSinceRowSpec [LibsignalPlacement] (f : State → State) : Prop :=
  HookOk f (withLsRet CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec) ∧
  HookOk f
    (withLsRet
      (withVmPreserved CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec)) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits),
    HookOk f
      (withLsRet
        (withAlloc A lim CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec))) ∧
  (∀ stk : Nat, 208 ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withLsRet (durationSinceEpochAtSpec stk))) ∧
  (∀ stk : Nat, 208 ≤ stk → stk ≤ 2 ^ 64 →
    HookOk f (withLsRet (withVmPreserved (durationSinceEpochAtSpec stk)))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat),
    208 ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withLsRet (withAlloc A lim (durationSinceEpochAtSpec stk))))

private theorem hookOk_withLsRet_withAlloc_of_ls [LibsignalPlacement] {α : Type}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {f : State → State} {spec : Spec α}
    (hh : HookOk f (withVmPreserved (withLsRet spec))) :
    HookOk f (withLsRet (withAlloc A lim spec)) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  exact hookOk_withAlloc_of_withVmPreserved A lim hh ⟨x, st⟩ R s0 hrun
    (by dsimp only [withLsRet, withAlloc] at hpre ⊢; simpa only [sepConj_assoc] using hpre) hsp

theorem DurationSinceRowSpec.of_ls_vm [LibsignalPlacement] {f : State → State}
    (h1 : HookOk f (withLsRet CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec))
    (h2 : ∀ stk : Nat, 208 ≤ stk → stk ≤ 2 ^ 64 → HookOk f (withLsRet (durationSinceEpochAtSpec stk)))
    (hvm : ∀ s : State, VmPreserved s (f s)) : DurationSinceRowSpec f :=
  let h1v := hookOk_withVmPreserved h1 hvm
  ⟨h1, h1v, fun A lim => hookOk_withLsRet_withAlloc_of_ls A lim h1v,
   h2,
   fun stk hlo hhi => hookOk_withVmPreserved (h2 stk hlo hhi) hvm,
   fun A lim stk hlo hhi =>
     hookOk_withLsRet_withAlloc_of_ls A lim (hookOk_withVmPreserved (h2 stk hlo hhi) hvm)⟩

theorem DurationSinceRowSpec.of_vm [LibsignalPlacement] {f : State → State}
    (h1 : HookOk f CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec)
    (h2 : ∀ stk : Nat, 208 ≤ stk → stk ≤ 2 ^ 64 → HookOk f (durationSinceEpochAtSpec stk))
    (hvm : ∀ s : State, VmPreserved s (f s)) : DurationSinceRowSpec f :=
  DurationSinceRowSpec.of_ls_vm
    (hookOk_withLsRet h1)
    (fun stk hlo hhi => hookOk_withLsRet (h2 stk hlo hhi))
    hvm

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.DurationSinceRowSpec
