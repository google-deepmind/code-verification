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
public import LibsignalBinary.Specifications.LibsignalPublicApi -- proof-setup: allow-public-import

/-!
# `SystemTime::add` Consumer `HookOk` Row Arm (`ExtraRowSpecs.TimeAddRowSpec`)

Row-owned consumer-contract leaf module for `lsTimeAddSym` in `ExtraGhostSpecs.ExtraRowSpec`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.TimeAddRowSpec

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (hookOk_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)

/-- `<std::time::SystemTime as Add<Duration>>::add` consumer `HookOk` arm narrowed with outermost
    `withLsRet` (`LibsignalPublicApi.timeAddSpec`, `withLsRet (withVmPreserved ...)` =
    `withLsRet timeAddBudgetSpec` by `rfl`, and `withLsRet (withAlloc ...)`). -/
@[expose] def TimeAddRowSpec [LibsignalPlacement] (f : State → State) : Prop :=
  HookOk f (withLsRet CryptoVerification.LibsignalPublicApi.timeAddSpec) ∧
  HookOk f (withLsRet (withVmPreserved CryptoVerification.LibsignalPublicApi.timeAddSpec)) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits),
    HookOk f (withLsRet (withAlloc A lim CryptoVerification.LibsignalPublicApi.timeAddSpec)))

private theorem hookOk_withLsRet_withAlloc_of_ls [LibsignalPlacement] {α : Type}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {f : State → State} {spec : Spec α}
    (hh : HookOk f (withVmPreserved (withLsRet spec))) :
    HookOk f (withLsRet (withAlloc A lim spec)) := by
  intro ⟨x, st⟩ R s0 hrun hpre hsp
  exact hookOk_withAlloc_of_withVmPreserved A lim hh ⟨x, st⟩ R s0 hrun
    (by dsimp only [withLsRet, withAlloc] at hpre ⊢; simpa only [sepConj_assoc] using hpre) hsp

theorem TimeAddRowSpec.of_ls_vm [LibsignalPlacement] {f : State → State}
    (h1 : HookOk f (withLsRet CryptoVerification.LibsignalPublicApi.timeAddSpec))
    (hvm : ∀ s : State, VmPreserved s (f s)) : TimeAddRowSpec f :=
  let hv := hookOk_withVmPreserved h1 hvm
  ⟨h1, hv, fun A lim => hookOk_withLsRet_withAlloc_of_ls A lim hv⟩

theorem TimeAddRowSpec.of_vm [LibsignalPlacement] {f : State → State}
    (h1 : HookOk f CryptoVerification.LibsignalPublicApi.timeAddSpec)
    (hvm : ∀ s : State, VmPreserved s (f s)) : TimeAddRowSpec f :=
  TimeAddRowSpec.of_ls_vm (hookOk_withLsRet h1) hvm

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.TimeAddRowSpec
