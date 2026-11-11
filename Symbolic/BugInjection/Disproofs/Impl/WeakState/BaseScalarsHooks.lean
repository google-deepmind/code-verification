/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.BugInjectionMutantImage
public import ProofLib.ProgramReflection
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLinkData
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.BaseData

/-! Kernel validation of placed header/layout scalars & hooked stub tree for `Symbolic.BugInjection.Disproofs.Impl.WeakState` (Rule 3). -/

@[expose] public section
set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.BaseScalarsHooks

open ProofLib.ProgramReflection
open CryptoVerification.BugInjection (mutantCliElfImage)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced (extractElfScalarsAndOkPlaced extractImageHooksPlaced)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.MutantLink (mutantMpl mutantMmpl)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.BaseData (baseHooks)

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1600000 in
theorem base_scalars : extractElfScalarsAndOkPlaced mutantMpl mutantMmpl mutantCliElfImage = some (
    0x46a000#64, 0x400040#64, 7, 0x471000#64, -- layout-bypass: concrete-mutant-trace-checkpoint
    0x46f000#64, 0x46f008#64, 0x46bbfc#64, 0x46bbfd#64, -- layout-bypass: concrete-mutant-trace-checkpoint
    0x46bce0#64, 0x46bce1#64, 0x46bcdc#64, 0x46bcdd#64) := by rfl_kernel -- layout-bypass: concrete-mutant-trace-checkpoint

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1600000 in
theorem base_hooks : extractImageHooksPlaced mutantMpl = baseHooks := by
  rfl_kernel

end Symbolic.BugInjection.Disproofs.Impl.WeakState.BaseScalarsHooks
