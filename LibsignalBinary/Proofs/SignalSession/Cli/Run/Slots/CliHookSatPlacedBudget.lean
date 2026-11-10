/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.HeapIntro

/-!
# Budget-Threaded `cliExternsPlaced` and `cliGhostExterns` Contracts (Placed)

`VmPreserved`-strengthened `HookSat (cliExternsPlaced mmpl W)` contracts for non-allocating rows of
`cliHookTablePlaced mmpl W`, together with budget-threaded ghost-hook bundles
(`CliGhostAllocHooks`, `CliGhostSpqrAllocHooks`, and `CliAllocHooks`) over
`cliGhostExterns g (cliExternsPlaced mmpl W)` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (LibsignalHooks LibsignalPlacement libsignalSessionExterns lsHandleErrorSym ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (derivePublicKeyBytesSpec diffieHellmanSpec extHookStack framelessMemcpySpec framelessMemcpy_hookOk hookMemcpy_region_trace_ok hookMemcpy_trace_ok hookMemmove_trace_ok hookMemset_region_trace_ok hookMemset_trace_ok memcpyName memmoveName memsetName noAllocShimSpec noAllocShim_hookOk pubFromSecretSpec sessionMemcpyRegionSpec sessionMemcpySpec sessionMemsetRegionSpec sessionMemsetSpec sessionShim_hookOk withStack zeroizeSecretSpec)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced cliHookTablePlaced lsBlackBoxSym lsDurationSinceSym lsFromUtf8Sym lsMemcpySym lsMemrchrSym lsMemsetSym lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym lsTimeAddSym lsWriteFileSym lsWriteStdoutSym writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli (cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.MainHops (allocHook0_fs cliIo deallocHook_fs extHookStack_le fromUtf8AsciiSpec hookMemcpy_fs hookMemmove_fs hookMemset_fs hookNoop_fs hookOk_withStack memrchrSpec pos_of_extHookStack_le reallocHook0_fs strlenSpec)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC allocHook0_fsT cliExternsPlaced_row cliExtraGhostSyms cliGhostExterns cliGhostExterns_alloc cliGhostExterns_allocZeroed cliGhostExterns_dealloc cliGhostExterns_memcpy_some cliGhostExterns_memset_some cliGhostExterns_other cliGhostExterns_realloc cliGhostExterns_shim deallocHook_fsT hookMemcpy_fsT hookMemset_fsT hookSat_of_eq reallocHook0_fsT)
open CryptoVerification.SignalSession.Cli.Slots (cliExternsPlaced_compress256Multi_sat cliExternsPlaced_compress256_sat cliExternsPlaced_derivePublicKeyBytes_sat cliExternsPlaced_diffieHellman_sat cliExternsPlaced_pubFromSecret_sat cliExternsPlaced_writeFile_sat cliExternsPlaced_writeStdout_sat cliGhostExterns_panic_handle_alloc_error cliGhostExterns_panic_handle_error cliGhostExterns_panic_option_expect_failed cliGhostExterns_sat_of_cliExternsPlaced compress256SingleSpec compress256_row_placed diffieHellman_row_placed durationSinceBoundedSpec durationSinceEpochAllocSpec pubFromSecret_row_placed writeFile_row_placed writeStdout_row_placed)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession.Cli.Main.Placed (lsProg_617 instIsLsBlockProg_617)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (durationSinceEpochBudgetSpec hookSat_withVmPreserved timeAddBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (PublicApiDecHooksPlaced)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget (Stage2ContractsMinPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookExactMemcpy HookSatExactMemcpy hookMemcpy_exact)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
  (hookOk_withVmPreserved hookOk_rustAllocWithStack hookOk_rustDeallocExternWithStack
   hookOk_rustReallocExternWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraListSpecOk ExtraSpecOk GhostRowSpecOk hookSat_cliGhostExterns_of_extraOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts
  (pureExtraGhosts pureExtraGhosts_specOk)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (framelessMemcpyAcpSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec
   sessionMemsetBudgetSpec sessionMemsetRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (rustAllocSpecWithStack rustDeallocExternSpecWithStack rustReallocExternSpecWithStack)

private theorem retHook_vm {f : State → State} {s : State} (h : VmPreserved s (f s)) :
    VmPreserved s (retHook f s) := h

private theorem setMem_vm (s : State) {m : Memory} (hp : ∀ a : BitVec 64, m.perm a = s.mem.perm a) :
    VmPreserved s (s.setMem m) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, hp, fun _ _ _ => by cases s; rfl⟩

private theorem writeBytes_perm_eq (m : Memory) (p : BitVec 64) (bs : List (BitVec 8))
    (a : BitVec 64) : (m.writeBytes p bs).perm a = m.perm a :=
  congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_writeBytes_norm m p bs) a

private theorem hookSat_cli_vm {α : Type} (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {sym : String} {f : State → State} {spec : Spec α}
    (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (hsat : HookSat (cliExternsPlaced mmpl W) sym spec)
    (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookSat (cliExternsPlaced mmpl W) sym (withVmPreserved spec) := by
  refine hookSat_withVmPreserved hsat fun g hg s => ?_
  have hfeq : cliExternsPlaced mmpl W sym = some f := cliExternsPlaced_row mmpl W hrow
  rw [hfeq] at hg
  injection hg with hfg
  subst hfg
  exact hvm s

private theorem hookNoop_vm (s : State) : VmPreserved s (hookNoop s) :=
  LibsignalBinary.Heap.VmPreserved.refl s

private theorem hookMemset_vm (s : State) : VmPreserved s (hookMemset s) :=
  retHook_vm (setMem_vm s (writeBytes_perm_eq _ _ _))

private theorem hookMemcpy_vm (s : State) : VmPreserved s (hookMemcpy s) :=
  retHook_vm (setMem_vm s (writeBytes_perm_eq _ _ _))

private theorem writeStdoutHook_vm (s : State) : VmPreserved s (writeStdoutHook s) := by
  unfold writeStdoutHook; try dsimp only
  split <;> exact LibsignalBinary.Heap.VmPreserved.refl s

private theorem writeFileHook_vm (s : State) : VmPreserved s (writeFileHook s) :=
  LibsignalBinary.Heap.SpecBudget.vmPreserved_writeFileHook s

private theorem compress256Hook_vm (W : CliHooks) (s : State) :
    VmPreserved s (CryptoVerification.LibsignalHmac.compress256Hook W.C.F s) := by
  unfold CryptoVerification.LibsignalHmac.compress256Hook CryptoVerification.LibsignalAesCbc.returnToLinkRegister
  exact setMem_vm s (writeBytes_perm_eq _ _ _)

private theorem pubFromSecretHook_vm (W : CliHooks) (s : State) :
    VmPreserved s (CryptoVerification.LibsignalTripleRatchet.pubFromSecretHook W.C.pubKey s) :=
  retHook_vm (setMem_vm s (writeBytes_perm_eq _ _ _))

private theorem diffieHellmanHook_vm (W : CliHooks) (s : State) :
    VmPreserved s (CryptoVerification.LibsignalTripleRatchet.diffieHellmanHook W.C.X s) :=
  retHook_vm (setMem_vm s (writeBytes_perm_eq _ _ _))

/-! ## 2. Budget and `VmPreserved` `HookSat` for non-allocating symbols -/

theorem cliExternsPlaced_shim_budget_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli
      sessionShimBudgetSpec :=
  ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hShim),
    hookOk_withVmPreserved sessionShim_hookOk hookNoop_vm⟩

theorem cliExternsPlaced_noAllocShim_budget_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli
      (withVmPreserved noAllocShimSpec) :=
  ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hShim),
    hookOk_withVmPreserved noAllocShim_hookOk hookNoop_vm⟩

theorem cliGhostExterns_sessionMemmove_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "memmove"
      (LibsignalBinary.Proofs.HookDischarge.Libc.Memmove.sessionMemmoveBoundedBudgetSpec stk) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.sessionMemmove_budget_ok stk

theorem cliGhostExterns_bcmp_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) "bcmp" (withVmPreserved cliBcmpSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.bcmp_budget_ok

theorem cliGhostExterns_bcmp_keepsFs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) "bcmp" (withVmPreserved cliBcmpSpec).keepsFs :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    (hRow.bcmp_budget_ok).keepsFs hRow.fs_eq

theorem cliGhostExterns_bcmpVregs_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) "bcmp"
      (withVmPreserved CryptoVerification.E2E.HooksE.bcmpVregsSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.bcmpVregs_budget_ok

theorem cliGhostExterns_e2eBcmp_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) "bcmp"
      (withVmPreserved CryptoVerification.E2E.HooksE.e2eBcmpSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow x R s0 hrun hpre hsp => by
    obtain ⟨hkf, hst, hout⟩ := hRow.bcmpVregs_budget_ok x R s0 hrun hpre hsp
    refine ⟨hkf, hst, ?_⟩
    rcases hout with ⟨hret, habi, hpost⟩ | hrest
    · refine Or.inl ⟨hret, habi, ?_⟩
      dsimp only [withVmPreserved, CryptoVerification.E2E.HooksE.bcmpVregsSpec,
        CryptoVerification.E2E.HooksE.e2eBcmpSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, ⟨hpost.2.1.1, hpost.2.1.2.2⟩, hpost.2.2⟩
    · exact Or.inr hrest

theorem cliGhostExterns_strlen_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "strlen"
      (withVmPreserved
        (LibsignalBinary.Proofs.HookDischarge.Libc.Strlen.withStrlenPadRO
          (strlenSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.strlen_budget_ok stk

theorem cliGhostExterns_strlenRO_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "strlen"
      (withVmPreserved
        (LibsignalBinary.Proofs.HookDischarge.Libc.Strlen.withStrlenPadRO
          (LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.strlenSpecRO stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.strlenRO_budget_ok stk

theorem cliGhostExterns_memrchr_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsMemrchrSym
      (withLsRet (withVmPreserved (memrchrSpec stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.memrchr_budget_ok hstk hstk_ub

theorem cliGhostExterns_memrchrRO_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsMemrchrSym
      (withLsRet (withVmPreserved
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.memrchrSpecRO stk))) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.memrchrRO_budget_ok hstk hstk_ub

theorem cliGhostExterns_fromUtf8_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) lsFromUtf8Sym
      (withVmPreserved (fromUtf8AsciiSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.fromUtf8_budget_ok stk

theorem cliGhostExterns_fromUtf8RO_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) lsFromUtf8Sym
      (withVmPreserved
        (LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO.fromUtf8AsciiSpecRO stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.fromUtf8RO_budget_ok stk

theorem cliExternsPlaced_writeFile_vm_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) lsWriteFileSym
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced cliIo stk)) :=
  hookSat_cli_vm mmpl W (writeFile_row_placed mmpl W)
    (cliExternsPlaced_writeFile_sat mmpl W stk) writeFileHook_vm

theorem cliExternsPlaced_writeStdout_vm_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) lsWriteStdoutSym
      (withVmPreserved
        (CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced stk)) :=
  hookSat_cli_vm mmpl W (writeStdout_row_placed mmpl W)
    (cliExternsPlaced_writeStdout_sat mmpl W stk) writeStdoutHook_vm

theorem cliExternsPlaced_writeFile_budget_sat {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) lsWriteFileSym
      (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeFileSpecPlaced
        cliIo A lim stk) := by
  rcases cliExternsPlaced_writeFile_sat mmpl W stk with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun ⟨x, st⟩ R s0 hrun hpre hsp => ?_⟩
  have hfeq : cliExternsPlaced mmpl W lsWriteFileSym = some writeFileHook :=
    cliExternsPlaced_row mmpl W (writeFile_row_placed mmpl W)
  have hvm : VmPreserved s0 (f s0) := by
    cases hf.symm.trans hfeq
    exact writeFileHook_vm s0
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeFileSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, _⟩, hmem⟩
  have hpre0 : s0.mem ⊨
      (CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced cliIo stk).pre x s0 ∗
        (A.pool lim st s0 ∗ R) := by
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases hok x (A.pool lim st s0 ∗ R) s0 hrun hpre0 hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hres, hrest⟩
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeFileSpecPlaced]
    have hpool : A.pool lim (M.stepEvents [] st) (f s0) = A.pool lim st s0 :=
      A.pool_transport lim st s0 (f s0) hvm
    have hrest' : (f s0).mem ⊨
        ((x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim st s0) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    refine Satisfies.mono (sepConj_mono_left
      (Entails.sepExists_right ([] : List LibsignalBinary.Heap.AllocEvent) ?_)) hrest'
    rw [hpool]
    exact Entails.pure_right ⟨LibsignalBinary.Heap.SpecBudget.writeFileEnv_nil x.path.length, hres⟩
      (Entails.refl _)
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeFileSpecPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem cliExternsPlaced_writeStdout_budget_sat {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat) :
    HookSat (cliExternsPlaced mmpl W) lsWriteStdoutSym
      (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeStdoutSpecPlaced
        A lim stk) := by
  rcases cliExternsPlaced_writeStdout_sat mmpl W stk with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun ⟨x, st⟩ R s0 hrun hpre hsp => ?_⟩
  have hfeq : cliExternsPlaced mmpl W lsWriteStdoutSym = some writeStdoutHook :=
    cliExternsPlaced_row mmpl W (writeStdout_row_placed mmpl W)
  have hvm : VmPreserved s0 (f s0) := by
    cases hf.symm.trans hfeq
    exact writeStdoutHook_vm s0
  dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeStdoutSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, _⟩, hmem⟩
  have hpre0 : s0.mem ⊨
      (CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced stk).pre x s0 ∗
        (A.pool lim st s0 ∗ R) := by
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases hok x (A.pool lim st s0 ∗ R) s0 hrun hpre0 hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hres, hrest⟩
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.writeStdoutSpecPlaced]
    have hpool : A.pool lim (M.stepEvents [] st) (f s0) = A.pool lim st s0 :=
      A.pool_transport lim st s0 (f s0) hvm
    have hrest' : (f s0).mem ⊨
        ((x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ A.pool lim st s0) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    refine Satisfies.mono (sepConj_mono_left
      (Entails.sepExists_right ([] : List LibsignalBinary.Heap.AllocEvent) ?_)) hrest'
    rw [hpool]
    exact Entails.pure_right ⟨LibsignalBinary.Heap.SpecBudget.writeStdoutEnv_nil, hres⟩
      (Entails.refl _)
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.writeStdoutSpecPlaced] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem cliGhostExterns_durationSinceEpoch_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsDurationSinceSym
      (withLsRet durationSinceEpochBudgetSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.durationSinceEpoch_budget_ok

theorem cliGhostExterns_durationSinceEpochAlloc_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsDurationSinceSym
      (withLsRet (withVmPreserved durationSinceEpochAllocSpec)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.durationSinceEpochAlloc_budget_ok

theorem cliGhostExterns_durationSinceBounded_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsDurationSinceSym
      (withLsRet (withVmPreserved durationSinceBoundedSpec)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.durationSinceBounded_budget_ok

theorem cliGhostExterns_timeAdd_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsTimeAddSym
      (withLsRet timeAddBudgetSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow => hRow.timeAdd_budget_ok

theorem cliGhostExterns_blackBox_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookSat (cliGhostExterns g baseExt) lsBlackBoxSym
      (withVmPreserved
        (CryptoVerification.LibsignalTripleRatchet.withStack
          CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec stk)) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.findReceiverBlackBox_budget_ok hstk hstk_ub

theorem cliGhostExterns_blackBoxSat_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) lsBlackBoxSym
      LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat.blackBoxSpecSat :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.blackBox_budget_ok (by decide : 16 ≤ 16) (by decide)

theorem cliExternsPlaced_compress256Multi_budget_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) CryptoVerification.SignalSession.lsCompress256Sym
      (withVmPreserved (CryptoVerification.LibsignalTripleRatchet.compress256Spec W.C.F)) :=
  hookSat_cli_vm mmpl W (compress256_row_placed mmpl W)
    (cliExternsPlaced_compress256Multi_sat mmpl W) (compress256Hook_vm W)

theorem cliExternsPlaced_compress256_budget_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) CryptoVerification.SignalSession.lsCompress256Sym
      (withVmPreserved (compress256SingleSpec W.C.F)) :=
  hookSat_cli_vm mmpl W (compress256_row_placed mmpl W)
    (cliExternsPlaced_compress256_sat mmpl W) (compress256Hook_vm W)

theorem cliExternsPlaced_pubFromSecret_budget_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) CryptoVerification.SignalSession.lsPubFromSecretSym
      (withVmPreserved (pubFromSecretSpec W.C.pubKey)) :=
  hookSat_cli_vm mmpl W (pubFromSecret_row_placed mmpl W)
    (cliExternsPlaced_pubFromSecret_sat mmpl W) (pubFromSecretHook_vm W)

theorem cliExternsPlaced_derivePublicKeyBytes_budget_sat (mmpl : Obj.MultiPlacement)
    (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) CryptoVerification.SignalSession.lsPubFromSecretSym
      (withVmPreserved (derivePublicKeyBytesSpec W.C.pubKey)) :=
  hookSat_cli_vm mmpl W (pubFromSecret_row_placed mmpl W)
    (cliExternsPlaced_derivePublicKeyBytes_sat mmpl W) (pubFromSecretHook_vm W)

theorem cliExternsPlaced_diffieHellman_budget_sat (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) CryptoVerification.SignalSession.lsDiffieHellmanSym
      (withVmPreserved (diffieHellmanSpec W.C.X)) :=
  hookSat_cli_vm mmpl W (diffieHellman_row_placed mmpl W)
    (cliExternsPlaced_diffieHellman_sat mmpl W) (diffieHellmanHook_vm W)

theorem cliGhostExterns_staticSecretDrop_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) CryptoVerification.SignalSession.lsStaticSecretDropSym
      (withVmPreserved zeroizeSecretSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.staticSecretDrop_budget_ok

theorem cliGhostExterns_sharedSecretDrop_budget_sat [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hOk : ExtraSpecOk g) :
    HookSat (cliGhostExterns g baseExt) CryptoVerification.SignalSession.lsSharedSecretDropSym
      (withVmPreserved zeroizeSecretSpec) :=
  hookSat_cliGhostExterns_of_extraOk g baseExt hOk fun _ _ hRow =>
    hRow.sharedSecretDrop_budget_ok

/-! ## 3. `HookOk` helpers and `CliGhostAllocHooks` -/

private theorem allocHookStack_le_extHookStack : allocHookStack ≤ extHookStack := by decide

private theorem hook_placed_rocl_ok [LibsignalPlacement] {α : Type} {H : LibsignalHooks}
    {sym : String} {spec : Spec α}
    (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok (lsProg_617 H) (lsρ sym) (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain (ls_hook_ok_ultra_of_mem hsat hmem)

private theorem hookSat_withStack_of_hookSat {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hsat : HookSat H sym spec) (stk : Nat)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookSat H sym (withStack spec stk) := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, hf, hookOk_withStack hok stk hpan hex hoom⟩

private theorem hookSat_keepsFs_of_hookSat {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hsat : HookSat H sym spec)
    (hfs : ∀ f, H sym = some f → ∀ s : State, (f s).fs = s.fs) :
    HookSat H sym spec.keepsFs := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, hf, hok.keepsFs (hfs f hf)⟩

/-- Witnesses that `E2E.allocHook0`, `E2E.deallocHook`, and `E2E.reallocHook0` satisfy
`rustCli{Alloc,Dealloc,Realloc}BudgetSpec M A lim`. -/
structure CliAllocHooks [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Prop where
  alloc : HookOk CryptoVerification.E2E.allocHook0 (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookOk CryptoVerification.E2E.deallocHook (rustCliDeallocBudgetSpec M A lim)
  realloc : HookOk CryptoVerification.E2E.reallocHook0 (rustCliReallocBudgetSpec M A lim)


/-- Witnesses that `g.alloc`, `g.dealloc`, and `g.realloc` satisfy
`rustCli{Alloc,Dealloc,Realloc}BudgetSpec`, preserve `State.fs`, and satisfy `HookFsTraced IsFsC`,
and that `g.memset` and `g.memcpy` satisfy all budget-threaded consumer specs (`VmPreserved`,
`State.fs` preservation, and `HookFsTraced IsFsC`) on the 37-row `cliHookTablePlaced`. -/
structure CliGhostAllocHooks [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (g : CliGhostHooks) : Prop where
  alloc : HookOk g.alloc (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookOk g.dealloc (rustCliDeallocBudgetSpec M A lim)
  realloc : HookOk g.realloc (rustCliReallocBudgetSpec M A lim)
  alloc_fs : ∀ s : State, (g.alloc s).fs = s.fs
  dealloc_fs : ∀ s : State, (g.dealloc s).fs = s.fs
  realloc_fs : ∀ s : State, (g.realloc s).fs = s.fs
  alloc_fsT : HookFsTraced IsFsC g.alloc
  dealloc_fsT : HookFsTraced IsFsC g.dealloc
  realloc_fsT : HookFsTraced IsFsC g.realloc
  shim_eq : g.shim = hookNoop := by rfl
  memset : ∃ f, g.memset = some f ∧
    (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
    (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
    HookOk f memsetRegionSpec ∧
    HookOk f sessionMemsetRegionSpec ∧
    (∀ s : State, VmPreserved s (f s)) ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  memcpy : ∃ f, g.memcpy = some f ∧
    (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
    (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
    HookOk f memcpyRegionSpec ∧
    HookOk f sessionMemcpyRegionSpec ∧
    HookOk f framelessMemcpySpec ∧
    HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
    (∀ s : State, VmPreserved s (f s)) ∧
    (∀ s : State, (f s).fs = s.fs) ∧
    HookFsTraced IsFsC f
  memcpy_exact : ∀ f, g.memcpy = some f → HookExactMemcpy f
  memset_acp : ∀ f, g.memset = some f →
    ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle
  extraOk : ExtraSpecOk g

/-- Extends `CliGhostAllocHooks` with `g.allocZeroed` (`rustCliAllocBudgetSpec M A lim true`) and
`HookFsTraced IsFsC g.allocZeroed`. -/
structure CliGhostSpqrAllocHooks [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (g : CliGhostHooks) : Prop extends CliGhostAllocHooks M A lim g where
  allocZeroed : HookOk g.allocZeroed (rustCliAllocBudgetSpec M A lim true)
  allocZeroed_fs : ∀ s : State, (g.allocZeroed s).fs = s.fs
  allocZeroed_fsT : HookFsTraced IsFsC g.allocZeroed

/-- Bump-allocator instantiation of `CliGhostHooks` (`allocHook0`, `deallocHook`, `reallocHook0`, `allocZeroedHook0`; no replay obligation). -/
noncomputable def bumpGhost : CliGhostHooks where
  alloc := CryptoVerification.E2E.allocHook0
  dealloc := CryptoVerification.E2E.deallocHook
  realloc := CryptoVerification.E2E.reallocHook0
  allocZeroed := CryptoVerification.E2E.allocZeroedHook0
  shim := hookNoop
  stringClone := none
  memset := some hookMemset
  memcpy := some hookMemcpy
  extra := pureExtraGhosts

theorem cliGhostAllocHooks_bumpGhost [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hA : CliAllocHooks M A lim) :
    CliGhostAllocHooks M A lim bumpGhost where
  alloc := hA.alloc
  dealloc := hA.dealloc
  realloc := hA.realloc
  alloc_fs := allocHook0_fs
  dealloc_fs := deallocHook_fs
  realloc_fs := reallocHook0_fs
  alloc_fsT := allocHook0_fsT
  dealloc_fsT := deallocHook_fsT
  realloc_fsT := reallocHook0_fsT
  shim_eq := rfl
  memset := ⟨hookMemset, rfl, fun stk hpos => hookMemset_ok stk hpos,
    fun stk hpos => hookMemset_trace_ok stk hpos, hookMemset_region_ok,
    hookMemset_region_trace_ok, hookMemset_vm, hookMemset_fs, hookMemset_fsT⟩
  memcpy := ⟨hookMemcpy, rfl, fun stk => hookMemcpy_ok stk, fun stk => hookMemcpy_trace_ok stk,
    hookMemcpy_region_ok, hookMemcpy_region_trace_ok, framelessMemcpy_hookOk,
    CryptoVerification.SpqrV1.Alloc.hookMemcpy_region_ro_trace_ok,
    hookMemcpy_vm, hookMemcpy_fs, hookMemcpy_fsT⟩
  memcpy_exact := fun f hf => by cases hf; exact hookMemcpy_exact
  memset_acp := fun f hf s => by cases hf; exact ⟨rfl, rfl⟩
  extraOk := pureExtraGhosts_specOk

theorem cliGhostExterns_memset_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g baseExt) "memset" (withVmPreserved (libcMemsetSpec stk)) := by
  obtain ⟨f, hf, hok, _, _, _, hvm, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g baseExt hf, hookOk_withVmPreserved (hok stk hpos) hvm⟩

theorem cliGhostExterns_sessionMemset_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g baseExt) "memset" (sessionMemsetBudgetSpec stk) := by
  obtain ⟨f, hf, _, hok, _, _, hvm, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g baseExt hf, hookOk_withVmPreserved (hok stk hpos) hvm⟩

theorem cliGhostExterns_memsetRegion_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memset" (withVmPreserved memsetRegionSpec) := by
  obtain ⟨f, hf, _, _, hok, _, hvm, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliGhostExterns_sessionMemsetRegion_budget_sat [LibsignalPlacement]
    (baseExt : LibsignalHooks) {g : CliGhostHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memset" sessionMemsetRegionBudgetSpec := by
  obtain ⟨f, hf, _, _, _, hok, hvm, _, _⟩ := hG.memset
  exact ⟨f, cliGhostExterns_memset_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliGhostExterns_memcpy_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "memcpy" (withVmPreserved (libcMemcpySpec stk)) := by
  obtain ⟨f, hf, hok, _, _, _, _, _, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved (hok stk) hvm⟩

theorem cliGhostExterns_sessionMemcpy_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) (stk : Nat) :
    HookSat (cliGhostExterns g baseExt) "memcpy" (sessionMemcpyBudgetSpec stk) := by
  obtain ⟨f, hf, _, hok, _, _, _, _, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved (hok stk) hvm⟩

theorem cliGhostExterns_memcpyRegion_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memcpy" (withVmPreserved memcpyRegionSpec) := by
  obtain ⟨f, hf, _, _, hok, _, _, _, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliGhostExterns_sessionMemcpyRegion_budget_sat [LibsignalPlacement]
    (baseExt : LibsignalHooks) {g : CliGhostHooks} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memcpy" sessionMemcpyRegionBudgetSpec := by
  obtain ⟨f, hf, _, _, _, hok, _, _, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliGhostExterns_framelessMemcpy_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memcpy" (withVmPreserved framelessMemcpySpec) := by
  obtain ⟨f, hf, _, _, _, _, hok, _, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliGhostExterns_memcpyRegionRO_budget_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g baseExt) "memcpy"
      (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) := by
  obtain ⟨f, hf, _, _, _, _, _, hok, hvm, _, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hookOk_withVmPreserved hok hvm⟩

theorem cliExternsPlaced_memset_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset"
      (withVmPreserved (libcMemsetSpec stk)) :=
  cliGhostExterns_memset_budget_sat (cliExternsPlaced mmpl W) hG stk hpos

theorem cliExternsPlaced_sessionMemset_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) (stk : Nat) (hpos : 0 < stk) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" (sessionMemsetBudgetSpec stk) :=
  cliGhostExterns_sessionMemset_budget_sat (cliExternsPlaced mmpl W) hG stk hpos

theorem cliExternsPlaced_memsetRegion_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset"
      (withVmPreserved memsetRegionSpec) :=
  cliGhostExterns_memsetRegion_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliExternsPlaced_sessionMemsetRegion_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memset" sessionMemsetRegionBudgetSpec :=
  cliGhostExterns_sessionMemsetRegion_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliExternsPlaced_memcpy_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) (stk : Nat) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      (withVmPreserved (libcMemcpySpec stk)) :=
  cliGhostExterns_memcpy_budget_sat (cliExternsPlaced mmpl W) hG stk

theorem cliExternsPlaced_sessionMemcpy_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) (stk : Nat) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" (sessionMemcpyBudgetSpec stk) :=
  cliGhostExterns_sessionMemcpy_budget_sat (cliExternsPlaced mmpl W) hG stk

theorem cliExternsPlaced_memcpyRegion_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      (withVmPreserved memcpyRegionSpec) :=
  cliGhostExterns_memcpyRegion_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliExternsPlaced_sessionMemcpyRegion_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" sessionMemcpyRegionBudgetSpec :=
  cliGhostExterns_sessionMemcpyRegion_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliExternsPlaced_framelessMemcpy_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      (withVmPreserved framelessMemcpySpec) :=
  cliGhostExterns_framelessMemcpy_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliExternsPlaced_memcpyRegionRO_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) :=
  cliGhostExterns_memcpyRegionRO_budget_sat (cliExternsPlaced mmpl W) hG

theorem cliGhostExterns_exactMemcpy_sat [LibsignalPlacement] (baseExt : LibsignalHooks)
    {g : CliGhostHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSatExactMemcpy (cliGhostExterns g baseExt) "memcpy" := by
  obtain ⟨f, hf, _⟩ := hG.memcpy
  exact ⟨f, cliGhostExterns_memcpy_some g baseExt hf, hG.memcpy_exact f hf⟩

theorem cliExternsPlaced_exactMemcpy_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSatExactMemcpy (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" :=
  cliGhostExterns_exactMemcpy_sat (cliExternsPlaced mmpl W) hG

/-- Post-F3 `A2''` bridge: `CliGhostAllocHooks` discharges `HkdfPlacedHooksExactSat` on
    `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_allocHooks
    [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  { memset := by
      obtain ⟨f, hf, _, _, _, hok, _⟩ := hG.memset
      exact ⟨f, cliGhostExterns_memset_some g _ hf, hok⟩
    memcpy := cliExternsPlaced_exactMemcpy_sat mmpl g W hG
    compress256 :=
      (cliGhostExterns_other g _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_row mmpl W (compress256_row_placed mmpl W)) }

/-- `Rust.withPanics` specialization of `HkdfPlacedHooksExactSat.of_allocHooks`. -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_allocHooks_withPanics
    [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HkdfPlacedHooksExactSat W.C.F
      (Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W))) := by
  rw [CryptoVerification.SignalSession.Cli.RunGlue.withPanics_cliGhostExterns mmpl g W]
  exact HkdfPlacedHooksExactSat.of_allocHooks hG

/-- Variant-extern lift of `HkdfPlacedHooksExactSat.of_allocHooks` (covers any `H` agreeing with
    `cliGhostExterns g (cliExternsPlaced mmpl W)` outside RNG). -/
theorem _root_.LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat.of_allocHooks_ext
    [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) {H : LibsignalHooks}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns g (cliExternsPlaced mmpl W) sym) :
    HkdfPlacedHooksExactSat W.C.F H := by
  have hBase : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactSat.of_allocHooks hG
  refine { memset := ?_, memcpy := ?_, compress256 := ?_ }
  · obtain ⟨f, hf, hok⟩ := hBase.memset
    exact ⟨f, (hExt lsMemsetSym (by decide)).trans hf, hok⟩
  · obtain ⟨f, hf, hex⟩ := hBase.memcpy
    exact ⟨f, (hExt lsMemcpySym (by decide)).trans hf, hex⟩
  · exact (hExt CryptoVerification.LibsignalTripleRatchet.lsCompress256Sym (by decide)).trans
      hBase.compress256

/-- `HookExactMemcpy` implies `HookOk f ConcatBudgetAux.framelessMemcpyAcpSpec`
    (`AllocCallPreserved ∧ VmPreserved`, 0-stack). -/
theorem hookExactMemcpy_framelessMemcpyAcp_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f framelessMemcpyAcpSpec := by
  rintro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  dsimp only [framelessMemcpyAcpSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hlen : bs.length ≤ 2 ^ 64 := hx2 ▸ Nat.le_of_lt (s0.readReg64 .x2).isLt
  have hrw : s0.mem.RW dst bs.length := (IsBlock.memRegion dst bs.length).rw hmem
  have hsrc_front : s0.mem ⊨ (src ↦ₛ bs) ∗ (memRegion dst bs.length ∗ R) := by
    rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
  have hb := IsBlock.pointsToBytes src bs
  have hread : s0.mem.readBytes src bs.length = bs := (hb.read hsrc_front).2
  have hreadable : s0.mem.Readable src bs.length :=
    fun a ha => ⟨by rw [hb.perm_rw hsrc_front ha]; rfl, hb.isLazyFree_false hsrc_front ha⟩
  have hdisj : bs.length = 0 ∨ DisjointRegions dst bs.length src bs.length := by
    by_cases h0 : bs.length = 0
    · exact Or.inl h0
    · have hpos : 0 < bs.length := Nat.pos_of_ne_zero h0
      exact Or.inr ((IsBlock.memRegion dst bs.length).disjoint hb hpos hpos hmem)
  obtain ⟨c, heq⟩ := hf hrun hsp hx0 hx1 hx2 rfl hread hrw hreadable hdisj
  have hvm : VmPreserved s0 (f s0) := by
    rw [heq]
    exact LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.vmPreserved_applyMemcpyClobber_writeBytes
      s0 dst bs (s0.readReg64 .lr) c
  have hacp : LibsignalBinary.Heap.AllocCallPreserved s0 (f s0) := by
    rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hkf : s0.mem.KeepsFrozen (f s0).mem := by
    rw [heq]; exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  have hsym : (f s0).symtab = s0.symtab := by rw [heq]; rfl
  have hret : Returned s0 (f s0) := by rw [heq]; exact ⟨rfl, rfl, hrun⟩
  have hcc : CallingConventionPreserved s0 (f s0) := by
    rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
  dsimp only [framelessMemcpyAcpSpec]
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  have hx0_ret : (f s0).readReg64 .x0 = dst := by rw [heq]; exact hx0
  refine ⟨⟨hx0_ret, hacp, hvm⟩, ?_⟩
  rw [heq]
  exact satisfies_writeBytes bs hlen hmem

theorem hookSat_framelessMemcpyAcp_of_exact {H : String → Option (State → State)} {name : String}
    (h : HookSatExactMemcpy H name) :
    HookSat H name framelessMemcpyAcpSpec := by
  rcases h with ⟨f, hf, hex⟩
  exact ⟨f, hf, hookExactMemcpy_framelessMemcpyAcp_ok hex⟩

theorem cliExternsPlaced_framelessMemcpyAcp_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" framelessMemcpyAcpSpec :=
  hookSat_framelessMemcpyAcp_of_exact (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)

/-- `HookExactMemcpy` implies `HookOk f ConcatBudgetAux.sessionMemcpyRegionROSpec`
    (read-only source `src ↦ᵣ bs`, `AllocCallPreserved ∧ VmPreserved`, 0-stack). -/
theorem hookExactMemcpy_sessionMemcpyRegionROAcp_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec := by
  rintro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hrw : s0.mem.RW dst bs.length := (IsBlock.memRegion dst bs.length).rw hmem
  have hsrc_front : s0.mem ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
  have hb := IsBlockRO.pointsToBytesRO src bs hlen
  have hread : s0.mem.readBytes src bs.length = bs := hb.read hsrc_front
  have hreadable : s0.mem.Readable src bs.length :=
    fun a ha => ⟨hb.perm_r hsrc_front ha, hb.isLazyFree_false hsrc_front ha⟩
  have hdisj : bs.length = 0 ∨ DisjointRegions dst bs.length src bs.length := by
    by_cases h0 : bs.length = 0
    · exact Or.inl h0
    · have hpos : 0 < bs.length := Nat.pos_of_ne_zero h0
      have hnd : ¬ InRegion dst bs.length src := fun h =>
        not_satisfies_ownsRO_ownsRW
          (ownsRO_pointsToBytesRO_at hlen (by simp [InRegion, hpos]))
          (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length src h))
          hsrc_front
      have hns : ¬ InRegion src bs.length dst := fun h =>
        not_satisfies_ownsRO_ownsRW
          (ownsRO_pointsToBytesRO_at hlen h)
          (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length dst (by simp [InRegion, hpos])))
          hsrc_front
      dsimp only [InRegion] at hnd hns
      exact Or.inr ⟨Nat.le_of_not_lt hnd, Nat.le_of_not_lt hns⟩
  obtain ⟨c, heq⟩ := hf hrun hsp hx0 hx1 hx2 rfl hread hrw hreadable hdisj
  have hvm : VmPreserved s0 (f s0) := by
    rw [heq]
    exact LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.vmPreserved_applyMemcpyClobber_writeBytes
      s0 dst bs (s0.readReg64 .lr) c
  have hacp : LibsignalBinary.Heap.AllocCallPreserved s0 (f s0) := by
    rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hkf : s0.mem.KeepsFrozen (f s0).mem := by
    rw [heq]; exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  have hsym : (f s0).symtab = s0.symtab := by rw [heq]; rfl
  have hret : Returned s0 (f s0) := by rw [heq]; exact ⟨rfl, rfl, hrun⟩
  have hcc : CallingConventionPreserved s0 (f s0) := by
    rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
  dsimp only [LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec]
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  have hx0_ret : (f s0).readReg64 .x0 = dst := by rw [heq]; exact hx0
  refine ⟨⟨hx0_ret, hacp, hvm⟩, ?_⟩
  rw [heq]
  exact satisfies_writeBytes bs hlen hmem

theorem hookSat_sessionMemcpyRegionROAcp_of_exact {H : String → Option (State → State)}
    {name : String} (h : HookSatExactMemcpy H name) :
    HookSat H name LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec := by
  rcases h with ⟨f, hf, hex⟩
  exact ⟨f, hf, hookExactMemcpy_sessionMemcpyRegionROAcp_ok hex⟩

theorem cliExternsPlaced_sessionMemcpyRegionROAcp_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux.sessionMemcpyRegionROSpec :=
  hookSat_sessionMemcpyRegionROAcp_of_exact (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)

/-- `HookExactMemcpy` implies `HookOk f RustStdAllocBudgetBridge.allocMemcpyVmSpec`
    (`AllocCallPreserved ∧ VmPreserved`). -/
theorem hookExactMemcpy_allocMemcpyVm_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec := by
  rintro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  dsimp only [LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_bv, hlt⟩, hm⟩
  have hx2 : (s0.readReg64 .x2).toNat = bs.length := by
    rw [hx2_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hpre' : s0.mem ⊨ framelessMemcpyAcpSpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [framelessMemcpyAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  rcases hookExactMemcpy_framelessMemcpyAcp_ok hf (dst, src, bs) R s0 hrun hpre' hsp with
    ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec,
      framelessMemcpyAcpSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hrest

theorem hookSat_allocMemcpyVm_of_exact {H : String → Option (State → State)} {name : String}
    (h : HookSatExactMemcpy H name) :
    HookSat H name LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec := by
  rcases h with ⟨f, hf, hex⟩
  exact ⟨f, hf, hookExactMemcpy_allocMemcpyVm_ok hex⟩

theorem cliExternsPlaced_allocMemcpyVm_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      LibsignalBinary.Heap.RustStdAllocBudgetBridge.allocMemcpyVmSpec :=
  hookSat_allocMemcpyVm_of_exact (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)

/-- `HookExactMemcpy` implies `HookOk f LibsignalBinary.Heap.allocMemcpyVmSpec`
    (`MallocngBridgeBudget.allocMemcpyVmSpec`, `AllocCallPreserved ∧ VmPreserved`). -/
theorem hookExactMemcpy_heapAllocMemcpyVm_ok {f : State → State}
    (hf : HookExactMemcpy f) :
    HookOk f LibsignalBinary.Heap.allocMemcpyVmSpec := by
  rintro ⟨dst, src, bs⟩ R s0 hrun hpre hsp
  dsimp only [LibsignalBinary.Heap.allocMemcpyVmSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_bv, hlt⟩, hm⟩
  have hx2 : (s0.readReg64 .x2).toNat = bs.length := by
    rw [hx2_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hpre' : s0.mem ⊨ framelessMemcpyAcpSpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [framelessMemcpyAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  rcases hookExactMemcpy_framelessMemcpyAcp_ok hf (dst, src, bs) R s0 hrun hpre' hsp with
    ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalBinary.Heap.allocMemcpyVmSpec, framelessMemcpyAcpSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hrest

theorem hookSat_heapAllocMemcpyVm_of_exact {H : String → Option (State → State)} {name : String}
    (h : HookSatExactMemcpy H name) :
    HookSat H name LibsignalBinary.Heap.allocMemcpyVmSpec := by
  rcases h with ⟨f, hf, hex⟩
  exact ⟨f, hf, hookExactMemcpy_heapAllocMemcpyVm_ok hex⟩

theorem cliExternsPlaced_heapAllocMemcpyVm_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy"
      LibsignalBinary.Heap.allocMemcpyVmSpec :=
  hookSat_heapAllocMemcpyVm_of_exact (cliExternsPlaced_exactMemcpy_sat mmpl g W hG)

theorem cliExternsPlaced_alloc_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSymCli
      (rustCliAllocBudgetSpec M A lim false) :=
  ⟨g.alloc, cliGhostExterns_alloc g _, hG.alloc⟩

theorem cliExternsPlaced_dealloc_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSymCli
      (rustCliDeallocBudgetSpec M A lim) :=
  ⟨g.dealloc, cliGhostExterns_dealloc g _, hG.dealloc⟩

theorem cliExternsPlaced_realloc_budget_sat [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustReallocSymCli
      (rustCliReallocBudgetSpec M A lim) :=
  ⟨g.realloc, cliGhostExterns_realloc g _, hG.realloc⟩

/-! ## 4. `AllocContractsXCliPlaced` and `AllocContractsFsPlaced` -/

private theorem cli_row_ghost_rocl_ok [LibsignalPlacement] {α : Type}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} {spec : Spec α}
    (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (hh : HookOk f spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide)
    (h10 : sym ≠ lsMemcpySym := by decide)
    (hExtra : cliExtraGhostSyms.contains sym = false ∨ g.extra.lookup sym = none := by
      left; decide) :
    subroutine_ok (lsProg_617 (cliGhostExterns g (cliExternsPlaced mmpl W))) (lsρ sym)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  hook_placed_rocl_ok
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W ⟨f, cliExternsPlaced_row mmpl W hrow, hh⟩
      h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hExtra)
    hmem

theorem allocContractsXCliPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.AllocContractsXCliPlaced A lim
      (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  alloc := hook_placed_rocl_ok
    ⟨g.alloc, cliGhostExterns_alloc g _,
      hookOk_rustAllocWithStack hG.alloc allocHookStack_le_extHookStack extHookStack_le⟩
  dealloc := hook_placed_rocl_ok
    ⟨g.dealloc, cliGhostExterns_dealloc g _,
      hookOk_rustDeallocExternWithStack hG.dealloc allocHookStack_le_extHookStack extHookStack_le⟩
  realloc := hook_placed_rocl_ok
    ⟨g.realloc, cliGhostExterns_realloc g _,
      hookOk_rustReallocExternWithStack hG.realloc allocHookStack_le_extHookStack extHookStack_le⟩
  shim stk _ _ := hook_placed_rocl_ok
    ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq),
      hookOk_withStack (hookOk_withVmPreserved sessionShim_hookOk hookNoop_vm) stk⟩
  memcpy stk _ _ := hook_placed_rocl_ok (cliExternsPlaced_memcpy_budget_sat mmpl g W hG stk)
  session_memcpy stk _ _ := hook_placed_rocl_ok
    (cliExternsPlaced_sessionMemcpy_budget_sat mmpl g W hG stk)
  memcpy_region stk _ _ := hook_placed_rocl_ok
    (hookSat_withStack_of_hookSat (cliExternsPlaced_memcpyRegion_budget_sat mmpl g W hG) stk)
  session_memcpy_region stk _ _ := hook_placed_rocl_ok
    (hookSat_withStack_of_hookSat (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG) stk)
  memset stk hle _ := hook_placed_rocl_ok
    (cliExternsPlaced_memset_budget_sat mmpl g W hG stk (pos_of_extHookStack_le hle))
  session_memset stk hle _ := hook_placed_rocl_ok
    (cliExternsPlaced_sessionMemset_budget_sat mmpl g W hG stk (pos_of_extHookStack_le hle))
  memset_region stk _ _ := hook_placed_rocl_ok
    (hookSat_withStack_of_hookSat (cliExternsPlaced_memsetRegion_budget_sat mmpl g W hG) stk)
  session_memset_region stk _ _ := hook_placed_rocl_ok
    (hookSat_withStack_of_hookSat (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG) stk)

theorem allocContractsFsPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.AllocContractsFsPlaced A lim
      (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  obtain ⟨fMs, hfMs, hMsLibc, hMsSess, hMsReg, hMsSessReg, hMsVm, hMsFs, _⟩ := hG.memset
  obtain ⟨fMc, hfMc, hMcLibc, hMcSess, hMcReg, hMcSessReg, _, hMcRO, hMcVm, hMcFs, _⟩ := hG.memcpy
  have hMsEq := cliGhostExterns_memset_some g (cliExternsPlaced mmpl W) hfMs
  have hMcEq := cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hfMc
  exact
    { alloc := hook_placed_rocl_ok
        ⟨g.alloc, cliGhostExterns_alloc g _,
          (hookOk_rustAllocWithStack hG.alloc allocHookStack_le_extHookStack extHookStack_le).keepsFs
            hG.alloc_fs⟩
      dealloc := hook_placed_rocl_ok
        ⟨g.dealloc, cliGhostExterns_dealloc g _,
          (hookOk_rustDeallocExternWithStack hG.dealloc allocHookStack_le_extHookStack
            extHookStack_le).keepsFs hG.dealloc_fs⟩
      realloc := hook_placed_rocl_ok
        ⟨g.realloc, cliGhostExterns_realloc g _,
          (hookOk_rustReallocExternWithStack hG.realloc allocHookStack_le_extHookStack
            extHookStack_le).keepsFs hG.realloc_fs⟩
      shim stk _ _ := hook_placed_rocl_ok
        ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq),
          (hookOk_withStack (hookOk_withVmPreserved sessionShim_hookOk hookNoop_vm) stk).keepsFs
            hookNoop_fs⟩
      memcpy stk _ _ := hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withVmPreserved (hMcLibc stk) hMcVm).keepsFs hMcFs⟩
      session_memcpy stk _ _ := hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withVmPreserved (hMcSess stk) hMcVm).keepsFs hMcFs⟩
      memcpy_region stk _ _ := hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack (hookOk_withVmPreserved hMcReg hMcVm) stk).keepsFs hMcFs⟩
      session_memcpy_region stk _ _ := hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack (hookOk_withVmPreserved hMcSessReg hMcVm) stk).keepsFs hMcFs⟩
      memset stk hle _ := hook_placed_rocl_ok
        ⟨fMs, hMsEq,
          (hookOk_withVmPreserved (hMsLibc stk (pos_of_extHookStack_le hle)) hMsVm).keepsFs hMsFs⟩
      session_memset stk hle _ := hook_placed_rocl_ok
        ⟨fMs, hMsEq,
          (hookOk_withVmPreserved (hMsSess stk (pos_of_extHookStack_le hle)) hMsVm).keepsFs hMsFs⟩
      memset_region stk _ _ := hook_placed_rocl_ok
        ⟨fMs, hMsEq, (hookOk_withStack (hookOk_withVmPreserved hMsReg hMsVm) stk).keepsFs hMsFs⟩
      session_memset_region stk _ _ := hook_placed_rocl_ok
        ⟨fMs, hMsEq,
          (hookOk_withStack (hookOk_withVmPreserved hMsSessReg hMsVm) stk).keepsFs hMsFs⟩
      session_memcpy_region_ro stk _ _ := hook_placed_rocl_ok
        ⟨fMc, hMcEq, (hookOk_withStack (hookOk_withVmPreserved hMcRO hMcVm) stk).keepsFs hMcFs⟩ }

/-- Constructs `AllocContractsXCliPlaced A lim H` from `HookSat H` witnesses for allocator, shim, and
`libc` memory hooks. -/
theorem allocContractsXCliPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSymCli sessionShimBudgetSpec)
    (hmemcpy : ∀ stk : Nat, HookSat H memcpyName (withVmPreserved (libcMemcpySpec stk)))
    (hsessMemcpy : ∀ stk : Nat, HookSat H memcpyName (sessionMemcpyBudgetSpec stk))
    (hmemcpyReg : HookSat H memcpyName (withVmPreserved memcpyRegionSpec))
    (hsessMemcpyReg : HookSat H memcpyName sessionMemcpyRegionBudgetSpec)
    (hmemset : ∀ stk : Nat, 0 < stk → HookSat H memsetName (withVmPreserved (libcMemsetSpec stk)))
    (hsessMemset : ∀ stk : Nat, 0 < stk → HookSat H memsetName (sessionMemsetBudgetSpec stk))
    (hmemsetReg : HookSat H memsetName (withVmPreserved memsetRegionSpec))
    (hsessMemsetReg : HookSat H memsetName sessionMemsetRegionBudgetSpec) :
    LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.AllocContractsXCliPlaced A lim H where
  alloc := by
    rcases halloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok
      ⟨f, hf, hookOk_rustAllocWithStack hok allocHookStack_le_extHookStack extHookStack_le⟩
  dealloc := by
    rcases hdealloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok
      ⟨f, hf, hookOk_rustDeallocExternWithStack hok allocHookStack_le_extHookStack extHookStack_le⟩
  realloc := by
    rcases hrealloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok
      ⟨f, hf, hookOk_rustReallocExternWithStack hok allocHookStack_le_extHookStack extHookStack_le⟩
  shim stk _ _ := hook_placed_rocl_ok (hookSat_withStack_of_hookSat hshim stk)
  memcpy stk _ _ := hook_placed_rocl_ok (hmemcpy stk)
  session_memcpy stk _ _ := hook_placed_rocl_ok (hsessMemcpy stk)
  memcpy_region stk _ _ := hook_placed_rocl_ok (hookSat_withStack_of_hookSat hmemcpyReg stk)
  session_memcpy_region stk _ _ := hook_placed_rocl_ok (hookSat_withStack_of_hookSat hsessMemcpyReg stk)
  memset stk hle _ := hook_placed_rocl_ok (hmemset stk (pos_of_extHookStack_le hle))
  session_memset stk hle _ := hook_placed_rocl_ok (hsessMemset stk (pos_of_extHookStack_le hle))
  memset_region stk _ _ := hook_placed_rocl_ok (hookSat_withStack_of_hookSat hmemsetReg stk)
  session_memset_region stk _ _ := hook_placed_rocl_ok (hookSat_withStack_of_hookSat hsessMemsetReg stk)

/-- Constructs `AllocContractsFsPlaced A lim H` when the allocator and `libc` hooks preserve
`State.fs`. -/
theorem allocContractsFsPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSymCli sessionShimBudgetSpec)
    (hmemcpy : ∀ stk : Nat, HookSat H memcpyName (withVmPreserved (libcMemcpySpec stk)))
    (hsessMemcpy : ∀ stk : Nat, HookSat H memcpyName (sessionMemcpyBudgetSpec stk))
    (hmemcpyReg : HookSat H memcpyName (withVmPreserved memcpyRegionSpec))
    (hsessMemcpyReg : HookSat H memcpyName sessionMemcpyRegionBudgetSpec)
    (hsessMemcpyRO : HookSat H memcpyName
      (withVmPreserved CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec))
    (hmemset : ∀ stk : Nat, 0 < stk → HookSat H memsetName (withVmPreserved (libcMemsetSpec stk)))
    (hsessMemset : ∀ stk : Nat, 0 < stk → HookSat H memsetName (sessionMemsetBudgetSpec stk))
    (hmemsetReg : HookSat H memsetName (withVmPreserved memsetRegionSpec))
    (hsessMemsetReg : HookSat H memsetName sessionMemsetRegionBudgetSpec)
    (hfs : ∀ sym ∈ [lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli,
        lsRustNoAllocShimSymCli, memcpyName, memsetName],
      ∀ f, H sym = some f → ∀ s : State, (f s).fs = s.fs) :
    LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.AllocContractsFsPlaced A lim H where
  alloc := by
    rcases halloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok ⟨f, hf,
      (hookOk_rustAllocWithStack hok allocHookStack_le_extHookStack extHookStack_le).keepsFs
        (hfs lsRustAllocSymCli (by decide) f hf)⟩
  dealloc := by
    rcases hdealloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok ⟨f, hf,
      (hookOk_rustDeallocExternWithStack hok allocHookStack_le_extHookStack extHookStack_le).keepsFs
        (hfs lsRustDeallocSymCli (by decide) f hf)⟩
  realloc := by
    rcases hrealloc with ⟨f, hf, hok⟩
    exact hook_placed_rocl_ok ⟨f, hf,
      (hookOk_rustReallocExternWithStack hok allocHookStack_le_extHookStack extHookStack_le).keepsFs
        (hfs lsRustReallocSymCli (by decide) f hf)⟩
  shim stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hshim stk)
      (hfs lsRustNoAllocShimSymCli (by decide))
  memcpy stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hmemcpy stk) (hfs memcpyName (by decide))
  session_memcpy stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hsessMemcpy stk) (hfs memcpyName (by decide))
  memcpy_region stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hmemcpyReg stk)
      (hfs memcpyName (by decide))
  session_memcpy_region stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hsessMemcpyReg stk)
      (hfs memcpyName (by decide))
  memset stk hle _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hmemset stk (pos_of_extHookStack_le hle))
      (hfs memsetName (by decide))
  session_memset stk hle _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hsessMemset stk (pos_of_extHookStack_le hle))
      (hfs memsetName (by decide))
  memset_region stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hmemsetReg stk)
      (hfs memsetName (by decide))
  session_memset_region stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hsessMemsetReg stk)
      (hfs memsetName (by decide))
  session_memcpy_region_ro stk _ _ := hook_placed_rocl_ok <|
    hookSat_keepsFs_of_hookSat (hookSat_withStack_of_hookSat hsessMemcpyRO stk)
      (hfs memcpyName (by decide))

/-! ## 5. Placed budget hook bundles at `cliGhostExterns` -/

theorem stage2ContractsMinPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hG : CliGhostAllocHooks M A lim g) :
    Stage2ContractsMinPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget.Stage2ContractsMinPlaced.of_hooks
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_sessionMemcpy_budget_sat mmpl g W hG extHookStack)

theorem codecHooksPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g) :
    CodecHooksPlaced M A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  shim := cliExternsPlaced_noAllocShim_budget_sat mmpl g W hG.shim_eq
  alloc := cliExternsPlaced_alloc_budget_sat mmpl g W hG
  realloc := cliExternsPlaced_realloc_budget_sat mmpl g W hG
  dealloc := cliExternsPlaced_dealloc_budget_sat mmpl g W hG
  memcpy := cliExternsPlaced_framelessMemcpy_budget_sat mmpl g W hG
  panic_alloc := cliGhostExterns_panic_handle_alloc_error mmpl g W
  panic_raw := cliGhostExterns_panic_handle_error mmpl g W

theorem publicApiDecHooksPlaced_of_hooks [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g)
    (hStrClone : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneBudgetSpec M A lim)) :
    PublicApiDecHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  shim := cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq
  alloc := cliExternsPlaced_alloc_budget_sat mmpl g W hG
  dealloc := cliExternsPlaced_dealloc_budget_sat mmpl g W hG
  memcpy := cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG
  stringClone := hStrClone
  handleError := cliGhostExterns_panic_handle_error mmpl g W
  expectFailed := cliGhostExterns_panic_option_expect_failed mmpl g W

theorem stage2ContractsMinPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSymCli sessionShimBudgetSpec)
    (hmemcpy : HookSat H memcpyName (sessionMemcpyBudgetSpec extHookStack)) :
    Stage2ContractsMinPlaced M A lim H :=
  LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget.Stage2ContractsMinPlaced.of_hooks halloc hdealloc hrealloc hshim hmemcpy

theorem codecHooksPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSymCli (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSymCli (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H memcpyName (withVmPreserved framelessMemcpySpec))
    (hPanicAlloc : H CryptoVerification.LibsignalTripleRatchet.Prost.lsHandleAllocErrorSym =
      some Rust.panicked)
    (hPanicRaw : H lsHandleErrorSym = some Rust.panicked) :
    CodecHooksPlaced M A lim H where
  shim := hshim
  alloc := halloc
  realloc := hrealloc
  dealloc := hdealloc
  memcpy := hmemcpy
  panic_alloc := hPanicAlloc
  panic_raw := hPanicRaw

theorem publicApiDecHooksPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSymCli sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSymCli (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSymCli (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H memcpyName sessionMemcpyRegionBudgetSpec)
    (hStrClone : HookSat H CryptoVerification.LibsignalPublicApi.MessageDecrypt.lsStringCloneSym
      (stringCloneBudgetSpec M A lim))
    (hHandleError : H lsHandleErrorSym = some Rust.panicked)
    (hExpectFailed :
      H CryptoVerification.LibsignalPublicApi.MessageDecrypt.lsExpectFailedSym =
        some Rust.panicked) :
    PublicApiDecHooksPlaced A lim H where
  shim := hshim
  alloc := halloc
  dealloc := hdealloc
  memcpy := hmemcpy
  stringClone := hStrClone
  handleError := hHandleError
  expectFailed := hExpectFailed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
