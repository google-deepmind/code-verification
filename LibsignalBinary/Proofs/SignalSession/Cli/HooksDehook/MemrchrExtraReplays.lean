/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostReplaysOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Card `CC-R0` (Row 1) — `memrchr` Route-`R0` `GhostRowReplayOn` (`HooksDehook.MemrchrExtraReplays`)

Cutover-2 `c`-card for `lsMemrchrSym` (`core::slice::memchr::memrchr`) on the Route-`R0`
(`WithLsRet.withLsRet` / `LsRetAddr624`) `.text.lib2` track (`MemrchrGhostReplaysOn.lean` stays
untouched):

1. **Row Anchor & `W`-Independent Ghost (`keepR_memrchr`, `memrchrSubProg`, `memrchrGhost`):**
   - `memrchrSubProg mpl := pureWordsProg (libsignalSessionLib.resolve mpl lsMemrchrSym) coreMemrchrWords`
     (`65` words = `260` B hull; the `2` panic blocks at `+0x104`/`+0x118` are never fetched under
     `masterMemrchrSpec.pre` and stay outside `keepR_memrchr`).
   - `memrchrGhost mpl mmpl` wraps `MemrchrGhostK.f3PureMemrchrGhostHookLs` (`P_real := emptyStdProg`,
     `fallback := memrchrHook`), so it has **zero `W : CliHooks` dependence**.
2. **State Preservation & `withLsRet` Consumer `HookOk` Arms (`0` layout premises):**
   - Unconditional `memrchrGhost_fs`, `memrchrGhost_fsT`, `memrchrGhost_vmPreserved`,
     `memrchrGhost_preserves_execFrozen`, and bounded-stack (`16 ≤ stk ≤ 2 ^ 64`) `withLsRet`
     consumer `HookOk` arms (`MainHops.memrchrSpec` and `CalleesRO.memrchrSpecRO`, plain,
     `withVmPreserved`, and `withAlloc`).
3. **Generic-`InvS` `GhostRowReplayOn` (`entryGuard := fun _ => True`, `F1` + `H1` compliant):**
   - `hCL` supplies `(memrchrSubProg mpl).CodeLoaded u.mem` at each intermediate call state `u`
     from `InvS u` (**H1**; never `s0.mem`), with `memrchrSubProg_codeLoaded_stripExecOutside_iff`
     bridging to `stripExecOutside (keepR_memrchr mpl) u.mem`.
   - `hRealHullNoExt` requires `externAt? pc = none` on `keepR_memrchr mpl pc = true` **only** on
     the de-hooked real program `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` (**F1**;
     zero `P_ghost` hull premise since `LsRetAddr624 (u.readReg64 .lr)` + `hKeep` discharges
     `keepR_memrchr mpl (u.readReg64 .lr) = false` directly from non-`.Exception`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrExtraReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced libsignalSessionLib lsFromUtf8Sym lsMemrchrSym memrchrHook)
open CryptoVerification.SignalSession.Cli.MainHops (memrchrSpec)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO (coreMemrchrWords)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ExecFrozen linkedCallHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (ExtraEntryGuard GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrCode
  (coreMemrchrWords_length pureWordsProg_memrchr_hasWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhost
  (withLsRet_withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostK
  (f3EmptyMemrchrGhostHookK_eq f3EmptyMemrchrGhostHookK_fs f3EmptyMemrchrGhostHookLs_eq
   f3EmptyMemrchrGhostHookLs_fs f3EmptyMemrchrGhostHookLs_fsT
   f3PureMemrchrGhostHookK f3PureMemrchrGhostHookLs
   f3PureMemrchrGhostHookLs_mainHopsMemrchr_budget_ok
   f3PureMemrchrGhostHookLs_mainHopsMemrchr_ok
   f3PureMemrchrGhostHookLs_memrchrRO_budget_ok
   f3PureMemrchrGhostHookLs_memrchrRO_ok
   f3PureMemrchrGhostHookLs_vmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrGhostReplaysOn
  (f3EmptyMemrchrGhostHookK_visitedIn f3EmptyMemrchrGhostHookLs_visitedIn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords
  (codeLoaded_stripExecOutside_of_keep)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (memrchrSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowSpec GhostRowSpecOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemrchrRowSpec
  (MemrchrRowSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_steps_lift_of_visitedIn_noExtern)

/-! ## 1. Row Anchor Definitions & `CodeLoaded` `stripExecOutside` Equivalence -/

/-- Byte length (`260` B = `65` words) of the active `coreMemrchrWords` hull. -/
@[expose] def memrchrHullByteLen : Nat := 260

/-- Kept-region byte predicate `[resolve mpl lsMemrchrSym, resolve mpl lsMemrchrSym + 260)`. -/
@[expose] def keepR_memrchr (mpl : Obj.MultiPlacement) (pc : BitVec 64) : Bool :=
  decide ((pc - libsignalSessionLib.resolve mpl lsMemrchrSym).toNat < memrchrHullByteLen)

theorem keepR_memrchr_entry (mpl : Obj.MultiPlacement) :
    keepR_memrchr mpl (libsignalSessionLib.resolve mpl lsMemrchrSym) = true := by
  unfold keepR_memrchr memrchrHullByteLen
  have hsub : libsignalSessionLib.resolve mpl lsMemrchrSym -
      libsignalSessionLib.resolve mpl lsMemrchrSym = 0#64 := by bv_omega
  rw [hsub]
  decide

/-- Pure `65`-word (`260`-byte) sub-program holding `coreMemrchrWords` at
    `libsignalSessionLib.resolve mpl lsMemrchrSym`. -/
@[expose] def memrchrSubProg (mpl : Obj.MultiPlacement) : Program :=
  pureWordsProg (libsignalSessionLib.resolve mpl lsMemrchrSym) coreMemrchrWords

private theorem pureWordsProg_base (entry : BitVec 64) (words : List (BitVec 32)) :
    (pureWordsProg entry words).base = entry := rfl

private theorem pureWordsProg_svc (entry : BitVec 64) (words : List (BitVec 32)) :
    (pureWordsProg entry words).svc = Syscall.standard := rfl

theorem memrchrSubProg_base (mpl : Obj.MultiPlacement) :
    (memrchrSubProg mpl).base = libsignalSessionLib.resolve mpl lsMemrchrSym :=
  pureWordsProg_base (libsignalSessionLib.resolve mpl lsMemrchrSym) coreMemrchrWords

theorem memrchrSubProg_svc (mpl : Obj.MultiPlacement) :
    (memrchrSubProg mpl).svc = Syscall.standard :=
  pureWordsProg_svc (libsignalSessionLib.resolve mpl lsMemrchrSym) coreMemrchrWords

theorem memrchrSubProg_externAt_none (mpl : Obj.MultiPlacement) (pc : BitVec 64) :
    (memrchrSubProg mpl).externAt? pc = none :=
  pureWordsProg_externAt_none (libsignalSessionLib.resolve mpl lsMemrchrSym) coreMemrchrWords pc

theorem memrchrSubProg_hasWords (mpl : Obj.MultiPlacement) :
    (memrchrSubProg mpl).hasWords (libsignalSessionLib.resolve mpl lsMemrchrSym) coreMemrchrWords :=
  pureWordsProg_memrchr_hasWords (libsignalSessionLib.resolve mpl lsMemrchrSym)

theorem memrchrSubProg_code_length (mpl : Obj.MultiPlacement) :
    (memrchrSubProg mpl).code.length = memrchrHullByteLen := by
  unfold memrchrSubProg memrchrHullByteLen pureWordsProg Program.ofWords
  rw [Program.length_flatMap_wordToBytesLE, coreMemrchrWords_length]

theorem keepR_memrchr_of_code_offset (mpl : Obj.MultiPlacement) {off : Nat}
    (hoff : off < (memrchrSubProg mpl).code.length) :
    keepR_memrchr mpl ((memrchrSubProg mpl).base + BitVec.ofNat 64 off) = true := by
  rw [memrchrSubProg_code_length] at hoff
  rw [memrchrSubProg_base]
  unfold keepR_memrchr
  have hsub : libsignalSessionLib.resolve mpl lsMemrchrSym + BitVec.ofNat 64 off -
      libsignalSessionLib.resolve mpl lsMemrchrSym = BitVec.ofNat 64 off := by bv_omega
  have hoff_lt : off < 2 ^ 64 := by
    have hb : memrchrHullByteLen = 260 := rfl
    omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]
  exact decide_eq_true hoff

theorem memrchrSubProg_codeLoaded_stripExecOutside {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (memrchrSubProg mpl).CodeLoaded mem) :
    (memrchrSubProg mpl).CodeLoaded (stripExecOutside (keepR_memrchr mpl) mem) :=
  codeLoaded_stripExecOutside_of_keep (fun _ hoff => keepR_memrchr_of_code_offset mpl hoff) hL

theorem memrchrSubProg_codeLoaded_of_stripExecOutside {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (memrchrSubProg mpl).CodeLoaded (stripExecOutside (keepR_memrchr mpl) mem)) :
    (memrchrSubProg mpl).CodeLoaded mem := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hk : keepR_memrchr mpl ((memrchrSubProg mpl).base + BitVec.ofNat 64 i) = true :=
    keepR_memrchr_of_code_offset mpl hi
  have hbyte := hL.byte_eq i hi
  have hperm := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [ProofLib.strip_read8] at hbyte
  rw [ProofLib.strip_perm_of_keep hk] at hperm
  rw [ProofLib.strip_isLazyFree] at hlf
  exact ⟨hbyte, hperm, hlf⟩

theorem memrchrSubProg_codeLoaded_stripExecOutside_iff {mpl : Obj.MultiPlacement} {mem : Memory} :
    (memrchrSubProg mpl).CodeLoaded (stripExecOutside (keepR_memrchr mpl) mem) ↔
      (memrchrSubProg mpl).CodeLoaded mem :=
  ⟨memrchrSubProg_codeLoaded_of_stripExecOutside, memrchrSubProg_codeLoaded_stripExecOutside⟩

/-- Route-`R0` (`withLsRet`) `W`-independent ghost hook for `lsMemrchrSym`. -/
@[expose] noncomputable def memrchrGhost [LibsignalPlacement]
    (mpl _mmpl : Obj.MultiPlacement) : State → State :=
  f3PureMemrchrGhostHookLs (keepR_memrchr mpl) (libsignalSessionLib.resolve mpl lsMemrchrSym)

/-- Spare `K`-narrowed (`memrchrSpecK`) `W`-independent ghost hook companion for `lsMemrchrSym`. -/
@[expose] noncomputable def memrchrGhostK (mpl _mmpl : Obj.MultiPlacement) : State → State :=
  f3PureMemrchrGhostHookK (keepR_memrchr mpl) (libsignalSessionLib.resolve mpl lsMemrchrSym)

/-- Block-`617` entry-state guard for Route-`R0` `lsMemrchrSym` (`True`: `LsRetAddr624` is extracted
    directly from non-`.Exception` at each call step). -/
@[expose] def memrchrEntryGuard (_mpl : Obj.MultiPlacement) (_s0 : State) : Prop :=
  True

/-! ## 2. State Preservation & `withLsRet` Consumer `HookOk` Arms (`0` Layout Premises) -/

theorem memrchrGhost_fs [LibsignalPlacement] (mpl mmpl : Obj.MultiPlacement) (s : State) :
    (memrchrGhost mpl mmpl s).fs = s.fs :=
  f3EmptyMemrchrGhostHookLs_fs (keepR_memrchr mpl) (memrchrSubProg mpl)
    (libsignalSessionLib.resolve mpl lsMemrchrSym) s

theorem memrchrGhost_fsT [LibsignalPlacement] (mpl mmpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (memrchrGhost mpl mmpl) :=
  f3EmptyMemrchrGhostHookLs_fsT (keepR_memrchr mpl) (memrchrSubProg mpl)
    (libsignalSessionLib.resolve mpl lsMemrchrSym)

theorem memrchrGhost_vmPreserved [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (s : State) :
    VmPreserved s (memrchrGhost mpl mmpl s) :=
  f3PureMemrchrGhostHookLs_vmPreserved (keepR_memrchr mpl)
    (libsignalSessionLib.resolve mpl lsMemrchrSym) s

theorem memrchrGhost_mainHopsMemrchr_ok [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (stk : Nat)
    (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhost mpl mmpl) (withLsRet (memrchrSpec stk)) :=
  f3PureMemrchrGhostHookLs_mainHopsMemrchr_ok (keepR_memrchr mpl)
    (libsignalSessionLib.resolve mpl lsMemrchrSym) stk hlo hhi

theorem memrchrGhost_mainHopsMemrchr_withVmPreserved_ok [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (stk : Nat)
    (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhost mpl mmpl) (withVmPreserved (withLsRet (memrchrSpec stk))) :=
  hookOk_withVmPreserved (memrchrGhost_mainHopsMemrchr_ok mpl mmpl stk hlo hhi)
    (memrchrGhost_vmPreserved mpl mmpl)

theorem memrchrGhost_mainHopsMemrchr_withAlloc_ls_ok [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhost mpl mmpl) (withAlloc A lim (withLsRet (memrchrSpec stk))) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (memrchrGhost_mainHopsMemrchr_withVmPreserved_ok mpl mmpl stk hlo hhi)

theorem memrchrGhost_mainHopsMemrchr_budget_ok [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (stk : Nat)
    (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhost mpl mmpl) (withLsRet (withVmPreserved (memrchrSpec stk))) :=
  f3PureMemrchrGhostHookLs_mainHopsMemrchr_budget_ok (keepR_memrchr mpl)
    (libsignalSessionLib.resolve mpl lsMemrchrSym) stk hlo hhi

theorem memrchrGhost_mainHopsMemrchr_withAlloc_ok [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhost mpl mmpl) (withLsRet (withAlloc A lim (memrchrSpec stk))) := by
  rw [withLsRet_withAlloc]
  exact memrchrGhost_mainHopsMemrchr_withAlloc_ls_ok mpl mmpl A lim stk hlo hhi

theorem memrchrGhost_memrchrRO_ok [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (stk : Nat)
    (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhost mpl mmpl) (withLsRet (memrchrSpecRO stk)) :=
  f3PureMemrchrGhostHookLs_memrchrRO_ok (keepR_memrchr mpl)
    (libsignalSessionLib.resolve mpl lsMemrchrSym) stk hlo hhi

theorem memrchrGhost_memrchrRO_withVmPreserved_ok [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (stk : Nat)
    (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhost mpl mmpl) (withVmPreserved (withLsRet (memrchrSpecRO stk))) :=
  hookOk_withVmPreserved (memrchrGhost_memrchrRO_ok mpl mmpl stk hlo hhi)
    (memrchrGhost_vmPreserved mpl mmpl)

theorem memrchrGhost_memrchrRO_withAlloc_ls_ok [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhost mpl mmpl) (withAlloc A lim (withLsRet (memrchrSpecRO stk))) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (memrchrGhost_memrchrRO_withVmPreserved_ok mpl mmpl stk hlo hhi)

theorem memrchrGhost_memrchrRO_budget_ok [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (stk : Nat)
    (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhost mpl mmpl) (withLsRet (withVmPreserved (memrchrSpecRO stk))) :=
  f3PureMemrchrGhostHookLs_memrchrRO_budget_ok (keepR_memrchr mpl)
    (libsignalSessionLib.resolve mpl lsMemrchrSym) stk hlo hhi

theorem memrchrGhost_memrchrRO_withAlloc_ok [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat) (hlo : 16 ≤ stk) (hhi : stk ≤ 2 ^ 64) :
    HookOk (memrchrGhost mpl mmpl) (withLsRet (withAlloc A lim (memrchrSpecRO stk))) := by
  rw [withLsRet_withAlloc]
  exact memrchrGhost_memrchrRO_withAlloc_ls_ok mpl mmpl A lim stk hlo hhi

/-! ## 3. `ExecFrozen` Preservation & Generic-`InvS` `GhostRowReplayOn` -/

private theorem linkedCallHook_preserves_execFrozen {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hfb : ∀ s : State, ExecFrozen s.mem → ExecFrozen (fallback s).mem)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem := by
  classical
  unfold linkedCallHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
    · change ExecFrozen (fallback u).mem
      exact hfb u hfr
  · exact hfr

private theorem memrchrHook_mem (s : State) : (memrchrHook s).mem = s.mem := by
  have heq : memrchrHook s =
      (if (!s.mem.canRead (s.readReg64 .x1) (s.readReg64 .x2).toNat) = true then
        CryptoVerification.SignalSession.unmodelled "memrchr: unreadable bytes" s
      else
        match ((List.range (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat).length).filter
          fun i => (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat)[i]? ==
            some ((s.readReg64 .x0).setWidth 8)).getLast? with
        | some i => retHook (fun st => (st.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s
        | none => retHook (fun st => st.writeReg64 .x0 0#64) s) := rfl
  rw [heq]
  split
  · rfl
  · split <;> rfl

theorem memrchrGhost_preserves_execFrozen [LibsignalPlacement] (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (memrchrGhost mpl mmpl u).mem := by
  unfold memrchrGhost f3PureMemrchrGhostHookLs
  rw [f3EmptyMemrchrGhostHookLs_eq]
  exact linkedCallHook_preserves_execFrozen
    (fun s hs => by rw [memrchrHook_mem]; exact hs) hfr

theorem memrchrGhostK_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (memrchrGhostK mpl mmpl u).mem := by
  unfold memrchrGhostK f3PureMemrchrGhostHookK
  rw [f3EmptyMemrchrGhostHookK_eq]
  exact linkedCallHook_preserves_execFrozen
    (fun s hs => by rw [memrchrHook_mem]; exact hs) hfr

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u
  dsimp only [State.setPC] at hpc ⊢
  subst hpc
  rfl

private theorem realProg617_svc (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard :=
  rfl

private theorem emptyStdProg_svc : emptyStdProg.svc = Syscall.standard :=
  rfl

private theorem emptyStdProg_externAt (pc : BitVec 64) :
    emptyStdProg.externAt? pc = none :=
  rfl

/-- **Artifact 2a (`CC-R0`, Row 1) — Generic-`InvS` `GhostRowReplayOn` for `lsMemrchrSym`:**
    Route `R0` (`entryGuard := fun _ => True`), extracting `LsRetAddr624 (u.readReg64 .lr)` from
    non-`.Exception` at each call step and requiring `externAt? pc = none` on `keepR_memrchr mpl`
    **only** on the de-hooked real program (`F1` + `H1` compliant). -/
theorem memrchrGhost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (memrchrSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_memrchr mpl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memrchr mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsMemrchrSym (fun _ => True)
      (memrchrGhost mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨memrchrGhost_preserves_execFrozen mpl mmpl hfr, memrchrGhost_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealHullNoExt W (keepR_memrchr_entry mpl), ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hCodeStrip :
        (memrchrSubProg mpl).CodeLoaded (stripExecOutside (keepR_memrchr mpl) u.mem) :=
      memrchrSubProg_codeLoaded_stripExecOutside (hCL u hInvU)
    obtain ⟨_, _, hfr_fu, hfs_fu, hvis⟩ :=
      f3EmptyMemrchrGhostHookLs_visitedIn
        (keepR := keepR_memrchr mpl)
        (P_sub := memrchrSubProg mpl)
        (entryTarget := libsignalSessionLib.resolve mpl lsMemrchrSym)
        (memrchrSubProg_svc mpl)
        (memrchrSubProg_externAt_none mpl)
        (memrchrSubProg_hasWords mpl)
        hKeep
        hrun
        hnoex
        hfr
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (libsignalSessionLib.resolve mpl lsMemrchrSym))
          (memrchrGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_memrchr mpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    rw [setPC_eq_self_of_pc_eq hpc] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (memrchrGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- Spare `K`-narrowed (`memrchrGhostK`) `GhostRowReplayOn` companion (`entryGuard := fun _ => True`,
    zero `hKeep` premise; spare only per `REV-PILOT` N2). -/
theorem memrchrGhostK_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (memrchrSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memrchr mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsMemrchrSym (fun _ => True)
      (memrchrGhostK mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨memrchrGhostK_preserves_execFrozen mpl mmpl hfr,
     f3EmptyMemrchrGhostHookK_fs (keepR_memrchr mpl) (memrchrSubProg mpl)
       (libsignalSessionLib.resolve mpl lsMemrchrSym) u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealHullNoExt W (keepR_memrchr_entry mpl), ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hCodeStrip :
        (memrchrSubProg mpl).CodeLoaded (stripExecOutside (keepR_memrchr mpl) u.mem) :=
      memrchrSubProg_codeLoaded_stripExecOutside (hCL u hInvU)
    obtain ⟨_, _, hfr_fu, hfs_fu, hvis⟩ :=
      f3EmptyMemrchrGhostHookK_visitedIn
        (keepR := keepR_memrchr mpl)
        (P_sub := memrchrSubProg mpl)
        (entryTarget := libsignalSessionLib.resolve mpl lsMemrchrSym)
        (memrchrSubProg_svc mpl)
        (memrchrSubProg_externAt_none mpl)
        (memrchrSubProg_hasWords mpl)
        hrun
        hnoex
        hfr
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (libsignalSessionLib.resolve mpl lsMemrchrSym))
          (memrchrGhostK mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_memrchr mpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    rw [setPC_eq_self_of_pc_eq hpc] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (memrchrGhostK mpl mmpl u) hInvU hkf hfs_fu⟩

/-! ## 4. `MemrchrRowSpec`, `GhostRowSpecOk`, `GhostRowOk` & `ExtraEntryGuard` Helpers -/

/-- Unconditional `MemrchrRowSpec` (`withLsRet` outermost, `extHookStack ≤ stk ≤ 2 ^ 64`) for
    `memrchrGhost mpl mmpl` (`0` layout or memory premises). -/
theorem memrchrGhost_memrchrRowSpec [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) :
    MemrchrRowSpec (memrchrGhost mpl mmpl) :=
  MemrchrRowSpec.of_ls_vm
    (fun stk hlo hhi =>
      memrchrGhost_mainHopsMemrchr_ok mpl mmpl stk
        (Nat.le_trans (by decide : 16 ≤ extHookStack) hlo) hhi)
    (fun stk hlo hhi =>
      memrchrGhost_memrchrRO_ok mpl mmpl stk
        (Nat.le_trans (by decide : 16 ≤ extHookStack) hlo) hhi)
    (memrchrGhost_vmPreserved mpl mmpl)

/-- **Artifact 1 (`CC-R0`, Row 1):** Unconditional `GhostRowSpecOk lsMemrchrSym (memrchrGhost mpl mmpl)`
    for all `(mpl, mmpl)` (`0` layout or memory premises). -/
theorem memrchrGhost_rowSpecOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) :
    GhostRowSpecOk lsMemrchrSym (memrchrGhost mpl mmpl) where
  fs_eq := memrchrGhost_fs mpl mmpl
  fsT := memrchrGhost_fsT mpl mmpl
  rowSpec := by
    unfold ExtraRowSpec
    have hd1 : (lsMemrchrSym == "bcmp") = false := by decide
    have hd2 : (lsMemrchrSym == "strlen") = false := by decide
    have hd3 : (lsMemrchrSym == "memmove") = false := by decide
    have hd4 : (lsMemrchrSym == lsFromUtf8Sym) = false := by decide
    have hd5 : (lsMemrchrSym == lsMemrchrSym) = true := by decide
    simp only [hd1, hd2, hd3, hd4, hd5, Bool.false_eq_true, ↓reduceIte]
    exact memrchrGhost_memrchrRowSpec mpl mmpl

/-- **Full per-row `GhostRowOk` bundle (`GhostRowSpecOk` ∧ `GhostRowReplayOn`)** for `lsMemrchrSym`
    (`entryGuard := fun _ => True`). -/
theorem memrchrGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (memrchrSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_memrchr mpl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memrchr mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl InvS EG lsMemrchrSym (fun _ => True)
      (memrchrGhost mpl mmpl) :=
  ⟨memrchrGhost_rowSpecOk mpl mmpl,
   memrchrGhost_rowReplayOn mpl mmpl InvS EG hCL hInvKeep hKeep hRealHullNoExt⟩

theorem extraEntryGuard_memrchr_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf lsMemrchrSym s0 ↔ memrchrEntryGuard mpl s0) :
    guardOf lsMemrchrSym s0 :=
  hGuardEq.mpr trivial

theorem extraEntryGuard_singleton_memrchr [LibsignalPlacement]
    {mpl mmpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hg : g.extra = [(lsMemrchrSym, memrchrGhost mpl mmpl)])
    (hGuardEq : guardOf lsMemrchrSym s0 ↔ memrchrEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 := by
  intro sym _ _ hLook
  rw [hg] at hLook
  simp only [List.lookup] at hLook
  by_cases hSym : (sym == lsMemrchrSym) = true
  · have hEq := eq_of_beq hSym
    subst hEq
    exact hGuardEq.mpr trivial
  · simp [hSym] at hLook

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrExtraReplays
