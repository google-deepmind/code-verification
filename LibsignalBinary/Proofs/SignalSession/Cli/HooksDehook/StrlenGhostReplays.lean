/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Card CC-LIBC (`strlen`) — `"strlen"` `CliGhostHooks.extra` SWAR-Padded Specs & `GhostRowReplayOn` (`HooksDehook.StrlenGhostReplays`)

Cutover-2 `c`-card assembly for the `libc.a` `"strlen"` row (`22` words = `88` B `muslStrlenWords`
directly at `strlenEntry mpl := libsignalSessionLib.resolve mpl "strlen"`), modeled on the `L1-c`
pilot (`HooksDehook.BcmpGhostReplays`):

1. **`W`-Independent Ghost Hook & SWAR-Padded `HookOk` Suite (`§1`–`§2`):**
   - Defines `strlenEntry mpl`, `keepR_strlen mpl := keepStrlenRange (strlenEntry mpl)`,
     `strlenSubProg mpl := pureWordsProg (strlenEntry mpl) muslStrlenWords`, and
     `strlenGhost mpl _mmpl := f3EmptyStrlenGhostHook (keepR_strlen mpl) (strlenSubProg mpl)
     (strlenEntry mpl)` (`W`-free: `P_real := emptyStdProg`, `fallback := strlenHook`).
   - Discharges `haddr : (strlenEntry mpl).toNat + strlenByteLen ≤ 2 ^ 64` internally via case-split
     against `(strlenSubProg mpl).CodeLoaded.no_wrap`, yielding **unconditional** (`0` layout or
     memory premises) `strlenGhost_vmPreserved`, `strlenGhost_fs`, `strlenGhost_fsT`, and all 7
     `withStrlenPadRO` (`= ArgvPad.strlenSpecROSat` under `withVmPreserved` by `rfl`) `HookOk`
     arms matching the `CC-ROWSPEC` narrowed `StrlenRowSpec`.
2. **`ExecFrozen` Preservation & Generic-`InvS` `GhostRowReplayOn` (`§3`):**
   - Proves `strlenGhost_rowReplayOn` over arbitrary `InvS : State → Prop` (`hCL` at intermediate
     call state `u` per `H1`; entry-excluded `pc ≠ strlenEntry mpl` ghost-program premise per `F1`;
     derives `haddr` directly from `hCodeU.no_wrap`), plus the `C4` interior-stub variant
     `strlenGhost_rowReplayOn_of_interior` and `K`-narrowed spare `strlenGhostK_rowReplayOn`.

## Scope Disclosures (`REV-PILOT` N1–N3)
- **N1 (post-Cutover-2 only):** `hRealHullNoExt` requires `"strlen"` to be removed from
  `cliHookTablePlaced` (`C2ExternTableFacts.realRxNoExtern`, `Lib2LayoutFacts.lean @a230f2671b:317`).
- **N2 (`K` replay spare):** `strlenGhostK_rowReplayOn` is an unguarded `K`-route spare; the
  Cutover-2 `ExtraListOk` route uses `strlenGhost` + `strlenEntryGuard`.
- **N3 (singleton vs. multi-row guard):** `ElfStrlenEntryGuard.extraEntryGuard_singleton_strlen`
  covers singleton `g.extra`; multi-row `g.extra` uses `extraEntryGuard_strlen_arm` per row.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open ProofLib.StdStartup (muslStrlenWords)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced libsignalSessionLib strlenHook)
open CryptoVerification.SignalSession.Cli.MainHops (strlenSpec)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.Fine (strlenHook_vmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (withStrlenPadRO)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen keepFsTrace linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (
  GhostRowOk GhostRowReplayOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode (
  hookOk_mainStrlen_padRO_of_master hookOk_strlenSpecRO_padRO_of_master
  masterStrlenSpec pureWordsProg_strlen_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost (
  KeepCoversStrlen keepCoversStrlen_keepStrlenRange keepFsTrace_strlenHook_eq
  keepFsTrace_strlenHook_master_ok keepStrlenRange strlenByteLen strlenByteLen_eq
  strlenGhostHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostK (
  f3EmptyStrlenGhostHook f3EmptyStrlenGhostHookK
  f3EmptyStrlenGhostHook_eq
  f3EmptyStrlenGhostHook_fs f3EmptyStrlenGhostHookK_fs
  f3EmptyStrlenGhostHook_fsT f3EmptyStrlenGhostHookK_fsT
  f3EmptyStrlenGhostHook_master_ok
  f3EmptyStrlenGhostHook_preserves_execFrozen f3EmptyStrlenGhostHookK_preserves_execFrozen
  f3EmptyStrlenGhostHook_visitedIn f3EmptyStrlenGhostHookK_visitedIn
  f3EmptyStrlenGhostHook_vmPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenLrTrap (
  StrlenEntryGuard
  f3EmptyStrlenGhostHook_keepLr_false_after_hook_of_codeLoaded_u
  keepStrlenRange_entry keepStrlenRange_iff
  strlen_codeLoaded_stripExecOutside_of_prog
  strlen_keepLr_false_after_hook_of_codeLoaded_u
  trapHook_f3EmptyStrlenGhostHook_of_cover
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (TrapHook)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved withAlloc
)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (strlenSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (
  ExtraRowSpec GhostRowSpecOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StrlenRowSpec (StrlenRowSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_steps_lift_of_visitedIn_noExtern
)

/-! ## 1. `"strlen"` Sub-Program, Kept Hull, `CodeLoaded` Strip Equivalence & Entry Guard -/

/-- Placed entry address of `"strlen"` in `libsignalSessionLib` (the 22-word `muslStrlenWords` block
    starts directly at `strlenEntry mpl`, with zero leading fallthrough prefix). -/
@[expose] def strlenEntry (mpl : Obj.MultiPlacement) : BitVec 64 :=
  libsignalSessionLib.resolve mpl "strlen"

/-- Kept-region byte predicate `[strlenEntry mpl, strlenEntry mpl + 88)` for `"strlen"`. -/
@[expose] def keepR_strlen (mpl : Obj.MultiPlacement) : BitVec 64 → Bool :=
  keepStrlenRange (strlenEntry mpl)

/-- `"strlen"`'s resolved entry address lies inside `keepR_strlen mpl`. -/
theorem keepR_strlen_entry (mpl : Obj.MultiPlacement) :
    keepR_strlen mpl (libsignalSessionLib.resolve mpl "strlen") = true :=
  keepStrlenRange_entry (strlenEntry mpl)

theorem keepCoversStrlen_keepR_strlen (mpl : Obj.MultiPlacement) :
    KeepCoversStrlen (keepR_strlen mpl) (strlenEntry mpl) :=
  keepCoversStrlen_keepStrlenRange (strlenEntry mpl)

/-- Pure 22-word (`88`-byte) sub-program holding `muslStrlenWords` at `strlenEntry mpl`. -/
@[expose] def strlenSubProg (mpl : Obj.MultiPlacement) : Program :=
  pureWordsProg (strlenEntry mpl) muslStrlenWords

theorem strlenSubProg_base (mpl : Obj.MultiPlacement) :
    (strlenSubProg mpl).base = strlenEntry mpl := by
  dsimp only [strlenSubProg, pureWordsProg, Program.ofWords]

theorem strlenSubProg_svc (mpl : Obj.MultiPlacement) :
    (strlenSubProg mpl).svc = Syscall.standard := by
  dsimp only [strlenSubProg, pureWordsProg, Program.ofWords]

theorem strlenSubProg_externAt_none (mpl : Obj.MultiPlacement) (pc : BitVec 64) :
    (strlenSubProg mpl).externAt? pc = none := by
  dsimp only [strlenSubProg, pureWordsProg, Program.ofWords]
  rfl

theorem strlenSubProg_hasWords (mpl : Obj.MultiPlacement) :
    (strlenSubProg mpl).hasWords (strlenEntry mpl) muslStrlenWords :=
  pureWordsProg_strlen_hasWords (strlenEntry mpl)

theorem strlenSubProg_code_length (mpl : Obj.MultiPlacement) :
    (strlenSubProg mpl).code.length = strlenByteLen := by
  dsimp only [strlenSubProg, pureWordsProg, Program.ofWords]
  rfl

/-- Any `CodeLoaded` witness for `strlenSubProg mpl` immediately implies the 64-bit non-wrap bound
    `(strlenEntry mpl).toNat + strlenByteLen ≤ 2 ^ 64`. -/
theorem strlenEntry_no_wrap_of_codeLoaded {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (strlenSubProg mpl).CodeLoaded mem) :
    (strlenEntry mpl).toNat + strlenByteLen ≤ 2 ^ 64 := by
  have h := hL.no_wrap
  rwa [strlenSubProg_base, strlenSubProg_code_length] at h

theorem keepR_strlen_of_code_offset (mpl : Obj.MultiPlacement) {off : Nat}
    (hoff : off < (strlenSubProg mpl).code.length) :
    keepR_strlen mpl ((strlenSubProg mpl).base + BitVec.ofNat 64 off) = true := by
  rw [strlenSubProg_code_length] at hoff
  rw [strlenSubProg_base]
  dsimp only [keepR_strlen]
  rw [keepStrlenRange_iff]
  have hsub : (strlenEntry mpl + BitVec.ofNat 64 off) - strlenEntry mpl =
      BitVec.ofNat 64 off := by bv_omega
  have hoff_lt : off < 2 ^ 64 := by
    rw [strlenByteLen_eq] at hoff
    omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]
  exact hoff

/-- Forward `CodeLoaded` projection onto `stripExecOutside (keepR_strlen mpl) mem`. -/
theorem strlenSubProg_codeLoaded_stripExecOutside {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (strlenSubProg mpl).CodeLoaded mem) :
    (strlenSubProg mpl).CodeLoaded (stripExecOutside (keepR_strlen mpl) mem) :=
  strlen_codeLoaded_stripExecOutside_of_prog (fun _ hoff => keepR_strlen_of_code_offset mpl hoff) hL

/-- Reverse `CodeLoaded` projection from `stripExecOutside (keepR_strlen mpl) mem` back to `mem`
    (bridging `Lib2LayoutFacts.f3CodeInv_rxWords_codeLoaded_strip` `@a230f2671b:203-215` to `H1`'s
    `(strlenSubProg mpl).CodeLoaded u.mem`). -/
theorem strlenSubProg_codeLoaded_of_stripExecOutside {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (strlenSubProg mpl).CodeLoaded (stripExecOutside (keepR_strlen mpl) mem)) :
    (strlenSubProg mpl).CodeLoaded mem := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hk : keepR_strlen mpl ((strlenSubProg mpl).base + BitVec.ofNat 64 i) = true :=
    keepR_strlen_of_code_offset mpl hi
  have hbyte := hL.byte_eq i hi
  have hperm := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [ProofLib.strip_read8] at hbyte
  rw [ProofLib.strip_perm_of_keep hk] at hperm
  rw [ProofLib.strip_isLazyFree] at hlf
  exact ⟨hbyte, hperm, hlf⟩

theorem strlenSubProg_codeLoaded_stripExecOutside_iff {mpl : Obj.MultiPlacement} {mem : Memory} :
    (strlenSubProg mpl).CodeLoaded (stripExecOutside (keepR_strlen mpl) mem) ↔
      (strlenSubProg mpl).CodeLoaded mem :=
  ⟨strlenSubProg_codeLoaded_of_stripExecOutside, strlenSubProg_codeLoaded_stripExecOutside⟩

/-- `W`-independent ghost hook for `"strlen"` (`CliGhostHooks.extra` entry
    `("strlen", strlenGhost mpl mmpl)`). Uses `StrlenGhostK.f3EmptyStrlenGhostHook`
    (`P_real := emptyStdProg`, `fallback := strlenHook`), never capturing `W : CliHooks`. -/
@[expose] noncomputable def strlenGhost (mpl _mmpl : Obj.MultiPlacement) : State → State :=
  f3EmptyStrlenGhostHook (keepR_strlen mpl) (strlenSubProg mpl) (strlenEntry mpl)

/-- `K`-narrowed `W`-independent ghost hook companion for `"strlen"`. -/
@[expose] noncomputable def strlenGhostK (mpl _mmpl : Obj.MultiPlacement) : State → State :=
  f3EmptyStrlenGhostHookK (keepR_strlen mpl) (strlenSubProg mpl) (strlenEntry mpl)

/-- Block-`617` entry-state `lr` guard for `"strlen"`:
    `keepR_strlen mpl (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ resolve mpl "strlen"`. -/
@[expose] def strlenEntryGuard (mpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  StrlenEntryGuard (strlenEntry mpl) (libsignalSessionLib.resolve mpl "strlen") s0

theorem strlenEntryGuard_iff (mpl : Obj.MultiPlacement) (s0 : State) :
    strlenEntryGuard mpl s0 ↔
      keepR_strlen mpl (s0.readReg64 .lr) = false ∧
        s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl "strlen" :=
  Iff.rfl

/-! ## 2. Unconditional `VmPreserved`, `fs`/`HookFsTraced` & SWAR-Padded `HookOk` Suite -/

private theorem not_activeRealRun_of_not_no_wrap {mpl : Obj.MultiPlacement}
    (hn : ¬ ((strlenEntry mpl).toNat + strlenByteLen ≤ 2 ^ 64)) (u : State) :
    ¬ ActiveRealRun (keepR_strlen mpl) emptyStdProg (strlenSubProg mpl) (strlenEntry mpl) u :=
  fun hReal => hn (strlenEntry_no_wrap_of_codeLoaded hReal.2.2.1)

theorem strlenGhost_fs (mpl mmpl : Obj.MultiPlacement) (s : State) :
    (strlenGhost mpl mmpl s).fs = s.fs :=
  f3EmptyStrlenGhostHook_fs (keepR_strlen mpl) (strlenSubProg mpl) (strlenEntry mpl) s

theorem strlenGhost_fsT (mpl mmpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (strlenGhost mpl mmpl) :=
  f3EmptyStrlenGhostHook_fsT (keepR_strlen mpl) (strlenSubProg mpl) (strlenEntry mpl)

theorem strlenGhostK_fs (mpl mmpl : Obj.MultiPlacement) (s : State) :
    (strlenGhostK mpl mmpl s).fs = s.fs :=
  f3EmptyStrlenGhostHookK_fs (keepR_strlen mpl) (strlenSubProg mpl) (strlenEntry mpl) s

theorem strlenGhostK_fsT (mpl mmpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (strlenGhostK mpl mmpl) :=
  f3EmptyStrlenGhostHookK_fsT (keepR_strlen mpl) (strlenSubProg mpl) (strlenEntry mpl)

/-- Unconditional pointwise `VmPreserved` for `strlenGhost mpl mmpl` (`0` address-wrap premises:
    if `(strlenEntry mpl).toNat + 88 > 2 ^ 64`, `ActiveRealRun` is impossible by `CodeLoaded.no_wrap`
    and `strlenGhost` falls back to `strlenHook`). -/
theorem strlenGhost_vmPreserved (mpl mmpl : Obj.MultiPlacement) (s0 : State) :
    VmPreserved s0 (strlenGhost mpl mmpl s0) := by
  by_cases haddr : (strlenEntry mpl).toNat + strlenByteLen ≤ 2 ^ 64
  · exact f3EmptyStrlenGhostHook_vmPreserved
      (strlenSubProg_svc mpl) (strlenSubProg_externAt_none mpl)
      (strlenSubProg_hasWords mpl) haddr s0
  · classical
    dsimp only [strlenGhost]
    rw [f3EmptyStrlenGhostHook_eq]
    unfold strlenGhostHook linkedCallHook
    split
    · have hnReal := not_activeRealRun_of_not_no_wrap haddr s0
      simp only [hnReal, ↓reduceDIte, keepFsTrace_strlenHook_eq]
      exact strlenHook_vmPreserved s0
    · exact VmPreserved.refl s0

/-- Unconditional `HookOk (strlenGhost mpl mmpl) masterStrlenSpec` (`0` address-wrap premises). -/
theorem strlenGhost_master_ok (mpl mmpl : Obj.MultiPlacement) :
    HookOk (strlenGhost mpl mmpl) masterStrlenSpec := by
  by_cases haddr : (strlenEntry mpl).toNat + strlenByteLen ≤ 2 ^ 64
  · exact f3EmptyStrlenGhostHook_master_ok
      (strlenSubProg_svc mpl) (strlenSubProg_externAt_none mpl)
      (strlenSubProg_hasWords mpl) haddr
  · intro x R s0 hrun hpre hsp
    classical
    have hActPre : ActiveRealPre masterStrlenSpec s0 := ⟨hrun, hsp, x, R, hpre⟩
    have hnReal := not_activeRealRun_of_not_no_wrap haddr s0
    have heq : strlenGhost mpl mmpl s0 = keepFsTrace strlenHook s0 := by
      dsimp only [strlenGhost]
      rw [f3EmptyStrlenGhostHook_eq]
      unfold strlenGhostHook linkedCallHook
      simp only [hActPre, hnReal, ↓reduceDIte]
    rw [heq]
    exact keepFsTrace_strlenHook_master_ok x R s0 hrun hpre hsp

theorem strlenGhost_mainStrlen_padRO_ok (mpl mmpl : Obj.MultiPlacement) (stk : Nat := 4096) :
    HookOk (strlenGhost mpl mmpl) (withStrlenPadRO (strlenSpec stk)) :=
  hookOk_mainStrlen_padRO_of_master (strlenGhost_master_ok mpl mmpl) stk

theorem strlenGhost_mainStrlen_padRO_budget_ok (mpl mmpl : Obj.MultiPlacement) (stk : Nat := 4096) :
    HookOk (strlenGhost mpl mmpl) (withVmPreserved (withStrlenPadRO (strlenSpec stk))) :=
  hookOk_withVmPreserved (strlenGhost_mainStrlen_padRO_ok mpl mmpl stk)
    (strlenGhost_vmPreserved mpl mmpl)

theorem strlenGhost_mainStrlen_padRO_withAlloc_ok (mpl mmpl : Obj.MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhost mpl mmpl) (withAlloc A lim (withStrlenPadRO (strlenSpec stk))) :=
  hookOk_withAlloc_of_withVmPreserved A lim (strlenGhost_mainStrlen_padRO_budget_ok mpl mmpl stk)

theorem strlenGhost_strlenSpecRO_padRO_ok (mpl mmpl : Obj.MultiPlacement) (stk : Nat := 4096) :
    HookOk (strlenGhost mpl mmpl) (withStrlenPadRO (strlenSpecRO stk)) :=
  hookOk_strlenSpecRO_padRO_of_master (strlenGhost_master_ok mpl mmpl) stk

/-- `withVmPreserved (withStrlenPadRO (strlenSpecRO stk))` is definitionally (`rfl`) identical to
    `ArgvPad.strlenSpecROSat stk`. -/
theorem strlenGhost_strlenSpecRO_padRO_budget_ok (mpl mmpl : Obj.MultiPlacement)
    (stk : Nat := 4096) :
    HookOk (strlenGhost mpl mmpl) (withVmPreserved (withStrlenPadRO (strlenSpecRO stk))) :=
  hookOk_withVmPreserved (strlenGhost_strlenSpecRO_padRO_ok mpl mmpl stk)
    (strlenGhost_vmPreserved mpl mmpl)

theorem strlenGhost_strlenSpecRO_padRO_withAlloc_ok (mpl mmpl : Obj.MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhost mpl mmpl) (withAlloc A lim (withStrlenPadRO (strlenSpecRO stk))) :=
  hookOk_withAlloc_of_withVmPreserved A lim (strlenGhost_strlenSpecRO_padRO_budget_ok mpl mmpl stk)

theorem strlenGhost_strlenSpecROSat_withAlloc_ok (mpl mmpl : Obj.MultiPlacement)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhost mpl mmpl)
      (withAlloc A lim (withVmPreserved (withStrlenPadRO (strlenSpecRO stk)))) :=
  hookOk_withAlloc_withVmPreserved A lim (strlenGhost_strlenSpecRO_padRO_budget_ok mpl mmpl stk)

theorem strlenGhost_strlenRowSpec (mpl mmpl : Obj.MultiPlacement) :
    StrlenRowSpec (strlenGhost mpl mmpl) :=
  StrlenRowSpec.of_vm
    (fun stk => strlenGhost_mainStrlen_padRO_ok mpl mmpl stk)
    (fun stk => strlenGhost_strlenSpecRO_padRO_ok mpl mmpl stk)
    (strlenGhost_vmPreserved mpl mmpl)

theorem strlenGhost_rowSpecOk [LibsignalPlacement] (mpl mmpl : Obj.MultiPlacement) :
    GhostRowSpecOk "strlen" (strlenGhost mpl mmpl) where
  fs_eq := strlenGhost_fs mpl mmpl
  fsT := strlenGhost_fsT mpl mmpl
  rowSpec := by
    change ExtraRowSpec "strlen" (strlenGhost mpl mmpl)
    simpa [ExtraRowSpec] using strlenGhost_strlenRowSpec mpl mmpl

/-! ## 3. `ExecFrozen` Preservation & Generic-`InvS` `GhostRowReplayOn` (Artifact 2a) -/

theorem strlenGhost_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (strlenGhost mpl mmpl u).mem ∧ (strlenGhost mpl mmpl u).fs = u.fs :=
  f3EmptyStrlenGhostHook_preserves_execFrozen
    (keepR_strlen mpl) (strlenSubProg mpl) (strlenEntry mpl) hfr

theorem strlenGhostK_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (strlenGhostK mpl mmpl u).mem ∧ (strlenGhostK mpl mmpl u).fs = u.fs :=
  f3EmptyStrlenGhostHookK_preserves_execFrozen
    (keepR_strlen mpl) (strlenSubProg mpl) (strlenEntry mpl) hfr

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

/-- **Artifact 2a (`C11` §1.3, §6.2) — Generic-`InvS` `GhostRowReplayOn` for `"strlen"`:**
    - **F1 compliance:** `hRealHullNoExt` quantifies over `keepR_strlen mpl pc = true` **only** on
      the de-hooked real program `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`. On the
      ghost program `cliProgExtPlacedAt mpl EG 617 W`, `hGhostNoExtNe` strictly excludes
      `pc ≠ libsignalSessionLib.resolve mpl "strlen"`, matching STARTUP's
      `f3Row_ghostProg617_externAt_none_of_ne_entry` (`Lib2LayoutFacts.lean @a230f2671b:368`).
    - **H1 compliance:** `hCL` supplies `(strlenSubProg mpl).CodeLoaded u.mem` at the intermediate
      call state `u` from `InvS u` (never `s0.mem`), which also automatically discharges
      `haddr : (strlenEntry mpl).toNat + strlenByteLen ≤ 2 ^ 64` via `hCodeU.no_wrap`. -/
theorem strlenGhost_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (strlenSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "strlen") =
        some (strlenGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_strlen mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_strlen mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "strlen" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG "strlen" (strlenEntryGuard mpl) (strlenGhost mpl mmpl) where
  preserves_execFrozen := fun _ _ _ hfr => strlenGhost_preserves_execFrozen mpl mmpl hfr
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    right
    refine ⟨hRealHullNoExt W (keepR_strlen_entry mpl), ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (strlenSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hLrOut : keepR_strlen mpl (u.readReg64 .lr) = false :=
      f3EmptyStrlenGhostHook_keepLr_false_after_hook_of_codeLoaded_u
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_sub := strlenSubProg mpl)
        (keepR := keepR_strlen mpl)
        (entryTarget := strlenEntry mpl)
        (strlenSubProg_hasWords mpl)
        (keepCoversStrlen_keepR_strlen mpl)
        (fun _ hk hne => hGhostNoExtNe W hk hne)
        (Or.inr (hGhostAt W))
        hEntry.1
        hRetPc
        hNoExSf
        hNotHaltSf
        u
        hCodeU
        hStepsAfter
        hrun
        hkf
    have hCodeStrip :
        (strlenSubProg mpl).CodeLoaded (stripExecOutside (keepR_strlen mpl) u.mem) :=
      strlenSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨hvis, _, hfr_fu, hfs_fu⟩ :=
      f3EmptyStrlenGhostHook_visitedIn
        (keep := keepR_strlen mpl)
        (P_sub := strlenSubProg mpl)
        (entryTarget := strlenEntry mpl)
        (strlenSubProg_svc mpl)
        (strlenSubProg_externAt_none mpl)
        (strlenSubProg_hasWords mpl)
        (strlenEntry_no_wrap_of_codeLoaded hCodeU)
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (strlenEntry mpl))
          (strlenGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC (strlenEntry mpl) = u := setPC_eq_self_of_pc_eq hpc
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (strlenGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- `C4` interior-stub signature wrapper for `strlenGhost_rowReplayOn` (accepting split `hRealNone`
    at `stubPc` + `hInteriorGhost` with the `Or.inr` `TrapHook` interior-stub disjunct on
    `pc ≠ resolve mpl "strlen"`). -/
theorem strlenGhost_rowReplayOn_of_interior
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (strlenSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "strlen") =
        some (strlenGhost mpl mmpl))
    (hRealNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl "strlen") = none)
    (hInteriorGhost : ∀ (W : CliHooks) (pc : BitVec 64),
      keepR_strlen mpl pc = true → pc ≠ libsignalSessionLib.resolve mpl "strlen" →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none ∧
      ((cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ gStub, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some gStub ∧
          ∀ L : BitVec 64, keepR_strlen mpl L = true → TrapHook L gStub)) :
    GhostRowReplayOn mpl mmpl InvS EG "strlen" (strlenEntryGuard mpl) (strlenGhost mpl mmpl) where
  preserves_execFrozen := fun _ _ _ hfr => strlenGhost_preserves_execFrozen mpl mmpl hfr
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    have hRealHullNoExt : ∀ {pc : BitVec 64},
        keepR_strlen mpl pc = true →
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl "strlen"
      · rw [hEq]; exact hRealNone W
      · exact (hInteriorGhost W pc hk hEq).1
    have hRegExt : ∀ pc : BitVec 64, keepStrlenRange (strlenEntry mpl) pc = true →
        (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
          ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
            ∀ L, keepStrlenRange (strlenEntry mpl) L = true → TrapHook L f := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl "strlen"
      · rw [hEq]
        exact Or.inr ⟨strlenGhost mpl mmpl, hGhostAt W, fun _ hL =>
          trapHook_f3EmptyStrlenGhostHook_of_cover (strlenSubProg mpl)
            (keepCoversStrlen_keepR_strlen mpl) hL⟩
      · rcases (hInteriorGhost W pc hk hEq).2 with hNone | ⟨gStub, hSome, hTrap⟩
        · exact Or.inl hNone
        · exact Or.inr ⟨gStub, hSome, hTrap⟩
    right
    refine ⟨hRealNone W, ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (strlenSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hLrOut : keepR_strlen mpl (u.readReg64 .lr) = false :=
      strlen_keepLr_false_after_hook_of_codeLoaded_u
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_sub := strlenSubProg mpl)
        (entryTarget := strlenEntry mpl)
        (f_stub := strlenGhost mpl mmpl)
        (strlenSubProg_hasWords mpl)
        hRegExt
        (fun _ hL => trapHook_f3EmptyStrlenGhostHook_of_cover (strlenSubProg mpl)
          (keepCoversStrlen_keepR_strlen mpl) hL)
        hEntry.1
        hRetPc
        hNoExSf
        hNotHaltSf
        u
        hCodeU
        hStepsAfter
        hrun
        hkf
    have hCodeStrip :
        (strlenSubProg mpl).CodeLoaded (stripExecOutside (keepR_strlen mpl) u.mem) :=
      strlenSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨hvis, _, hfr_fu, hfs_fu⟩ :=
      f3EmptyStrlenGhostHook_visitedIn
        (keep := keepR_strlen mpl)
        (P_sub := strlenSubProg mpl)
        (entryTarget := strlenEntry mpl)
        (strlenSubProg_svc mpl)
        (strlenSubProg_externAt_none mpl)
        (strlenSubProg_hasWords mpl)
        (strlenEntry_no_wrap_of_codeLoaded hCodeU)
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (strlenEntry mpl))
          (strlenGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt hk)
        hvis
    have hSetPC : u.setPC (strlenEntry mpl) = u := setPC_eq_self_of_pc_eq hpc
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (strlenGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- `K`-narrowed `strlenGhostK` companion `GhostRowReplayOn` (requires **zero** entry `lr` guard:
    `entryGuard := fun _ => True`, since `strlenGhostK` transitions to `.Exception` if
    `lr ∈ keepR_strlen mpl`). -/
theorem strlenGhostK_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (strlenSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_strlen mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG "strlen" (fun _ => True) (strlenGhostK mpl mmpl) where
  preserves_execFrozen := fun _ _ _ hfr => strlenGhostK_preserves_execFrozen mpl mmpl hfr
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealHullNoExt W (keepR_strlen_entry mpl), ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (strlenSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hCodeStrip :
        (strlenSubProg mpl).CodeLoaded (stripExecOutside (keepR_strlen mpl) u.mem) :=
      strlenSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨hvis, _, hfr_fu, hfs_fu⟩ :=
      f3EmptyStrlenGhostHookK_visitedIn
        (keep := keepR_strlen mpl)
        (P_sub := strlenSubProg mpl)
        (entryTarget := strlenEntry mpl)
        (strlenSubProg_svc mpl)
        (strlenSubProg_externAt_none mpl)
        (strlenSubProg_hasWords mpl)
        (strlenEntry_no_wrap_of_codeLoaded hCodeU)
        hrun
        hnoex
        hfr
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (strlenEntry mpl))
          (strlenGhostK mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC (strlenEntry mpl) = u := setPC_eq_self_of_pc_eq hpc
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (strlenGhostK mpl mmpl u) hInvU hkf hfs_fu⟩

/-- Combined `GhostRowOk` (`GhostRowSpecOk` + `GhostRowReplayOn`) for `"strlen"`. -/
theorem strlenGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (strlenSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "strlen") =
        some (strlenGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_strlen mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_strlen mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "strlen" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl InvS EG "strlen" (strlenEntryGuard mpl) (strlenGhost mpl mmpl) :=
  ⟨strlenGhost_rowSpecOk mpl mmpl,
   strlenGhost_rowReplayOn mpl mmpl InvS EG hCL hInvKeep hGhostAt hRealHullNoExt hGhostNoExtNe⟩

/-- Combined `GhostRowOk` (`C4` interior-stub variant) for `"strlen"`. -/
theorem strlenGhost_rowOk_of_interior [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (strlenSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "strlen") =
        some (strlenGhost mpl mmpl))
    (hRealNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl "strlen") = none)
    (hInteriorGhost : ∀ (W : CliHooks) (pc : BitVec 64),
      keepR_strlen mpl pc = true → pc ≠ libsignalSessionLib.resolve mpl "strlen" →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none ∧
      ((cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ gStub, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some gStub ∧
          ∀ L : BitVec 64, keepR_strlen mpl L = true → TrapHook L gStub)) :
    GhostRowOk mpl mmpl InvS EG "strlen" (strlenEntryGuard mpl) (strlenGhost mpl mmpl) :=
  ⟨strlenGhost_rowSpecOk mpl mmpl,
   strlenGhost_rowReplayOn_of_interior mpl mmpl InvS EG hCL hInvKeep hGhostAt hRealNone
     hInteriorGhost⟩

/-- Guard-strengthening adapter on `GhostRowReplayOn` (for `ExtraListReplaysOn` when `guardOf sym`
    implies `entryGuard`). -/
theorem ghostRowReplayOn_of_guard_imp
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {sym : String} {entryGuard guard' : State → Prop} {f : State → State}
    (hRow : GhostRowReplayOn mpl mmpl InvS EG sym entryGuard f)
    (hImp : ∀ s0 : State, guard' s0 → entryGuard s0) :
    GhostRowReplayOn mpl mmpl InvS EG sym guard' f where
  preserves_execFrozen := hRow.preserves_execFrozen
  replay_at_stub := fun W s0 sf hG hRet hNoEx hNHalt =>
    hRow.replay_at_stub W s0 sf (hImp s0 hG) hRet hNoEx hNHalt

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays
