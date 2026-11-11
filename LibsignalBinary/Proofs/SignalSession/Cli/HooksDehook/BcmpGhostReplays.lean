/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BcmpRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Card L1-c Pilot — `"bcmp"` Row Consumer Spec & Generic-`InvS` Ghost Replay (`HooksDehook.BcmpGhostReplays`)

Pilot card **`c`** (`L1-c`) for `"bcmp"` in the `W2-C11` `CliGhostHooks.extra` framework
(`w2_c11_design_v2.md` §§1.2–1.3, §§6.1–6.2), delivering **Artifact 1** (`GhostRowSpecOk`) and
the generic-`InvS` **Artifact 2a** (`GhostRowReplayOn`) in the lightweight `Cli/HooksDehook` cone
(`0` `CliElfLib` / `ElfF3Relink` / C2 / trusted imports):

1. **Row Anchor & `W`-Independent Ghost (`bcmpHullBase`, `keepR_bcmp`, `bcmpSubProg`, `bcmpGhost`):**
   - `"bcmp"` is in `libsignalSessionLib`, whereas `"memcmp"` is unhooked and absent from
     `libsignalSessionLib`. `bcmpHullBase mpl := libsignalSessionLib.resolve mpl "bcmp" - memcmpByteLen`
     encodes the C2 `2C` stock `libc.a` layout convention that `memcmp` (`52` B = `13` words) sits
     immediately before `bcmp` (`4` B = `1` word `b #-52`), giving the unconditional identity
     `bcmpHullBase mpl + memcmpByteLen = libsignalSessionLib.resolve mpl "bcmp"`. Because this is a
     pure definition (`0` premises), on any hypothetical layout where `memcmp` did not immediately
     precede `bcmp`, the downstream `(bcmpSubProg mpl).CodeLoaded u.mem` hypothesis would simply be
     undischargeable rather than unsound.
   - `bcmpGhost mpl mmpl` wraps `BcmpGhostK.f3EmptyBcmpGhostHook` (`P_real := emptyStdProg`,
     `fallback := hookBcmpFallback`), so it has **zero `W : CliHooks` dependence** (`REV-PILOT` Q1/N1)
     and fits directly into `CliGhostHooks.extra : List (String × (State → State))`.
2. **Artifact 1 — Unconditional `GhostRowSpecOk "bcmp" (bcmpGhost mpl mmpl)` (`0` premises):**
   - `bcmpGhost_rowSpecOk` proves `fs_eq`, `fsT : HookFsTraced IsFsC`, and `BcmpRowSpec` (all `6`
     consumer arms: `cliBcmpSpec` and `bcmpVregsSpec`, plain, `withVmPreserved`, and `withAlloc A lim`)
     unconditionally for every `(mpl, mmpl)` via `BcmpRowSpec.of_vm`.
3. **Artifact 2a — Generic-`InvS` `GhostRowReplayOn` (`F1` + `H1` compliant):**
   - **F1 (`pc ≠ resolve mpl "bcmp"` exclusion on `P_ghost`, whole-hull on de-hooked `P_real`):**
     `hRealHullNoExt` quantifies over all `keepR_bcmp mpl pc = true` **only** on the de-hooked real
     program `P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` (post-Cutover-2, once
     `"bcmp"` is dropped from `cliHookTablePlaced`, so neither `memcmp` nor `bcmp` carries an extern
     hook on `P_real`). On the ghost program `P_ghost := cliProgExtPlacedAt mpl EG 617 W`, `stubPc :=
     libsignalSessionLib.resolve mpl "bcmp"` carries `some (bcmpGhost mpl mmpl)`, so `hGhostNoExtNe`
     **strictly excludes `pc ≠ libsignalSessionLib.resolve mpl "bcmp"`** and routes through
     `BcmpLrTrap.f3EmptyBcmpGhostHook_keepLr_false_after_hook_of_codeLoaded_u`.
   - **H1 (`CodeLoaded u.mem` from `InvS u`):** `hCL` extracts `(bcmpSubProg mpl).CodeLoaded u.mem`
     from `InvS u` at each intermediate call state `u` (never `s0.mem`). We also export
     `bcmpSubProg_codeLoaded_stripExecOutside_iff` so `hCL` can equivalently be supplied in
     `stripExecOutside (keepR_bcmp mpl) u.mem` form (matching STARTUP's
     `Lib2LayoutFacts.f3CodeInv_rxWords_codeLoaded_strip`, `Lib2LayoutFacts.lean @a230f2671b:203-215`).
   - Also supports the general `C4` interior-hook disjunct (`bcmpGhost_rowReplayOn_of_interior`,
     matching `w2_c11_design_v2.md` §6.2 `:432–451` verbatim) and `K`-narrowed `bcmpGhostK`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen keepFsTrace linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BcmpRowSpec (
  BcmpRowSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (
  ExtraRowSpec GhostRowSpecOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (
  GhostRowOk GhostRowReplayOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (
  TrapHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode (
  memcmpByteLen bcmpHullWords pureWordsProg_bcmpHull_hasWords pureWordsProg_externAt_none
  hookBcmpFallback
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostK (
  f3EmptyBcmpGhostHook f3EmptyBcmpGhostHookK
  f3EmptyBcmpGhostHook_eq f3EmptyBcmpGhostHookK_eq
  f3EmptyBcmpGhostHook_fs f3EmptyBcmpGhostHookK_fs
  f3EmptyBcmpGhostHook_fsT f3EmptyBcmpGhostHookK_fsT
  f3EmptyBcmpGhostHook_vmPreserved
  f3EmptyBcmpGhostHook_dirCliBcmp_ok f3EmptyBcmpGhostHook_bcmpVregs_ok
  f3EmptyBcmpGhostHook_visitedIn f3EmptyBcmpGhostHookK_visitedIn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap (
  bcmpHullByteLen keepBcmpHull keepBcmpHull_iff keepBcmpHull_entry
  bcmpHullWords_eq_canonical bcmpHull_codeLoaded_stripExecOutside
  BcmpEntryGuard
  bcmpHull_keepLr_false_after_hook_of_codeLoaded_u
  bcmpHull_reg_ext_of_stub_excluded
  trapHook_f3EmptyBcmpGhostHook_of_cover
  f3EmptyBcmpGhostHook_keepLr_false_after_hook_of_codeLoaded_u
  f3EmptyBcmpGhostHookK_keepLr_false_after_hook_of_codeLoaded_u
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_steps_lift_of_visitedIn_noExtern
)

/-! ## 1. Row Anchor Definitions, Algebraic Identities & `CodeLoaded` Bridges -/

/-- Computed base address of the contiguous 56-byte (`14`-word) `memcmp ++ bcmp` hull for placement
    `mpl`, defined relative to `"bcmp"` (`resolve mpl "bcmp" - memcmpByteLen`) because `"memcmp"` is
    unhooked and absent from `libsignalSessionLib`.
    *Layout note (`HOOKS-PREP` M0 note 2):* Encodes the C2 `2C` stock `libc.a` layout where `13`-word
    `memcmp` (`52` B) sits immediately before `1`-word `bcmp` (`b #-52` at `+52`). If a placement had
    other bytes at `resolve mpl "bcmp" - 52#64`, `(bcmpSubProg mpl).CodeLoaded u.mem` would simply not
    hold; no axiom or layout assumption is baked in. -/
@[expose] def bcmpHullBase (mpl : Obj.MultiPlacement) : BitVec 64 :=
  libsignalSessionLib.resolve mpl "bcmp" - memcmpByteLen

/-- Unconditional BitVec identity: `bcmpHullBase mpl + memcmpByteLen = resolve mpl "bcmp"`. -/
theorem bcmpHullBase_add_memcmpByteLen (mpl : Obj.MultiPlacement) :
    bcmpHullBase mpl + memcmpByteLen = libsignalSessionLib.resolve mpl "bcmp" := by
  dsimp only [bcmpHullBase]
  bv_omega

/-- Kept-region byte predicate `[bcmpHullBase mpl, bcmpHullBase mpl + 56)` for `"bcmp"`. -/
@[expose] def keepR_bcmp (mpl : Obj.MultiPlacement) : BitVec 64 → Bool :=
  keepBcmpHull (bcmpHullBase mpl)

/-- `"bcmp"`'s resolved entry address lies inside `keepR_bcmp mpl`. -/
theorem keepR_bcmp_entry (mpl : Obj.MultiPlacement) :
    keepR_bcmp mpl (libsignalSessionLib.resolve mpl "bcmp") = true := by
  dsimp only [keepR_bcmp]
  rw [← bcmpHullBase_add_memcmpByteLen mpl]
  exact keepBcmpHull_entry (bcmpHullBase mpl)

/-- Pure 14-word (`56`-byte) sub-program holding `bcmpHullWords (bcmpHullBase mpl)` at
    `bcmpHullBase mpl` (with default `resolve := fun _ => bcmpHullBase mpl`, so
    `resolve "memcmp" = bcmpHullBase mpl` holds by `rfl`). -/
@[expose] def bcmpSubProg (mpl : Obj.MultiPlacement) : Program :=
  pureWordsProg (bcmpHullBase mpl) (bcmpHullWords (bcmpHullBase mpl))

theorem bcmpSubProg_base (mpl : Obj.MultiPlacement) :
    (bcmpSubProg mpl).base = bcmpHullBase mpl := rfl

theorem bcmpSubProg_svc (mpl : Obj.MultiPlacement) :
    (bcmpSubProg mpl).svc = Syscall.standard := rfl

theorem bcmpSubProg_externAt_none (mpl : Obj.MultiPlacement) (pc : BitVec 64) :
    (bcmpSubProg mpl).externAt? pc = none :=
  pureWordsProg_externAt_none (bcmpHullBase mpl) (bcmpHullWords (bcmpHullBase mpl)) pc

theorem bcmpSubProg_hasWords (mpl : Obj.MultiPlacement) :
    (bcmpSubProg mpl).hasWords (bcmpHullBase mpl) (bcmpHullWords (bcmpHullBase mpl)) :=
  pureWordsProg_bcmpHull_hasWords (bcmpHullBase mpl)

theorem bcmpSubProg_code_length (mpl : Obj.MultiPlacement) :
    (bcmpSubProg mpl).code.length = bcmpHullByteLen := by
  dsimp only [bcmpSubProg, pureWordsProg, Program.ofWords]
  rw [bcmpHullWords_eq_canonical (m := bcmpHullBase mpl) rfl]
  rfl

theorem keepR_bcmp_of_code_offset (mpl : Obj.MultiPlacement) {off : Nat}
    (hoff : off < (bcmpSubProg mpl).code.length) :
    keepR_bcmp mpl ((bcmpSubProg mpl).base + BitVec.ofNat 64 off) = true := by
  rw [bcmpSubProg_code_length] at hoff
  dsimp only [keepR_bcmp, bcmpSubProg_base]
  rw [keepBcmpHull_iff]
  have hsub : (bcmpHullBase mpl + BitVec.ofNat 64 off) - bcmpHullBase mpl =
      BitVec.ofNat 64 off := by bv_omega
  have hoff_lt : off < 2 ^ 64 := by
    have hb : bcmpHullByteLen = 56 := rfl
    omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]
  exact hoff

/-- Forward `CodeLoaded` projection onto `stripExecOutside (keepR_bcmp mpl) mem`. -/
theorem bcmpSubProg_codeLoaded_stripExecOutside {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (bcmpSubProg mpl).CodeLoaded mem) :
    (bcmpSubProg mpl).CodeLoaded (stripExecOutside (keepR_bcmp mpl) mem) :=
  bcmpHull_codeLoaded_stripExecOutside (fun _ hoff => keepR_bcmp_of_code_offset mpl hoff) hL

/-- Reverse `CodeLoaded` projection from `stripExecOutside (keepR_bcmp mpl) mem` back to `mem`
    (so STARTUP's `f3CodeInv_rxWords_codeLoaded_strip` `Lib2LayoutFacts.lean @a230f2671b:203-215`
    directly discharges `H1`'s `(bcmpSubProg mpl).CodeLoaded u.mem` premise). -/
theorem bcmpSubProg_codeLoaded_of_stripExecOutside {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (bcmpSubProg mpl).CodeLoaded (stripExecOutside (keepR_bcmp mpl) mem)) :
    (bcmpSubProg mpl).CodeLoaded mem := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hk : keepR_bcmp mpl ((bcmpSubProg mpl).base + BitVec.ofNat 64 i) = true :=
    keepR_bcmp_of_code_offset mpl hi
  have hbyte := hL.byte_eq i hi
  have hperm := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [ProofLib.strip_read8] at hbyte
  rw [ProofLib.strip_perm_of_keep hk] at hperm
  rw [ProofLib.strip_isLazyFree] at hlf
  exact ⟨hbyte, hperm, hlf⟩

theorem bcmpSubProg_codeLoaded_stripExecOutside_iff {mpl : Obj.MultiPlacement} {mem : Memory} :
    (bcmpSubProg mpl).CodeLoaded (stripExecOutside (keepR_bcmp mpl) mem) ↔
      (bcmpSubProg mpl).CodeLoaded mem :=
  ⟨bcmpSubProg_codeLoaded_of_stripExecOutside, bcmpSubProg_codeLoaded_stripExecOutside⟩

/-- `W`-independent ghost hook for `"bcmp"` (`CliGhostHooks.extra` entry `("bcmp", bcmpGhost mpl mmpl)`).
    Uses `BcmpGhostK.f3EmptyBcmpGhostHook` (`P_real := emptyStdProg`, `fallback := hookBcmpFallback`),
    never capturing `W : CliHooks` (`REV-PILOT` Q1/N1). -/
@[expose] noncomputable def bcmpGhost (mpl _mmpl : Obj.MultiPlacement) : State → State :=
  f3EmptyBcmpGhostHook (keepR_bcmp mpl) (bcmpSubProg mpl)
    (bcmpHullBase mpl + memcmpByteLen)

/-- `K`-narrowed `W`-independent ghost hook companion for `"bcmp"`. -/
@[expose] noncomputable def bcmpGhostK (mpl _mmpl : Obj.MultiPlacement) : State → State :=
  f3EmptyBcmpGhostHookK (keepR_bcmp mpl) (bcmpSubProg mpl)
    (bcmpHullBase mpl + memcmpByteLen)

/-- Block-`617` entry-state `lr` guard for `"bcmp"` (`C11` §6.3):
    `keepR_bcmp mpl (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ resolve mpl "bcmp"`. -/
@[expose] def bcmpEntryGuard (mpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  BcmpEntryGuard (bcmpHullBase mpl) (libsignalSessionLib.resolve mpl "bcmp") s0

theorem bcmpEntryGuard_iff (mpl : Obj.MultiPlacement) (s0 : State) :
    bcmpEntryGuard mpl s0 ↔
      keepR_bcmp mpl (s0.readReg64 .lr) = false ∧
        s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl "bcmp" :=
  Iff.rfl

/-! ## 2. Artifact 1 — Unconditional `GhostRowSpecOk "bcmp" (bcmpGhost mpl mmpl)` -/

theorem bcmpGhost_fs (mpl mmpl : Obj.MultiPlacement) (s : State) :
    (bcmpGhost mpl mmpl s).fs = s.fs :=
  f3EmptyBcmpGhostHook_fs (keepR_bcmp mpl) (bcmpSubProg mpl)
    (bcmpHullBase mpl + memcmpByteLen) s

theorem bcmpGhost_fsT (mpl mmpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (bcmpGhost mpl mmpl) :=
  f3EmptyBcmpGhostHook_fsT (keepR_bcmp mpl) (bcmpSubProg mpl)
    (bcmpHullBase mpl + memcmpByteLen)

theorem bcmpGhost_vmPreserved (mpl mmpl : Obj.MultiPlacement) (s : State) :
    LibsignalBinary.Heap.VmPreserved s (bcmpGhost mpl mmpl s) :=
  f3EmptyBcmpGhostHook_vmPreserved (bcmpSubProg_svc mpl) (bcmpSubProg_externAt_none mpl)
    (bcmpSubProg_hasWords mpl) rfl s

/-- Unconditional `BcmpRowSpec` for `bcmpGhost mpl mmpl` (`0` layout or memory premises). -/
theorem bcmpGhost_bcmpRowSpec (mpl mmpl : Obj.MultiPlacement) :
    BcmpRowSpec (bcmpGhost mpl mmpl) :=
  BcmpRowSpec.of_vm
    (f3EmptyBcmpGhostHook_dirCliBcmp_ok (bcmpSubProg_svc mpl) (bcmpSubProg_externAt_none mpl)
      (bcmpSubProg_hasWords mpl) rfl)
    (f3EmptyBcmpGhostHook_bcmpVregs_ok (bcmpSubProg_svc mpl) (bcmpSubProg_externAt_none mpl)
      (bcmpSubProg_hasWords mpl) rfl)
    (bcmpGhost_vmPreserved mpl mmpl)

/-- **Artifact 1 (`C11` §1.2, §6.1):** Unconditional `GhostRowSpecOk "bcmp" (bcmpGhost mpl mmpl)`
    for all `(mpl, mmpl)` (`0` stock-side or layout premises). -/
theorem bcmpGhost_rowSpecOk [LibsignalPlacement] (mpl mmpl : Obj.MultiPlacement) :
    GhostRowSpecOk "bcmp" (bcmpGhost mpl mmpl) where
  fs_eq := bcmpGhost_fs mpl mmpl
  fsT := bcmpGhost_fsT mpl mmpl
  rowSpec := by
    change ExtraRowSpec "bcmp" (bcmpGhost mpl mmpl)
    simpa [ExtraRowSpec] using bcmpGhost_bcmpRowSpec mpl mmpl

/-! ## 3. `ExecFrozen` Preservation & Generic-`InvS` `GhostRowReplayOn` (Artifact 2a) -/

/-- `linkedCallHook` preserves `ExecFrozen` whenever `fallback` preserves `ExecFrozen` (`REV-PILOT` N4):
    - On `ActiveRealPre ∧ ActiveRealRun`, `ActiveRealRun`'s witness carries `ExecFrozen sf.mem`;
    - On `ActiveRealPre ∧ ¬ ActiveRealRun`, `keepFsTrace fallback u` has `.mem = (fallback u).mem`;
    - On `¬ ActiveRealPre`, `.mem = u.mem`. -/
theorem linkedCallHook_preserves_execFrozen {α : Type}
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

theorem hookBcmpFallback_mem (s : State) :
    (hookBcmpFallback s).mem = s.mem := rfl

/-- `f3EmptyBcmpGhostHook` preserves `ExecFrozen` unconditionally (`REV-PILOT` N4). -/
theorem f3EmptyBcmpGhostHook_preserves_execFrozen
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (f3EmptyBcmpGhostHook keepR P_sub entryTarget u).mem := by
  rw [f3EmptyBcmpGhostHook_eq]
  exact linkedCallHook_preserves_execFrozen
    (fun s hs => by rw [hookBcmpFallback_mem]; exact hs) hfr

/-- `f3EmptyBcmpGhostHookK` preserves `ExecFrozen` unconditionally. -/
theorem f3EmptyBcmpGhostHookK_preserves_execFrozen
    (keepR : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (f3EmptyBcmpGhostHookK keepR P_sub entryTarget u).mem := by
  rw [f3EmptyBcmpGhostHookK_eq]
  exact linkedCallHook_preserves_execFrozen
    (fun s hs => by rw [hookBcmpFallback_mem]; exact hs) hfr

theorem bcmpGhost_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (bcmpGhost mpl mmpl u).mem :=
  f3EmptyBcmpGhostHook_preserves_execFrozen (keepR_bcmp mpl) (bcmpSubProg mpl)
    (bcmpHullBase mpl + memcmpByteLen) hfr

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

/-- **Artifact 2a (`C11` §1.3, §6.2) — Generic-`InvS` `GhostRowReplayOn` for `"bcmp"`:**
    - **F1 compliance (`HOOKS-PREP` M0 note 3):** `hRealHullNoExt` quantifies over the whole 56 B
      hull `keepR_bcmp mpl pc = true` **only** on the de-hooked real program
      `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` (valid post-Cutover-2 once `"bcmp"` is
      removed from `cliHookTablePlaced`). On the ghost program `cliProgExtPlacedAt mpl EG 617 W`,
      `hGhostNoExtNe` **strictly excludes `pc ≠ libsignalSessionLib.resolve mpl "bcmp"`**, matching
      STARTUP's `f3Row_ghostProg617_externAt_none_of_ne_entry`
      (`Lib2LayoutFacts.lean @a230f2671b:368`).
    - **H1 compliance (`HOOKS-PREP` M0 note 4):** `hCL` supplies `(bcmpSubProg mpl).CodeLoaded u.mem`
      at the intermediate call state `u` from `InvS u` (never `s0.mem`). -/
theorem bcmpGhost_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (bcmpSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "bcmp") =
        some (bcmpGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_bcmp mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_bcmp mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "bcmp" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG "bcmp" (bcmpEntryGuard mpl) (bcmpGhost mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨bcmpGhost_preserves_execFrozen mpl mmpl hfr, bcmpGhost_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    right
    refine ⟨hRealHullNoExt W (keepR_bcmp_entry mpl), ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (bcmpSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hLrOut : keepR_bcmp mpl (u.readReg64 .lr) = false :=
      f3EmptyBcmpGhostHook_keepLr_false_after_hook_of_codeLoaded_u
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_sub := bcmpSubProg mpl)
        (keepR := keepR_bcmp mpl)
        (m := bcmpHullBase mpl)
        (stubPc := libsignalSessionLib.resolve mpl "bcmp")
        (entryTarget := bcmpHullBase mpl + memcmpByteLen)
        rfl
        (bcmpSubProg_hasWords mpl)
        (fun _ h => h)
        (fun _ hk hne => hGhostNoExtNe W hk hne)
        (hGhostAt W)
        hEntry.1
        hRetPc
        hNoExSf
        hNotHaltSf
        u
        hCodeU
        hStepsAfter
        hrun
        hkf
    have hCodeStrip : (bcmpSubProg mpl).CodeLoaded (stripExecOutside (keepR_bcmp mpl) u.mem) :=
      bcmpSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨_, _, hfr_fu, hfs_fu, hvis⟩ :=
      f3EmptyBcmpGhostHook_visitedIn
        (keepR := keepR_bcmp mpl)
        (P_sub := bcmpSubProg mpl)
        (m := bcmpHullBase mpl)
        (bcmpSubProg_svc mpl)
        (bcmpSubProg_externAt_none mpl)
        (bcmpSubProg_hasWords mpl)
        rfl
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (bcmpHullBase mpl + memcmpByteLen))
          (bcmpGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC (bcmpHullBase mpl + memcmpByteLen) = u :=
      setPC_eq_self_of_pc_eq (hpc.trans (bcmpHullBase_add_memcmpByteLen mpl).symm)
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (bcmpGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- `C4` interior-stub signature wrapper for `bcmpGhost_rowReplayOn` (accepting split `hRealNone`
    at `stubPc` + `hInteriorGhost` with the `Or.inr` `TrapHook` interior-stub disjunct on
    `pc ≠ resolve mpl "bcmp"`). -/
theorem bcmpGhost_rowReplayOn_of_interior
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (bcmpSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "bcmp") =
        some (bcmpGhost mpl mmpl))
    (hRealNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl "bcmp") = none)
    (hInteriorGhost : ∀ (W : CliHooks) (pc : BitVec 64),
      keepR_bcmp mpl pc = true → pc ≠ libsignalSessionLib.resolve mpl "bcmp" →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none ∧
      ((cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ gStub, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some gStub ∧
          ∀ L : BitVec 64, keepR_bcmp mpl L = true → TrapHook L gStub)) :
    GhostRowReplayOn mpl mmpl InvS EG "bcmp" (bcmpEntryGuard mpl) (bcmpGhost mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨bcmpGhost_preserves_execFrozen mpl mmpl hfr, bcmpGhost_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    have hRealHullNoExt : ∀ {pc : BitVec 64},
        keepR_bcmp mpl pc = true →
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl "bcmp"
      · rw [hEq]; exact hRealNone W
      · exact (hInteriorGhost W pc hk hEq).1
    have hRegExt : ∀ pc : BitVec 64, keepBcmpHull (bcmpHullBase mpl) pc = true →
        (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
          ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
            ∀ L, keepBcmpHull (bcmpHullBase mpl) L = true → TrapHook L f := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl "bcmp"
      · rw [hEq]
        exact Or.inr ⟨bcmpGhost mpl mmpl, hGhostAt W, fun L hL =>
          trapHook_f3EmptyBcmpGhostHook_of_cover (bcmpSubProg mpl)
            (bcmpHullBase mpl + memcmpByteLen) (fun _ h => h) hL⟩
      · rcases (hInteriorGhost W pc hk hEq).2 with hNone | ⟨gStub, hSome, hTrap⟩
        · exact Or.inl hNone
        · exact Or.inr ⟨gStub, hSome, hTrap⟩
    right
    refine ⟨hRealNone W, ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (bcmpSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hLrOut : keepR_bcmp mpl (u.readReg64 .lr) = false :=
      bcmpHull_keepLr_false_after_hook_of_codeLoaded_u
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_sub := bcmpSubProg mpl)
        (m := bcmpHullBase mpl)
        (f_stub := bcmpGhost mpl mmpl)
        rfl
        (bcmpSubProg_hasWords mpl)
        hRegExt
        (fun _ hL => trapHook_f3EmptyBcmpGhostHook_of_cover (bcmpSubProg mpl)
          (bcmpHullBase mpl + memcmpByteLen) (fun _ h => h) hL)
        hEntry.1
        hRetPc
        hNoExSf
        hNotHaltSf
        u
        hCodeU
        hStepsAfter
        hrun
        hkf
    have hCodeStrip : (bcmpSubProg mpl).CodeLoaded (stripExecOutside (keepR_bcmp mpl) u.mem) :=
      bcmpSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨_, _, hfr_fu, hfs_fu, hvis⟩ :=
      f3EmptyBcmpGhostHook_visitedIn
        (keepR := keepR_bcmp mpl)
        (P_sub := bcmpSubProg mpl)
        (m := bcmpHullBase mpl)
        (bcmpSubProg_svc mpl)
        (bcmpSubProg_externAt_none mpl)
        (bcmpSubProg_hasWords mpl)
        rfl
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (bcmpHullBase mpl + memcmpByteLen))
          (bcmpGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt hk)
        hvis
    have hSetPC : u.setPC (bcmpHullBase mpl + memcmpByteLen) = u :=
      setPC_eq_self_of_pc_eq (hpc.trans (bcmpHullBase_add_memcmpByteLen mpl).symm)
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (bcmpGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- `K`-narrowed `bcmpGhostK` companion `GhostRowReplayOn` (requires **zero** entry `lr` guard:
    `entryGuard := fun _ => True`, since `bcmpGhostK` transitions to `.Exception` if `lr ∈ keepR`). -/
theorem bcmpGhostK_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (bcmpSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_bcmp mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG "bcmp" (fun _ => True) (bcmpGhostK mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨f3EmptyBcmpGhostHookK_preserves_execFrozen (keepR_bcmp mpl) (bcmpSubProg mpl)
      (bcmpHullBase mpl + memcmpByteLen) hfr,
     f3EmptyBcmpGhostHookK_fs (keepR_bcmp mpl) (bcmpSubProg mpl)
      (bcmpHullBase mpl + memcmpByteLen) u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealHullNoExt W (keepR_bcmp_entry mpl), ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hCodeStrip : (bcmpSubProg mpl).CodeLoaded (stripExecOutside (keepR_bcmp mpl) u.mem) :=
      bcmpSubProg_codeLoaded_stripExecOutside (hCL u hInvU)
    obtain ⟨_, _, hfr_fu, hfs_fu, hvis⟩ :=
      f3EmptyBcmpGhostHookK_visitedIn
        (keepR := keepR_bcmp mpl)
        (P_sub := bcmpSubProg mpl)
        (m := bcmpHullBase mpl)
        (bcmpSubProg_svc mpl)
        (bcmpSubProg_externAt_none mpl)
        (bcmpSubProg_hasWords mpl)
        rfl
        hrun
        hnoex
        hfr
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (bcmpHullBase mpl + memcmpByteLen))
          (bcmpGhostK mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC (bcmpHullBase mpl + memcmpByteLen) = u :=
      setPC_eq_self_of_pc_eq (hpc.trans (bcmpHullBase_add_memcmpByteLen mpl).symm)
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (bcmpGhostK mpl mmpl u) hInvU hkf hfs_fu⟩

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

/-- Full per-row `GhostRowOk` bundle (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) for `"bcmp"`. -/
theorem bcmpGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (bcmpSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "bcmp") =
        some (bcmpGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_bcmp mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_bcmp mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "bcmp" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl InvS EG "bcmp" (bcmpEntryGuard mpl) (bcmpGhost mpl mmpl) :=
  ⟨bcmpGhost_rowSpecOk mpl mmpl,
   bcmpGhost_rowReplayOn mpl mmpl InvS EG hCL hInvKeep hGhostAt hRealHullNoExt hGhostNoExtNe⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays
