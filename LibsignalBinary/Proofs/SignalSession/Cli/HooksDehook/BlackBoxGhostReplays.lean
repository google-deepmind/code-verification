/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BlackBoxRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Card CC-DALEK — `lsBlackBoxSym` Row Consumer Spec & Generic-`InvS` Ghost Replay (`HooksDehook.BlackBoxGhostReplays`)

Cutover-2 `c`-card for `subtle::black_box::<u8>` (`lsBlackBoxSym`) in the `W2-C11`
`CliGhostHooks.extra` framework (`ccard_recipe.md` §2.2, §5 row 5), modeled directly on
`BcmpGhostReplays.lean` (`0` `CliElfLib` / `ElfF3Relink` / C2 / trusted imports):

1. **Row Anchor & `W`-Independent Ghost (`keepR_blackBox`, `blackBoxSubProg`, `blackBoxGhost`):**
   - Single-block 5-word (`20` B = `blackBoxByteLen`) region `blackBoxU8Words` anchored directly at
     `libsignalSessionLib.resolve mpl lsBlackBoxSym`.
   - `blackBoxGhost mpl mmpl` wraps `BlackBoxGhost.f3EmptyBlackBoxGhostHook`
     (`P_real := emptyStdProg`, `fallback := blackBoxHook`), with **zero `W : CliHooks`
     dependence**.
2. **Artifact 1 — Unconditional `GhostRowSpecOk lsBlackBoxSym (blackBoxGhost mpl mmpl)` (`0` premises):**
   - `blackBoxGhost_rowSpecOk` proves `fs_eq`, `fsT : HookFsTraced IsFsC`, and `BlackBoxRowSpec`
     (plain, `withVmPreserved`, and `withAlloc A lim` over all `16 ≤ stk ≤ 2 ^ 64`) unconditionally
     via `BlackBoxRowSpec.of_vm`.
3. **Artifact 2a — Generic-`InvS` `GhostRowReplayOn` & `GhostRowOk` (`F1` + `H1` compliant):**
   - **F1 (`pc ≠ resolve mpl lsBlackBoxSym` exclusion on `P_ghost`, whole-hull on de-hooked
     `P_real`):** `hRealHullNoExt` quantifies over `keepR_blackBox mpl pc = true` on `P_real` only;
     `hGhostNoExtNe` strictly excludes `pc ≠ libsignalSessionLib.resolve mpl lsBlackBoxSym` on
     `P_ghost` and routes through
     `BlackBoxLrTrap.f3EmptyBlackBoxGhostHook_keepLr_false_after_hook_of_codeLoaded_u`.
   - **H1 (`CodeLoaded u.mem` from `InvS u`):** `hCL` supplies `(blackBoxSubProg mpl).CodeLoaded u.mem`
     at intermediate call state `u` from `InvS u` (never `s0.mem`), accompanied by
     `blackBoxSubProg_codeLoaded_stripExecOutside_iff`.
   - Includes `C4` interior-stub wrapper `blackBoxGhost_rowReplayOn_of_interior`, `K`-narrowed spare
     `blackBoxGhostK_rowReplayOn`, full `blackBoxGhost_rowOk`, and per-arm / singleton entry-guard
     helpers `extraEntryGuard_blackBox_arm` / `extraEntryGuard_singleton_blackBox` (`.text.lib2`
     layout instantiation belongs to the C2 layout / STARTUP seat per `02:28Z` split).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced libsignalSessionLib
  lsBlackBoxSym lsDurationSinceSym lsFromUtf8Sym lsMemrchrSym lsTimeAddSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC)
open LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8 (blackBoxU8Words)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BlackBoxRowSpec (
  BlackBoxRowSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (
  ExtraRowSpec GhostRowSpecOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (
  ExtraEntryGuard GhostRowOk GhostRowReplayOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (pureWordsProg_externAt_none)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (emptyStdProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (TrapHook)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxCode (
  pureWordsProg_blackBoxU8_hasWords
  subroutine_ok_processBlackBox_of_hasWords
  hookOk_sessionBlackBox_of_master
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhost (
  f3EmptyBlackBoxGhostHook f3EmptyBlackBoxGhostHookK
  f3EmptyBlackBoxGhostHook_fs f3EmptyBlackBoxGhostHookK_fs
  f3EmptyBlackBoxGhostHook_fsT
  f3EmptyBlackBoxGhostHook_preserves_execFrozen f3EmptyBlackBoxGhostHookK_preserves_execFrozen
  f3EmptyBlackBoxGhostHook_master_ok_of_process
  f3EmptyBlackBoxGhostHook_vmPreserved_of_process
  f3EmptyBlackBoxGhostHook_visitedIn f3EmptyBlackBoxGhostHookK_visitedIn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxLrTrap (
  blackBoxByteLen keepBlackBox keepBlackBox_iff keepBlackBox_entry
  blackBox_codeLoaded_stripExecOutside
  BlackBoxEntryGuard
  blackBox_keepLr_false_after_hook_of_codeLoaded_u
  trapHook_f3EmptyBlackBoxGhostHook_of_cover
  f3EmptyBlackBoxGhostHook_keepLr_false_after_hook_of_codeLoaded_u
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_steps_lift_of_visitedIn_noExtern
)

/-! ## 1. Row Anchor Definitions, Algebraic Identities & `CodeLoaded` Bridges -/

/-- Kept-region byte predicate `[resolve mpl lsBlackBoxSym, resolve mpl lsBlackBoxSym + 20)`
    for `lsBlackBoxSym`. -/
@[expose] def keepR_blackBox (mpl : Obj.MultiPlacement) : BitVec 64 → Bool :=
  keepBlackBox (libsignalSessionLib.resolve mpl lsBlackBoxSym)

/-- `lsBlackBoxSym`'s resolved entry address lies inside `keepR_blackBox mpl`. -/
theorem keepR_blackBox_entry (mpl : Obj.MultiPlacement) :
    keepR_blackBox mpl (libsignalSessionLib.resolve mpl lsBlackBoxSym) = true :=
  keepBlackBox_entry (libsignalSessionLib.resolve mpl lsBlackBoxSym)

/-- Pure 5-word (`20`-byte) sub-program holding `blackBoxU8Words` at
    `libsignalSessionLib.resolve mpl lsBlackBoxSym`. -/
@[expose] def blackBoxSubProg (mpl : Obj.MultiPlacement) : Program :=
  pureWordsProg (libsignalSessionLib.resolve mpl lsBlackBoxSym) blackBoxU8Words

theorem blackBoxSubProg_base (mpl : Obj.MultiPlacement) :
    (blackBoxSubProg mpl).base = libsignalSessionLib.resolve mpl lsBlackBoxSym := by
  dsimp only [blackBoxSubProg, pureWordsProg, Program.ofWords]

theorem blackBoxSubProg_svc (mpl : Obj.MultiPlacement) :
    (blackBoxSubProg mpl).svc = Syscall.standard := rfl

theorem blackBoxSubProg_externAt_none (mpl : Obj.MultiPlacement) (pc : BitVec 64) :
    (blackBoxSubProg mpl).externAt? pc = none :=
  pureWordsProg_externAt_none (libsignalSessionLib.resolve mpl lsBlackBoxSym) blackBoxU8Words pc

theorem blackBoxSubProg_hasWords (mpl : Obj.MultiPlacement) :
    (blackBoxSubProg mpl).hasWords (libsignalSessionLib.resolve mpl lsBlackBoxSym)
      blackBoxU8Words :=
  pureWordsProg_blackBoxU8_hasWords (libsignalSessionLib.resolve mpl lsBlackBoxSym)

theorem blackBoxSubProg_code_length (mpl : Obj.MultiPlacement) :
    (blackBoxSubProg mpl).code.length = blackBoxByteLen := rfl

theorem keepR_blackBox_of_code_offset (mpl : Obj.MultiPlacement) {off : Nat}
    (hoff : off < (blackBoxSubProg mpl).code.length) :
    keepR_blackBox mpl ((blackBoxSubProg mpl).base + BitVec.ofNat 64 off) = true := by
  rw [blackBoxSubProg_code_length] at hoff
  rw [blackBoxSubProg_base]
  dsimp only [keepR_blackBox]
  rw [keepBlackBox_iff]
  have hsub :
      (libsignalSessionLib.resolve mpl lsBlackBoxSym + BitVec.ofNat 64 off) -
        libsignalSessionLib.resolve mpl lsBlackBoxSym =
      BitVec.ofNat 64 off := by bv_omega
  have hoff_lt : off < 2 ^ 64 := by
    have hb : blackBoxByteLen = 20 := rfl
    omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]
  exact hoff

/-- Forward `CodeLoaded` projection onto `stripExecOutside (keepR_blackBox mpl) mem`. -/
theorem blackBoxSubProg_codeLoaded_stripExecOutside {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (blackBoxSubProg mpl).CodeLoaded mem) :
    (blackBoxSubProg mpl).CodeLoaded (stripExecOutside (keepR_blackBox mpl) mem) :=
  blackBox_codeLoaded_stripExecOutside (fun _ hoff => keepR_blackBox_of_code_offset mpl hoff) hL

/-- Reverse `CodeLoaded` projection from `stripExecOutside (keepR_blackBox mpl) mem` back to `mem`. -/
theorem blackBoxSubProg_codeLoaded_of_stripExecOutside {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (blackBoxSubProg mpl).CodeLoaded (stripExecOutside (keepR_blackBox mpl) mem)) :
    (blackBoxSubProg mpl).CodeLoaded mem := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hk : keepR_blackBox mpl ((blackBoxSubProg mpl).base + BitVec.ofNat 64 i) = true :=
    keepR_blackBox_of_code_offset mpl hi
  have hbyte := hL.byte_eq i hi
  have hperm := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [ProofLib.strip_read8] at hbyte
  rw [ProofLib.strip_perm_of_keep hk] at hperm
  rw [ProofLib.strip_isLazyFree] at hlf
  exact ⟨hbyte, hperm, hlf⟩

theorem blackBoxSubProg_codeLoaded_stripExecOutside_iff {mpl : Obj.MultiPlacement} {mem : Memory} :
    (blackBoxSubProg mpl).CodeLoaded (stripExecOutside (keepR_blackBox mpl) mem) ↔
      (blackBoxSubProg mpl).CodeLoaded mem :=
  ⟨blackBoxSubProg_codeLoaded_of_stripExecOutside, blackBoxSubProg_codeLoaded_stripExecOutside⟩

/-- `W`-independent ghost hook for `lsBlackBoxSym`
    (`CliGhostHooks.extra` entry `(lsBlackBoxSym, blackBoxGhost mpl mmpl)`). -/
@[expose] noncomputable def blackBoxGhost (mpl _mmpl : Obj.MultiPlacement) : State → State :=
  f3EmptyBlackBoxGhostHook (keepR_blackBox mpl) (blackBoxSubProg mpl)
    (libsignalSessionLib.resolve mpl lsBlackBoxSym)

/-- `K`-narrowed `W`-independent ghost hook companion for `lsBlackBoxSym` (spare only; N2). -/
@[expose] noncomputable def blackBoxGhostK (mpl _mmpl : Obj.MultiPlacement) : State → State :=
  f3EmptyBlackBoxGhostHookK (keepR_blackBox mpl) (blackBoxSubProg mpl)
    (libsignalSessionLib.resolve mpl lsBlackBoxSym)

/-- Block-`617` entry-state `lr` guard for `lsBlackBoxSym`:
    `keepR_blackBox mpl (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ resolve mpl lsBlackBoxSym`. -/
@[expose] def blackBoxEntryGuard (mpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  BlackBoxEntryGuard (libsignalSessionLib.resolve mpl lsBlackBoxSym)
    (libsignalSessionLib.resolve mpl lsBlackBoxSym) s0

theorem blackBoxEntryGuard_iff (mpl : Obj.MultiPlacement) (s0 : State) :
    blackBoxEntryGuard mpl s0 ↔
      keepR_blackBox mpl (s0.readReg64 .lr) = false ∧
        s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl lsBlackBoxSym :=
  Iff.rfl

/-! ## 2. Artifact 1 — Unconditional `GhostRowSpecOk lsBlackBoxSym (blackBoxGhost mpl mmpl)` -/

theorem blackBoxGhost_fs (mpl mmpl : Obj.MultiPlacement) (s : State) :
    (blackBoxGhost mpl mmpl s).fs = s.fs :=
  f3EmptyBlackBoxGhostHook_fs (keepR_blackBox mpl) (blackBoxSubProg mpl)
    (libsignalSessionLib.resolve mpl lsBlackBoxSym) s

theorem blackBoxGhost_fsT (mpl mmpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (blackBoxGhost mpl mmpl) :=
  f3EmptyBlackBoxGhostHook_fsT (keepR_blackBox mpl) (blackBoxSubProg mpl)
    (libsignalSessionLib.resolve mpl lsBlackBoxSym)

theorem blackBoxGhost_vmPreserved (mpl mmpl : Obj.MultiPlacement) (s : State) :
    LibsignalBinary.Heap.VmPreserved s (blackBoxGhost mpl mmpl s) :=
  f3EmptyBlackBoxGhostHook_vmPreserved_of_process
    (blackBoxSubProg_svc mpl)
    (blackBoxSubProg_externAt_none mpl)
    (subroutine_ok_processBlackBox_of_hasWords (blackBoxSubProg_externAt_none mpl)
      (blackBoxSubProg_hasWords mpl))
    s

/-- Unconditional `BlackBoxRowSpec` for `blackBoxGhost mpl mmpl` (`0` layout or memory premises). -/
theorem blackBoxGhost_blackBoxRowSpec (mpl mmpl : Obj.MultiPlacement) :
    BlackBoxRowSpec (blackBoxGhost mpl mmpl) :=
  BlackBoxRowSpec.of_vm
    (fun _ hlo hhi =>
      hookOk_sessionBlackBox_of_master ⟨hlo, hhi⟩
        (f3EmptyBlackBoxGhostHook_master_ok_of_process
          (blackBoxSubProg_svc mpl)
          (blackBoxSubProg_externAt_none mpl)
          (subroutine_ok_processBlackBox_of_hasWords (blackBoxSubProg_externAt_none mpl)
            (blackBoxSubProg_hasWords mpl))))
    (blackBoxGhost_vmPreserved mpl mmpl)

/-- **Artifact 1 (`C11` §1.2, §6.1):** Unconditional
    `GhostRowSpecOk lsBlackBoxSym (blackBoxGhost mpl mmpl)` for all `(mpl, mmpl)`
    (`0` stock-side or layout premises). -/
theorem blackBoxGhost_rowSpecOk [LibsignalPlacement] (mpl mmpl : Obj.MultiPlacement) :
    GhostRowSpecOk lsBlackBoxSym (blackBoxGhost mpl mmpl) where
  fs_eq := blackBoxGhost_fs mpl mmpl
  fsT := blackBoxGhost_fsT mpl mmpl
  rowSpec := by
    have h1 : (lsBlackBoxSym == "bcmp") = false := by decide
    have h2 : (lsBlackBoxSym == "strlen") = false := by decide
    have h3 : (lsBlackBoxSym == "memmove") = false := by decide
    have h4 : (lsBlackBoxSym == lsFromUtf8Sym) = false := by decide
    have h5 : (lsBlackBoxSym == lsMemrchrSym) = false := by decide
    have h6 : (lsBlackBoxSym == lsDurationSinceSym) = false := by decide
    have h7 : (lsBlackBoxSym == lsTimeAddSym) = false := by decide
    have h8 : (lsBlackBoxSym == lsBlackBoxSym) = true := by decide
    dsimp only [ExtraRowSpec]
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, Bool.false_eq_true, ↓reduceIte]
    exact blackBoxGhost_blackBoxRowSpec mpl mmpl

/-! ## 3. `ExecFrozen` Preservation & Generic-`InvS` `GhostRowReplayOn` (Artifact 2a) -/

theorem blackBoxGhost_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (blackBoxGhost mpl mmpl u).mem :=
  f3EmptyBlackBoxGhostHook_preserves_execFrozen (keepR_blackBox mpl) (blackBoxSubProg mpl)
    (libsignalSessionLib.resolve mpl lsBlackBoxSym) hfr

theorem blackBoxGhostK_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (blackBoxGhostK mpl mmpl u).mem :=
  f3EmptyBlackBoxGhostHookK_preserves_execFrozen (keepR_blackBox mpl) (blackBoxSubProg mpl)
    (libsignalSessionLib.resolve mpl lsBlackBoxSym) hfr

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

/-- **Artifact 2a (`C11` §1.3, §6.2) — Generic-`InvS` `GhostRowReplayOn` for `lsBlackBoxSym`:**
    - **F1 compliance:** `hRealHullNoExt` quantifies over `keepR_blackBox mpl pc = true` **only** on
      the de-hooked real program `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` (post-Cutover-2).
      On the ghost program `cliProgExtPlacedAt mpl EG 617 W`, `hGhostNoExtNe` strictly excludes
      `pc ≠ libsignalSessionLib.resolve mpl lsBlackBoxSym`.
    - **H1 compliance:** `hCL` supplies `(blackBoxSubProg mpl).CodeLoaded u.mem` at intermediate call
      state `u` from `InvS u` (never `s0.mem`). -/
theorem blackBoxGhost_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (blackBoxSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsBlackBoxSym) = some (blackBoxGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_blackBox mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_blackBox mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsBlackBoxSym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsBlackBoxSym
      (blackBoxEntryGuard mpl) (blackBoxGhost mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨blackBoxGhost_preserves_execFrozen mpl mmpl hfr, blackBoxGhost_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    right
    refine ⟨hRealHullNoExt W (keepR_blackBox_entry mpl), ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (blackBoxSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hLrOut : keepR_blackBox mpl (u.readReg64 .lr) = false :=
      f3EmptyBlackBoxGhostHook_keepLr_false_after_hook_of_codeLoaded_u
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_sub := blackBoxSubProg mpl)
        (keepR := keepR_blackBox mpl)
        (entry := libsignalSessionLib.resolve mpl lsBlackBoxSym)
        (stubPc := libsignalSessionLib.resolve mpl lsBlackBoxSym)
        (entryTarget := libsignalSessionLib.resolve mpl lsBlackBoxSym)
        (blackBoxSubProg_hasWords mpl)
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
    have hCodeStrip :
        (blackBoxSubProg mpl).CodeLoaded (stripExecOutside (keepR_blackBox mpl) u.mem) :=
      blackBoxSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨hvis, hfr_fu, hfs_fu⟩ :=
      f3EmptyBlackBoxGhostHook_visitedIn
        (keep := keepR_blackBox mpl)
        (P_sub := blackBoxSubProg mpl)
        (entryTarget := libsignalSessionLib.resolve mpl lsBlackBoxSym)
        (blackBoxSubProg_svc mpl)
        (blackBoxSubProg_externAt_none mpl)
        (blackBoxSubProg_hasWords mpl)
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (libsignalSessionLib.resolve mpl lsBlackBoxSym))
          (blackBoxGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_blackBox mpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC (libsignalSessionLib.resolve mpl lsBlackBoxSym) = u :=
      setPC_eq_self_of_pc_eq hpc
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (blackBoxGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- `C4` interior-stub signature wrapper for `blackBoxGhost_rowReplayOn` (accepting split
    `hRealNone` at `stubPc` + `hInteriorGhost` with the `Or.inr` `TrapHook` interior-stub disjunct
    on `pc ≠ resolve mpl lsBlackBoxSym`). -/
theorem blackBoxGhost_rowReplayOn_of_interior
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (blackBoxSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsBlackBoxSym) = some (blackBoxGhost mpl mmpl))
    (hRealNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsBlackBoxSym) = none)
    (hInteriorGhost : ∀ (W : CliHooks) (pc : BitVec 64),
      keepR_blackBox mpl pc = true → pc ≠ libsignalSessionLib.resolve mpl lsBlackBoxSym →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none ∧
      ((cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ gStub, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some gStub ∧
          ∀ L : BitVec 64, keepR_blackBox mpl L = true → TrapHook L gStub)) :
    GhostRowReplayOn mpl mmpl InvS EG lsBlackBoxSym
      (blackBoxEntryGuard mpl) (blackBoxGhost mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨blackBoxGhost_preserves_execFrozen mpl mmpl hfr, blackBoxGhost_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    have hRealHullNoExt : ∀ {pc : BitVec 64},
        keepR_blackBox mpl pc = true →
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl lsBlackBoxSym
      · rw [hEq]; exact hRealNone W
      · exact (hInteriorGhost W pc hk hEq).1
    have hRegExt : ∀ pc : BitVec 64,
        keepBlackBox (libsignalSessionLib.resolve mpl lsBlackBoxSym) pc = true →
        (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
          ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
            ∀ L, keepBlackBox (libsignalSessionLib.resolve mpl lsBlackBoxSym) L = true →
              TrapHook L f := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl lsBlackBoxSym
      · rw [hEq]
        exact Or.inr ⟨blackBoxGhost mpl mmpl, hGhostAt W, fun L hL =>
          trapHook_f3EmptyBlackBoxGhostHook_of_cover (blackBoxSubProg mpl)
            (libsignalSessionLib.resolve mpl lsBlackBoxSym) (fun _ h => h) hL⟩
      · rcases (hInteriorGhost W pc hk hEq).2 with hNone | ⟨gStub, hSome, hTrap⟩
        · exact Or.inl hNone
        · exact Or.inr ⟨gStub, hSome, hTrap⟩
    right
    refine ⟨hRealNone W, ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (blackBoxSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hLrOut : keepR_blackBox mpl (u.readReg64 .lr) = false :=
      blackBox_keepLr_false_after_hook_of_codeLoaded_u
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_sub := blackBoxSubProg mpl)
        (entry := libsignalSessionLib.resolve mpl lsBlackBoxSym)
        (f_stub := blackBoxGhost mpl mmpl)
        (blackBoxSubProg_hasWords mpl)
        hRegExt
        (fun _ hL => trapHook_f3EmptyBlackBoxGhostHook_of_cover (blackBoxSubProg mpl)
          (libsignalSessionLib.resolve mpl lsBlackBoxSym) (fun _ h => h) hL)
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
        (blackBoxSubProg mpl).CodeLoaded (stripExecOutside (keepR_blackBox mpl) u.mem) :=
      blackBoxSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨hvis, hfr_fu, hfs_fu⟩ :=
      f3EmptyBlackBoxGhostHook_visitedIn
        (keep := keepR_blackBox mpl)
        (P_sub := blackBoxSubProg mpl)
        (entryTarget := libsignalSessionLib.resolve mpl lsBlackBoxSym)
        (blackBoxSubProg_svc mpl)
        (blackBoxSubProg_externAt_none mpl)
        (blackBoxSubProg_hasWords mpl)
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (libsignalSessionLib.resolve mpl lsBlackBoxSym))
          (blackBoxGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_blackBox mpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt hk)
        hvis
    have hSetPC : u.setPC (libsignalSessionLib.resolve mpl lsBlackBoxSym) = u :=
      setPC_eq_self_of_pc_eq hpc
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (blackBoxGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- `K`-narrowed `blackBoxGhostK` companion `GhostRowReplayOn` (`entryGuard := fun _ => True`;
    spare only per N2). -/
theorem blackBoxGhostK_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (blackBoxSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_blackBox mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsBlackBoxSym
      (fun _ => True) (blackBoxGhostK mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨blackBoxGhostK_preserves_execFrozen mpl mmpl hfr,
     f3EmptyBlackBoxGhostHookK_fs (keepR_blackBox mpl) (blackBoxSubProg mpl)
       (libsignalSessionLib.resolve mpl lsBlackBoxSym) u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealHullNoExt W (keepR_blackBox_entry mpl), ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hCodeStrip :
        (blackBoxSubProg mpl).CodeLoaded (stripExecOutside (keepR_blackBox mpl) u.mem) :=
      blackBoxSubProg_codeLoaded_stripExecOutside (hCL u hInvU)
    obtain ⟨hvis, hfr_fu, hfs_fu⟩ :=
      f3EmptyBlackBoxGhostHookK_visitedIn
        (keep := keepR_blackBox mpl)
        (P_sub := blackBoxSubProg mpl)
        (entryTarget := libsignalSessionLib.resolve mpl lsBlackBoxSym)
        (blackBoxSubProg_svc mpl)
        (blackBoxSubProg_externAt_none mpl)
        (blackBoxSubProg_hasWords mpl)
        hrun
        hnoex
        hfr
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (libsignalSessionLib.resolve mpl lsBlackBoxSym))
          (blackBoxGhostK mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_blackBox mpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC (libsignalSessionLib.resolve mpl lsBlackBoxSym) = u :=
      setPC_eq_self_of_pc_eq hpc
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (blackBoxGhostK mpl mmpl u) hInvU hkf hfs_fu⟩

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

/-- Full per-row `GhostRowOk` bundle (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) for `lsBlackBoxSym`. -/
theorem blackBoxGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (blackBoxSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsBlackBoxSym) = some (blackBoxGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_blackBox mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_blackBox mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsBlackBoxSym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl InvS EG lsBlackBoxSym
      (blackBoxEntryGuard mpl) (blackBoxGhost mpl mmpl) :=
  ⟨blackBoxGhost_rowSpecOk mpl mmpl,
   blackBoxGhost_rowReplayOn mpl mmpl InvS EG
     hCL hInvKeep hGhostAt hRealHullNoExt hGhostNoExtNe⟩

/-! ## 4. Per-Arm & Singleton `ExtraEntryGuard` Helpers (`.text.lib2` Interface) -/

/-- Per-arm `lsBlackBoxSym` discharge for any `guardOf : String → State → Prop` agreeing with
    `blackBoxEntryGuard mpl` on `lsBlackBoxSym`. -/
theorem extraEntryGuard_blackBox_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf lsBlackBoxSym s0 ↔ blackBoxEntryGuard mpl s0)
    (hBlackBoxGuard : blackBoxEntryGuard mpl s0) :
    guardOf lsBlackBoxSym s0 :=
  hGuardEq.mpr hBlackBoxGuard

/-- Table-level `ExtraEntryGuard guardOf g s0` discharge when `g.extra` carries the singleton
    `lsBlackBoxSym` row `[(lsBlackBoxSym, blackBoxGhost mpl mmpl)]` (N3). -/
theorem extraEntryGuard_singleton_blackBox
    {mpl mmpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hg : g.extra = [(lsBlackBoxSym, blackBoxGhost mpl mmpl)])
    (hGuardEq : guardOf lsBlackBoxSym s0 ↔ blackBoxEntryGuard mpl s0)
    (hBlackBoxGuard : blackBoxEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 := by
  intro sym f _ hLook
  rw [hg] at hLook
  simp only [List.lookup] at hLook
  by_cases hSym : (sym == lsBlackBoxSym) = true
  · have hEq : sym = lsBlackBoxSym := eq_of_beq hSym
    subst hEq
    exact hGuardEq.mpr hBlackBoxGuard
  · simp [hSym] at hLook

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays
