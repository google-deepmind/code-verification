/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StaticSecretDropRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Card CC-DALEK — `lsStaticSecretDropSym` Row Consumer Spec & Generic-`InvS` Ghost Replay (`HooksDehook.StaticSecretDropGhostReplays`)

Cutover-2 `c`-card for `<x25519_dalek::StaticSecret as Drop>::drop` (`lsStaticSecretDropSym`) in
the `W2-C11` `CliGhostHooks.extra` framework (`ccard_recipe.md` §2.2, §5 row 6), modeled directly
on `BcmpGhostReplays.lean` (`0` `CliElfLib` / `ElfF3Relink` / C2 / trusted imports):

1. **Row Anchor & `W`-Independent Ghost (`keepR_staticSecretDrop`, `staticSecretDropSubProg`,
   `staticSecretDropGhost`):**
   - Single-block 63-word (`252` B = `staticSecretDropByteLen`) region `zeroize32Words` anchored
     directly at `libsignalSessionLib.resolve mpl lsStaticSecretDropSym`.
   - `staticSecretDropGhost mpl mmpl` wraps `ZeroizeGhost.f3EmptyZeroizeGhostHook`
     (`P_real := emptyStdProg`, `fallback := zeroizeSecretHook`), with **zero `W : CliHooks`
     dependence**.
2. **Artifact 1 — Unconditional `GhostRowSpecOk lsStaticSecretDropSym (staticSecretDropGhost mpl mmpl)`
   (`0` premises):**
   - `staticSecretDropGhost_rowSpecOk` proves `fs_eq`, `fsT : HookFsTraced IsFsC`, and
     `StaticSecretDropRowSpec` (`zeroizeSecretSpec`, plain, `withVmPreserved`, and `withAlloc A lim`)
     unconditionally via `StaticSecretDropRowSpec.of_vm`.
3. **Artifact 2a — Generic-`InvS` `GhostRowReplayOn` & `GhostRowOk` (`F1` + `H1` compliant):**
   - **F1 (`pc ≠ resolve mpl lsStaticSecretDropSym` exclusion on `P_ghost`, whole-hull on de-hooked
     `P_real`):** `hRealHullNoExt` quantifies over `keepR_staticSecretDrop mpl pc = true` on
     `P_real` only; `hGhostNoExtNe` strictly excludes
     `pc ≠ libsignalSessionLib.resolve mpl lsStaticSecretDropSym` on `P_ghost` and routes through
     `ZeroizeLrTrap.f3EmptyStaticSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u`.
   - **H1 (`CodeLoaded u.mem` from `InvS u`):** `hCL` supplies
     `(staticSecretDropSubProg mpl).CodeLoaded u.mem` at intermediate call state `u` from `InvS u`
     (never `s0.mem`), accompanied by `staticSecretDropSubProg_codeLoaded_stripExecOutside_iff`.
   - Includes `C4` interior-stub wrapper `staticSecretDropGhost_rowReplayOn_of_interior`,
     `K`-narrowed spare `staticSecretDropGhostK_rowReplayOn`, full `staticSecretDropGhost_rowOk`,
     and per-arm / singleton entry-guard helpers `extraEntryGuard_staticSecretDrop_arm` /
     `extraEntryGuard_singleton_staticSecretDrop` (`.text.lib2` layout instantiation belongs to the
     C2 layout / STARTUP seat per `02:28Z` split).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced libsignalSessionLib
  lsBlackBoxSym lsDurationSinceSym lsFromUtf8Sym lsMemrchrSym lsStaticSecretDropSym lsTimeAddSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (zeroize32Words)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StaticSecretDropRowSpec (
  StaticSecretDropRowSpec
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
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode (
  pureWordsProg_zeroize32_hasWords
  subroutine_ok_processZeroize_of_hasWords
  hookOk_zeroizeSecret_of_master
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost (
  f3EmptyZeroizeGhostHook f3EmptyZeroizeGhostHookK
  f3EmptyZeroizeGhostHook_fs f3EmptyZeroizeGhostHookK_fs
  f3EmptyZeroizeGhostHook_fsT
  f3EmptyZeroizeGhostHook_preserves_execFrozen f3EmptyZeroizeGhostHookK_preserves_execFrozen
  f3EmptyZeroizeGhostHook_master_ok_of_process
  f3EmptyZeroizeGhostHook_vmPreserved_of_process
  f3EmptyZeroizeGhostHook_visitedIn f3EmptyZeroizeGhostHookK_visitedIn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap (
  staticSecretDropByteLen keepStaticSecretDrop keepStaticSecretDrop_iff keepStaticSecretDrop_entry
  staticSecretDrop_codeLoaded_stripExecOutside
  StaticSecretDropEntryGuard
  staticSecretDrop_keepLr_false_after_hook_of_codeLoaded_u
  trapHook_f3EmptyZeroizeGhostHook_of_cover_static
  f3EmptyStaticSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_steps_lift_of_visitedIn_noExtern
)

/-! ## 1. Row Anchor Definitions, Algebraic Identities & `CodeLoaded` Bridges -/

/-- Kept-region byte predicate `[resolve mpl lsStaticSecretDropSym, resolve mpl lsStaticSecretDropSym + 252)`
    for `lsStaticSecretDropSym`. -/
@[expose] def keepR_staticSecretDrop (mpl : Obj.MultiPlacement) : BitVec 64 → Bool :=
  keepStaticSecretDrop (libsignalSessionLib.resolve mpl lsStaticSecretDropSym)

/-- `lsStaticSecretDropSym`'s resolved entry address lies inside `keepR_staticSecretDrop mpl`. -/
theorem keepR_staticSecretDrop_entry (mpl : Obj.MultiPlacement) :
    keepR_staticSecretDrop mpl (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) = true :=
  keepStaticSecretDrop_entry (libsignalSessionLib.resolve mpl lsStaticSecretDropSym)

/-- Pure 63-word (`252`-byte) sub-program holding `zeroize32Words` at
    `libsignalSessionLib.resolve mpl lsStaticSecretDropSym`. -/
@[expose] def staticSecretDropSubProg (mpl : Obj.MultiPlacement) : Program :=
  pureWordsProg (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) zeroize32Words

theorem staticSecretDropSubProg_base (mpl : Obj.MultiPlacement) :
    (staticSecretDropSubProg mpl).base =
      libsignalSessionLib.resolve mpl lsStaticSecretDropSym := by
  dsimp only [staticSecretDropSubProg, pureWordsProg, Program.ofWords]

theorem staticSecretDropSubProg_svc (mpl : Obj.MultiPlacement) :
    (staticSecretDropSubProg mpl).svc = Syscall.standard := rfl

theorem staticSecretDropSubProg_externAt_none (mpl : Obj.MultiPlacement) (pc : BitVec 64) :
    (staticSecretDropSubProg mpl).externAt? pc = none :=
  pureWordsProg_externAt_none
    (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) zeroize32Words pc

theorem staticSecretDropSubProg_hasWords (mpl : Obj.MultiPlacement) :
    (staticSecretDropSubProg mpl).hasWords
      (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) zeroize32Words :=
  pureWordsProg_zeroize32_hasWords (libsignalSessionLib.resolve mpl lsStaticSecretDropSym)

private theorem flatMap_wordToBytesLE_length (ws : List (BitVec 32)) :
    (ws.flatMap Program.wordToBytesLE).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w tl ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, ih]
    have hw : (Program.wordToBytesLE w).length = 4 := rfl
    omega

theorem staticSecretDropSubProg_code_length (mpl : Obj.MultiPlacement) :
    (staticSecretDropSubProg mpl).code.length = staticSecretDropByteLen := by
  dsimp only [staticSecretDropSubProg, pureWordsProg, Program.ofWords]
  rw [flatMap_wordToBytesLE_length]
  rfl

theorem keepR_staticSecretDrop_of_code_offset (mpl : Obj.MultiPlacement) {off : Nat}
    (hoff : off < (staticSecretDropSubProg mpl).code.length) :
    keepR_staticSecretDrop mpl
      ((staticSecretDropSubProg mpl).base + BitVec.ofNat 64 off) = true := by
  rw [staticSecretDropSubProg_code_length] at hoff
  rw [staticSecretDropSubProg_base]
  dsimp only [keepR_staticSecretDrop]
  rw [keepStaticSecretDrop_iff]
  have hsub :
      (libsignalSessionLib.resolve mpl lsStaticSecretDropSym + BitVec.ofNat 64 off) -
        libsignalSessionLib.resolve mpl lsStaticSecretDropSym =
      BitVec.ofNat 64 off := by bv_omega
  have hoff_lt : off < 2 ^ 64 := by
    have hb : staticSecretDropByteLen = 252 := rfl
    omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]
  exact hoff

/-- Forward `CodeLoaded` projection onto `stripExecOutside (keepR_staticSecretDrop mpl) mem`. -/
theorem staticSecretDropSubProg_codeLoaded_stripExecOutside
    {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (staticSecretDropSubProg mpl).CodeLoaded mem) :
    (staticSecretDropSubProg mpl).CodeLoaded
      (stripExecOutside (keepR_staticSecretDrop mpl) mem) :=
  staticSecretDrop_codeLoaded_stripExecOutside
    (fun _ hoff => keepR_staticSecretDrop_of_code_offset mpl hoff) hL

/-- Reverse `CodeLoaded` projection from `stripExecOutside (keepR_staticSecretDrop mpl) mem` back
    to `mem`. -/
theorem staticSecretDropSubProg_codeLoaded_of_stripExecOutside
    {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (staticSecretDropSubProg mpl).CodeLoaded
      (stripExecOutside (keepR_staticSecretDrop mpl) mem)) :
    (staticSecretDropSubProg mpl).CodeLoaded mem := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hk : keepR_staticSecretDrop mpl
      ((staticSecretDropSubProg mpl).base + BitVec.ofNat 64 i) = true :=
    keepR_staticSecretDrop_of_code_offset mpl hi
  have hbyte := hL.byte_eq i hi
  have hperm := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [ProofLib.strip_read8] at hbyte
  rw [ProofLib.strip_perm_of_keep hk] at hperm
  rw [ProofLib.strip_isLazyFree] at hlf
  exact ⟨hbyte, hperm, hlf⟩

theorem staticSecretDropSubProg_codeLoaded_stripExecOutside_iff
    {mpl : Obj.MultiPlacement} {mem : Memory} :
    (staticSecretDropSubProg mpl).CodeLoaded
      (stripExecOutside (keepR_staticSecretDrop mpl) mem) ↔
      (staticSecretDropSubProg mpl).CodeLoaded mem :=
  ⟨staticSecretDropSubProg_codeLoaded_of_stripExecOutside,
   staticSecretDropSubProg_codeLoaded_stripExecOutside⟩

/-- `W`-independent ghost hook for `lsStaticSecretDropSym`
    (`CliGhostHooks.extra` entry `(lsStaticSecretDropSym, staticSecretDropGhost mpl mmpl)`). -/
@[expose] noncomputable def staticSecretDropGhost (mpl _mmpl : Obj.MultiPlacement) :
    State → State :=
  f3EmptyZeroizeGhostHook (keepR_staticSecretDrop mpl) (staticSecretDropSubProg mpl)
    (libsignalSessionLib.resolve mpl lsStaticSecretDropSym)

/-- `K`-narrowed `W`-independent ghost hook companion for `lsStaticSecretDropSym`
    (spare only; N2). -/
@[expose] noncomputable def staticSecretDropGhostK (mpl _mmpl : Obj.MultiPlacement) :
    State → State :=
  f3EmptyZeroizeGhostHookK (keepR_staticSecretDrop mpl) (staticSecretDropSubProg mpl)
    (libsignalSessionLib.resolve mpl lsStaticSecretDropSym)

/-- Block-`617` entry-state `lr` guard for `lsStaticSecretDropSym`:
    `keepR_staticSecretDrop mpl (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ resolve mpl lsStaticSecretDropSym`. -/
@[expose] def staticSecretDropEntryGuard (mpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  StaticSecretDropEntryGuard (libsignalSessionLib.resolve mpl lsStaticSecretDropSym)
    (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) s0

theorem staticSecretDropEntryGuard_iff (mpl : Obj.MultiPlacement) (s0 : State) :
    staticSecretDropEntryGuard mpl s0 ↔
      keepR_staticSecretDrop mpl (s0.readReg64 .lr) = false ∧
        s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl lsStaticSecretDropSym :=
  Iff.rfl

/-! ## 2. Artifact 1 — Unconditional `GhostRowSpecOk lsStaticSecretDropSym (staticSecretDropGhost mpl mmpl)` -/

theorem staticSecretDropGhost_fs (mpl mmpl : Obj.MultiPlacement) (s : State) :
    (staticSecretDropGhost mpl mmpl s).fs = s.fs :=
  f3EmptyZeroizeGhostHook_fs (keepR_staticSecretDrop mpl) (staticSecretDropSubProg mpl)
    (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) s

theorem staticSecretDropGhost_fsT (mpl mmpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (staticSecretDropGhost mpl mmpl) :=
  f3EmptyZeroizeGhostHook_fsT (keepR_staticSecretDrop mpl) (staticSecretDropSubProg mpl)
    (libsignalSessionLib.resolve mpl lsStaticSecretDropSym)

theorem staticSecretDropGhost_vmPreserved (mpl mmpl : Obj.MultiPlacement) (s : State) :
    LibsignalBinary.Heap.VmPreserved s (staticSecretDropGhost mpl mmpl s) :=
  f3EmptyZeroizeGhostHook_vmPreserved_of_process
    (staticSecretDropSubProg_svc mpl)
    (staticSecretDropSubProg_externAt_none mpl)
    (subroutine_ok_processZeroize_of_hasWords (staticSecretDropSubProg_externAt_none mpl)
      (staticSecretDropSubProg_hasWords mpl))
    s

/-- Unconditional `StaticSecretDropRowSpec` for `staticSecretDropGhost mpl mmpl`
    (`0` layout or memory premises). -/
theorem staticSecretDropGhost_staticSecretDropRowSpec (mpl mmpl : Obj.MultiPlacement) :
    StaticSecretDropRowSpec (staticSecretDropGhost mpl mmpl) :=
  StaticSecretDropRowSpec.of_vm
    (hookOk_zeroizeSecret_of_master
      (f3EmptyZeroizeGhostHook_master_ok_of_process
        (staticSecretDropSubProg_svc mpl)
        (staticSecretDropSubProg_externAt_none mpl)
        (subroutine_ok_processZeroize_of_hasWords (staticSecretDropSubProg_externAt_none mpl)
          (staticSecretDropSubProg_hasWords mpl))))
    (staticSecretDropGhost_vmPreserved mpl mmpl)

/-- **Artifact 1 (`C11` §1.2, §6.1):** Unconditional
    `GhostRowSpecOk lsStaticSecretDropSym (staticSecretDropGhost mpl mmpl)` for all `(mpl, mmpl)`
    (`0` stock-side or layout premises). -/
theorem staticSecretDropGhost_rowSpecOk [LibsignalPlacement] (mpl mmpl : Obj.MultiPlacement) :
    GhostRowSpecOk lsStaticSecretDropSym (staticSecretDropGhost mpl mmpl) where
  fs_eq := staticSecretDropGhost_fs mpl mmpl
  fsT := staticSecretDropGhost_fsT mpl mmpl
  rowSpec := by
    have h1 : (lsStaticSecretDropSym == "bcmp") = false := by decide
    have h2 : (lsStaticSecretDropSym == "strlen") = false := by decide
    have h3 : (lsStaticSecretDropSym == "memmove") = false := by decide
    have h4 : (lsStaticSecretDropSym == lsFromUtf8Sym) = false := by decide
    have h5 : (lsStaticSecretDropSym == lsMemrchrSym) = false := by decide
    have h6 : (lsStaticSecretDropSym == lsDurationSinceSym) = false := by decide
    have h7 : (lsStaticSecretDropSym == lsTimeAddSym) = false := by decide
    have h8 : (lsStaticSecretDropSym == lsBlackBoxSym) = false := by decide
    have h9 : (lsStaticSecretDropSym == lsStaticSecretDropSym) = true := by decide
    dsimp only [ExtraRowSpec]
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, Bool.false_eq_true, ↓reduceIte]
    exact staticSecretDropGhost_staticSecretDropRowSpec mpl mmpl

/-! ## 3. `ExecFrozen` Preservation & Generic-`InvS` `GhostRowReplayOn` (Artifact 2a) -/

theorem staticSecretDropGhost_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (staticSecretDropGhost mpl mmpl u).mem :=
  f3EmptyZeroizeGhostHook_preserves_execFrozen (keepR_staticSecretDrop mpl)
    (staticSecretDropSubProg mpl)
    (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) hfr

theorem staticSecretDropGhostK_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (staticSecretDropGhostK mpl mmpl u).mem :=
  f3EmptyZeroizeGhostHookK_preserves_execFrozen (keepR_staticSecretDrop mpl)
    (staticSecretDropSubProg mpl)
    (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) hfr

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

/-- **Artifact 2a (`C11` §1.3, §6.2) — Generic-`InvS` `GhostRowReplayOn` for
    `lsStaticSecretDropSym`:**
    - **F1 compliance:** `hRealHullNoExt` quantifies over `keepR_staticSecretDrop mpl pc = true`
      **only** on the de-hooked real program `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`
      (post-Cutover-2). On the ghost program `cliProgExtPlacedAt mpl EG 617 W`, `hGhostNoExtNe`
      strictly excludes `pc ≠ libsignalSessionLib.resolve mpl lsStaticSecretDropSym`.
    - **H1 compliance:** `hCL` supplies `(staticSecretDropSubProg mpl).CodeLoaded u.mem` at
      intermediate call state `u` from `InvS u` (never `s0.mem`). -/
theorem staticSecretDropGhost_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (staticSecretDropSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) =
        some (staticSecretDropGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_staticSecretDrop mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_staticSecretDrop mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsStaticSecretDropSym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsStaticSecretDropSym
      (staticSecretDropEntryGuard mpl) (staticSecretDropGhost mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨staticSecretDropGhost_preserves_execFrozen mpl mmpl hfr,
     staticSecretDropGhost_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    right
    refine ⟨hRealHullNoExt W (keepR_staticSecretDrop_entry mpl), ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (staticSecretDropSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hLrOut : keepR_staticSecretDrop mpl (u.readReg64 .lr) = false :=
      f3EmptyStaticSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_sub := staticSecretDropSubProg mpl)
        (keepR := keepR_staticSecretDrop mpl)
        (entry := libsignalSessionLib.resolve mpl lsStaticSecretDropSym)
        (stubPc := libsignalSessionLib.resolve mpl lsStaticSecretDropSym)
        (entryTarget := libsignalSessionLib.resolve mpl lsStaticSecretDropSym)
        (staticSecretDropSubProg_hasWords mpl)
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
        (staticSecretDropSubProg mpl).CodeLoaded
          (stripExecOutside (keepR_staticSecretDrop mpl) u.mem) :=
      staticSecretDropSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨hvis, hfr_fu, hfs_fu⟩ :=
      f3EmptyZeroizeGhostHook_visitedIn
        (keep := keepR_staticSecretDrop mpl)
        (P_sub := staticSecretDropSubProg mpl)
        (entryTarget := libsignalSessionLib.resolve mpl lsStaticSecretDropSym)
        (staticSecretDropSubProg_svc mpl)
        (staticSecretDropSubProg_externAt_none mpl)
        (staticSecretDropSubProg_hasWords mpl)
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (libsignalSessionLib.resolve mpl lsStaticSecretDropSym))
          (staticSecretDropGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_staticSecretDrop mpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) = u :=
      setPC_eq_self_of_pc_eq hpc
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (staticSecretDropGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- `C4` interior-stub signature wrapper for `staticSecretDropGhost_rowReplayOn` (accepting split
    `hRealNone` at `stubPc` + `hInteriorGhost` with the `Or.inr` `TrapHook` interior-stub disjunct
    on `pc ≠ resolve mpl lsStaticSecretDropSym`). -/
theorem staticSecretDropGhost_rowReplayOn_of_interior
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (staticSecretDropSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) =
        some (staticSecretDropGhost mpl mmpl))
    (hRealNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) = none)
    (hInteriorGhost : ∀ (W : CliHooks) (pc : BitVec 64),
      keepR_staticSecretDrop mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsStaticSecretDropSym →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none ∧
      ((cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ gStub, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some gStub ∧
          ∀ L : BitVec 64, keepR_staticSecretDrop mpl L = true → TrapHook L gStub)) :
    GhostRowReplayOn mpl mmpl InvS EG lsStaticSecretDropSym
      (staticSecretDropEntryGuard mpl) (staticSecretDropGhost mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨staticSecretDropGhost_preserves_execFrozen mpl mmpl hfr,
     staticSecretDropGhost_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    have hRealHullNoExt : ∀ {pc : BitVec 64},
        keepR_staticSecretDrop mpl pc = true →
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl lsStaticSecretDropSym
      · rw [hEq]; exact hRealNone W
      · exact (hInteriorGhost W pc hk hEq).1
    have hRegExt : ∀ pc : BitVec 64,
        keepStaticSecretDrop (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) pc = true →
        (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
          ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
            ∀ L, keepStaticSecretDrop
              (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) L = true →
              TrapHook L f := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl lsStaticSecretDropSym
      · rw [hEq]
        exact Or.inr ⟨staticSecretDropGhost mpl mmpl, hGhostAt W, fun L hL =>
          trapHook_f3EmptyZeroizeGhostHook_of_cover_static (staticSecretDropSubProg mpl)
            (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) (fun _ h => h) hL⟩
      · rcases (hInteriorGhost W pc hk hEq).2 with hNone | ⟨gStub, hSome, hTrap⟩
        · exact Or.inl hNone
        · exact Or.inr ⟨gStub, hSome, hTrap⟩
    right
    refine ⟨hRealNone W, ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (staticSecretDropSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hLrOut : keepR_staticSecretDrop mpl (u.readReg64 .lr) = false :=
      staticSecretDrop_keepLr_false_after_hook_of_codeLoaded_u
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_sub := staticSecretDropSubProg mpl)
        (entry := libsignalSessionLib.resolve mpl lsStaticSecretDropSym)
        (f_stub := staticSecretDropGhost mpl mmpl)
        (staticSecretDropSubProg_hasWords mpl)
        hRegExt
        (fun _ hL => trapHook_f3EmptyZeroizeGhostHook_of_cover_static
          (staticSecretDropSubProg mpl)
          (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) (fun _ h => h) hL)
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
        (staticSecretDropSubProg mpl).CodeLoaded
          (stripExecOutside (keepR_staticSecretDrop mpl) u.mem) :=
      staticSecretDropSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨hvis, hfr_fu, hfs_fu⟩ :=
      f3EmptyZeroizeGhostHook_visitedIn
        (keep := keepR_staticSecretDrop mpl)
        (P_sub := staticSecretDropSubProg mpl)
        (entryTarget := libsignalSessionLib.resolve mpl lsStaticSecretDropSym)
        (staticSecretDropSubProg_svc mpl)
        (staticSecretDropSubProg_externAt_none mpl)
        (staticSecretDropSubProg_hasWords mpl)
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (libsignalSessionLib.resolve mpl lsStaticSecretDropSym))
          (staticSecretDropGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_staticSecretDrop mpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt hk)
        hvis
    have hSetPC : u.setPC (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) = u :=
      setPC_eq_self_of_pc_eq hpc
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (staticSecretDropGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- `K`-narrowed `staticSecretDropGhostK` companion `GhostRowReplayOn`
    (`entryGuard := fun _ => True`; spare only per N2). -/
theorem staticSecretDropGhostK_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (staticSecretDropSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_staticSecretDrop mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsStaticSecretDropSym
      (fun _ => True) (staticSecretDropGhostK mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨staticSecretDropGhostK_preserves_execFrozen mpl mmpl hfr,
     f3EmptyZeroizeGhostHookK_fs (keepR_staticSecretDrop mpl) (staticSecretDropSubProg mpl)
       (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealHullNoExt W (keepR_staticSecretDrop_entry mpl), ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hCodeStrip :
        (staticSecretDropSubProg mpl).CodeLoaded
          (stripExecOutside (keepR_staticSecretDrop mpl) u.mem) :=
      staticSecretDropSubProg_codeLoaded_stripExecOutside (hCL u hInvU)
    obtain ⟨hvis, hfr_fu, hfs_fu⟩ :=
      f3EmptyZeroizeGhostHookK_visitedIn
        (keep := keepR_staticSecretDrop mpl)
        (P_sub := staticSecretDropSubProg mpl)
        (entryTarget := libsignalSessionLib.resolve mpl lsStaticSecretDropSym)
        (staticSecretDropSubProg_svc mpl)
        (staticSecretDropSubProg_externAt_none mpl)
        (staticSecretDropSubProg_hasWords mpl)
        hrun
        hnoex
        hfr
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (libsignalSessionLib.resolve mpl lsStaticSecretDropSym))
          (staticSecretDropGhostK mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_staticSecretDrop mpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) = u :=
      setPC_eq_self_of_pc_eq hpc
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (staticSecretDropGhostK mpl mmpl u) hInvU hkf hfs_fu⟩

/-- Guard-strengthening adapter on `GhostRowReplayOn`. -/
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

/-- Full per-row `GhostRowOk` bundle (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) for
    `lsStaticSecretDropSym`. -/
theorem staticSecretDropGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (staticSecretDropSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) =
        some (staticSecretDropGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_staticSecretDrop mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_staticSecretDrop mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsStaticSecretDropSym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl InvS EG lsStaticSecretDropSym
      (staticSecretDropEntryGuard mpl) (staticSecretDropGhost mpl mmpl) :=
  ⟨staticSecretDropGhost_rowSpecOk mpl mmpl,
   staticSecretDropGhost_rowReplayOn mpl mmpl InvS EG
     hCL hInvKeep hGhostAt hRealHullNoExt hGhostNoExtNe⟩

/-! ## 4. Per-Arm & Singleton `ExtraEntryGuard` Helpers (`.text.lib2` Interface) -/

/-- Per-arm `lsStaticSecretDropSym` discharge for any `guardOf : String → State → Prop` agreeing
    with `staticSecretDropEntryGuard mpl` on `lsStaticSecretDropSym`. -/
theorem extraEntryGuard_staticSecretDrop_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf lsStaticSecretDropSym s0 ↔ staticSecretDropEntryGuard mpl s0)
    (hDropGuard : staticSecretDropEntryGuard mpl s0) :
    guardOf lsStaticSecretDropSym s0 :=
  hGuardEq.mpr hDropGuard

/-- Table-level `ExtraEntryGuard guardOf g s0` discharge when `g.extra` carries the singleton
    `lsStaticSecretDropSym` row `[(lsStaticSecretDropSym, staticSecretDropGhost mpl mmpl)]` (N3). -/
theorem extraEntryGuard_singleton_staticSecretDrop
    {mpl mmpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hg : g.extra = [(lsStaticSecretDropSym, staticSecretDropGhost mpl mmpl)])
    (hGuardEq : guardOf lsStaticSecretDropSym s0 ↔ staticSecretDropEntryGuard mpl s0)
    (hDropGuard : staticSecretDropEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 := by
  intro sym f _ hLook
  rw [hg] at hLook
  simp only [List.lookup] at hLook
  by_cases hSym : (sym == lsStaticSecretDropSym) = true
  · have hEq : sym = lsStaticSecretDropSym := eq_of_beq hSym
    subst hEq
    exact hGuardEq.mpr hDropGuard
  · simp [hSym] at hLook

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays
