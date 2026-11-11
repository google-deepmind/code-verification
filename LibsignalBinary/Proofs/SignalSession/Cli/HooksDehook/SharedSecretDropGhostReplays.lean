/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Card CC-DALEK — `lsSharedSecretDropSym` Row Consumer Spec & Generic-`InvS` Ghost Replay (`HooksDehook.SharedSecretDropGhostReplays`)

Cutover-2 `c`-card for `<x25519_dalek::SharedSecret as Drop>::drop` (`lsSharedSecretDropSym`) in
the `W2-C11` `CliGhostHooks.extra` framework (`ccard_recipe.md` §2.2, §5 row 7), modeled directly
on `BcmpGhostReplays.lean` (`0` `CliElfLib` / `ElfF3Relink` / C2 / trusted imports):

1. **Row Anchor & `W`-Independent Ghost (`sharedSecretDropHullBase`, `keepR_sharedSecretDrop`,
   `sharedSecretDropSubProg`, `sharedSecretDropGhost`):**
   - `lsSharedSecretDropSym` (`b #-252`, `4` B = `1` word) is in `libsignalSessionLib`, whereas
     `<MontgomeryPoint as Zeroize>::zeroize` (`252` B = `63` words `zeroize32Words`) is unhooked
     and absent from `libsignalSessionLib`. Following `BcmpGhostReplays.bcmpHullBase`,
     `sharedSecretDropHullBase mpl := libsignalSessionLib.resolve mpl lsSharedSecretDropSym -
     sharedSecretDropEntryOff` (`252#64`) encodes the contiguous `64`-word (`256` B) hull base
     with the unconditional identity
     `sharedSecretDropHullBase mpl + sharedSecretDropEntryOff =
     libsignalSessionLib.resolve mpl lsSharedSecretDropSym` (`0` premises; if a hypothetical
     layout placed other bytes at `- 252#64`, `(sharedSecretDropSubProg mpl).CodeLoaded u.mem`
     would simply not hold rather than introducing any assumption).
   - `sharedSecretDropGhost mpl mmpl` wraps `ZeroizeGhost.f3EmptySharedSecretDropGhostHook`
     (`P_real := emptyStdProg`, `fallback := zeroizeSecretHook`), with **zero `W : CliHooks`
     dependence**.
2. **Artifact 1 — Unconditional `GhostRowSpecOk lsSharedSecretDropSym (sharedSecretDropGhost mpl mmpl)`
   (`0` premises):**
   - `sharedSecretDropGhost_rowSpecOk` proves `fs_eq`, `fsT : HookFsTraced IsFsC`, and
     `SharedSecretDropRowSpec` (`zeroizeSecretSpec`, plain, `withVmPreserved`, and `withAlloc A lim`)
     unconditionally via `SharedSecretDropRowSpec.of_vm`.
3. **Artifact 2a — Generic-`InvS` `GhostRowReplayOn` & `GhostRowOk` (`F1` + `H1` compliant):**
   - **F1 (`pc ≠ resolve mpl lsSharedSecretDropSym` exclusion ONLY on `P_ghost`, whole-hull on
     de-hooked `P_real`):** `hRealHullNoExt` quantifies over all `256` B
     `keepR_sharedSecretDrop mpl pc = true` on `P_real` only; `hGhostNoExtNe` strictly excludes
     `pc ≠ libsignalSessionLib.resolve mpl lsSharedSecretDropSym` on `P_ghost` (unhooked `zeroize`
     at `sharedSecretDropHullBase mpl` is NOT excluded!) and routes through
     `SharedSecretDropLrTrap.f3EmptySharedSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u`.
   - **H1 (`CodeLoaded u.mem` from `InvS u`):** `hCL` supplies
     `(sharedSecretDropSubProg mpl).CodeLoaded u.mem` at intermediate call state `u` from `InvS u`
     (never `s0.mem`), accompanied by `sharedSecretDropSubProg_codeLoaded_stripExecOutside_iff`.
   - Includes `C4` interior-stub wrapper `sharedSecretDropGhost_rowReplayOn_of_interior`,
     `K`-narrowed spare `sharedSecretDropGhostK_rowReplayOn`, full `sharedSecretDropGhost_rowOk`,
     and per-arm / singleton entry-guard helpers `extraEntryGuard_sharedSecretDrop_arm` /
     `extraEntryGuard_singleton_sharedSecretDrop` (`.text.lib2` layout instantiation belongs to the
     C2 layout / STARTUP seat per `02:28Z` split).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced libsignalSessionLib
  lsBlackBoxSym lsDurationSinceSym lsFromUtf8Sym lsMemrchrSym
  lsSharedSecretDropSym lsStaticSecretDropSym lsTimeAddSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec (
  SharedSecretDropRowSpec
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
  sharedSecretDropHullWords
  hookOk_zeroizeSecret_of_master
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost (
  sharedSecretDropEntryOff
  f3EmptySharedSecretDropGhostHook f3EmptySharedSecretDropGhostHookK
  f3EmptyZeroizeGhostHook_fs f3EmptyZeroizeGhostHookK_fs
  f3EmptyZeroizeGhostHook_fsT
  f3EmptyZeroizeGhostHook_preserves_execFrozen f3EmptyZeroizeGhostHookK_preserves_execFrozen
  subroutine_ok_sharedSecretHull_processZeroize_of_hasWords
  f3EmptyZeroizeGhostHook_master_ok_of_process
  f3EmptyZeroizeGhostHook_vmPreserved_of_process
  f3EmptySharedSecretDropGhostHook_visitedIn f3EmptySharedSecretDropGhostHookK_visitedIn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap (
  sharedSecretDropHullByteLen keepSharedSecretDropHull
  keepSharedSecretDropHull_iff keepSharedSecretDropHull_entry
  pureWordsProg_sharedSecretDropHull_hasWords
  sharedSecretDropHull_codeLoaded_stripExecOutside
  SharedSecretDropEntryGuard
  trapHook_f3EmptySharedSecretDropGhostHook_of_cover
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropLrTrap (
  sharedSecretDropHull_keepLr_false_after_hook_of_codeLoaded_u
  f3EmptySharedSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_steps_lift_of_visitedIn_noExtern
)

/-! ## 1. Row Anchor Definitions, Algebraic Identities & `CodeLoaded` Bridges -/

/-- Computed base address of the contiguous 256-byte (`64`-word)
    `zeroize32Words ++ [sharedSecretDropBackWord]` hull for placement `mpl`, defined relative to
    `lsSharedSecretDropSym` (`resolve mpl lsSharedSecretDropSym - sharedSecretDropEntryOff`)
    because `<MontgomeryPoint as Zeroize>::zeroize` (`252` B) is unhooked and absent from
    `libsignalSessionLib`. -/
@[expose] def sharedSecretDropHullBase (mpl : Obj.MultiPlacement) : BitVec 64 :=
  libsignalSessionLib.resolve mpl lsSharedSecretDropSym - sharedSecretDropEntryOff

/-- Unconditional BitVec identity:
    `sharedSecretDropHullBase mpl + sharedSecretDropEntryOff = resolve mpl lsSharedSecretDropSym`. -/
theorem sharedSecretDropHullBase_add_entryOff (mpl : Obj.MultiPlacement) :
    sharedSecretDropHullBase mpl + sharedSecretDropEntryOff =
      libsignalSessionLib.resolve mpl lsSharedSecretDropSym := by
  dsimp only [sharedSecretDropHullBase]
  bv_omega

/-- Kept-region byte predicate `[sharedSecretDropHullBase mpl, sharedSecretDropHullBase mpl + 256)`
    for `lsSharedSecretDropSym`. -/
@[expose] def keepR_sharedSecretDrop (mpl : Obj.MultiPlacement) : BitVec 64 → Bool :=
  keepSharedSecretDropHull (sharedSecretDropHullBase mpl)

/-- `lsSharedSecretDropSym`'s resolved entry address lies inside `keepR_sharedSecretDrop mpl`. -/
theorem keepR_sharedSecretDrop_entry (mpl : Obj.MultiPlacement) :
    keepR_sharedSecretDrop mpl (libsignalSessionLib.resolve mpl lsSharedSecretDropSym) = true := by
  dsimp only [keepR_sharedSecretDrop]
  rw [← sharedSecretDropHullBase_add_entryOff mpl]
  exact keepSharedSecretDropHull_entry (sharedSecretDropHullBase mpl)

/-- Pure 64-word (`256`-byte) sub-program holding `sharedSecretDropHullWords` at
    `sharedSecretDropHullBase mpl`. -/
@[expose] def sharedSecretDropSubProg (mpl : Obj.MultiPlacement) : Program :=
  pureWordsProg (sharedSecretDropHullBase mpl) sharedSecretDropHullWords

theorem sharedSecretDropSubProg_base (mpl : Obj.MultiPlacement) :
    (sharedSecretDropSubProg mpl).base = sharedSecretDropHullBase mpl := rfl

theorem sharedSecretDropSubProg_svc (mpl : Obj.MultiPlacement) :
    (sharedSecretDropSubProg mpl).svc = Syscall.standard := rfl

theorem sharedSecretDropSubProg_externAt_none (mpl : Obj.MultiPlacement) (pc : BitVec 64) :
    (sharedSecretDropSubProg mpl).externAt? pc = none :=
  pureWordsProg_externAt_none (sharedSecretDropHullBase mpl) sharedSecretDropHullWords pc

theorem sharedSecretDropSubProg_hasWords (mpl : Obj.MultiPlacement) :
    (sharedSecretDropSubProg mpl).hasWords
      (sharedSecretDropHullBase mpl) sharedSecretDropHullWords :=
  pureWordsProg_sharedSecretDropHull_hasWords (sharedSecretDropHullBase mpl)

private theorem flatMap_wordToBytesLE_length (ws : List (BitVec 32)) :
    (ws.flatMap Program.wordToBytesLE).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w tl ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, ih]
    have hw : (Program.wordToBytesLE w).length = 4 := rfl
    omega

theorem sharedSecretDropSubProg_code_length (mpl : Obj.MultiPlacement) :
    (sharedSecretDropSubProg mpl).code.length = sharedSecretDropHullByteLen := by
  dsimp only [sharedSecretDropSubProg, pureWordsProg, Program.ofWords]
  rw [flatMap_wordToBytesLE_length]
  rfl

theorem keepR_sharedSecretDrop_of_code_offset (mpl : Obj.MultiPlacement) {off : Nat}
    (hoff : off < (sharedSecretDropSubProg mpl).code.length) :
    keepR_sharedSecretDrop mpl
      ((sharedSecretDropSubProg mpl).base + BitVec.ofNat 64 off) = true := by
  rw [sharedSecretDropSubProg_code_length] at hoff
  rw [sharedSecretDropSubProg_base]
  dsimp only [keepR_sharedSecretDrop]
  rw [keepSharedSecretDropHull_iff]
  have hsub :
      (sharedSecretDropHullBase mpl + BitVec.ofNat 64 off) - sharedSecretDropHullBase mpl =
      BitVec.ofNat 64 off := by bv_omega
  have hoff_lt : off < 2 ^ 64 := by
    have hb : sharedSecretDropHullByteLen = 256 := rfl
    omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]
  exact hoff

/-- Forward `CodeLoaded` projection onto `stripExecOutside (keepR_sharedSecretDrop mpl) mem`. -/
theorem sharedSecretDropSubProg_codeLoaded_stripExecOutside
    {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (sharedSecretDropSubProg mpl).CodeLoaded mem) :
    (sharedSecretDropSubProg mpl).CodeLoaded
      (stripExecOutside (keepR_sharedSecretDrop mpl) mem) :=
  sharedSecretDropHull_codeLoaded_stripExecOutside
    (fun _ hoff => keepR_sharedSecretDrop_of_code_offset mpl hoff) hL

/-- Reverse `CodeLoaded` projection from `stripExecOutside (keepR_sharedSecretDrop mpl) mem` back
    to `mem`. -/
theorem sharedSecretDropSubProg_codeLoaded_of_stripExecOutside
    {mpl : Obj.MultiPlacement} {mem : Memory}
    (hL : (sharedSecretDropSubProg mpl).CodeLoaded
      (stripExecOutside (keepR_sharedSecretDrop mpl) mem)) :
    (sharedSecretDropSubProg mpl).CodeLoaded mem := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hk : keepR_sharedSecretDrop mpl
      ((sharedSecretDropSubProg mpl).base + BitVec.ofNat 64 i) = true :=
    keepR_sharedSecretDrop_of_code_offset mpl hi
  have hbyte := hL.byte_eq i hi
  have hperm := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [ProofLib.strip_read8] at hbyte
  rw [ProofLib.strip_perm_of_keep hk] at hperm
  rw [ProofLib.strip_isLazyFree] at hlf
  exact ⟨hbyte, hperm, hlf⟩

theorem sharedSecretDropSubProg_codeLoaded_stripExecOutside_iff
    {mpl : Obj.MultiPlacement} {mem : Memory} :
    (sharedSecretDropSubProg mpl).CodeLoaded
      (stripExecOutside (keepR_sharedSecretDrop mpl) mem) ↔
      (sharedSecretDropSubProg mpl).CodeLoaded mem :=
  ⟨sharedSecretDropSubProg_codeLoaded_of_stripExecOutside,
   sharedSecretDropSubProg_codeLoaded_stripExecOutside⟩

/-- `W`-independent ghost hook for `lsSharedSecretDropSym`
    (`CliGhostHooks.extra` entry `(lsSharedSecretDropSym, sharedSecretDropGhost mpl mmpl)`). -/
@[expose] noncomputable def sharedSecretDropGhost (mpl _mmpl : Obj.MultiPlacement) :
    State → State :=
  f3EmptySharedSecretDropGhostHook (keepR_sharedSecretDrop mpl) (sharedSecretDropSubProg mpl)
    (sharedSecretDropHullBase mpl)

/-- `K`-narrowed `W`-independent ghost hook companion for `lsSharedSecretDropSym`
    (spare only; N2). -/
@[expose] noncomputable def sharedSecretDropGhostK (mpl _mmpl : Obj.MultiPlacement) :
    State → State :=
  f3EmptySharedSecretDropGhostHookK (keepR_sharedSecretDrop mpl) (sharedSecretDropSubProg mpl)
    (sharedSecretDropHullBase mpl)

/-- Block-`617` entry-state `lr` guard for `lsSharedSecretDropSym`:
    `keepR_sharedSecretDrop mpl (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ resolve mpl lsSharedSecretDropSym`. -/
@[expose] def sharedSecretDropEntryGuard (mpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  SharedSecretDropEntryGuard (sharedSecretDropHullBase mpl)
    (libsignalSessionLib.resolve mpl lsSharedSecretDropSym) s0

theorem sharedSecretDropEntryGuard_iff (mpl : Obj.MultiPlacement) (s0 : State) :
    sharedSecretDropEntryGuard mpl s0 ↔
      keepR_sharedSecretDrop mpl (s0.readReg64 .lr) = false ∧
        s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl lsSharedSecretDropSym :=
  Iff.rfl

/-! ## 2. Artifact 1 — Unconditional `GhostRowSpecOk lsSharedSecretDropSym (sharedSecretDropGhost mpl mmpl)` -/

theorem sharedSecretDropGhost_fs (mpl mmpl : Obj.MultiPlacement) (s : State) :
    (sharedSecretDropGhost mpl mmpl s).fs = s.fs :=
  f3EmptyZeroizeGhostHook_fs (keepR_sharedSecretDrop mpl) (sharedSecretDropSubProg mpl)
    (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff) s

theorem sharedSecretDropGhost_fsT (mpl mmpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (sharedSecretDropGhost mpl mmpl) :=
  f3EmptyZeroizeGhostHook_fsT (keepR_sharedSecretDrop mpl) (sharedSecretDropSubProg mpl)
    (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff)

theorem sharedSecretDropGhost_vmPreserved (mpl mmpl : Obj.MultiPlacement) (s : State) :
    LibsignalBinary.Heap.VmPreserved s (sharedSecretDropGhost mpl mmpl s) :=
  f3EmptyZeroizeGhostHook_vmPreserved_of_process
    (sharedSecretDropSubProg_svc mpl)
    (sharedSecretDropSubProg_externAt_none mpl)
    (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords
      (sharedSecretDropSubProg_externAt_none mpl)
      (sharedSecretDropSubProg_hasWords mpl))
    s

/-- Unconditional `SharedSecretDropRowSpec` for `sharedSecretDropGhost mpl mmpl`
    (`0` layout or memory premises). -/
theorem sharedSecretDropGhost_sharedSecretDropRowSpec (mpl mmpl : Obj.MultiPlacement) :
    SharedSecretDropRowSpec (sharedSecretDropGhost mpl mmpl) :=
  SharedSecretDropRowSpec.of_vm
    (hookOk_zeroizeSecret_of_master
      (f3EmptyZeroizeGhostHook_master_ok_of_process
        (sharedSecretDropSubProg_svc mpl)
        (sharedSecretDropSubProg_externAt_none mpl)
        (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords
          (sharedSecretDropSubProg_externAt_none mpl)
          (sharedSecretDropSubProg_hasWords mpl))))
    (sharedSecretDropGhost_vmPreserved mpl mmpl)

/-- **Artifact 1 (`C11` §1.2, §6.1):** Unconditional
    `GhostRowSpecOk lsSharedSecretDropSym (sharedSecretDropGhost mpl mmpl)` for all `(mpl, mmpl)`
    (`0` stock-side or layout premises). -/
theorem sharedSecretDropGhost_rowSpecOk [LibsignalPlacement] (mpl mmpl : Obj.MultiPlacement) :
    GhostRowSpecOk lsSharedSecretDropSym (sharedSecretDropGhost mpl mmpl) where
  fs_eq := sharedSecretDropGhost_fs mpl mmpl
  fsT := sharedSecretDropGhost_fsT mpl mmpl
  rowSpec := by
    have h1 : (lsSharedSecretDropSym == "bcmp") = false := by decide
    have h2 : (lsSharedSecretDropSym == "strlen") = false := by decide
    have h3 : (lsSharedSecretDropSym == "memmove") = false := by decide
    have h4 : (lsSharedSecretDropSym == lsFromUtf8Sym) = false := by decide
    have h5 : (lsSharedSecretDropSym == lsMemrchrSym) = false := by decide
    have h6 : (lsSharedSecretDropSym == lsDurationSinceSym) = false := by decide
    have h7 : (lsSharedSecretDropSym == lsTimeAddSym) = false := by decide
    have h8 : (lsSharedSecretDropSym == lsBlackBoxSym) = false := by decide
    have h9 : (lsSharedSecretDropSym == lsStaticSecretDropSym) = false := by decide
    have h10 : (lsSharedSecretDropSym == lsSharedSecretDropSym) = true := by decide
    dsimp only [ExtraRowSpec]
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Bool.false_eq_true, ↓reduceIte]
    exact sharedSecretDropGhost_sharedSecretDropRowSpec mpl mmpl

/-! ## 3. `ExecFrozen` Preservation & Generic-`InvS` `GhostRowReplayOn` (Artifact 2a) -/

theorem sharedSecretDropGhost_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (sharedSecretDropGhost mpl mmpl u).mem :=
  f3EmptyZeroizeGhostHook_preserves_execFrozen (keepR_sharedSecretDrop mpl)
    (sharedSecretDropSubProg mpl)
    (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff) hfr

theorem sharedSecretDropGhostK_preserves_execFrozen (mpl mmpl : Obj.MultiPlacement)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (sharedSecretDropGhostK mpl mmpl u).mem :=
  f3EmptyZeroizeGhostHookK_preserves_execFrozen (keepR_sharedSecretDrop mpl)
    (sharedSecretDropSubProg mpl)
    (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff) hfr

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
    `lsSharedSecretDropSym`:**
    - **F1 compliance:** `hRealHullNoExt` quantifies over all `256` B
      `keepR_sharedSecretDrop mpl pc = true` **only** on the de-hooked real program
      `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` (post-Cutover-2, once
      `lsSharedSecretDropSym` is dropped from `cliHookTablePlaced`, so neither `zeroize` nor
      `SharedSecret::drop` carries an extern hook on `P_real`). On the ghost program
      `cliProgExtPlacedAt mpl EG 617 W`, `hGhostNoExtNe` strictly excludes
      `pc ≠ libsignalSessionLib.resolve mpl lsSharedSecretDropSym` ONLY (unhooked `zeroize` at
      `sharedSecretDropHullBase mpl` is NOT excluded).
    - **H1 compliance:** `hCL` supplies `(sharedSecretDropSubProg mpl).CodeLoaded u.mem` at
      intermediate call state `u` from `InvS u` (never `s0.mem`). -/
theorem sharedSecretDropGhost_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (sharedSecretDropSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsSharedSecretDropSym) =
        some (sharedSecretDropGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_sharedSecretDrop mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_sharedSecretDrop mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsSharedSecretDropSym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsSharedSecretDropSym
      (sharedSecretDropEntryGuard mpl) (sharedSecretDropGhost mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨sharedSecretDropGhost_preserves_execFrozen mpl mmpl hfr,
     sharedSecretDropGhost_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    have hGhostAtEntry :
        (cliProgExtPlacedAt mpl EG 617 W).externAt?
          (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff) =
          some (sharedSecretDropGhost mpl mmpl) := by
      rw [sharedSecretDropHullBase_add_entryOff mpl]
      exact hGhostAt W
    right
    refine ⟨hRealHullNoExt W (keepR_sharedSecretDrop_entry mpl), ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (sharedSecretDropSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hLrOut : keepR_sharedSecretDrop mpl (u.readReg64 .lr) = false :=
      f3EmptySharedSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_sub := sharedSecretDropSubProg mpl)
        (keepR := keepR_sharedSecretDrop mpl)
        (m := sharedSecretDropHullBase mpl)
        (sharedSecretDropSubProg_hasWords mpl)
        (fun _ h => h)
        (fun _ hk hne =>
          hGhostNoExtNe W hk (fun hEq =>
            hne (hEq.trans (sharedSecretDropHullBase_add_entryOff mpl).symm)))
        hGhostAtEntry
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
        (sharedSecretDropSubProg mpl).CodeLoaded
          (stripExecOutside (keepR_sharedSecretDrop mpl) u.mem) :=
      sharedSecretDropSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨hvis, hfr_fu, hfs_fu⟩ :=
      f3EmptySharedSecretDropGhostHook_visitedIn
        (keep := keepR_sharedSecretDrop mpl)
        (P_sub := sharedSecretDropSubProg mpl)
        (m := sharedSecretDropHullBase mpl)
        (sharedSecretDropSubProg_svc mpl)
        (sharedSecretDropSubProg_externAt_none mpl)
        (sharedSecretDropSubProg_hasWords mpl)
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff))
          (sharedSecretDropGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_sharedSecretDrop mpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff) = u :=
      setPC_eq_self_of_pc_eq (hpc.trans (sharedSecretDropHullBase_add_entryOff mpl).symm)
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (sharedSecretDropGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- `C4` interior-stub signature wrapper for `sharedSecretDropGhost_rowReplayOn` (accepting split
    `hRealNone` at `stubPc` + `hInteriorGhost` with the `Or.inr` `TrapHook` interior-stub disjunct
    on `pc ≠ resolve mpl lsSharedSecretDropSym`). -/
theorem sharedSecretDropGhost_rowReplayOn_of_interior
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (sharedSecretDropSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsSharedSecretDropSym) =
        some (sharedSecretDropGhost mpl mmpl))
    (hRealNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsSharedSecretDropSym) = none)
    (hInteriorGhost : ∀ (W : CliHooks) (pc : BitVec 64),
      keepR_sharedSecretDrop mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsSharedSecretDropSym →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none ∧
      ((cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
        ∃ gStub, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some gStub ∧
          ∀ L : BitVec 64, keepR_sharedSecretDrop mpl L = true → TrapHook L gStub)) :
    GhostRowReplayOn mpl mmpl InvS EG lsSharedSecretDropSym
      (sharedSecretDropEntryGuard mpl) (sharedSecretDropGhost mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨sharedSecretDropGhost_preserves_execFrozen mpl mmpl hfr,
     sharedSecretDropGhost_fs mpl mmpl u⟩
  replay_at_stub := by
    intro W s0 sf _ _ _ hEntry hRetPc hNoExSf hNotHaltSf
    have hRealHullNoExt : ∀ {pc : BitVec 64},
        keepR_sharedSecretDrop mpl pc = true →
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl lsSharedSecretDropSym
      · rw [hEq]; exact hRealNone W
      · exact (hInteriorGhost W pc hk hEq).1
    have hRegExt : ∀ pc : BitVec 64,
        keepSharedSecretDropHull (sharedSecretDropHullBase mpl) pc = true →
        (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none ∨
          ∃ f, (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = some f ∧
            ∀ L, keepSharedSecretDropHull (sharedSecretDropHullBase mpl) L = true →
              TrapHook L f := by
      intro pc hk
      by_cases hEq : pc = libsignalSessionLib.resolve mpl lsSharedSecretDropSym
      · rw [hEq]
        exact Or.inr ⟨sharedSecretDropGhost mpl mmpl, hGhostAt W, fun L hL =>
          trapHook_f3EmptySharedSecretDropGhostHook_of_cover
            (sharedSecretDropSubProg mpl) (fun _ h => h) hL⟩
      · rcases (hInteriorGhost W pc hk hEq).2 with hNone | ⟨gStub, hSome, hTrap⟩
        · exact Or.inl hNone
        · exact Or.inr ⟨gStub, hSome, hTrap⟩
    right
    refine ⟨hRealNone W, ?_⟩
    intro u _ hStepsAfter hpc hrun hnoex hkf hfr hInvU
    have hCodeU : (sharedSecretDropSubProg mpl).CodeLoaded u.mem := hCL u hInvU
    have hLrOut : keepR_sharedSecretDrop mpl (u.readReg64 .lr) = false :=
      sharedSecretDropHull_keepLr_false_after_hook_of_codeLoaded_u
        (P_ghost := cliProgExtPlacedAt mpl EG 617 W)
        (P_sub := sharedSecretDropSubProg mpl)
        (m := sharedSecretDropHullBase mpl)
        (f_stub := sharedSecretDropGhost mpl mmpl)
        (sharedSecretDropSubProg_hasWords mpl)
        hRegExt
        (fun _ hL => trapHook_f3EmptySharedSecretDropGhostHook_of_cover
          (sharedSecretDropSubProg mpl) (fun _ h => h) hL)
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
        (sharedSecretDropSubProg mpl).CodeLoaded
          (stripExecOutside (keepR_sharedSecretDrop mpl) u.mem) :=
      sharedSecretDropSubProg_codeLoaded_stripExecOutside hCodeU
    obtain ⟨hvis, hfr_fu, hfs_fu⟩ :=
      f3EmptySharedSecretDropGhostHook_visitedIn
        (keep := keepR_sharedSecretDrop mpl)
        (P_sub := sharedSecretDropSubProg mpl)
        (m := sharedSecretDropHullBase mpl)
        (sharedSecretDropSubProg_svc mpl)
        (sharedSecretDropSubProg_externAt_none mpl)
        (sharedSecretDropSubProg_hasWords mpl)
        hrun
        hnoex
        hfr
        hLrOut
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff))
          (sharedSecretDropGhost mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_sharedSecretDrop mpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt hk)
        hvis
    have hSetPC : u.setPC (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff) = u :=
      setPC_eq_self_of_pc_eq (hpc.trans (sharedSecretDropHullBase_add_entryOff mpl).symm)
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (sharedSecretDropGhost mpl mmpl u) hInvU hkf hfs_fu⟩

/-- `K`-narrowed `sharedSecretDropGhostK` companion `GhostRowReplayOn`
    (`entryGuard := fun _ => True`; spare only per N2). -/
theorem sharedSecretDropGhostK_rowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (sharedSecretDropSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_sharedSecretDrop mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsSharedSecretDropSym
      (fun _ => True) (sharedSecretDropGhostK mpl mmpl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨sharedSecretDropGhostK_preserves_execFrozen mpl mmpl hfr,
     f3EmptyZeroizeGhostHookK_fs (keepR_sharedSecretDrop mpl) (sharedSecretDropSubProg mpl)
       (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff) u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    refine ⟨hRealHullNoExt W (keepR_sharedSecretDrop_entry mpl), ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hCodeStrip :
        (sharedSecretDropSubProg mpl).CodeLoaded
          (stripExecOutside (keepR_sharedSecretDrop mpl) u.mem) :=
      sharedSecretDropSubProg_codeLoaded_stripExecOutside (hCL u hInvU)
    obtain ⟨hvis, hfr_fu, hfs_fu⟩ :=
      f3EmptySharedSecretDropGhostHookK_visitedIn
        (keep := keepR_sharedSecretDrop mpl)
        (P_sub := sharedSecretDropSubProg mpl)
        (m := sharedSecretDropHullBase mpl)
        (sharedSecretDropSubProg_svc mpl)
        (sharedSecretDropSubProg_externAt_none mpl)
        (sharedSecretDropSubProg_hasWords mpl)
        hrun
        hnoex
        hfr
        hCodeStrip
    have hStepsSetPC :
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
          (u.setPC (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff))
          (sharedSecretDropGhostK mpl mmpl u) :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (D := keepR_sharedSecretDrop mpl)
        (P1 := emptyStdProg)
        (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
        (fun pc _ => emptyStdProg_externAt pc)
        (fun _ hk => hRealHullNoExt W hk)
        hvis
    have hSetPC : u.setPC (sharedSecretDropHullBase mpl + sharedSecretDropEntryOff) = u :=
      setPC_eq_self_of_pc_eq (hpc.trans (sharedSecretDropHullBase_add_entryOff mpl).symm)
    rw [hSetPC] at hStepsSetPC
    exact ⟨hStepsSetPC, hfr_fu, hInvKeep u (sharedSecretDropGhostK mpl mmpl u) hInvU hkf hfs_fu⟩

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
    `lsSharedSecretDropSym`. -/
theorem sharedSecretDropGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hCL : ∀ u : State, InvS u → (sharedSecretDropSubProg mpl).CodeLoaded u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsSharedSecretDropSym) =
        some (sharedSecretDropGhost mpl mmpl))
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_sharedSecretDrop mpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_sharedSecretDrop mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl lsSharedSecretDropSym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl InvS EG lsSharedSecretDropSym
      (sharedSecretDropEntryGuard mpl) (sharedSecretDropGhost mpl mmpl) :=
  ⟨sharedSecretDropGhost_rowSpecOk mpl mmpl,
   sharedSecretDropGhost_rowReplayOn mpl mmpl InvS EG
     hCL hInvKeep hGhostAt hRealHullNoExt hGhostNoExtNe⟩

/-! ## 4. Per-Arm & Singleton `ExtraEntryGuard` Helpers (`.text.lib2` Interface) -/

/-- Per-arm `lsSharedSecretDropSym` discharge for any `guardOf : String → State → Prop` agreeing
    with `sharedSecretDropEntryGuard mpl` on `lsSharedSecretDropSym`. -/
theorem extraEntryGuard_sharedSecretDrop_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf lsSharedSecretDropSym s0 ↔ sharedSecretDropEntryGuard mpl s0)
    (hDropGuard : sharedSecretDropEntryGuard mpl s0) :
    guardOf lsSharedSecretDropSym s0 :=
  hGuardEq.mpr hDropGuard

/-- Table-level `ExtraEntryGuard guardOf g s0` discharge when `g.extra` carries the singleton
    `lsSharedSecretDropSym` row `[(lsSharedSecretDropSym, sharedSecretDropGhost mpl mmpl)]` (N3). -/
theorem extraEntryGuard_singleton_sharedSecretDrop
    {mpl mmpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hg : g.extra = [(lsSharedSecretDropSym, sharedSecretDropGhost mpl mmpl)])
    (hGuardEq : guardOf lsSharedSecretDropSym s0 ↔ sharedSecretDropEntryGuard mpl s0)
    (hDropGuard : sharedSecretDropEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 := by
  intro sym f _ hLook
  rw [hg] at hLook
  simp only [List.lookup] at hLook
  by_cases hSym : (sym == lsSharedSecretDropSym) = true
  · have hEq : sym = lsSharedSecretDropSym := eq_of_beq hSym
    subst hEq
    exact hGuardEq.mpr hDropGuard
  · simp [hSym] at hLook

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays
