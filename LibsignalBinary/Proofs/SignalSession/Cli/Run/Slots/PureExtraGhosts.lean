/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.HooksE.WrapperHooksCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
import LibsignalBinary.Proofs.HookDischarge.Libc.Strlen
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WP.StateNorm

/-!
# Pure / Unplaced 10-Row `extra` Ghost Witness (`Cli.Run.Slots.PureExtraGhosts`)

Constructs the `W`-free, placement-free 10-row `pureExtraGhosts : ExtraGhostTable` witness for
Cutover 2B's unplaced/pure ghost hook bundles (`a0Ghost`, `bumpGhost`, and `hole2_ghFixed`),
together with:
- `pureBcmpFn` / `pureBcmpFn_ok` and `pureUtf8Err`,
- `pureExtraGhosts_specOk : ExtraFullListSpecOk pureExtraGhosts`,
- `pureExtraGhosts_fsT` (`HookFsTraced IsFsC` for `CliGhostHooksFs.extra_fsT`),
- `pureExtraGhosts_trace_eq` and `pureExtraGhosts_noAllocFailed` (for `ExternNoAllocFailed`),
- `pureExtraGhosts_vmPreserved`, `pureExtraGhosts_perm_eq`, and
  `pureExtraGhosts_preserves_execFrozen` (for `h2ef_hole2_ghFixed_preserves_execFrozen`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (timeAddHook)
open CryptoVerification.E2E.HooksE (bcmpVregsSpec timeAddHook_ok)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalPublicApi (timeAddSpec)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.LibsignalTripleRatchet
  (blackBoxHook_ok blackBoxSpec extHookStack withStack zeroizeSecretHook zeroizeSecretHook_ok
   zeroizeSecretSpec)
open CryptoVerification.RustHeap (allocFailedEvent)
open CryptoVerification.SignalSession
  (cliBcmpHook durationSinceExactHook fromUtf8Hook lsBlackBoxSym lsDurationSinceSym lsFromUtf8Sym
   lsMemrchrSym lsSharedSecretDropSym lsStaticSecretDropSym lsTimeAddSym memrchrHook strlenHook
   unmodelled)
open CryptoVerification.SignalSession.Cli (cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.MainHops
  (fromUtf8AsciiSpec fromUtf8Hook_ok hookMemmove_fs hookOk_withStack memrchrHook_ok memrchrSpec
   strlenHook_ok strlenSpec)
open CryptoVerification.SignalSession.Cli.RunGlue
  (IsFsC blackBoxHook_fsT bytesAt_readBytes cliBcmpHook_fsT durationSinceExactHook_fsT
   fromUtf8Hook_fsT hookMemmove_fsT memrchrHook_fsT strlenHook_fsT timeAddHook_fsT
   zeroizeSecretHook_fsT)
open CryptoVerification.SignalSession.Cli.Slots
  (durationSinceBoundedSpec durationSinceEpochAtSpec durationSinceExactHook_bounded_ok
   durationSinceExactHook_epoch_at_ok)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (perm_write32_norm perm_write64_norm perm_writeBytes_norm)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
  (hookMemmove_bounded_ok hookMemmove_sessionBounded_ok)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (withStrlenPadRO)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (fromUtf8Hook_ro_ok fromUtf8Hook_vmPreserved memrchrHook_ro_ok memrchrHook_vmPreserved
   strlenHook_ro_ok strlenHook_vmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (BcmpRowSpec BlackBoxRowSpec CompleteExtraKeysList DurationSinceRowSpec ExtraFullListSpecOk
   ExtraGhostTable ExtraListSpecOk ExtraRowSpec FreshExtraKeysList FromUtf8RowSpec GhostRowSpecOk
   MemmoveRowSpec MemrchrRowSpec SharedSecretDropRowSpec StaticSecretDropRowSpec StrlenRowSpec
   TimeAddRowSpec cliExtraGhostSyms)

/-! ## 1. Pure `bcmp` & `from_utf8` Value Helpers and 10-Row `pureExtraGhosts` Table -/

/-- Pure `W`-free `bcmp` return-value function (`0` iff equal, `1` otherwise). -/
@[expose] def pureBcmpFn (a b : List (BitVec 8)) : BitVec 64 :=
  if a = b then 0#64 else 1#64

theorem pureBcmpFn_ok :
    ∀ a b : List (BitVec 8), a.length = b.length →
      ((pureBcmpFn a b).setWidth 32 = 0#32 ↔ a = b) := by
  intro a b _
  unfold pureBcmpFn
  by_cases hab : a = b <;> simp [hab]

/-- Pure `W`-free `from_utf8` error payload function. -/
@[expose] def pureUtf8Err (_ : List (BitVec 8)) : BitVec 64 × BitVec 16 :=
  (0#64, 0#16)

/-- 10-row pure/unplaced `ExtraGhostTable` in canonical `cliExtraGhostSyms` key order, binding
    `"memmove"` at index `0` to `ProofLib.hookMemmove`. -/
@[expose] noncomputable def pureExtraGhosts : ExtraGhostTable :=
  [ ("memmove", hookMemmove)
  , ("bcmp", cliBcmpHook pureBcmpFn)
  , ("strlen", strlenHook)
  , (lsMemrchrSym, memrchrHook)
  , (lsFromUtf8Sym, fromUtf8Hook pureUtf8Err)
  , (lsDurationSinceSym, durationSinceExactHook)
  , (lsTimeAddSym, timeAddHook)
  , (lsBlackBoxSym, blackBoxHook)
  , (lsStaticSecretDropSym, zeroizeSecretHook)
  , (lsSharedSecretDropSym, zeroizeSecretHook)
  ]

/-- `pureExtraGhosts.lookup "memmove"` reduces definitionally to `some hookMemmove` by `rfl`. -/
theorem pureExtraGhosts_lookup_memmove :
    pureExtraGhosts.lookup "memmove" = some hookMemmove :=
  rfl

theorem pureExtraGhosts_fresh : FreshExtraKeysList pureExtraGhosts := by
  decide

theorem pureExtraGhosts_complete : CompleteExtraKeysList pureExtraGhosts := by
  decide

private theorem pureExtraGhosts_lookup_cases {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) :
    (sym = "memmove" ∧ f = hookMemmove) ∨
    (sym = "bcmp" ∧ f = cliBcmpHook pureBcmpFn) ∨
    (sym = "strlen" ∧ f = strlenHook) ∨
    (sym = lsMemrchrSym ∧ f = memrchrHook) ∨
    (sym = lsFromUtf8Sym ∧ f = fromUtf8Hook pureUtf8Err) ∨
    (sym = lsDurationSinceSym ∧ f = durationSinceExactHook) ∨
    (sym = lsTimeAddSym ∧ f = timeAddHook) ∨
    (sym = lsBlackBoxSym ∧ f = blackBoxHook) ∨
    (sym = lsStaticSecretDropSym ∧ f = zeroizeSecretHook) ∨
    (sym = lsSharedSecretDropSym ∧ f = zeroizeSecretHook) := by
  dsimp only [pureExtraGhosts, List.lookup] at hLook
  by_cases h1 : sym = "memmove"
  · subst h1; simp at hLook; exact Or.inl ⟨rfl, hLook.symm⟩
  · simp only [beq_eq_false_iff_ne.mpr h1] at hLook
    by_cases h2 : sym = "bcmp"
    · subst h2; simp at hLook; exact Or.inr (Or.inl ⟨rfl, hLook.symm⟩)
    · simp only [beq_eq_false_iff_ne.mpr h2] at hLook
      by_cases h3 : sym = "strlen"
      · subst h3; simp at hLook; exact Or.inr (Or.inr (Or.inl ⟨rfl, hLook.symm⟩))
      · simp only [beq_eq_false_iff_ne.mpr h3] at hLook
        by_cases h4 : sym = lsMemrchrSym
        · subst h4; simp at hLook
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hLook.symm⟩)))
        · simp only [beq_eq_false_iff_ne.mpr h4] at hLook
          by_cases h5 : sym = lsFromUtf8Sym
          · subst h5; simp at hLook
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hLook.symm⟩))))
          · simp only [beq_eq_false_iff_ne.mpr h5] at hLook
            by_cases h6 : sym = lsDurationSinceSym
            · subst h6; simp at hLook
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hLook.symm⟩)))))
            · simp only [beq_eq_false_iff_ne.mpr h6] at hLook
              by_cases h7 : sym = lsTimeAddSym
              · subst h7; simp at hLook
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hLook.symm⟩))))))
              · simp only [beq_eq_false_iff_ne.mpr h7] at hLook
                by_cases h8 : sym = lsBlackBoxSym
                · subst h8; simp at hLook
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inl ⟨rfl, hLook.symm⟩)))))))
                · simp only [beq_eq_false_iff_ne.mpr h8] at hLook
                  by_cases h9 : sym = lsStaticSecretDropSym
                  · subst h9; simp at hLook
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inl ⟨rfl, hLook.symm⟩))))))))
                  · simp only [beq_eq_false_iff_ne.mpr h9] at hLook
                    by_cases h10 : sym = lsSharedSecretDropSym
                    · subst h10; simp at hLook
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr ⟨rfl, hLook.symm⟩))))))))
                    · simp only [beq_eq_false_iff_ne.mpr h10] at hLook
                      cases hLook

/-! ## 2. Private Per-Row `HookOk`, `VmPreserved`, `fs_eq`, and `trace_eq` Lemmas -/

private theorem hookOk_withStrlenPadRO_of_hookOk {f : State → State}
    {spec : Spec (BitVec 64 × List (BitVec 8))}
    (hf : HookOk f spec) :
    HookOk f (withStrlenPadRO spec) := by
  intro ⟨p, s⟩ R s0 hrun hpre hsp
  dsimp only [withStrlenPadRO] at hpre
  rw [sepConj_assoc] at hpre
  exact hf (p, s) R s0 hrun (Satisfies.of_sep_right hpre) hsp

private theorem setMem_vm (s : State) {m' : Memory} (hp : ∀ a, m'.perm a = s.mem.perm a) :
    VmPreserved s (s.setMem m') :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, hp, fun _ _ _ => rfl⟩

private theorem retHook_vm {g : State → State} {s : State} (hg : VmPreserved s (g s)) :
    VmPreserved s (retHook g s) := by
  unfold retHook
  exact hg

private theorem returnToLr_vm {s0 s : State} (hs : VmPreserved s0 s) :
    VmPreserved s0 (returnToLinkRegister s) := by
  unfold returnToLinkRegister
  exact hs

private theorem hookMemmove_vm (s : State) : VmPreserved s (hookMemmove s) := by
  unfold hookMemmove hookMemcpy
  exact retHook_vm (setMem_vm s fun a => congrFun (perm_writeBytes_norm _ _ _) a)

private theorem hookMemmove_acp (s : State) : AllocCallPreserved s (hookMemmove s) := by
  unfold hookMemmove hookMemcpy retHook
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem pureBcmpHook_ok : HookOk (cliBcmpHook pureBcmpFn) cliBcmpSpec := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [cliBcmpSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hlenA : x.bsA.length ≤ 2 ^ 64 := by
    have := (s0.readReg64 .x2).isLt
    omega
  have hreadA := bytesAt_readBytes hmem hlenA
  have hmemB : s0.mem ⊨ bytesAt x.bRo x.b x.bsB ∗
      (bytesAt x.aRo x.a x.bsA ∗ (stackAt s0.sp extHookStack ∗ R)) := by
    rwa [← sepConj_assoc, sepConj_comm (bytesAt x.aRo x.a x.bsA), sepConj_assoc] at hmem
  have hreadB := bytesAt_readBytes hmemB (by omega)
  rw [hlen] at hreadB
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [cliBcmpSpec, cliBcmpHook, retHook]
  rw [hx0, hx1, hx2, hreadA, hreadB]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨pureBcmpFn_ok x.bsA x.bsB hlen.symm, rfl⟩, hmem⟩

private theorem pureBcmpHook_vregs_ok : HookOk (cliBcmpHook pureBcmpFn) bcmpVregsSpec := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [bcmpVregsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hreadA : s0.mem.readBytes x.a x.bsA.length = x.bsA :=
    ((IsBlock.pointsToBytes x.a x.bsA).read hmem).2
  have hmemB : s0.mem ⊨ (x.b ↦ₛ x.bsB) ∗ ((x.a ↦ₛ x.bsA) ∗ (stackAt s0.sp extHookStack ∗ R)) := by
    ac_nf at hmem ⊢
  have hreadB : s0.mem.readBytes x.b x.bsA.length = x.bsB := by
    rw [← hlen]; exact ((IsBlock.pointsToBytes x.b x.bsB).read hmemB).2
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [bcmpVregsSpec, cliBcmpHook, retHook]
  rw [hx0, hx1, hx2, hreadA, hreadB]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨pureBcmpFn_ok x.bsA x.bsB hlen.symm, rfl, rfl⟩, hmem⟩

private theorem pureBcmpHook_vm (s : State) : VmPreserved s (cliBcmpHook pureBcmpFn s) :=
  VmPreserved.refl s

private theorem durationSinceExactHook_vm (s : State) :
    VmPreserved s (durationSinceExactHook s) := by
  unfold durationSinceExactHook; try dsimp only
  split
  · exact VmPreserved.refl s
  · try dsimp only
    split
    · refine retHook_vm (setMem_vm s fun a => ?_)
      simp only [perm_write32_norm, perm_write64_norm]
    · exact VmPreserved.refl s

private theorem timeAddHook_vm (s : State) : VmPreserved s (timeAddHook s) := by
  unfold timeAddHook
  try dsimp only
  split <;> (split <;> exact VmPreserved.refl s)

private theorem blackBoxHook_vm (s : State) : VmPreserved s (blackBoxHook s) :=
  VmPreserved.refl s

private theorem zeroizeSecretHook_vm (s : State) : VmPreserved s (zeroizeSecretHook s) := by
  unfold zeroizeSecretHook
  exact returnToLr_vm (setMem_vm s fun a => congrFun (perm_writeBytes_norm _ _ _) a)

private theorem fromUtf8Hook_fs (s : State) : (fromUtf8Hook pureUtf8Err s).fs = s.fs := by
  unfold fromUtf8Hook; dsimp only
  split
  · rfl
  · split <;> rfl

private theorem durationSinceExactHook_fs (s : State) :
    (durationSinceExactHook s).fs = s.fs := by
  unfold durationSinceExactHook; dsimp only
  split
  · rfl
  · split <;> rfl

private theorem timeAddHook_fs (s : State) : (timeAddHook s).fs = s.fs := by
  unfold timeAddHook; dsimp only
  split <;> (split <;> rfl)

private theorem memrchrHook_fs (s : State) : (memrchrHook s).fs = s.fs := by
  unfold memrchrHook
  change (if (!s.mem.canRead (s.readReg64 .x1) (s.readReg64 .x2).toNat) = true then
      unmodelled "memrchr: unreadable bytes" s
    else
      match ((List.range (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat).length).filter
        fun i => (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat)[i]? ==
          some ((s.readReg64 .x0).setWidth 8)).getLast? with
      | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s
      | none => retHook (fun s => s.writeReg64 .x0 0#64) s).fs = s.fs
  split
  · rfl
  · split <;> rfl

private theorem strlenHook_fs (s : State) : (strlenHook s).fs = s.fs := by
  unfold strlenHook; dsimp only
  split <;> rfl

private theorem hookMemmove_trace (s : State) : (hookMemmove s).trace = s.trace :=
  rfl

private theorem strlenHook_trace (s : State) : (strlenHook s).trace = s.trace := by
  unfold strlenHook; dsimp only
  split <;> rfl

private theorem memrchrHook_trace (s : State) : (memrchrHook s).trace = s.trace := by
  unfold memrchrHook
  change (if (!s.mem.canRead (s.readReg64 .x1) (s.readReg64 .x2).toNat) = true then
      unmodelled "memrchr: unreadable bytes" s
    else
      match ((List.range (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat).length).filter
        fun i => (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat)[i]? ==
          some ((s.readReg64 .x0).setWidth 8)).getLast? with
      | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s
      | none => retHook (fun s => s.writeReg64 .x0 0#64) s).trace = s.trace
  split
  · rfl
  · split <;> rfl

private theorem fromUtf8Hook_trace (s : State) : (fromUtf8Hook pureUtf8Err s).trace = s.trace := by
  unfold fromUtf8Hook; dsimp only
  split
  · rfl
  · split <;> rfl

private theorem durationSinceExactHook_trace (s : State) :
    (durationSinceExactHook s).trace = s.trace := by
  unfold durationSinceExactHook; dsimp only
  split
  · rfl
  · split <;> rfl

private theorem timeAddHook_trace (s : State) : (timeAddHook s).trace = s.trace := by
  unfold timeAddHook; dsimp only
  split <;> (split <;> rfl)

/-! ## 3. Per-Row `GhostRowSpecOk` & Table-Level `ExtraFullListSpecOk` -/

private theorem memmove_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk "memmove" hookMemmove := by
  refine ⟨hookMemmove_fs, hookMemmove_fsT, ?_⟩
  change MemmoveRowSpec hookMemmove
  exact MemmoveRowSpec.of_vm (fun stk => hookMemmove_bounded_ok stk)
    (fun stk => hookMemmove_sessionBounded_ok stk) hookMemmove_vm hookMemmove_acp

private theorem bcmp_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk "bcmp" (cliBcmpHook pureBcmpFn) := by
  refine ⟨fun _ => rfl, cliBcmpHook_fsT pureBcmpFn, ?_⟩
  change BcmpRowSpec (cliBcmpHook pureBcmpFn)
  exact BcmpRowSpec.of_vm pureBcmpHook_ok pureBcmpHook_vregs_ok pureBcmpHook_vm

private theorem strlen_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk "strlen" strlenHook := by
  refine ⟨strlenHook_fs, strlenHook_fsT, ?_⟩
  change StrlenRowSpec strlenHook
  exact StrlenRowSpec.of_vm
    (fun stk => hookOk_withStrlenPadRO_of_hookOk (strlenHook_ok stk))
    (fun stk => hookOk_withStrlenPadRO_of_hookOk (strlenHook_ro_ok stk))
    strlenHook_vmPreserved

private theorem memrchr_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMemrchrSym memrchrHook := by
  refine ⟨memrchrHook_fs, memrchrHook_fsT, ?_⟩
  have hd1 : (lsMemrchrSym == "bcmp") = false := by decide
  have hd2 : (lsMemrchrSym == "strlen") = false := by decide
  have hd3 : (lsMemrchrSym == "memmove") = false := by decide
  have hd4 : (lsMemrchrSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsMemrchrSym == lsMemrchrSym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, Bool.false_eq_true, ↓reduceIte]
  exact MemrchrRowSpec.of_vm (fun stk _ _ => memrchrHook_ok stk)
    (fun stk _ _ => memrchrHook_ro_ok stk) memrchrHook_vmPreserved

private theorem fromUtf8_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsFromUtf8Sym (fromUtf8Hook pureUtf8Err) := by
  refine ⟨fromUtf8Hook_fs, fromUtf8Hook_fsT pureUtf8Err, ?_⟩
  have hd1 : (lsFromUtf8Sym == "bcmp") = false := by decide
  have hd2 : (lsFromUtf8Sym == "strlen") = false := by decide
  have hd3 : (lsFromUtf8Sym == "memmove") = false := by decide
  have hd4 : (lsFromUtf8Sym == lsFromUtf8Sym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, Bool.false_eq_true, ↓reduceIte]
  exact FromUtf8RowSpec.of_vm (fun stk => fromUtf8Hook_ok stk pureUtf8Err)
    (fun stk => fromUtf8Hook_ro_ok stk pureUtf8Err) (fromUtf8Hook_vmPreserved pureUtf8Err)

private theorem durationSince_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsDurationSinceSym durationSinceExactHook := by
  refine ⟨durationSinceExactHook_fs, durationSinceExactHook_fsT, ?_⟩
  have hd1 : (lsDurationSinceSym == "bcmp") = false := by decide
  have hd2 : (lsDurationSinceSym == "strlen") = false := by decide
  have hd3 : (lsDurationSinceSym == "memmove") = false := by decide
  have hd4 : (lsDurationSinceSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsDurationSinceSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsDurationSinceSym == lsDurationSinceSym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, Bool.false_eq_true, ↓reduceIte]
  exact DurationSinceRowSpec.of_vm durationSinceExactHook_bounded_ok
    (fun stk _ _ => durationSinceExactHook_epoch_at_ok stk) durationSinceExactHook_vm

private theorem timeAdd_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsTimeAddSym timeAddHook := by
  refine ⟨timeAddHook_fs, timeAddHook_fsT, ?_⟩
  have hd1 : (lsTimeAddSym == "bcmp") = false := by decide
  have hd2 : (lsTimeAddSym == "strlen") = false := by decide
  have hd3 : (lsTimeAddSym == "memmove") = false := by decide
  have hd4 : (lsTimeAddSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsTimeAddSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsTimeAddSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsTimeAddSym == lsTimeAddSym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, Bool.false_eq_true, ↓reduceIte]
  exact TimeAddRowSpec.of_vm timeAddHook_ok timeAddHook_vm

private theorem blackBox_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsBlackBoxSym blackBoxHook := by
  refine ⟨fun _ => rfl, blackBoxHook_fsT, ?_⟩
  have hd1 : (lsBlackBoxSym == "bcmp") = false := by decide
  have hd2 : (lsBlackBoxSym == "strlen") = false := by decide
  have hd3 : (lsBlackBoxSym == "memmove") = false := by decide
  have hd4 : (lsBlackBoxSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsBlackBoxSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsBlackBoxSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsBlackBoxSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsBlackBoxSym == lsBlackBoxSym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, Bool.false_eq_true, ↓reduceIte]
  exact BlackBoxRowSpec.of_vm (fun stk _ _ => hookOk_withStack blackBoxHook_ok stk)
    blackBoxHook_vm

private theorem staticSecretDrop_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsStaticSecretDropSym zeroizeSecretHook := by
  refine ⟨fun _ => rfl, zeroizeSecretHook_fsT, ?_⟩
  have hd1 : (lsStaticSecretDropSym == "bcmp") = false := by decide
  have hd2 : (lsStaticSecretDropSym == "strlen") = false := by decide
  have hd3 : (lsStaticSecretDropSym == "memmove") = false := by decide
  have hd4 : (lsStaticSecretDropSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsStaticSecretDropSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsStaticSecretDropSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsStaticSecretDropSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsStaticSecretDropSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsStaticSecretDropSym == lsStaticSecretDropSym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, Bool.false_eq_true, ↓reduceIte]
  exact StaticSecretDropRowSpec.of_vm zeroizeSecretHook_ok zeroizeSecretHook_vm

private theorem sharedSecretDrop_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsSharedSecretDropSym zeroizeSecretHook := by
  refine ⟨fun _ => rfl, zeroizeSecretHook_fsT, ?_⟩
  have hd1 : (lsSharedSecretDropSym == "bcmp") = false := by decide
  have hd2 : (lsSharedSecretDropSym == "strlen") = false := by decide
  have hd3 : (lsSharedSecretDropSym == "memmove") = false := by decide
  have hd4 : (lsSharedSecretDropSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsSharedSecretDropSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsSharedSecretDropSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsSharedSecretDropSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsSharedSecretDropSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsSharedSecretDropSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsSharedSecretDropSym == lsSharedSecretDropSym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, Bool.false_eq_true, ↓reduceIte]
  exact SharedSecretDropRowSpec.of_vm zeroizeSecretHook_ok zeroizeSecretHook_vm

theorem pureExtraGhosts_listSpecOk [LibsignalPlacement] :
    ExtraListSpecOk pureExtraGhosts where
  fresh := pureExtraGhosts_fresh
  rowOk := by
    intro sym f hLook
    rcases pureExtraGhosts_lookup_cases hLook with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact memmove_ghostRowSpecOk
    · exact bcmp_ghostRowSpecOk
    · exact strlen_ghostRowSpecOk
    · exact memrchr_ghostRowSpecOk
    · exact fromUtf8_ghostRowSpecOk
    · exact durationSince_ghostRowSpecOk
    · exact timeAdd_ghostRowSpecOk
    · exact blackBox_ghostRowSpecOk
    · exact staticSecretDrop_ghostRowSpecOk
    · exact sharedSecretDrop_ghostRowSpecOk

/-- Complete 10-row consumer spec bundle (`ExtraFullListSpecOk`) for `pureExtraGhosts`
    (`0` `LinkedAt` / `MultiPlacement` hypotheses). -/
theorem pureExtraGhosts_specOk [LibsignalPlacement] :
    ExtraFullListSpecOk pureExtraGhosts where
  toExtraListSpecOk := pureExtraGhosts_listSpecOk
  complete := pureExtraGhosts_complete

/-! ## 4. Placement-Free `fsT`, `noAllocFailed`, `VmPreserved`, and `ExecFrozen` Helpers -/

theorem pureExtraGhosts_lookup_fsT {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) :
    HookFsTraced IsFsC f := by
  rcases pureExtraGhosts_lookup_cases hLook with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hookMemmove_fsT
  · exact cliBcmpHook_fsT pureBcmpFn
  · exact strlenHook_fsT
  · exact memrchrHook_fsT
  · exact fromUtf8Hook_fsT pureUtf8Err
  · exact durationSinceExactHook_fsT
  · exact timeAddHook_fsT
  · exact blackBoxHook_fsT
  · exact zeroizeSecretHook_fsT
  · exact zeroizeSecretHook_fsT

/-- `CliGhostHooksFs.extra_fsT` companion for `pureExtraGhosts` (placement-free). -/
theorem pureExtraGhosts_fsT :
    ∀ sym f,
      cliExtraGhostSyms.contains sym = true →
      pureExtraGhosts.lookup sym = some f →
      HookFsTraced IsFsC f :=
  fun _ _ _ hLook => pureExtraGhosts_lookup_fsT hLook

theorem pureExtraGhosts_fs_eq {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (s : State) :
    (f s).fs = s.fs := by
  rcases pureExtraGhosts_lookup_cases hLook with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hookMemmove_fs s
  · rfl
  · exact strlenHook_fs s
  · exact memrchrHook_fs s
  · exact fromUtf8Hook_fs s
  · exact durationSinceExactHook_fs s
  · exact timeAddHook_fs s
  · rfl
  · rfl
  · rfl

theorem pureExtraGhosts_trace_eq {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (s : State) :
    (f s).trace = s.trace := by
  rcases pureExtraGhosts_lookup_cases hLook with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hookMemmove_trace s
  · rfl
  · exact strlenHook_trace s
  · exact memrchrHook_trace s
  · exact fromUtf8Hook_trace s
  · exact durationSinceExactHook_trace s
  · exact timeAddHook_trace s
  · rfl
  · rfl
  · rfl

/-- Every hook in `pureExtraGhosts` leaves `s.trace` unchanged, hence satisfies
    `CliInitSlotOkPlacedAt.HookNoAllocFailed f` definitionally. -/
theorem pureExtraGhosts_noAllocFailed {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (s : State) :
    ∃ d : List TraceEvent, (f s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d :=
  ⟨[], by rw [pureExtraGhosts_trace_eq hLook s, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩

theorem pureExtraGhosts_vmPreserved {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (s : State) :
    VmPreserved s (f s) := by
  rcases pureExtraGhosts_lookup_cases hLook with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hookMemmove_vm s
  · exact pureBcmpHook_vm s
  · exact strlenHook_vmPreserved s
  · exact memrchrHook_vmPreserved s
  · exact fromUtf8Hook_vmPreserved pureUtf8Err s
  · exact durationSinceExactHook_vm s
  · exact timeAddHook_vm s
  · exact blackBoxHook_vm s
  · exact zeroizeSecretHook_vm s
  · exact zeroizeSecretHook_vm s

theorem pureExtraGhosts_perm_eq {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (u : State) (a : BitVec 64) :
    (f u).mem.perm a = u.mem.perm a :=
  (pureExtraGhosts_vmPreserved hLook u).2.2.1 a

/-- Every hook in `pureExtraGhosts` preserves `AllocGhostLinkTransfer.ExecFrozen`
    (`∀ a, (m.perm a).x = true → (m.perm a).r = true ∧ (m.perm a).w = false`), matching
    `ExecFrozen u.mem → ExecFrozen (f u).mem` definitionally. -/
theorem pureExtraGhosts_preserves_execFrozen {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (u : State)
    (hfr : ∀ a : BitVec 64,
      (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) :
    ∀ a : BitVec 64,
      ((f u).mem.perm a).x = true → ((f u).mem.perm a).r = true ∧ ((f u).mem.perm a).w = false := by
  intro a hx
  rw [pureExtraGhosts_perm_eq hLook u a] at hx ⊢
  exact hfr a hx

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts
