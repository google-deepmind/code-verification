/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import

/-!
# Per-Row `extra` Ghost Replay & `ExtraOk` Bundle (`Cli.HooksDehook.ExtraGhostReplay`)

Untrusted (`Role::Proof`) Block-`617` trajectory replay layer for `#1255` Cutover 2
(`CliGhostHooks.extra : List (String × (State → State))`), implementing the binding `H-REV2`
requirements (`rev_c11_design_v2.md` M1, M3, M4):

1. **Row-internal `keepR` & parametric `entryGuard` (`GhostRowReplayOn`):**
   `GhostRowReplayOn` is a pure `Prop` structure with **zero data fields**: each row's code-region
   predicate `keepR : BitVec 64 → Bool` stays purely internal to that row's proof (never unioned
   across `extra`), and `entryGuard : State → Prop` is passed as a parameter (`guardOf sym` in
   `ExtraListEntryGuard` / `ExtraListReplaysOn`).
2. **Guarded trajectory-aware (`On`) per-row `ExtraListReplaysOn` / `ExtraReplaysOn`:**
   Matches `GhostExternReplaysOn`'s behind-stub Arm 1 ∨ Arm 2 shape at `resolve mpl sym` without
   requiring outer `hole2_keepSub (u.readReg64 .lr) = false`, and lifts directly into
   `GhostExternReplaysOn keep_outer InvS` for any outer `keep_outer` (`fun _ => false` in
   Cutover 2, per H-REV2 M3).
3. **Full per-row & table bundles (`GhostRowOk`, `ExtraListOk` / `ExtraOk`) + single-row transfer
   companion (`block617TransferFixedG_of_extraRow`).**
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliExternsPlaced cliProcessInputs libsignalSessionLib
   lsMemcpySym lsMemsetSym lsReadFileSym lsReadStdinSym lsRustAllocSymCli
   lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli
   lsStringCloneSym)
open CryptoVerification.SignalSession.Cli (RunAnswer)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (GhostExternReplaysOn GhostSymActive subroutine_ok_transfer_ghostS)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable ExtraListSpecOk GhostRowSpecOk cliExtraGhostSyms
   cliGhostExternsNamed cliGhostExternsWithExtra cliGhostExternsWithExtra_nil
   named_eq_false_of_extra_contains)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (cliGhostExternsNamed cliGhostExternsWithExtra_nil)

/-! ## 1. Extended `GhostSymActiveWithExtra` & Case-Analysis Lemmas -/

/-- 10-disjunct named-arm prefix of `GhostSymActive` / `GhostSymActiveWithExtra`
    (excluding `cliExtraGhostSyms` / `extra`). -/
@[expose] def GhostSymActiveNamed (ghFixed : CliGhostHooks)
    (sym : String) (f : State → State) : Prop :=
  (sym = lsRustAllocSymCli ∧ f = ghFixed.alloc) ∨
  (sym = lsRustDeallocSymCli ∧ f = ghFixed.dealloc) ∨
  (sym = lsRustReallocSymCli ∧ f = ghFixed.realloc) ∨
  (sym = lsRustAllocZeroedSymCli ∧ f = ghFixed.allocZeroed) ∨
  (sym = lsRustNoAllocShimSymCli ∧ f = ghFixed.shim) ∨
  (sym = lsStringCloneSym ∧ ghFixed.stringClone = some f) ∨
  (sym = lsReadFileSym ∧ ∃ h, ghFixed.readFile = some ⟨f, h⟩) ∨
  (sym = lsReadStdinSym ∧ ∃ h, ghFixed.readStdin = some ⟨f, h⟩) ∨
  (sym = lsMemsetSym ∧ ghFixed.memset = some f) ∨
  (sym = lsMemcpySym ∧ ghFixed.memcpy = some f)

/-- Extended 11-way `GhostSymActive` predicate over `(ghFixed, extra)`. In Commit 2B,
    `GhostSymActive ghFixed sym f` becomes definitionally
    `GhostSymActiveWithExtra ghFixed ghFixed.extra sym f`. -/
@[expose] def GhostSymActiveWithExtra (ghFixed : CliGhostHooks) (extra : ExtraGhostTable)
    (sym : String) (f : State → State) : Prop :=
  (sym = lsRustAllocSymCli ∧ f = ghFixed.alloc) ∨
  (sym = lsRustDeallocSymCli ∧ f = ghFixed.dealloc) ∨
  (sym = lsRustReallocSymCli ∧ f = ghFixed.realloc) ∨
  (sym = lsRustAllocZeroedSymCli ∧ f = ghFixed.allocZeroed) ∨
  (sym = lsRustNoAllocShimSymCli ∧ f = ghFixed.shim) ∨
  (sym = lsStringCloneSym ∧ ghFixed.stringClone = some f) ∨
  (sym = lsReadFileSym ∧ ∃ h, ghFixed.readFile = some ⟨f, h⟩) ∨
  (sym = lsReadStdinSym ∧ ∃ h, ghFixed.readStdin = some ⟨f, h⟩) ∨
  (sym = lsMemsetSym ∧ ghFixed.memset = some f) ∨
  (sym = lsMemcpySym ∧ ghFixed.memcpy = some f) ∨
  (cliExtraGhostSyms.contains sym = true ∧ extra.lookup sym = some f)

/-- Definitional bridge `GhostSymActive gh = GhostSymActiveWithExtra gh gh.extra`. -/
theorem GhostSymActive_eq_withExtra (gh : CliGhostHooks) :
    GhostSymActive gh = GhostSymActiveWithExtra gh gh.extra := rfl

/-- Decomposition of `GhostSymActiveWithExtra` into `GhostSymActiveNamed` ∨ 11th `extra` arm. -/
theorem GhostSymActiveWithExtra_iff_named_or_extra
    (gh : CliGhostHooks) (extra : ExtraGhostTable)
    (sym : String) (f : State → State) :
    GhostSymActiveWithExtra gh extra sym f ↔
      GhostSymActiveNamed gh sym f ∨
        (cliExtraGhostSyms.contains sym = true ∧ extra.lookup sym = some f) := by
  unfold GhostSymActiveWithExtra GhostSymActiveNamed
  simp only [or_assoc]

/-- Decomposition of `GhostSymActive` into `GhostSymActiveNamed` ∨ 11th `gh.extra` arm. -/
theorem GhostSymActive_iff_named_or_extra
    (gh : CliGhostHooks) (sym : String) (f : State → State) :
    GhostSymActive gh sym f ↔
      GhostSymActiveNamed gh sym f ∨
        (cliExtraGhostSyms.contains sym = true ∧ gh.extra.lookup sym = some f) :=
  GhostSymActiveWithExtra_iff_named_or_extra gh gh.extra sym f

/-- Unconditional converse (`h2b2` / `h2ef` soundness check): holds for **arbitrary** `ghFixed`
    and `extra` with **zero** freshness assumptions because the 11th disjunct carries
    `cliExtraGhostSyms.contains sym = true` (which excludes all 10 named symbols). -/
theorem cliGhostExternsWithExtra_eq_some_of_active
    (ghFixed : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State)) {sym : String} {f : State → State}
    (hAct : GhostSymActiveWithExtra ghFixed extra sym f) :
    cliGhostExternsWithExtra ghFixed extra baseExt sym = some f := by
  unfold cliGhostExternsWithExtra
  rcases hAct with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, hsc⟩ | ⟨rfl, ⟨_, hrf⟩⟩ | ⟨rfl, ⟨_, hrs⟩⟩ | ⟨rfl, hms⟩ | ⟨rfl, hmc⟩ | ⟨hDom, hLook⟩
  · simp
  · have h1 : (lsRustDeallocSymCli == lsRustAllocSymCli) = false := by decide
    simp [h1]
  · have h1 : (lsRustReallocSymCli == lsRustAllocSymCli) = false := by decide
    have h2 : (lsRustReallocSymCli == lsRustDeallocSymCli) = false := by decide
    simp [h1, h2]
  · have h1 : (lsRustAllocZeroedSymCli == lsRustAllocSymCli) = false := by decide
    have h2 : (lsRustAllocZeroedSymCli == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsRustAllocZeroedSymCli == lsRustReallocSymCli) = false := by decide
    simp [h1, h2, h3]
  · have h1 : (lsRustNoAllocShimSymCli == lsRustAllocSymCli) = false := by decide
    have h2 : (lsRustNoAllocShimSymCli == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsRustNoAllocShimSymCli == lsRustReallocSymCli) = false := by decide
    have h4 : (lsRustNoAllocShimSymCli == lsRustAllocZeroedSymCli) = false := by decide
    simp [h1, h2, h3, h4]
  · have h1 : (lsStringCloneSym == lsRustAllocSymCli) = false := by decide
    have h2 : (lsStringCloneSym == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsStringCloneSym == lsRustReallocSymCli) = false := by decide
    have h4 : (lsStringCloneSym == lsRustAllocZeroedSymCli) = false := by decide
    have h5 : (lsStringCloneSym == lsRustNoAllocShimSymCli) = false := by decide
    simp [h1, h2, h3, h4, h5, hsc]
  · have h1 : (lsReadFileSym == lsRustAllocSymCli) = false := by decide
    have h2 : (lsReadFileSym == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsReadFileSym == lsRustReallocSymCli) = false := by decide
    have h4 : (lsReadFileSym == lsRustAllocZeroedSymCli) = false := by decide
    have h5 : (lsReadFileSym == lsRustNoAllocShimSymCli) = false := by decide
    have h6 : (lsReadFileSym == lsStringCloneSym) = false := by decide
    simp [h1, h2, h3, h4, h5, h6, hrf]
  · have h1 : (lsReadStdinSym == lsRustAllocSymCli) = false := by decide
    have h2 : (lsReadStdinSym == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsReadStdinSym == lsRustReallocSymCli) = false := by decide
    have h4 : (lsReadStdinSym == lsRustAllocZeroedSymCli) = false := by decide
    have h5 : (lsReadStdinSym == lsRustNoAllocShimSymCli) = false := by decide
    have h6 : (lsReadStdinSym == lsStringCloneSym) = false := by decide
    have h7' : (lsReadStdinSym == lsReadFileSym) = false := by decide
    simp [h1, h2, h3, h4, h5, h6, h7', hrs]
  · have h1 : (lsMemsetSym == lsRustAllocSymCli) = false := by decide
    have h2 : (lsMemsetSym == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsMemsetSym == lsRustReallocSymCli) = false := by decide
    have h4 : (lsMemsetSym == lsRustAllocZeroedSymCli) = false := by decide
    have h5 : (lsMemsetSym == lsRustNoAllocShimSymCli) = false := by decide
    have h6 : (lsMemsetSym == lsStringCloneSym) = false := by decide
    have h7 : (lsMemsetSym == lsReadFileSym) = false := by decide
    have h8 : (lsMemsetSym == lsReadStdinSym) = false := by decide
    have h9 : (lsMemsetSym == lsMemsetSym) = true := rfl
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hms, Bool.false_eq_true, ↓reduceIte]
  · have h1 : (lsMemcpySym == lsRustAllocSymCli) = false := by decide
    have h2 : (lsMemcpySym == lsRustDeallocSymCli) = false := by decide
    have h3 : (lsMemcpySym == lsRustReallocSymCli) = false := by decide
    have h4 : (lsMemcpySym == lsRustAllocZeroedSymCli) = false := by decide
    have h5 : (lsMemcpySym == lsRustNoAllocShimSymCli) = false := by decide
    have h6 : (lsMemcpySym == lsStringCloneSym) = false := by decide
    have h7 : (lsMemcpySym == lsReadFileSym) = false := by decide
    have h8 : (lsMemcpySym == lsReadStdinSym) = false := by decide
    have h9 : (lsMemcpySym == lsMemsetSym) = false := by decide
    have h10 : (lsMemcpySym == lsMemcpySym) = true := rfl
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hmc, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := named_eq_false_of_extra_contains hDom
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hDom, hLook, Bool.false_eq_true,
      ↓reduceIte]

/-- Every `GhostSymActiveNamed` pair evaluates to `some f` in `cliGhostExternsWithExtra gh [] b`. -/
theorem cliGhostExternsWithExtra_nil_of_named
    (gh : CliGhostHooks) (b : String → Option (State → State))
    {sym : String} {f : State → State}
    (hNamed : GhostSymActiveNamed gh sym f) :
    cliGhostExternsWithExtra gh [] b sym = some f :=
  cliGhostExternsWithExtra_eq_some_of_active gh [] b
    ((GhostSymActiveWithExtra_iff_named_or_extra gh [] sym f).mpr (Or.inl hNamed))

/-- Equivalence of the two H-REV4 Step-3 formulations at `baseExt := fun _ => none`. -/
theorem cliGhostExternsWithExtra_nil_none_iff
    (gh : CliGhostHooks) {sym : String} {f : State → State} :
    cliGhostExternsWithExtra gh [] (fun _ => none) sym = some f ↔
      cliExtraGhostSyms.contains sym = false ∧
        CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns gh (fun _ => none) sym = some f := by
  constructor
  · intro h
    cases hc : cliExtraGhostSyms.contains sym with
    | false =>
      refine ⟨rfl, ?_⟩
      unfold CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns cliGhostExternsWithExtra at h ⊢
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact h
    | true =>
      rcases named_eq_false_of_extra_contains hc with
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      unfold cliGhostExternsWithExtra at h
      simp only [List.lookup, hc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
        Bool.false_eq_true, ↓reduceIte] at h
      cases h
  · rintro ⟨hc, h⟩
    unfold CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns at h
    unfold cliGhostExternsWithExtra at h ⊢
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact h

theorem cliGhostExternsWithExtra_none_imp
    (ghFixed : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State)) {sym : String}
    (h : cliGhostExternsWithExtra ghFixed extra baseExt sym = none) :
    baseExt sym = none := by
  unfold cliGhostExternsWithExtra at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h
  · cases hg : ghFixed.stringClone <;> simp only [hg] at h <;> try cases h
    exact h
  · split at h
    · cases hg : ghFixed.readFile with
      | none => simp only [hg] at h; exact h
      | some v => rcases v with ⟨f, hf⟩; simp only [hg] at h; cases h
    · split at h
      · cases hg : ghFixed.readStdin with
        | none => simp only [hg] at h; exact h
        | some v => rcases v with ⟨f, hf⟩; simp only [hg] at h; cases h
      · split at h
        · cases hg : ghFixed.memset <;> simp only [hg] at h <;> try cases h
          exact h
        · split at h
          · cases hg : ghFixed.memcpy <;> simp only [hg] at h <;> try cases h
            exact h
          · split at h
            · cases hg : extra.lookup sym <;> simp only [hg] at h <;> try cases h
              exact h
            · exact h

theorem cliGhostExternsWithExtra_some_cases
    (ghFixed : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State)) {sym : String} {f : State → State}
    (h : cliGhostExternsWithExtra ghFixed extra baseExt sym = some f) :
    GhostSymActiveWithExtra ghFixed extra sym f ∨ baseExt sym = some f := by
  unfold cliGhostExternsWithExtra at h
  by_cases h1 : sym == lsRustAllocSymCli
  · simp only [h1, ↓reduceIte, Option.some.injEq] at h
    exact Or.inl (Or.inl ⟨beq_iff_eq.mp h1, h.symm⟩)
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    by_cases h2 : sym == lsRustDeallocSymCli
    · simp only [h2, ↓reduceIte, Option.some.injEq] at h
      exact Or.inl (Or.inr (Or.inl ⟨beq_iff_eq.mp h2, h.symm⟩))
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h3 : sym == lsRustReallocSymCli
      · simp only [h3, ↓reduceIte, Option.some.injEq] at h
        exact Or.inl (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp h3, h.symm⟩)))
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
        by_cases h4 : sym == lsRustAllocZeroedSymCli
        · simp only [h4, ↓reduceIte, Option.some.injEq] at h
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp h4, h.symm⟩))))
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
          by_cases h5 : sym == lsRustNoAllocShimSymCli
          · simp only [h5, ↓reduceIte, Option.some.injEq] at h
            exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp h5, h.symm⟩)))))
          · simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
            by_cases h6 : sym == lsStringCloneSym
            · simp only [h6, ↓reduceIte] at h
              cases hg : ghFixed.stringClone with
              | some g' =>
                rw [hg] at h; injection h with hf; subst hf
                exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inl ⟨beq_iff_eq.mp h6, hg⟩))))))
              | none => rw [hg] at h; exact Or.inr h
            · simp only [h6, Bool.false_eq_true, ↓reduceIte] at h
              by_cases h7 : sym == lsReadFileSym
              · simp only [h7, ↓reduceIte] at h
                cases hg : ghFixed.readFile with
                | some gh' =>
                  rcases gh' with ⟨g', hg'⟩
                  rw [hg] at h; injection h with hf; subst hf
                  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inl ⟨beq_iff_eq.mp h7, hg', hg⟩)))))))
                | none => rw [hg] at h; exact Or.inr h
              · simp only [h7, Bool.false_eq_true, ↓reduceIte] at h
                by_cases h8 : sym == lsReadStdinSym
                · simp only [h8, ↓reduceIte] at h
                  cases hg : ghFixed.readStdin with
                  | some gh' =>
                    rcases gh' with ⟨g', hg'⟩
                    rw [hg] at h; injection h with hf; subst hf
                    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inl ⟨beq_iff_eq.mp h8, hg', hg⟩))))))))
                  | none => rw [hg] at h; exact Or.inr h
                · simp only [h8, Bool.false_eq_true, ↓reduceIte] at h
                  by_cases h9 : sym == lsMemsetSym
                  · simp only [h9, ↓reduceIte] at h
                    cases hg : ghFixed.memset with
                    | some g' =>
                      rw [hg] at h; injection h with hf; subst hf
                      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inl ⟨beq_iff_eq.mp h9, hg⟩)))))))))
                    | none => rw [hg] at h; exact Or.inr h
                  · simp only [h9, Bool.false_eq_true, ↓reduceIte] at h
                    by_cases h10 : sym == lsMemcpySym
                    · simp only [h10, ↓reduceIte] at h
                      cases hg : ghFixed.memcpy with
                      | some g' =>
                        rw [hg] at h; injection h with hf; subst hf
                        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                          (Or.inr (Or.inr (Or.inl ⟨beq_iff_eq.mp h10, hg⟩))))))))))
                      | none => rw [hg] at h; exact Or.inr h
                    · simp only [h10, Bool.false_eq_true, ↓reduceIte] at h
                      cases hDom : cliExtraGhostSyms.contains sym with
                      | false =>
                        simp only [hDom, Bool.false_eq_true, ↓reduceIte] at h
                        exact Or.inr h
                      | true =>
                        simp only [hDom, ↓reduceIte] at h
                        cases hLook : extra.lookup sym with
                        | some g' =>
                          rw [hLook] at h; injection h with hf; subst hf
                          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                            (Or.inr (Or.inr (Or.inr ⟨hDom, hLook⟩))))))))))
                        | none => rw [hLook] at h; exact Or.inr h

/-! ## 2. Per-Row `GhostRowReplayOn` (Parametric `entryGuard`, No Data Fields) & `ExtraReplaysOn` -/

/-- **Per-row behind-stub `On` replay obligation (`GhostRowReplayOn`):**
    Takes THIS row's entry-state guard `entryGuard : State → Prop` as a parameter (so
    `GhostRowReplayOn` is a pure `Prop` structure with zero data fields — H-REV2 M1) and keeps the
    row's code-region predicate `keepR : BitVec 64 → Bool` purely internal to the row's proof
    (never unioned across `extra`). Produces the exact behind-stub `GhostExternReplaysOn`
    disjunction at `stubPc := libsignalSessionLib.resolve mpl sym` from the Block-`617` trajectory
    endpoints `(s0, sf)` without requiring outer `keep_outer (u.readReg64 .lr) = false`. -/
structure GhostRowReplayOn
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (sym : String) (entryGuard : State → Prop) (f : State → State) : Prop where
  /-- `ExecFrozen` + `fs` preservation for `H2ExecFrozenWire` (`ghFixed_preserves_execFrozen`). -/
  preserves_execFrozen :
    ∀ u : State, u.status = .Running → (∀ msg, (f u).status ≠ .Exception msg) →
      ExecFrozen u.mem → ExecFrozen (f u).mem ∧ (f u).fs = u.fs
  /-- Guarded trajectory-aware (`On`) behind-stub replay at `resolve mpl sym`. -/
  replay_at_stub :
    ∀ (W : CliHooks) (s0 sf : State),
      let stubPc  := libsignalSessionLib.resolve mpl sym
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      let P_real  := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
      entryGuard s0 →
      (sf.status = .Running → sf.pc = s0.readReg64 .lr) →
      (∀ msg, sf.status ≠ .Exception msg) →
      sf.status ≠ .Halted →
      (P_real.externAt? stubPc = some f ∧
        ∀ u : State,
          Steps P_ghost s0 u → Steps P_ghost (f u) sf →
          u.pc = stubPc → u.status = .Running →
          (∀ msg, (f u).status ≠ .Exception msg) →
          u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem → InvS u →
          ExecFrozen (f u).mem ∧ InvS (f u)) ∨
      (P_real.externAt? stubPc = none ∧
        ∀ u : State,
          Steps P_ghost s0 u → Steps P_ghost (f u) sf →
          u.pc = stubPc → u.status = .Running →
          (∀ msg, (f u).status ≠ .Exception msg) →
          u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem → InvS u →
          Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvS (f u))

/-- Lift `GhostRowReplayOn` into the exact `GhostExternReplaysOn keep_outer InvS` disjunction at
    `pc = libsignalSessionLib.resolve mpl sym` for **any** outer `keep_outer` (`fun _ => false` in
    Cutover 2, per H-REV2 M3). -/
theorem ghostExternReplaysOn_arm_of_rowReplayOn
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    {EG : CliHooks → String → Option (State → State)}
    {sym : String} {entryGuard : State → Prop} {f : State → State}
    (keep_outer : BitVec 64 → Bool)
    (hRow : GhostRowReplayOn mpl mmpl InvS EG sym entryGuard f)
    {W : CliHooks} {s0 sf : State} {pc : BitVec 64}
    (hpc_eq : pc = libsignalSessionLib.resolve mpl sym)
    (hGuard0 : entryGuard s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    let P_ghost := cliProgExtPlacedAt mpl EG 617 W
    let P_real  := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
    (P_real.externAt? pc = some f ∧
      ∀ u : State,
        Steps P_ghost s0 u → Steps P_ghost (f u) sf →
        u.pc = pc → u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem → InvS u →
        ExecFrozen (f u).mem ∧ InvS (f u)) ∨
    (P_real.externAt? pc = none ∧
      ∀ u : State,
        Steps P_ghost s0 u → Steps P_ghost (f u) sf →
        u.pc = pc → u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem →
        keep_outer (u.readReg64 .lr) = false → InvS u →
        Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvS (f u)) := by
  subst hpc_eq
  rcases hRow.replay_at_stub W s0 sf hGuard0 hret_pc hnoex_sf hnhalt_sf with
    ⟨hreal_some, harm1⟩ | ⟨hreal_none, harm2⟩
  · exact Or.inl ⟨hreal_some, harm1⟩
  · exact Or.inr ⟨hreal_none,
      fun u hs1 hs2 hpc hrun hnoex hkf hfr _hlr hinv =>
        harm2 u hs1 hs2 hpc hrun hnoex hkf hfr hinv⟩

/-- Combined Block-`617` entry guard across all active `(sym, f)` rows in `extra`, parameterized by
    the **same** `guardOf : String → State → Prop` threaded into `ExtraListReplaysOn`. -/
@[expose] def ExtraListEntryGuard
    (guardOf : String → State → Prop) (extra : ExtraGhostTable) (s0 : State) : Prop :=
  ∀ sym f,
    cliExtraGhostSyms.contains sym = true →
    extra.lookup sym = some f →
    guardOf sym s0

abbrev ExtraEntryGuard
    (guardOf : String → State → Prop) (g : CliGhostHooks) (s0 : State) : Prop :=
  ExtraListEntryGuard guardOf g.extra s0

theorem ExtraListEntryGuard.nil (guardOf : String → State → Prop) (s0 : State) :
    ExtraListEntryGuard guardOf [] s0 :=
  fun _ _ _ hLook => by cases hLook

/-- Per-row `ExtraListReplaysOn` across all active `(sym, f)` entries in `extra`, tied to `guardOf`
    so `ExtraListEntryGuard guardOf extra s0` feeds `hRow.replay_at_stub` directly (H-REV2 M1). -/
@[expose] def ExtraListReplaysOn
    (mpl mmpl : Obj.MultiPlacement) (InvS : State → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable) : Prop :=
  ∀ sym f,
    cliExtraGhostSyms.contains sym = true →
    extra.lookup sym = some f →
    GhostRowReplayOn mpl mmpl InvS
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      sym (guardOf sym) f

abbrev ExtraReplaysOn
    (mpl mmpl : Obj.MultiPlacement) (InvS : State → Prop)
    (guardOf : String → State → Prop) (g : CliGhostHooks) : Prop :=
  ExtraListReplaysOn mpl mmpl InvS guardOf g g.extra

theorem ExtraListReplaysOn.nil
    (mpl mmpl : Obj.MultiPlacement) (InvS : State → Prop)
    (guardOf : String → State → Prop) (g : CliGhostHooks) :
    ExtraListReplaysOn mpl mmpl InvS guardOf g [] :=
  fun _ _ _ hLook => by cases hLook

/-- Direct WP4 replay-arm discharge combining `ExtraListEntryGuard guardOf extra s0` and
    `ExtraListReplaysOn mpl mmpl InvS guardOf g extra` at any active `extra` stub `pc`. -/
theorem extraListReplaysOn_arm
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    {guardOf : String → State → Prop} {g : CliGhostHooks} {extra : ExtraGhostTable}
    (keep_outer : BitVec 64 → Bool)
    (hReplays : ExtraListReplaysOn mpl mmpl InvS guardOf g extra)
    {W : CliHooks} {s0 sf : State}
    (hEntry : ExtraListEntryGuard guardOf extra s0)
    {sym : String} {f : State → State} {pc : BitVec 64}
    (hDom : cliExtraGhostSyms.contains sym = true)
    (hLook : extra.lookup sym = some f)
    (hpc_eq : pc = libsignalSessionLib.resolve mpl sym)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    let EG := fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')
    let P_ghost := cliProgExtPlacedAt mpl EG 617 W
    let P_real  := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W
    (P_real.externAt? pc = some f ∧
      ∀ u : State,
        Steps P_ghost s0 u → Steps P_ghost (f u) sf →
        u.pc = pc → u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem → InvS u →
        ExecFrozen (f u).mem ∧ InvS (f u)) ∨
    (P_real.externAt? pc = none ∧
      ∀ u : State,
        Steps P_ghost s0 u → Steps P_ghost (f u) sf →
        u.pc = pc → u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem →
        keep_outer (u.readReg64 .lr) = false → InvS u →
        Steps P_real u (f u) ∧ ExecFrozen (f u).mem ∧ InvS (f u)) :=
  ghostExternReplaysOn_arm_of_rowReplayOn keep_outer
    (hReplays sym f hDom hLook) hpc_eq (hEntry sym f hDom hLook)
    hret_pc hnoex_sf hnhalt_sf

/-- Full per-row bundle (`GhostRowSpecOk` consumer specs ∧ `GhostRowReplayOn` per-row replay). -/
@[expose] def GhostRowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (sym : String) (entryGuard : State → Prop) (f : State → State) : Prop :=
  GhostRowSpecOk sym f ∧ GhostRowReplayOn mpl mmpl InvS EG sym entryGuard f

/-- Complete `ExtraListOk` bundle combining `ExtraListSpecOk` (`FreshExtraKeysList` + `GhostRowSpecOk`)
    and `ExtraListReplaysOn` under `guardOf`. -/
structure ExtraListOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (InvS : State → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable) : Prop where
  specOk  : ExtraListSpecOk extra
  replays : ExtraListReplaysOn mpl mmpl InvS guardOf g extra

abbrev ExtraOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (InvS : State → Prop)
    (guardOf : String → State → Prop) (g : CliGhostHooks) : Prop :=
  ExtraListOk mpl mmpl InvS guardOf g g.extra

theorem ExtraListOk.nil [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (InvS : State → Prop)
    (guardOf : String → State → Prop) (g : CliGhostHooks) :
    ExtraListOk mpl mmpl InvS guardOf g [] :=
  ⟨ExtraListSpecOk.nil, ExtraListReplaysOn.nil mpl mmpl InvS guardOf g⟩

/-! ## 3. Monotonicity (`noNewHooks`) & Single-Row Transfer Companion (`block617TransferFixedG_of_extraRow`) -/

private theorem findSome?_stubs_none_of_ext_none_imp
    (exts : List String) (ρ : String → BitVec 64) (base : BitVec 64) (off : Nat)
    {E₁ E₂ : String → Option (State → State)}
    (hImp : ∀ s : String, E₁ s = none → E₂ s = none)
    (h : ((exts.map fun e => (e, (ρ e - base).toNat)).findSome?
      fun (n, o) => if o == off then E₁ n else none) = none) :
    ((exts.map fun e => (e, (ρ e - base).toNat)).findSome?
      fun (n, o) => if o == off then E₂ n else none) = none := by
  induction exts with
  | nil => rfl
  | cons e tl ih =>
    simp only [List.map_cons, List.findSome?_cons] at h ⊢
    cases hoo : ((ρ e - base).toNat == off) with
    | false =>
      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ih h
    | true =>
      simp only [hoo, ↓reduceIte] at h ⊢
      cases he : E₁ e with
      | none =>
        rw [he] at h
        rw [hImp e he]
        exact ih h
      | some _ =>
        rw [he] at h
        cases h

private theorem findSome?_const_none {α β : Type} (xs : List α) (p : α → Bool) :
    (xs.findSome? fun x => if p x then (none : Option β) else none) = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.findSome?_cons]
    cases p hd <;> exact ih

/-- Monotonicity of `cliGhostExternsWithExtra` (`EG W sym = none → baseExt sym = none`) lifted to
    `cliProgExtPlacedAt`. -/
theorem noNewHooks_cliProgExtPlacedAt_withExtra
    (mpl mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (extra : ExtraGhostTable) :
    ∀ (W : CliHooks) (pc : BitVec 64),
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W')) 617 W).externAt? pc =
        none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
  intro W pc h
  unfold cliProgExtPlacedAt Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program
    Program.externAt? Program.hookAtOff? at h ⊢
  dsimp only at h ⊢
  rw [findSome?_const_none, Option.or_none] at h ⊢
  exact findSome?_stubs_none_of_ext_none_imp
    (libsignalSessionLib.blockLib 617).text.externs
    (libsignalSessionLib.blockPlacement mpl 617).ρ
    (libsignalSessionLib.blockPlacement mpl 617).base
    (pc - (libsignalSessionLib.blockPlacement mpl 617).base).toNat
    (fun _ hs => cliGhostExternsWithExtra_none_imp g extra (cliExternsPlaced mmpl W) hs) h

/-- Prepend a pure entry-state guard `⌜Guard s⌝ ∗` to `spec.pre` while leaving `post`, `onPanic`,
    `onExit`, and `onOom` definitionally unchanged (`rfl`-identical to
    `Block617TransferG.withEntryGuard`). -/
@[expose] def withExtraEntryGuard {α : Type} (Guard : State → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜Guard s⌝ ∗ spec.pre x s }

/-- Generalized Block-`617` transfer hypothesis with real-side entry guard `Guard` (`rfl`-identical
    to `Block617TransferG.Block617TransferFixedHypG`). -/
@[expose] def ExtraBlock617TransferFixedHypG
    (mpl mmpl : Obj.MultiPlacement)
    (EG ER : CliHooks → String → Option (State → State))
    (Guard : State → Prop)
    (CodeOk_ghost CodeOk_real : Memory → Prop)
    (libcAddr brkStart : BitVec 64) (stk : Nat) : Prop :=
  ∀ (W : CliHooks) (Run : Inputs → RunAnswer → Prop),
    (∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl EG 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_ghost
          (fineHookRustCliAllocBudget γ mmpl tp brkStart)
          cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs)) →
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl ER 617 W)
        (mpl.base 617)
        (withExtraEntryGuard Guard
          (b2MainSpecTightNeedLocksFineAt libcAddr CodeOk_real
            (fineHookRustCliAllocBudget γ mmpl tp brkStart)
            cliBudgetLimits fineCostModel.init stk (cliStaticsPlacedAt mpl) Run cliProcessInputs))

/-- Single-row `ExtraBlock617TransferFixedHypG` transfer combinator (`keep := fun _ => false`) for
    any row `(sym, f)` carrying its own `GhostRowReplayOn` under `entryGuard` (when all other stubs
    agree between `EG` and `cliExternsPlaced mmpl`). -/
theorem block617TransferFixedG_of_extraRow
    {mpl mmpl : Obj.MultiPlacement}
    {EG : CliHooks → String → Option (State → State)}
    {CodeOk_ghost CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    {sym : String} {entryGuard : State → Prop} {f : State → State}
    (InvMem : Memory → Prop) (PredFs : FsState → Prop)
    (hRow : GhostRowReplayOn mpl mmpl (fun u => InvMem u.mem ∧ PredFs u.fs) EG sym entryGuard f)
    (hCode : ∀ m : Memory, CodeOk_real m → CodeOk_ghost m)
    (hGhostCL : ∀ (W : CliHooks) (m : Memory), CodeOk_ghost m →
      (cliProgExtPlacedAt mpl EG 617 W).CodeLoaded m)
    (hFr0 : ∀ m : Memory, CodeOk_real m → ExecFrozen m)
    (hInv0 : ∀ m : Memory, CodeOk_real m → InvMem m)
    (hInvStable : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
    (hFs0 : ∀ i : Inputs, PredFs (initFsState (cliProcessInputs i)))
    (hghost_stub : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl sym) = some f)
    (hother : ∀ (W : CliHooks) (pc : BitVec 64),
      pc ≠ libsignalSessionLib.resolve mpl sym →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc =
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc)
    (hreal_stub_none : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hRealHooks : ∀ (W : CliHooks) (pc : BitVec 64) (gfn : State → State),
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some gfn →
      ∀ u : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem → PredFs u.fs →
        ExecFrozen (gfn u).mem ∧ PredFs (gfn u).fs)
    (hSvcFs : ∀ (W : CliHooks) (s0 sf z : State),
      let P_ghost := cliProgExtPlacedAt mpl EG 617 W
      Steps P_ghost s0 z → Steps P_ghost (Syscall.standard z) sf →
      z.status = .Running → P_ghost.externAt? z.pc = none →
      P_ghost.fetchMem z.mem z.pc = some (.system false 0#16) →
      ExecFrozen z.mem → InvMem z.mem → PredFs z.fs →
      PredFs (Syscall.standard z).fs) :
    ExtraBlock617TransferFixedHypG mpl mmpl EG (cliExternsPlaced mmpl) entryGuard
      CodeOk_ghost CodeOk_real libcAddr brkStart stk := by
  let stubPc := libsignalSessionLib.resolve mpl sym
  intro W Run hGhostOk γ tp
  have hNoNewHooks : ∀ pc : BitVec 64,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
    intro pc hgn
    by_cases hpc : pc = stubPc
    · subst hpc; exact hreal_stub_none W
    · rw [← hother W pc hpc]; exact hgn
  refine subroutine_ok_transfer_ghostS (keep := fun _ => false) (InvMem := InvMem) (PredFs := PredFs)
    rfl rfl hNoNewHooks hInvStable ?_ ?_ (hGhostOk γ tp)
  · intro g R s0 hm _hpc _ _
    dsimp only [withExtraEntryGuard, b2MainSpecTightNeedLocksFineAt] at hm ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm
    obtain ⟨hGuard0, hm_real⟩ := hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm_real ⊢
    obtain ⟨⟨hReal0, hCase, hInpOk, hEntry, hStk⟩, hm_frame⟩ := hm_real
    have hGhost0 : CodeOk_ghost s0.mem := hCode s0.mem hReal0
    have hFsInit : PredFs s0.fs := hEntry.2.1 ▸ hFs0 g.i
    refine ⟨⟨⟨hGhost0, hCase, hInpOk, hEntry, hStk⟩, hm_frame⟩,
      hGhostCL W s0.mem hGhost0, hFr0 s0.mem hReal0, hInv0 s0.mem hReal0, hFsInit, ?_⟩
    intro sf _hsteps hout
    have hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr := by
      intro hrun
      rcases hout with ⟨⟨hpc_sf, _, _⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
      · exact hpc_sf
      · rw [hrun] at hp; cases hp
      · rw [hrun] at he; cases he
      · rw [hrun] at ho; cases ho
    have hnoex_sf : ∀ msg, sf.status ≠ .Exception msg := by
      intro msg hex
      rcases hout with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
      · rw [hex] at hr; cases hr
      · rw [hex] at hp; cases hp
      · rw [hex] at he; cases he
      · rw [hex] at ho; cases ho
    have hnhalt_sf : sf.status ≠ .Halted := by
      intro hh
      rcases hout with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
      · rw [hh] at hr; cases hr
      · rw [hh] at hp; cases hp
      · rw [hh] at he; cases he
      · rw [hh] at ho; cases ho
    refine ⟨?_, hSvcFs W s0 sf, fun _ _ _ _ _ => rfl⟩
    intro pc gfn hgpc
    by_cases hpc : pc = stubPc
    · subst hpc
      rw [hghost_stub W] at hgpc
      injection hgpc with hfg; subst hfg
      exact ghostExternReplaysOn_arm_of_rowReplayOn (fun _ => false) hRow rfl
        hGuard0 hret_pc hnoex_sf hnhalt_sf
    · have hreal_eq :
          (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some gfn := by
        rw [← hother W pc hpc]; exact hgpc
      refine Or.inl ⟨hreal_eq, ?_⟩
      intro u _ _ _ hrun _ hkf hfr ⟨hinv, hpfs⟩
      obtain ⟨hfr', hpfs'⟩ := hRealHooks W pc gfn hreal_eq u hrun hfr hinv hpfs
      exact ⟨hfr', hInvStable u.mem (gfn u).mem hinv hkf, hpfs'⟩
  · intro _g _R _s0 _sf _ _ _ hout
    exact hout

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
