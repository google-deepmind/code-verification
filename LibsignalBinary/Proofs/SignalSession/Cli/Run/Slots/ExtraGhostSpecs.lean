/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Strlen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BcmpRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BlackBoxRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.DurationSinceRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FromUtf8RowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemmoveRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemrchrRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StaticSecretDropRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StrlenRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.TimeAddRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalPublicApi -- proof-setup: allow-public-import

/-!
# Generic `extra` Ghost Table Consumer Contracts (`Cli.Run.Slots.ExtraGhostSpecs`)

Untrusted (`Role::Proof`) consumer-spec (`HookOk` / `HookSat` / `VmPreserved` / `withAlloc` /
`HookFsTraced`) layer for `#1255` Cutover 2 (`CliGhostHooks.extra : List (String × (State → State))`):

1. **Symbol partition & key freshness (`cliNamedGhostSyms`, `cliExtraGhostSyms`, `FreshExtraKeysList`):**
   Partitions the 10 named ghost slots (5 F3 alloc + 3 F3 optional + Stage A `lsMemsetSym` /
   `lsMemcpySym` from `BcmpHookPlaced`) from the 10 Cutover-2 `extra` symbols (`"memmove"`, `"bcmp"`,
   `"strlen"`, `lsMemrchrSym`, `lsFromUtf8Sym`, `lsDurationSinceSym`, `lsTimeAddSym`, `lsBlackBoxSym`,
   `lsStaticSecretDropSym`, `lsSharedSecretDropSym`), with kernel-decidable disjointness
   (`cliExtraGhostSyms_disjoint_named`).
2. **Domain-guarded `extra` dispatch (`cliGhostExternsWithExtra`):**
   Checks the 10 named `CliGhostHooks` arms first, then dispatches `extra.lookup sym` **only** when
   `cliExtraGhostSyms.contains sym = true`. All panic/crypto/write/fmt symbols pass through to
   `baseExt sym` unconditionally (`by left; decide`) with zero bundle hypotheses.
   In Commit 2B, `cliGhostExterns g baseExt sym` is redefined as (or proved `rfl`-equal to)
   `cliGhostExternsWithExtra g g.extra baseExt sym`.
3. **Per-row consumer `HookOk` table (`ExtraRowSpec`, `GhostRowSpecOk`, `ExtraListSpecOk`,
   `ExtraSpecOk`):**
   Imports the 10 row-owned `ExtraRowSpecs.*RowSpec` leaf modules and bundles `FreshExtraKeysList`
   + per-row `GhostRowSpecOk` into `ExtraSpecOk g` (`ExtraListSpecOk g.extra`) for the R1 bundles
   (`CliGhostA0Hooks`, `CliGhostAllocHooks`, `CliGhostSpqrAllocHooks`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E.HooksE (bcmpVregsSpec e2eBcmpSpec hookOk_bcmpSpec_of_vregs)
open CryptoVerification.LibsignalPublicApi.StoreKit (extract_withLsRoCl withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet
  (blackBoxSpec extHookStack withStack zeroizeSecretSpec)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession
  (lsBlackBoxSym lsDurationSinceSym lsFromUtf8Sym lsMemcpySym lsMemrchrSym lsMemsetSym
   lsReadFileSym lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli
   lsRustNoAllocShimSymCli lsRustReallocSymCli lsSharedSecretDropSym lsStaticSecretDropSym
   lsStringCloneSym lsTimeAddSym)
open CryptoVerification.SignalSession.Cli (cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.MainHops
  (fromUtf8AsciiSpec memrchrSpec strlenSpec)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks ExtraGhostTable IsFsC cliExtraGhostSyms cliExtraGhostSyms_disjoint_named
   cliExtraGhostSyms_not_named cliGhostExterns cliGhostExternsNamed cliGhostExternsWithExtra
   cliGhostExternsWithExtra_extra_some cliGhostExternsWithExtra_other cliNamedGhostSyms
   named_eq_false_of_extra_contains)
open CryptoVerification.SignalSession.Cli.Slots
  (durationSinceEpochAllocSpec durationSinceEpochAtSpec)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (durationSinceEpochBudgetSpec timeAddBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
  (libcMemmoveBoundedSpec sessionMemmoveBoundedBudgetSpec sessionMemmoveBoundedSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (withStrlenPadRO)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (fromUtf8AsciiSpecRO memrchrSpecRO strlenSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BcmpRowSpec (BcmpRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BlackBoxRowSpec
  (BlackBoxRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.DurationSinceRowSpec
  (DurationSinceRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FromUtf8RowSpec
  (FromUtf8RowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemmoveRowSpec
  (MemmoveRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemrchrRowSpec
  (MemrchrRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec
  (SharedSecretDropRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StaticSecretDropRowSpec
  (StaticSecretDropRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StrlenRowSpec (StrlenRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.TimeAddRowSpec
  (TimeAddRowSpec)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BcmpRowSpec (BcmpRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BlackBoxRowSpec
  (BlackBoxRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.DurationSinceRowSpec
  (DurationSinceRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FromUtf8RowSpec
  (FromUtf8RowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemmoveRowSpec
  (MemmoveRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemrchrRowSpec
  (MemrchrRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec
  (SharedSecretDropRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StaticSecretDropRowSpec
  (StaticSecretDropRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StrlenRowSpec (StrlenRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.TimeAddRowSpec
  (TimeAddRowSpec)

/-! ## 1. Named vs. Extra Ghost Symbol Lists & Key Freshness -/

export CryptoVerification.SignalSession.Cli.RunGlue
  (ExtraGhostTable cliNamedGhostSyms cliExtraGhostSyms cliExtraGhostSyms_disjoint_named
   cliExtraGhostSyms_not_named)
export CryptoVerification.SignalSession.Cli.RunGlue
  (named_eq_false_of_extra_contains cliGhostExternsNamed cliGhostExternsWithExtra
   cliGhostExternsWithExtra_extra_some cliGhostExternsWithExtra_other)

/-- At `extra = []`, `cliGhostExternsWithExtra` collapses to the pre-2B 10-way `cliGhostExternsNamed`
    (using `named_eq_false_of_extra_contains` on the `cliExtraGhostSyms.contains sym = true` branch,
    where `[].lookup sym = none` falls back to `b sym`). -/
theorem cliGhostExternsWithExtra_nil (gh : CliGhostHooks)
    (b : String → Option (State → State)) :
    cliGhostExternsWithExtra gh [] b = cliGhostExternsNamed gh b := by
  funext sym
  unfold cliGhostExternsWithExtra cliGhostExternsNamed
  cases hc : cliExtraGhostSyms.contains sym with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]
  | true =>
    rcases named_eq_false_of_extra_contains hc with
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    simp only [List.lookup, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Bool.false_eq_true, ↓reduceIte]

/-- Key-only projection that never inspects (potentially `noncomputable`) `State → State` values. -/
@[expose] def cliGhostExtraKeys {V : Type} : List (String × V) → List String
  | [] => []
  | (k, _) :: tl => k :: cliGhostExtraKeys tl

@[simp] theorem cliGhostExtraKeys_eq_map_fst {V : Type} (l : List (String × V)) :
    cliGhostExtraKeys l = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [cliGhostExtraKeys, ih]

/-- Kernel-`rfl`-reducible key freshness check: keys are pairwise distinct (`Nodup`), drawn from
    `cliExtraGhostSyms`, and disjoint from `cliNamedGhostSyms`. -/
@[expose] def freshExtraKeysListB {V : Type} (extra : List (String × V)) : Bool :=
  let ks := cliGhostExtraKeys extra
  ks.Pairwise (· != ·) &&
    ks.all (fun k => cliExtraGhostSyms.contains k && !(cliNamedGhostSyms.contains k))

/-- Propositional key freshness side condition (`Nodup` + inside `cliExtraGhostSyms` + disjoint
    from `cliNamedGhostSyms`). Decidable even when paired `State → State` values are noncomputable. -/
abbrev FreshExtraKeysList {V : Type} (extra : List (String × V)) : Prop :=
  (extra.map Prod.fst).Nodup ∧
    ∀ k ∈ extra.map Prod.fst, k ∈ cliExtraGhostSyms ∧ k ∉ cliNamedGhostSyms

abbrev FreshExtraKeys (g : CliGhostHooks) : Prop :=
  FreshExtraKeysList g.extra

theorem FreshExtraKeysList.nil {V : Type} : FreshExtraKeysList ([] : List (String × V)) :=
  ⟨List.nodup_nil, fun _ h => nomatch h⟩

/-- Key-completeness predicate: every symbol in `cliExtraGhostSyms` is bound in `extra`.
    Uses `extra.map Prod.fst` so `by decide` closes concrete 10-row tables without inspecting
    noncomputable `State → State` functions. -/
abbrev CompleteExtraKeysList {V : Type} (extra : List (String × V)) : Prop :=
  ∀ sym ∈ cliExtraGhostSyms, sym ∈ extra.map Prod.fst

private theorem lookup_isSome_of_mem_map_fst {V : Type} {l : List (String × V)} {sym : String}
    (hmem : sym ∈ l.map Prod.fst) :
    (l.lookup sym).isSome = true := by
  induction l with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    by_cases hsk : sym = k
    · subst hsk
      simp [List.lookup]
    · simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with hsk' | htl
      · exact absurd hsk' hsk
      · have hbeq : (sym == k) = false := beq_eq_false_iff_ne.mpr hsk
        simp [List.lookup, hbeq, ih htl]

/-- Extract `(extra.lookup sym).isSome = true` from `CompleteExtraKeysList extra` and
    `cliExtraGhostSyms.contains sym = true`. -/
theorem CompleteExtraKeysList.lookup_isSome {V : Type} {extra : List (String × V)}
    (hComp : CompleteExtraKeysList extra) {sym : String}
    (hDom : cliExtraGhostSyms.contains sym = true) :
    (extra.lookup sym).isSome = true :=
  lookup_isSome_of_mem_map_fst (hComp sym (List.contains_iff_mem.mp hDom))

/-! ## 3. `ExtraRowSpec`, `GhostRowSpecOk`, `ExtraListSpecOk` & `ExtraSpecOk` -/

/-- Row-specific `HookOk` dispatcher (`ExtraRowSpec` per H-REV2 §6(b2)/M4) routing each of the
    10 Cutover-2 symbols to its row-owned `*RowSpec` leaf predicate. -/
@[expose] def ExtraRowSpec [LibsignalPlacement] (sym : String) (f : State → State) : Prop :=
  if sym == "bcmp" then BcmpRowSpec f
  else if sym == "strlen" then StrlenRowSpec f
  else if sym == "memmove" then MemmoveRowSpec f
  else if sym == lsFromUtf8Sym then FromUtf8RowSpec f
  else if sym == lsMemrchrSym then MemrchrRowSpec f
  else if sym == lsDurationSinceSym then DurationSinceRowSpec f
  else if sym == lsTimeAddSym then TimeAddRowSpec f
  else if sym == lsBlackBoxSym then BlackBoxRowSpec f
  else if sym == lsStaticSecretDropSym then StaticSecretDropRowSpec f
  else if sym == lsSharedSecretDropSym then SharedSecretDropRowSpec f
  else False

/-- Complete consumer-side obligation for a Cutover-2 ghost hook `(sym, f)`:
    1. `fs_eq` (`(f s).fs = s.fs`),
    2. `fsT` (`HookFsTraced IsFsC f`),
    3. `rowSpec` (`ExtraRowSpec sym f` — covers plain, RO, `withVmPreserved`, and `withAlloc`
       consumer specs; `withLsRoCl` follows generically via `hookOk_withLsRoCl`). -/
structure GhostRowSpecOk [LibsignalPlacement] (sym : String) (f : State → State) : Prop where
  fs_eq   : ∀ s : State, (f s).fs = s.fs
  fsT     : HookFsTraced IsFsC f
  rowSpec : ExtraRowSpec sym f

/-- R1 bundle predicate over an `extra` table: key freshness + `GhostRowSpecOk` for every entry. -/
structure ExtraListSpecOk [LibsignalPlacement] (extra : ExtraGhostTable) : Prop where
  fresh : FreshExtraKeysList extra := by decide
  rowOk : ∀ sym f, extra.lookup sym = some f → GhostRowSpecOk sym f := by
    intro _ _ h; cases h

theorem ExtraListSpecOk.nil [LibsignalPlacement] : ExtraListSpecOk [] :=
  ⟨FreshExtraKeysList.nil, fun _ _ h => by cases h⟩

theorem ExtraListSpecOk.fsT [LibsignalPlacement] {extra : ExtraGhostTable}
    (hOk : ExtraListSpecOk extra) :
    ∀ sym f, cliExtraGhostSyms.contains sym = true →
      extra.lookup sym = some f → HookFsTraced IsFsC f :=
  fun sym f _ hLook => (hOk.rowOk sym f hLook).fsT

/-- Complete R1 consumer spec bundle over a populated 10-row `extra` table
    (`ExtraListSpecOk` + `CompleteExtraKeysList`). -/
structure ExtraFullListSpecOk [LibsignalPlacement] (extra : ExtraGhostTable) : Prop
    extends ExtraListSpecOk extra where
  complete : CompleteExtraKeysList extra := by decide

/-- R1 bundle field predicate (`extraOk : ExtraSpecOk g`) on `CliGhostHooks` in Cutover 2B:
    guarantees key freshness, `GhostRowSpecOk` on every row, and completeness across all 10
    `cliExtraGhostSyms`. -/
abbrev ExtraSpecOk [LibsignalPlacement] (g : CliGhostHooks) : Prop :=
  ExtraFullListSpecOk g.extra

/-- Direct `(extra.lookup sym).isSome = true` projection on `ExtraFullListSpecOk` / `ExtraSpecOk`
    so callers of `hookSat_withExtra_of_isSome` can pass `(hSome := hG.extraOk.lookup_isSome)`. -/
theorem ExtraFullListSpecOk.lookup_isSome [LibsignalPlacement] {extra : ExtraGhostTable}
    (hOk : ExtraFullListSpecOk extra) {sym : String}
    (hDom : cliExtraGhostSyms.contains sym = true := by decide) :
    (extra.lookup sym).isSome = true :=
  hOk.complete.lookup_isSome hDom

/-- `HookFsTraced` projection on `ExtraFullListSpecOk` / `ExtraSpecOk`. -/
theorem ExtraFullListSpecOk.fsT [LibsignalPlacement] {extra : ExtraGhostTable}
    (hOk : ExtraFullListSpecOk extra) :
    ∀ sym f, cliExtraGhostSyms.contains sym = true →
      extra.lookup sym = some f → HookFsTraced IsFsC f :=
  hOk.toExtraListSpecOk.fsT

/-! ## 4. Generic Framing (`withLsRoCl`, Twin Congruence) & `HookSat` Lift Combinators -/

/-- Congruence transfer between duplicate `Spec α` definitions with identical fields (e.g.
    `LibsignalTripleRatchet.blackBoxSpec` ↔ `FindReceiverChainIndex.blackBoxSpec`, or
    `withVmPreserved LibsignalPublicApi.timeAddSpec` ↔ `timeAddBudgetSpec`). -/
theorem hookOk_congr {α : Type} {f : State → State} {spec₁ spec₂ : Spec α}
    (h : HookOk f spec₁)
    (hpre  : spec₁.pre = spec₂.pre := by rfl)
    (hpost : spec₁.post = spec₂.post := by rfl)
    (hpan  : spec₁.onPanic = spec₂.onPanic := by rfl)
    (hexit : spec₁.onExit = spec₂.onExit := by rfl)
    (hoom  : spec₁.onOom = spec₂.onOom := by rfl) :
    HookOk f spec₂ := by
  cases spec₁; cases spec₂
  dsimp at hpre hpost hpan hexit hoom
  subst hpre hpost hpan hexit hoom
  exact h

/-- Any `HookOk f spec` automatically satisfies `StoreKit.withLsRoCl pl spec` via `KeepsFrozen`. -/
theorem hookOk_withLsRoCl {α : Type} {f : State → State} (pl : MultiPlacement) {spec : Spec α}
    (h : HookOk f spec) :
    HookOk f (withLsRoCl pl spec) := by
  intro x R s0 hrun hpre hsp
  have ⟨hcrl0, hpre'⟩ := extract_withLsRoCl hpre
  rcases h x R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  have hcrlf := hcrl0.of_keepsFrozen hkeep
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcrlf, hpost⟩
  · exact Or.inr hrest

/-- Lift `HookSat hooks sym spec` to `HookSat hooks sym (StoreKit.withLsRoCl pl spec)`. -/
theorem hookSat_withLsRoCl {α : Type} {hooks : String → Option (State → State)}
    (pl : MultiPlacement) {sym : String} {spec : Spec α}
    (h : HookSat hooks sym spec) :
    HookSat hooks sym (withLsRoCl pl spec) := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, hf, hookOk_withLsRoCl pl hok⟩

/-- Generic `HookSat` lift over `cliGhostExternsWithExtra`: covers both pre-cutover (`lookup = none`,
    delegating to `hBase`) and post-cutover (`lookup = some f`, extracting from `hOk`).
    Stable public API consumed by `HOOKS-PREP` (`EX-MEMRCHR`, `EX-STRLEN-PAD`). -/
theorem hookSat_withExtra_of_base [LibsignalPlacement] {α : Type}
    (g : CliGhostHooks) {extra : ExtraGhostTable}
    (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hDom : cliExtraGhostSyms.contains sym = true)
    (hRow : ∀ f, extra.lookup sym = some f → GhostRowSpecOk sym f → HookOk f spec)
    (hOk : ExtraListSpecOk extra)
    (hBase : HookSat baseExt sym spec) :
    HookSat (cliGhostExternsWithExtra g extra baseExt) sym spec := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := named_eq_false_of_extra_contains hDom
  cases hLook : extra.lookup sym with
  | some f =>
    exact ⟨f, cliGhostExternsWithExtra_extra_some g extra baseExt hLook hDom,
      hRow f hLook (hOk.rowOk sym f hLook)⟩
  | none =>
    have heq : cliGhostExternsWithExtra g extra baseExt sym = baseExt sym := by
      unfold cliGhostExternsWithExtra
      simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hDom, hLook, Bool.false_eq_true,
        ↓reduceIte]
    rcases hBase with ⟨fb, hfb, hokb⟩
    exact ⟨fb, heq.trans hfb, hokb⟩

/-- `cliGhostExterns`-targeted companion to `hookSat_withExtra_of_base`: identical argument
    order (`g`, `baseExt`, `hDom`, `hRow`, `hOk : ExtraSpecOk g`, `hBase`), concluding
    `HookSat (cliGhostExterns g baseExt) sym spec` directly.
    - In Commit 2A (before `cliGhostExterns` dispatches `g.extra`), `named_eq_false_of_extra_contains`
      rewrites `cliGhostExterns g baseExt sym = baseExt sym`.
    - In Commit 2B (once `cliGhostExterns g baseExt sym := cliGhostExternsWithExtra g g.extra
      baseExt sym`), the **identical signature** delegates in 1 line to
      `hookSat_withExtra_of_base g baseExt hDom hRow hOk hBase`, allowing `HOOKS-PREP` (`EX-MEMRCHR`,
      `EX-STRLEN-PAD`) to switch `#1328`'s `*Sat` bridges immediately on Commit 2A with zero
      re-editing at Commit 2B. -/
theorem hookSat_cliGhostExterns_of_base [LibsignalPlacement] {α : Type}
    (g : CliGhostHooks)
    (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hDom : cliExtraGhostSyms.contains sym = true)
    (hRow : ∀ f, g.extra.lookup sym = some f → GhostRowSpecOk sym f → HookOk f spec)
    (hOk : ExtraSpecOk g)
    (hBase : HookSat baseExt sym spec) :
    HookSat (cliGhostExterns g baseExt) sym spec :=
  hookSat_withExtra_of_base g baseExt hDom hRow hOk.toExtraListSpecOk hBase

/-- Post-cutover `HookSat` lift requiring **no** `baseExt` hypothesis when `sym` is populated in
    `extra` (`(extra.lookup sym).isSome = true`, closed by `rfl`/`decide` on concrete tables). -/
theorem hookSat_withExtra_of_isSome [LibsignalPlacement] {α : Type}
    (g : CliGhostHooks) {extra : ExtraGhostTable}
    (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hRow : ∀ f, extra.lookup sym = some f → GhostRowSpecOk sym f → HookOk f spec)
    (hOk : ExtraListSpecOk extra)
    (hDom : cliExtraGhostSyms.contains sym = true := by decide)
    (hSome : (extra.lookup sym).isSome = true := by decide) :
    HookSat (cliGhostExternsWithExtra g extra baseExt) sym spec := by
  cases hLook : extra.lookup sym with
  | none => rw [hLook] at hSome; cases hSome
  | some f =>
    exact ⟨f, cliGhostExternsWithExtra_extra_some g extra baseExt hLook hDom,
      hRow f hLook (hOk.rowOk sym f hLook)⟩

/-- Table-parametric companion to `hookSat_cliGhostExterns_of_extraOk` on
    `cliGhostExternsWithExtra g extra baseExt`. -/
theorem hookSat_withExtra_of_fullOk [LibsignalPlacement] {α : Type}
    (g : CliGhostHooks) {extra : ExtraGhostTable}
    (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hOk : ExtraFullListSpecOk extra)
    (hRow : ∀ f, extra.lookup sym = some f → GhostRowSpecOk sym f → HookOk f spec)
    (hDom : cliExtraGhostSyms.contains sym = true := by decide) :
    HookSat (cliGhostExternsWithExtra g extra baseExt) sym spec :=
  hookSat_withExtra_of_isSome g baseExt hRow hOk.toExtraListSpecOk hDom (hOk.lookup_isSome hDom)

/-- **Primary 2B R1 consumer lift (baseExt-free):** derive `HookSat (cliGhostExterns g baseExt) sym spec`
    for any `sym ∈ cliExtraGhostSyms` directly from `hOk : ExtraSpecOk g` (`hG.extraOk`) with NO
    `baseExt` hypothesis. -/
theorem hookSat_cliGhostExterns_of_extraOk [LibsignalPlacement] {α : Type}
    (g : CliGhostHooks) (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hOk : ExtraSpecOk g)
    (hRow : ∀ f, g.extra.lookup sym = some f → GhostRowSpecOk sym f → HookOk f spec)
    (hDom : cliExtraGhostSyms.contains sym = true := by decide) :
    HookSat (cliGhostExterns g baseExt) sym spec :=
  hookSat_withExtra_of_fullOk g baseExt hOk hRow hDom

/-! ## 5. Per-Row Plain, RO, `withVmPreserved`, & `withAlloc` Extractors from `GhostRowSpecOk` -/

theorem GhostRowSpecOk.bcmp_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : BcmpRowSpec f := by
  have hp := h.rowSpec; dsimp only [ExtraRowSpec] at hp; exact hp

theorem GhostRowSpecOk.bcmp_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : HookOk f cliBcmpSpec :=
  h.bcmp_row.1

theorem GhostRowSpecOk.bcmp_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : HookOk f (withVmPreserved cliBcmpSpec) :=
  h.bcmp_row.2.1

theorem GhostRowSpecOk.bcmp_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim cliBcmpSpec) :=
  h.bcmp_row.2.2.1 A lim

theorem GhostRowSpecOk.bcmpVregs_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : HookOk f bcmpVregsSpec :=
  h.bcmp_row.2.2.2.1

theorem GhostRowSpecOk.bcmpVregs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : HookOk f (withVmPreserved bcmpVregsSpec) :=
  h.bcmp_row.2.2.2.2.1

theorem GhostRowSpecOk.bcmpVregs_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim bcmpVregsSpec) :=
  h.bcmp_row.2.2.2.2.2 A lim

theorem GhostRowSpecOk.e2eBcmp_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : HookOk f e2eBcmpSpec :=
  hookOk_bcmpSpec_of_vregs h.bcmpVregs_ok

theorem GhostRowSpecOk.strlen_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f) : StrlenRowSpec f := by
  have hp := h.rowSpec; dsimp only [ExtraRowSpec] at hp; exact hp

theorem GhostRowSpecOk.strlen_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f) (stk : Nat) :
    HookOk f (withStrlenPadRO (strlenSpec stk)) :=
  h.strlen_row.1 stk

theorem GhostRowSpecOk.strlen_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f) (stk : Nat) :
    HookOk f (withVmPreserved (withStrlenPadRO (strlenSpec stk))) :=
  h.strlen_row.2.1 stk

theorem GhostRowSpecOk.strlen_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (withStrlenPadRO (strlenSpec stk))) :=
  h.strlen_row.2.2.1 A lim stk

theorem GhostRowSpecOk.strlenRO_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f) (stk : Nat) :
    HookOk f (withStrlenPadRO (strlenSpecRO stk)) :=
  h.strlen_row.2.2.2.1 stk

theorem GhostRowSpecOk.strlenRO_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f) (stk : Nat) :
    HookOk f (withVmPreserved (withStrlenPadRO (strlenSpecRO stk))) :=
  h.strlen_row.2.2.2.2.1 stk

theorem GhostRowSpecOk.strlenRO_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (withStrlenPadRO (strlenSpecRO stk))) :=
  h.strlen_row.2.2.2.2.2.1 A lim stk

theorem GhostRowSpecOk.strlenROSat_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (withVmPreserved (withStrlenPadRO (strlenSpecRO stk)))) :=
  h.strlen_row.2.2.2.2.2.2 A lim stk

theorem GhostRowSpecOk.memmove_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) : MemmoveRowSpec f := by
  have hp := h.rowSpec; dsimp only [ExtraRowSpec] at hp; exact hp

theorem GhostRowSpecOk.memmove_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) (stk : Nat) :
    HookOk f (libcMemmoveBoundedSpec stk) :=
  h.memmove_row.1 stk

theorem GhostRowSpecOk.memmove_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) (stk : Nat) :
    HookOk f (withVmPreserved (libcMemmoveBoundedSpec stk)) :=
  h.memmove_row.2.1 stk

theorem GhostRowSpecOk.memmove_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (libcMemmoveBoundedSpec stk)) :=
  h.memmove_row.2.2.1 A lim stk

theorem GhostRowSpecOk.sessionMemmove_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) (stk : Nat) :
    HookOk f (sessionMemmoveBoundedSpec stk) :=
  h.memmove_row.2.2.2.1 stk

theorem GhostRowSpecOk.sessionMemmove_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) (stk : Nat) :
    HookOk f (sessionMemmoveBoundedBudgetSpec stk) :=
  h.memmove_row.2.2.2.2.1 stk

theorem GhostRowSpecOk.sessionMemmove_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (sessionMemmoveBoundedSpec stk)) :=
  h.memmove_row.2.2.2.2.2.1 A lim stk

theorem GhostRowSpecOk.memmove_allocCallPreserved [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) :
    ∀ s : State, AllocCallPreserved s (f s) :=
  h.memmove_row.2.2.2.2.2.2

theorem GhostRowSpecOk.fromUtf8_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f) : FromUtf8RowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsFromUtf8Sym == "bcmp") = false := by decide
  have hd2 : (lsFromUtf8Sym == "strlen") = false := by decide
  have hd3 : (lsFromUtf8Sym == "memmove") = false := by decide
  have hd4 : (lsFromUtf8Sym == lsFromUtf8Sym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.fromUtf8_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f) (stk : Nat) :
    HookOk f (fromUtf8AsciiSpec stk) :=
  h.fromUtf8_row.1 stk

theorem GhostRowSpecOk.fromUtf8_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f) (stk : Nat) :
    HookOk f (withVmPreserved (fromUtf8AsciiSpec stk)) :=
  h.fromUtf8_row.2.1 stk

theorem GhostRowSpecOk.fromUtf8_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (fromUtf8AsciiSpec stk)) :=
  h.fromUtf8_row.2.2.1 A lim stk

theorem GhostRowSpecOk.fromUtf8RO_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f) (stk : Nat) :
    HookOk f (fromUtf8AsciiSpecRO stk) :=
  h.fromUtf8_row.2.2.2.1 stk

theorem GhostRowSpecOk.fromUtf8RO_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f) (stk : Nat) :
    HookOk f (withVmPreserved (fromUtf8AsciiSpecRO stk)) :=
  h.fromUtf8_row.2.2.2.2.1 stk

theorem GhostRowSpecOk.fromUtf8RO_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (fromUtf8AsciiSpecRO stk)) :=
  h.fromUtf8_row.2.2.2.2.2 A lim stk

theorem GhostRowSpecOk.memrchr_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f) : MemrchrRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsMemrchrSym == "bcmp") = false := by decide
  have hd2 : (lsMemrchrSym == "strlen") = false := by decide
  have hd3 : (lsMemrchrSym == "memmove") = false := by decide
  have hd4 : (lsMemrchrSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsMemrchrSym == lsMemrchrSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.memrchr_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (memrchrSpec stk)) :=
  h.memrchr_row.1 stk hstk hstk_ub

theorem GhostRowSpecOk.memrchr_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (memrchrSpec stk))) :=
  h.memrchr_row.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.memrchr_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (memrchrSpec stk))) :=
  h.memrchr_row.2.2.1 A lim stk hstk hstk_ub

theorem GhostRowSpecOk.memrchrRO_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (memrchrSpecRO stk)) :=
  h.memrchr_row.2.2.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.memrchrRO_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (memrchrSpecRO stk))) :=
  h.memrchr_row.2.2.2.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.memrchrRO_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (memrchrSpecRO stk))) :=
  h.memrchr_row.2.2.2.2.2 A lim stk hstk hstk_ub

theorem GhostRowSpecOk.durationSince_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) : DurationSinceRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsDurationSinceSym == "bcmp") = false := by decide
  have hd2 : (lsDurationSinceSym == "strlen") = false := by decide
  have hd3 : (lsDurationSinceSym == "memmove") = false := by decide
  have hd4 : (lsDurationSinceSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsDurationSinceSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsDurationSinceSym == lsDurationSinceSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.durationSinceBounded_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) :
    HookOk f (withLsRet CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec) :=
  h.durationSince_row.1

theorem GhostRowSpecOk.durationSinceBounded_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) :
    HookOk f (withLsRet (withVmPreserved
      CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec)) :=
  h.durationSince_row.2.1

theorem GhostRowSpecOk.durationSinceBounded_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withLsRet (withAlloc A lim
      CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec)) :=
  h.durationSince_row.2.2.1 A lim

theorem GhostRowSpecOk.durationSinceEpochAt_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) {stk : Nat}
    (hstk : 208 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (durationSinceEpochAtSpec stk)) :=
  h.durationSince_row.2.2.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.durationSinceEpochAt_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) {stk : Nat}
    (hstk : 208 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (durationSinceEpochAtSpec stk))) :=
  h.durationSince_row.2.2.2.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.durationSinceEpochAt_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : 208 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (durationSinceEpochAtSpec stk))) :=
  h.durationSince_row.2.2.2.2.2 A lim stk hstk hstk_ub

theorem GhostRowSpecOk.durationSinceEpoch_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) :
    HookOk f (withLsRet durationSinceEpochBudgetSpec) :=
  h.durationSinceEpochAt_budget_ok (by decide : 208 ≤ extHookStack) (by decide)

theorem GhostRowSpecOk.durationSinceEpochAlloc_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) :
    HookOk f (withLsRet (withVmPreserved durationSinceEpochAllocSpec)) :=
  h.durationSinceEpochAt_budget_ok (by decide : 208 ≤ allocHookStack) (by decide)

theorem GhostRowSpecOk.timeAdd_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f) : TimeAddRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsTimeAddSym == "bcmp") = false := by decide
  have hd2 : (lsTimeAddSym == "strlen") = false := by decide
  have hd3 : (lsTimeAddSym == "memmove") = false := by decide
  have hd4 : (lsTimeAddSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsTimeAddSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsTimeAddSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsTimeAddSym == lsTimeAddSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.publicApiTimeAdd_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f) :
    HookOk f (withLsRet CryptoVerification.LibsignalPublicApi.timeAddSpec) :=
  h.timeAdd_row.1

theorem GhostRowSpecOk.e2eTimeAdd_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f) :
    HookOk f (withLsRet CryptoVerification.E2E.HooksE.timeAddSpec) :=
  hookOk_congr h.publicApiTimeAdd_ok

theorem GhostRowSpecOk.publicApiTimeAdd_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f) :
    HookOk f (withLsRet (withVmPreserved CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  h.timeAdd_row.2.1

theorem GhostRowSpecOk.timeAdd_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f) :
    HookOk f (withLsRet timeAddBudgetSpec) :=
  hookOk_congr h.publicApiTimeAdd_budget_ok

theorem GhostRowSpecOk.publicApiTimeAdd_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withLsRet (withAlloc A lim CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  h.timeAdd_row.2.2 A lim

theorem GhostRowSpecOk.blackBox_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f) : BlackBoxRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsBlackBoxSym == "bcmp") = false := by decide
  have hd2 : (lsBlackBoxSym == "strlen") = false := by decide
  have hd3 : (lsBlackBoxSym == "memmove") = false := by decide
  have hd4 : (lsBlackBoxSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsBlackBoxSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsBlackBoxSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsBlackBoxSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsBlackBoxSym == lsBlackBoxSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.blackBox_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withStack blackBoxSpec stk) :=
  h.blackBox_row.1 stk hstk hstk_ub

theorem GhostRowSpecOk.blackBox_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withVmPreserved (withStack blackBoxSpec stk)) :=
  h.blackBox_row.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.blackBox_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withAlloc A lim (withStack blackBoxSpec stk)) :=
  h.blackBox_row.2.2 A lim stk hstk hstk_ub

theorem GhostRowSpecOk.findReceiverBlackBox_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withStack CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec stk) :=
  hookOk_congr (h.blackBox_ok hstk hstk_ub)

theorem GhostRowSpecOk.findReceiverBlackBox_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withVmPreserved
      (withStack CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec stk)) :=
  hookOk_congr (h.blackBox_budget_ok hstk hstk_ub)

theorem GhostRowSpecOk.staticSecretDrop_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsStaticSecretDropSym f) : StaticSecretDropRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsStaticSecretDropSym == "bcmp") = false := by decide
  have hd2 : (lsStaticSecretDropSym == "strlen") = false := by decide
  have hd3 : (lsStaticSecretDropSym == "memmove") = false := by decide
  have hd4 : (lsStaticSecretDropSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsStaticSecretDropSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsStaticSecretDropSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsStaticSecretDropSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsStaticSecretDropSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsStaticSecretDropSym == lsStaticSecretDropSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.staticSecretDrop_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsStaticSecretDropSym f) :
    HookOk f zeroizeSecretSpec :=
  h.staticSecretDrop_row.1

theorem GhostRowSpecOk.staticSecretDrop_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsStaticSecretDropSym f) :
    HookOk f (withVmPreserved zeroizeSecretSpec) :=
  h.staticSecretDrop_row.2.1

theorem GhostRowSpecOk.staticSecretDrop_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsStaticSecretDropSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim zeroizeSecretSpec) :=
  h.staticSecretDrop_row.2.2 A lim

theorem GhostRowSpecOk.sharedSecretDrop_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsSharedSecretDropSym f) : SharedSecretDropRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
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
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, Bool.false_eq_true,
    ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.sharedSecretDrop_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsSharedSecretDropSym f) :
    HookOk f zeroizeSecretSpec :=
  h.sharedSecretDrop_row.1

theorem GhostRowSpecOk.sharedSecretDrop_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsSharedSecretDropSym f) :
    HookOk f (withVmPreserved zeroizeSecretSpec) :=
  h.sharedSecretDrop_row.2.1

theorem GhostRowSpecOk.sharedSecretDrop_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsSharedSecretDropSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim zeroizeSecretSpec) :=
  h.sharedSecretDrop_row.2.2 A lim

/-! ## 6. Kernel Reduction Smoke Checks on `List.lookup` & `FreshExtraKeysList` -/

theorem extra_lookup_hit_smoke (f : State → State) :
    ({ alloc := id, dealloc := id, realloc := id, allocZeroed := id,
       extra := [("memmove", f)] } : CliGhostHooks).extra.lookup "memmove" = some f :=
  rfl

theorem extra_lookup_miss_smoke (f : State → State) :
    ({ alloc := id, dealloc := id, realloc := id, allocZeroed := id,
       extra := [("memmove", f)] } : CliGhostHooks).extra.lookup "memset" = none :=
  rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
