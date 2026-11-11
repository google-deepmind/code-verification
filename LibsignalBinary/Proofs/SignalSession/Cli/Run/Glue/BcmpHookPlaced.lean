/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `bcmp`, `cliExternsPlaced`, and `cliGhostExterns` Helpers

Lookup lemmas for the 39-entry `cliHookTablePlaced mmpl W` extern map (`cliExternsPlaced`), `HookSat`
and block-level `subroutine_ok` proofs for `"bcmp"`, and the `CliGhostHooks` / `cliGhostExterns`
ghost-hook overlay for allocator, `<String as Clone>::clone`, `read_file`, and `read_stdin` symbols.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-- Mangled symbol of `<alloc::string::String as core::clone::Clone>::clone` (`rfl`-equal to
`MessageDecrypt.lsStringCloneSym`). -/
abbrev CryptoVerification.SignalSession.lsStringCloneSym : String :=
  "_RNvXs4_NtCs69KKACWg7bl_5alloc6stringNtB5_6StringNtNtCskxtBwYRO61I_4core5clone5Clone5clone"

/-- Symbol name for `memset` (de-hooked from `cliHookTablePlaced` on the 37-row table; overlaid
    via `CliGhostHooks.memset`). -/
abbrev CryptoVerification.SignalSession.lsMemsetSym : String := "memset"

/-- Symbol name for `memcpy` (de-hooked from `cliHookTablePlaced` on the 37-row table; overlaid
    via `CliGhostHooks.memcpy`). -/
abbrev CryptoVerification.SignalSession.lsMemcpySym : String := "memcpy"

namespace CryptoVerification.SignalSession.Cli.RunGlue

open Arm64 ProofLib
open CryptoVerification
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli

/-- The `27` mangled symbol names of `cliHookTablePlaced mmpl W` (independent of `mmpl` and `W`). -/
def cliHookNamesPlaced : List String :=
  ["_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512",
   "_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards",
   "_RNvMsg_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint8compress",
   "_RNvXso_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPointNtNtNtCskxtBwYRO61I_4core3ops5arith3Neg3neg",
   "_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free",
   "_RNvMsw_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint35vartime_double_scalar_mul_basepoint",
   "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar20from_bytes_mod_order",
   "_RNvMNtCs2wR8L9wiBdT_16curve25519_dalek6scalarNtB2_6Scalar25from_bytes_mod_order_wide",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11encapsulate",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk1",
   "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk2",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate2",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental26decapsulate_compressed_key",
   "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes",
   "_RNvCs65XVORQObL2_12libcrux_hmac4hmac",
   lsWriteFileSym,
   lsWriteStdoutSym,
   lsFmtWriteSym,
   lsFormatInnerSym,
   lsCompress256Sym,
   lsAesEncSym,
   lsAesDecSym,
   lsPubFromSecretSym,
   lsDiffieHellmanSym]

theorem cliHookNamesPlaced_eq (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (cliHookTablePlaced mmpl W).map Prod.fst = cliHookNamesPlaced := rfl

theorem cliHookNamesPlaced_nodup : cliHookNamesPlaced.Nodup := by
  unfold cliHookNamesPlaced
  decide

theorem cliHookNamesPlaced_notPanic :
    cliHookNamesPlaced.all (fun n => !isCliPanicSymbolPlaced n) = true := by
  rw [List.all_eq_true]
  intro n hn
  simp only [cliHookNamesPlaced, lsWriteFileSym, lsWriteStdoutSym,
    lsFmtWriteSym, lsFormatInnerSym, lsCompress256Sym,
    lsAesEncSym, lsAesDecSym, lsPubFromSecretSym, lsDiffieHellmanSym,
    List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
  simp [isCliPanicSymbolPlaced, cliPanicSymbolsPlaced, Rust.isPanicSymbol]

private theorem lookup_of_mem_nodup_placed {α : Type} :
    ∀ (L : List (String × α)) (n : String) (v : α),
      (L.map Prod.fst).Nodup → (n, v) ∈ L → L.lookup n = some v
  | [], _, _, _, hm => nomatch hm
  | (k, w) :: rest, n, v, hnd, hm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with hhead | htail
    · cases hhead
      simp [List.lookup]
    · have hne : (n == k) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        subst heq
        exact hnd.1 (List.mem_map.mpr ⟨(n, v), htail, rfl⟩)
      simp [List.lookup, hne, lookup_of_mem_nodup_placed rest n v hnd.2 htail]

private theorem lookup_of_not_mem_placed {α : Type} :
    ∀ (L : List (String × α)) (n : String),
      n ∉ L.map Prod.fst → L.lookup n = none
  | [], _, _ => rfl
  | (k, _) :: rest, n, hnm => by
    rw [List.map_cons, List.mem_cons, not_or] at hnm
    have hne : (n == k) = false := beq_eq_false_iff_ne.mpr hnm.1
    simp [List.lookup, hne, lookup_of_not_mem_placed rest n hnm.2]

/-- Every `(n, h)` row of `cliHookTablePlaced mmpl W` resolves to `some h` in `cliExternsPlaced mmpl W`. -/
theorem cliExternsPlaced_row (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {n : String} {h : State → State}
    (hm : (n, h) ∈ cliHookTablePlaced mmpl W) : cliExternsPlaced mmpl W n = some h := by
  have hn : n ∈ cliHookNamesPlaced := by
    rw [← cliHookNamesPlaced_eq mmpl W]
    exact List.mem_map.mpr ⟨(n, h), hm, rfl⟩
  have hp : isCliPanicSymbolPlaced n = false := by
    have := List.all_eq_true.mp cliHookNamesPlaced_notPanic n hn
    simpa using this
  unfold cliExternsPlaced
  simp only [hp, Bool.false_eq_true, ↓reduceIte]
  exact lookup_of_mem_nodup_placed _ n h
    (by rw [cliHookNamesPlaced_eq mmpl W]; exact cliHookNamesPlaced_nodup) hm

/-- Every non-panic symbol outside `cliHookNamesPlaced` maps to `none` in `cliExternsPlaced mmpl W`. -/
theorem cliExternsPlaced_none (mmpl : Obj.MultiPlacement) (W : CliHooks) {n : String}
    (hn : n ∉ cliHookNamesPlaced) (hp : isCliPanicSymbolPlaced n = false) :
    cliExternsPlaced mmpl W n = none := by
  unfold cliExternsPlaced
  simp only [hp, Bool.false_eq_true, ↓reduceIte]
  exact lookup_of_not_mem_placed _ n (by rw [cliHookNamesPlaced_eq mmpl W]; exact hn)

/-- Every symbol in `cliPanicSymbolsPlaced` maps to `some Rust.panicked` in `cliExternsPlaced mmpl W`. -/
theorem cliExternsPlaced_panic_of_mem (mmpl : Obj.MultiPlacement) (W : CliHooks) {n : String}
    (hn : n ∈ cliPanicSymbolsPlaced) : cliExternsPlaced mmpl W n = some Rust.panicked := by
  simp [cliExternsPlaced, isCliPanicSymbolPlaced, hn]

/-- `cliExternsPlaced mmpl W` is already closed under `Rust.withPanics`. -/
@[simp]
theorem withPanics_cliExternsPlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    Rust.withPanics (cliExternsPlaced mmpl W) = cliExternsPlaced mmpl W := by
  funext n
  by_cases hp : Rust.isPanicSymbol n = true
  · unfold Rust.withPanics cliExternsPlaced isCliPanicSymbolPlaced
    simp [hp]
  · simp [Rust.withPanics, hp]

/-! ## Ghost-Hook Overlay (`CliGhostHooks` & `cliGhostExterns`) -/

/-- Type alias for the generic Cutover-2 ghost hook association list. -/
abbrev ExtraGhostTable : Type := List (String × (State → State))

/-- The 10 named `CliGhostHooks` dispatch symbols (5 F3 alloc + 3 F3 optional + Stage A
    `lsMemsetSym` / `lsMemcpySym`). -/
def cliNamedGhostSyms : List String :=
  [lsRustAllocSymCli, lsRustDeallocSymCli, lsRustReallocSymCli,
   lsRustAllocZeroedSymCli, lsRustNoAllocShimSymCli,
   lsStringCloneSym, lsReadFileSym, lsReadStdinSym,
   lsMemsetSym, lsMemcpySym]

/-- The 10 Cutover-2 symbols eligible for `CliGhostHooks.extra` dispatch. -/
def cliExtraGhostSyms : List String :=
  ["memmove", "bcmp", "strlen",
   lsMemrchrSym, lsFromUtf8Sym, lsDurationSinceSym, lsTimeAddSym,
   lsBlackBoxSym, lsStaticSecretDropSym, lsSharedSecretDropSym]

theorem cliExtraGhostSyms_disjoint_named :
    (cliExtraGhostSyms.all fun s => !(cliNamedGhostSyms.contains s)) = true := by
  decide

theorem cliExtraGhostSyms_not_named {sym : String}
    (h : cliExtraGhostSyms.contains sym = true) :
    cliNamedGhostSyms.contains sym = false := by
  have hmem : sym ∈ cliExtraGhostSyms := List.contains_iff_mem.mp h
  have hall := List.all_eq_true.mp cliExtraGhostSyms_disjoint_named sym hmem
  cases hc : cliNamedGhostSyms.contains sym
  · rfl
  · rw [hc] at hall; cases hall

theorem named_eq_false_of_extra_contains {sym : String}
    (h : cliExtraGhostSyms.contains sym = true) :
    (sym == lsRustAllocSymCli) = false ∧
    (sym == lsRustDeallocSymCli) = false ∧
    (sym == lsRustReallocSymCli) = false ∧
    (sym == lsRustAllocZeroedSymCli) = false ∧
    (sym == lsRustNoAllocShimSymCli) = false ∧
    (sym == lsStringCloneSym) = false ∧
    (sym == lsReadFileSym) = false ∧
    (sym == lsReadStdinSym) = false ∧
    (sym == lsMemsetSym) = false ∧
    (sym == lsMemcpySym) = false := by
  have hnn := cliExtraGhostSyms_not_named h
  have hnot_mem : sym ∉ cliNamedGhostSyms := by
    intro hm
    have hc : cliNamedGhostSyms.contains sym = true := List.contains_iff_mem.mpr hm
    rw [hc] at hnn; cases hnn
  dsimp only [cliNamedGhostSyms] at hnot_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot_mem
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hnot_mem
  exact ⟨beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2,
    beq_eq_false_iff_ne.mpr h3, beq_eq_false_iff_ne.mpr h4,
    beq_eq_false_iff_ne.mpr h5, beq_eq_false_iff_ne.mpr h6,
    beq_eq_false_iff_ne.mpr h7, beq_eq_false_iff_ne.mpr h8,
    beq_eq_false_iff_ne.mpr h9, beq_eq_false_iff_ne.mpr h10⟩

/-- Ghost-hook functions for the 5 bump-allocator symbols removed in F3 (`lsRustNoAllocShimSymCli`,
    `lsRustAllocSymCli`, `lsRustDeallocSymCli`, `lsRustReallocSymCli`, `lsRustAllocZeroedSymCli`),
    plus an optional ghost hook for `lsStringCloneSym` (when replaying Block `623` or
    `stringCloneHookMallocng` via `HookSat`) and optional `HookFsTraced IsFsC`-bundled ghost hooks
    for `lsReadFileSym` and `lsReadStdinSym` (replaying Blocks `618` / `620` via `GhostExternReplays`),
    plus optional ghost-hook slots `memset` and `memcpy` (default `none`; wired into
    `cliGhostExterns` dispatch in `#1255` Stage A / WP6c), and a generic `extra` association-list
    slot (default `[]`; `#1255` Cutover-2 extra ghost hooks). -/
structure CliGhostHooks where
  alloc : State → State
  dealloc : State → State
  realloc : State → State
  allocZeroed : State → State
  shim : State → State := hookNoop
  stringClone : Option (State → State) := none
  readFile : Option { f : State → State // HookFsTraced IsFsC f } := none
  readStdin : Option { f : State → State // HookFsTraced IsFsC f } := none
  memset : Option (State → State) := none
  memcpy : Option (State → State) := none
  extra : List (String × (State → State)) := []

/-- Pre-2B 10-way named-slot dispatch of `cliGhostExterns` (without `extra`). -/
def cliGhostExternsNamed (g : CliGhostHooks)
    (baseExt : String → Option (State → State)) (sym : String) :
    Option (State → State) :=
  if sym == lsRustAllocSymCli then some g.alloc
  else if sym == lsRustDeallocSymCli then some g.dealloc
  else if sym == lsRustReallocSymCli then some g.realloc
  else if sym == lsRustAllocZeroedSymCli then some g.allocZeroed
  else if sym == lsRustNoAllocShimSymCli then some g.shim
  else if sym == lsStringCloneSym then
    match g.stringClone with | some f => some f | none => baseExt sym
  else if sym == lsReadFileSym then
    match g.readFile with | some ⟨f, _⟩ => some f | none => baseExt sym
  else if sym == lsReadStdinSym then
    match g.readStdin with | some ⟨f, _⟩ => some f | none => baseExt sym
  else if sym == lsMemsetSym then
    match g.memset with | some f => some f | none => baseExt sym
  else if sym == lsMemcpySym then
    match g.memcpy with | some f => some f | none => baseExt sym
  else baseExt sym

/-- Full 10-named + domain-guarded `extra` extern dispatcher. -/
def cliGhostExternsWithExtra (g : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State)) (sym : String) :
    Option (State → State) :=
  if sym == lsRustAllocSymCli then some g.alloc
  else if sym == lsRustDeallocSymCli then some g.dealloc
  else if sym == lsRustReallocSymCli then some g.realloc
  else if sym == lsRustAllocZeroedSymCli then some g.allocZeroed
  else if sym == lsRustNoAllocShimSymCli then some g.shim
  else if sym == lsStringCloneSym then
    match g.stringClone with | some f => some f | none => baseExt sym
  else if sym == lsReadFileSym then
    match g.readFile with | some ⟨f, _⟩ => some f | none => baseExt sym
  else if sym == lsReadStdinSym then
    match g.readStdin with | some ⟨f, _⟩ => some f | none => baseExt sym
  else if sym == lsMemsetSym then
    match g.memset with | some f => some f | none => baseExt sym
  else if sym == lsMemcpySym then
    match g.memcpy with | some f => some f | none => baseExt sym
  else if cliExtraGhostSyms.contains sym then
    match extra.lookup sym with | some f => some f | none => baseExt sym
  else baseExt sym

@[simp] theorem cliGhostExternsWithExtra_extra_some (g : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State)) {sym : String} {f : State → State}
    (hLook : extra.lookup sym = some f)
    (hDom : cliExtraGhostSyms.contains sym = true := by decide) :
    cliGhostExternsWithExtra g extra baseExt sym = some f := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := named_eq_false_of_extra_contains hDom
  unfold cliGhostExternsWithExtra
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hDom, hLook, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExternsWithExtra_other (g : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State)) {sym : String}
    (h1 : sym ≠ lsRustAllocSymCli)
    (h2 : sym ≠ lsRustDeallocSymCli)
    (h3 : sym ≠ lsRustReallocSymCli)
    (h4 : sym ≠ lsRustAllocZeroedSymCli)
    (h5 : sym ≠ lsRustNoAllocShimSymCli)
    (h6 : sym ≠ lsStringCloneSym)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide)
    (h10 : sym ≠ lsMemcpySym := by decide)
    (hExtra : cliExtraGhostSyms.contains sym = false ∨ extra.lookup sym = none := by
      left; decide) :
    cliGhostExternsWithExtra g extra baseExt sym = baseExt sym := by
  unfold cliGhostExternsWithExtra
  simp only [beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2,
    beq_eq_false_iff_ne.mpr h3, beq_eq_false_iff_ne.mpr h4,
    beq_eq_false_iff_ne.mpr h5, beq_eq_false_iff_ne.mpr h6,
    beq_eq_false_iff_ne.mpr h7, beq_eq_false_iff_ne.mpr h8,
    beq_eq_false_iff_ne.mpr h9, beq_eq_false_iff_ne.mpr h10, Bool.false_eq_true, ↓reduceIte]
  rcases hExtra with hDomF | hLookN
  · simp only [hDomF, Bool.false_eq_true, ↓reduceIte]
  · cases hDom : cliExtraGhostSyms.contains sym
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte, hLookN]

/-- Overlays `g : CliGhostHooks` onto a base extern map `baseExt : LibsignalHooks`
    (10 named ghost slots + domain-guarded Cutover-2 `g.extra` table). -/
def cliGhostExterns (g : CliGhostHooks) (baseExt : LibsignalHooks) : LibsignalHooks :=
  cliGhostExternsWithExtra g g.extra baseExt

/-- Definitional bridge `cliGhostExterns g = cliGhostExternsWithExtra g g.extra`. -/
theorem cliGhostExterns_eq_withExtra (g : CliGhostHooks) :
    cliGhostExterns g = cliGhostExternsWithExtra g g.extra := rfl

@[simp] theorem cliGhostExterns_extra_some (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {sym : String} {f : State → State}
    (hLook : g.extra.lookup sym = some f)
    (hDom : cliExtraGhostSyms.contains sym = true := by decide) :
    cliGhostExterns g baseExt sym = some f :=
  cliGhostExternsWithExtra_extra_some g g.extra baseExt hLook hDom

@[simp] theorem cliGhostExterns_alloc (g : CliGhostHooks) (baseExt : LibsignalHooks) :
    cliGhostExterns g baseExt lsRustAllocSymCli = some g.alloc := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsRustAllocSymCli == lsRustAllocSymCli) = true := by decide
  simp only [h1, ↓reduceIte]

@[simp] theorem cliGhostExterns_dealloc (g : CliGhostHooks) (baseExt : LibsignalHooks) :
    cliGhostExterns g baseExt lsRustDeallocSymCli = some g.dealloc := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsRustDeallocSymCli == lsRustAllocSymCli) = false := by decide
  have h2 : (lsRustDeallocSymCli == lsRustDeallocSymCli) = true := by decide
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

@[simp] theorem cliGhostExterns_realloc (g : CliGhostHooks) (baseExt : LibsignalHooks) :
    cliGhostExterns g baseExt lsRustReallocSymCli = some g.realloc := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsRustReallocSymCli == lsRustAllocSymCli) = false := by decide
  have h2 : (lsRustReallocSymCli == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsRustReallocSymCli == lsRustReallocSymCli) = true := by decide
  simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]

@[simp] theorem cliGhostExterns_allocZeroed (g : CliGhostHooks) (baseExt : LibsignalHooks) :
    cliGhostExterns g baseExt lsRustAllocZeroedSymCli = some g.allocZeroed := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsRustAllocZeroedSymCli == lsRustAllocSymCli) = false := by decide
  have h2 : (lsRustAllocZeroedSymCli == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsRustAllocZeroedSymCli == lsRustReallocSymCli) = false := by decide
  have h4 : (lsRustAllocZeroedSymCli == lsRustAllocZeroedSymCli) = true := by decide
  simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]

@[simp] theorem cliGhostExterns_shim (g : CliGhostHooks) (baseExt : LibsignalHooks) :
    cliGhostExterns g baseExt lsRustNoAllocShimSymCli = some g.shim := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsRustNoAllocShimSymCli == lsRustAllocSymCli) = false := by decide
  have h2 : (lsRustNoAllocShimSymCli == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsRustNoAllocShimSymCli == lsRustReallocSymCli) = false := by decide
  have h4 : (lsRustNoAllocShimSymCli == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : (lsRustNoAllocShimSymCli == lsRustNoAllocShimSymCli) = true := by decide
  simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExterns_stringClone_some (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {f : State → State} (hf : g.stringClone = some f) :
    cliGhostExterns g baseExt lsStringCloneSym = some f := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsStringCloneSym == lsRustAllocSymCli) = false := by decide
  have h2 : (lsStringCloneSym == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsStringCloneSym == lsRustReallocSymCli) = false := by decide
  have h4 : (lsStringCloneSym == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : (lsStringCloneSym == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : (lsStringCloneSym == lsStringCloneSym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, hf, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExterns_stringClone_none (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hf : g.stringClone = none) :
    cliGhostExterns g baseExt lsStringCloneSym = baseExt lsStringCloneSym := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsStringCloneSym == lsRustAllocSymCli) = false := by decide
  have h2 : (lsStringCloneSym == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsStringCloneSym == lsRustReallocSymCli) = false := by decide
  have h4 : (lsStringCloneSym == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : (lsStringCloneSym == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : (lsStringCloneSym == lsStringCloneSym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, hf, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExterns_readFile_some (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {f : State → State} {hfsT : HookFsTraced IsFsC f} (hf : g.readFile = some ⟨f, hfsT⟩) :
    cliGhostExterns g baseExt lsReadFileSym = some f := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsReadFileSym == lsRustAllocSymCli) = false := by decide
  have h2 : (lsReadFileSym == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsReadFileSym == lsRustReallocSymCli) = false := by decide
  have h4 : (lsReadFileSym == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : (lsReadFileSym == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : (lsReadFileSym == lsStringCloneSym) = false := by decide
  have h7 : (lsReadFileSym == lsReadFileSym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, h7, hf, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExterns_readFile_none (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hf : g.readFile = none) :
    cliGhostExterns g baseExt lsReadFileSym = baseExt lsReadFileSym := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsReadFileSym == lsRustAllocSymCli) = false := by decide
  have h2 : (lsReadFileSym == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsReadFileSym == lsRustReallocSymCli) = false := by decide
  have h4 : (lsReadFileSym == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : (lsReadFileSym == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : (lsReadFileSym == lsStringCloneSym) = false := by decide
  have h7 : (lsReadFileSym == lsReadFileSym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, h7, hf, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExterns_readStdin_some (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {f : State → State} {hfsT : HookFsTraced IsFsC f} (hf : g.readStdin = some ⟨f, hfsT⟩) :
    cliGhostExterns g baseExt lsReadStdinSym = some f := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsReadStdinSym == lsRustAllocSymCli) = false := by decide
  have h2 : (lsReadStdinSym == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsReadStdinSym == lsRustReallocSymCli) = false := by decide
  have h4 : (lsReadStdinSym == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : (lsReadStdinSym == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : (lsReadStdinSym == lsStringCloneSym) = false := by decide
  have h7 : (lsReadStdinSym == lsReadFileSym) = false := by decide
  have h8 : (lsReadStdinSym == lsReadStdinSym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, hf, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExterns_readStdin_none (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hf : g.readStdin = none) :
    cliGhostExterns g baseExt lsReadStdinSym = baseExt lsReadStdinSym := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsReadStdinSym == lsRustAllocSymCli) = false := by decide
  have h2 : (lsReadStdinSym == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsReadStdinSym == lsRustReallocSymCli) = false := by decide
  have h4 : (lsReadStdinSym == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : (lsReadStdinSym == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : (lsReadStdinSym == lsStringCloneSym) = false := by decide
  have h7 : (lsReadStdinSym == lsReadFileSym) = false := by decide
  have h8 : (lsReadStdinSym == lsReadStdinSym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, hf, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExterns_memset_some (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {f : State → State} (hf : g.memset = some f) :
    cliGhostExterns g baseExt lsMemsetSym = some f := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsMemsetSym == lsRustAllocSymCli) = false := by decide
  have h2 : (lsMemsetSym == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsMemsetSym == lsRustReallocSymCli) = false := by decide
  have h4 : (lsMemsetSym == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : (lsMemsetSym == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : (lsMemsetSym == lsStringCloneSym) = false := by decide
  have h7 : (lsMemsetSym == lsReadFileSym) = false := by decide
  have h8 : (lsMemsetSym == lsReadStdinSym) = false := by decide
  have h9 : (lsMemsetSym == lsMemsetSym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hf, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExterns_memset_none (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hf : g.memset = none) :
    cliGhostExterns g baseExt lsMemsetSym = baseExt lsMemsetSym := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsMemsetSym == lsRustAllocSymCli) = false := by decide
  have h2 : (lsMemsetSym == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsMemsetSym == lsRustReallocSymCli) = false := by decide
  have h4 : (lsMemsetSym == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : (lsMemsetSym == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : (lsMemsetSym == lsStringCloneSym) = false := by decide
  have h7 : (lsMemsetSym == lsReadFileSym) = false := by decide
  have h8 : (lsMemsetSym == lsReadStdinSym) = false := by decide
  have h9 : (lsMemsetSym == lsMemsetSym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hf, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExterns_memcpy_some (g : CliGhostHooks) (baseExt : LibsignalHooks)
    {f : State → State} (hf : g.memcpy = some f) :
    cliGhostExterns g baseExt lsMemcpySym = some f := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsMemcpySym == lsRustAllocSymCli) = false := by decide
  have h2 : (lsMemcpySym == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsMemcpySym == lsRustReallocSymCli) = false := by decide
  have h4 : (lsMemcpySym == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : (lsMemcpySym == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : (lsMemcpySym == lsStringCloneSym) = false := by decide
  have h7 : (lsMemcpySym == lsReadFileSym) = false := by decide
  have h8 : (lsMemcpySym == lsReadStdinSym) = false := by decide
  have h9 : (lsMemcpySym == lsMemsetSym) = false := by decide
  have h10 : (lsMemcpySym == lsMemcpySym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hf, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExterns_memcpy_none (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (hf : g.memcpy = none) :
    cliGhostExterns g baseExt lsMemcpySym = baseExt lsMemcpySym := by
  unfold cliGhostExterns cliGhostExternsWithExtra
  have h1 : (lsMemcpySym == lsRustAllocSymCli) = false := by decide
  have h2 : (lsMemcpySym == lsRustDeallocSymCli) = false := by decide
  have h3 : (lsMemcpySym == lsRustReallocSymCli) = false := by decide
  have h4 : (lsMemcpySym == lsRustAllocZeroedSymCli) = false := by decide
  have h5 : (lsMemcpySym == lsRustNoAllocShimSymCli) = false := by decide
  have h6 : (lsMemcpySym == lsStringCloneSym) = false := by decide
  have h7 : (lsMemcpySym == lsReadFileSym) = false := by decide
  have h8 : (lsMemcpySym == lsReadStdinSym) = false := by decide
  have h9 : (lsMemcpySym == lsMemsetSym) = false := by decide
  have h10 : (lsMemcpySym == lsMemcpySym) = true := by decide
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hf, Bool.false_eq_true, ↓reduceIte]

theorem cliGhostExterns_other (g : CliGhostHooks) (baseExt : LibsignalHooks) {sym : String}
    (h1 : sym ≠ lsRustAllocSymCli)
    (h2 : sym ≠ lsRustDeallocSymCli)
    (h3 : sym ≠ lsRustReallocSymCli)
    (h4 : sym ≠ lsRustAllocZeroedSymCli)
    (h5 : sym ≠ lsRustNoAllocShimSymCli)
    (h6 : sym ≠ lsStringCloneSym)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide)
    (h10 : sym ≠ lsMemcpySym := by decide)
    (hExtra : cliExtraGhostSyms.contains sym = false ∨ g.extra.lookup sym = none := by
      left; decide) :
    cliGhostExterns g baseExt sym = baseExt sym :=
  cliGhostExternsWithExtra_other g g.extra baseExt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hExtra

/-- `ext`-parametric `lsReadFileSym` hook overlay (`rfl`-equal to
    `ReadFileBudgetPlaced.withReadFileHook`). -/
def withReadFileHook (rfh : State → State) (ext : LibsignalHooks) : LibsignalHooks :=
  fun s => if s == lsReadFileSym then some rfh else ext s

/-- `ext`-parametric `lsReadStdinSym` hook overlay. -/
def withReadStdinHook (rsh : State → State) (ext : LibsignalHooks) : LibsignalHooks :=
  fun s => if s == lsReadStdinSym then some rsh else ext s

theorem withReadFileHook_cliGhostExterns (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (rfh : State → State) (hrfh : HookFsTraced IsFsC rfh) :
    withReadFileHook rfh (cliGhostExterns g baseExt) =
      cliGhostExterns { g with readFile := some ⟨rfh, hrfh⟩ } baseExt := by
  funext sym
  by_cases hrf : sym = lsReadFileSym
  · subst hrf
    have hself : (lsReadFileSym == lsReadFileSym) = true := by decide
    simp only [withReadFileHook, hself, ↓reduceIte]
    exact (cliGhostExterns_readFile_some _ baseExt rfl).symm
  · have hrf_b : (sym == lsReadFileSym) = false := beq_eq_false_iff_ne.mpr hrf
    simp only [withReadFileHook, hrf_b, Bool.false_eq_true, ↓reduceIte]
    unfold cliGhostExterns cliGhostExternsWithExtra
    simp only [hrf_b, Bool.false_eq_true, ↓reduceIte]

theorem withReadStdinHook_cliGhostExterns (g : CliGhostHooks) (baseExt : LibsignalHooks)
    (rsh : State → State) (hrsh : HookFsTraced IsFsC rsh) :
    withReadStdinHook rsh (cliGhostExterns g baseExt) =
      cliGhostExterns { g with readStdin := some ⟨rsh, hrsh⟩ } baseExt := by
  funext sym
  by_cases hrs : sym = lsReadStdinSym
  · subst hrs
    have hself : (lsReadStdinSym == lsReadStdinSym) = true := by decide
    simp only [withReadStdinHook, hself, ↓reduceIte]
    exact (cliGhostExterns_readStdin_some _ baseExt rfl).symm
  · have hrs_b : (sym == lsReadStdinSym) = false := beq_eq_false_iff_ne.mpr hrs
    simp only [withReadStdinHook, hrs_b, Bool.false_eq_true, ↓reduceIte]
    unfold cliGhostExterns cliGhostExternsWithExtra
    simp only [hrs_b, Bool.false_eq_true, ↓reduceIte]

theorem withReadStdinHook_withReadFileHook_cliGhostExterns (g : CliGhostHooks)
    (baseExt : LibsignalHooks) (rfh : State → State) (hrfh : HookFsTraced IsFsC rfh)
    (rsh : State → State) (hrsh : HookFsTraced IsFsC rsh) :
    withReadStdinHook rsh (withReadFileHook rfh (cliGhostExterns g baseExt)) =
      cliGhostExterns { g with readFile := some ⟨rfh, hrfh⟩, readStdin := some ⟨rsh, hrsh⟩ }
        baseExt := by
  rw [withReadFileHook_cliGhostExterns g baseExt rfh hrfh,
    withReadStdinHook_cliGhostExterns _ baseExt rsh hrsh]

theorem hookSat_of_eq {α : Type} {H₁ H₂ : String → Option (State → State)}
    {sym : String} {spec : Spec α}
    (heq : H₁ sym = H₂ sym) (h : HookSat H₂ sym spec) : HookSat H₁ sym spec := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, heq.trans hf, hok⟩

private theorem extra_isPanicSymbol_false :
    (cliExtraGhostSyms.all fun s => !(Rust.isPanicSymbol s)) = true := by
  rw [List.all_eq_true]
  intro s hs
  simp only [cliExtraGhostSyms, lsMemrchrSym, lsFromUtf8Sym, lsDurationSinceSym, lsTimeAddSym,
    lsBlackBoxSym, lsStaticSecretDropSym, lsSharedSecretDropSym,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Rust.isPanicSymbol]

theorem cliGhostExterns_panic_of_mem (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {n : String} (hn : n ∈ cliPanicSymbolsPlaced) :
    cliGhostExterns g (cliExternsPlaced mmpl W) n = some Rust.panicked := by
  have h1 : n ≠ lsRustAllocSymCli := by intro he; subst he; exact nomatch hn
  have h2 : n ≠ lsRustDeallocSymCli := by intro he; subst he; exact nomatch hn
  have h3 : n ≠ lsRustReallocSymCli := by intro he; subst he; exact nomatch hn
  have h4 : n ≠ lsRustAllocZeroedSymCli := by intro he; subst he; exact nomatch hn
  have h5 : n ≠ lsRustNoAllocShimSymCli := by intro he; subst he; exact nomatch hn
  have h6 : n ≠ lsStringCloneSym := by intro he; subst he; exact nomatch hn
  have h7 : n ≠ lsReadFileSym := by intro he; subst he; exact nomatch hn
  have h8 : n ≠ lsReadStdinSym := by intro he; subst he; exact nomatch hn
  have h9 : n ≠ lsMemsetSym := by intro he; subst he; exact nomatch hn
  have h10 : n ≠ lsMemcpySym := by intro he; subst he; exact nomatch hn
  have hExtra : cliExtraGhostSyms.contains n = false := by
    cases hc : cliExtraGhostSyms.contains n
    · rfl
    · have hm := List.contains_iff_mem.mp hc
      dsimp only [cliExtraGhostSyms] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact nomatch hn
  rw [cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (Or.inl hExtra)]
  exact cliExternsPlaced_panic_of_mem mmpl W hn

@[simp]
theorem withPanics_cliGhostExterns (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks) :
    Rust.withPanics (cliGhostExterns g (cliExternsPlaced mmpl W)) =
      cliGhostExterns g (cliExternsPlaced mmpl W) := by
  funext n
  by_cases hp : Rust.isPanicSymbol n = true
  · have h1 : n ≠ lsRustAllocSymCli := by
      intro he; subst he
      have hf : Rust.isPanicSymbol lsRustAllocSymCli = false := by simp [lsRustAllocSymCli, Rust.isPanicSymbol]
      exact Bool.false_ne_true (hf.symm.trans hp)
    have h2 : n ≠ lsRustDeallocSymCli := by
      intro he; subst he
      have hf : Rust.isPanicSymbol lsRustDeallocSymCli = false := by simp [lsRustDeallocSymCli, Rust.isPanicSymbol]
      exact Bool.false_ne_true (hf.symm.trans hp)
    have h3 : n ≠ lsRustReallocSymCli := by
      intro he; subst he
      have hf : Rust.isPanicSymbol lsRustReallocSymCli = false := by simp [lsRustReallocSymCli, Rust.isPanicSymbol]
      exact Bool.false_ne_true (hf.symm.trans hp)
    have h4 : n ≠ lsRustAllocZeroedSymCli := by
      intro he; subst he
      have hf : Rust.isPanicSymbol lsRustAllocZeroedSymCli = false := by simp [lsRustAllocZeroedSymCli, Rust.isPanicSymbol]
      exact Bool.false_ne_true (hf.symm.trans hp)
    have h5 : n ≠ lsRustNoAllocShimSymCli := by
      intro he; subst he
      have hf : Rust.isPanicSymbol lsRustNoAllocShimSymCli = false := by simp [lsRustNoAllocShimSymCli, Rust.isPanicSymbol]
      exact Bool.false_ne_true (hf.symm.trans hp)
    have h6 : n ≠ lsStringCloneSym := by
      intro he; subst he
      have hf : Rust.isPanicSymbol lsStringCloneSym = false := by simp [lsStringCloneSym, Rust.isPanicSymbol]
      exact Bool.false_ne_true (hf.symm.trans hp)
    have h7 : n ≠ lsReadFileSym := by
      intro he; subst he
      have hf : Rust.isPanicSymbol lsReadFileSym = false := by simp [lsReadFileSym, Rust.isPanicSymbol]
      exact Bool.false_ne_true (hf.symm.trans hp)
    have h8 : n ≠ lsReadStdinSym := by
      intro he; subst he
      have hf : Rust.isPanicSymbol lsReadStdinSym = false := by simp [lsReadStdinSym, Rust.isPanicSymbol]
      exact Bool.false_ne_true (hf.symm.trans hp)
    have h9 : n ≠ lsMemsetSym := by
      intro he; subst he
      have hf : Rust.isPanicSymbol lsMemsetSym = false := by simp [lsMemsetSym, Rust.isPanicSymbol]
      exact Bool.false_ne_true (hf.symm.trans hp)
    have h10 : n ≠ lsMemcpySym := by
      intro he; subst he
      have hf : Rust.isPanicSymbol lsMemcpySym = false := by simp [lsMemcpySym, Rust.isPanicSymbol]
      exact Bool.false_ne_true (hf.symm.trans hp)
    have hExtra : cliExtraGhostSyms.contains n = false := by
      cases hc : cliExtraGhostSyms.contains n
      · rfl
      · have hall := List.all_eq_true.mp extra_isPanicSymbol_false n (List.contains_iff_mem.mp hc)
        rw [hp] at hall; cases hall
    unfold Rust.withPanics
    simp only [hp, ↓reduceIte]
    rw [cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (Or.inl hExtra)]
    unfold cliExternsPlaced isCliPanicSymbolPlaced
    simp [hp]
  · simp [Rust.withPanics, hp]

end CryptoVerification.SignalSession.Cli.RunGlue

namespace CryptoVerification.SignalSession.Cli
export RunGlue (CliGhostHooks cliGhostExterns withReadFileHook withReadStdinHook
  withReadFileHook_cliGhostExterns withReadStdinHook_cliGhostExterns
  withReadStdinHook_withReadFileHook_cliGhostExterns)
end CryptoVerification.SignalSession.Cli
