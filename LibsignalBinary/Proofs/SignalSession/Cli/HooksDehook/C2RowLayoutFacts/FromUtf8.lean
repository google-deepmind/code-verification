/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Generic & Cutover-2 (`C2`) `Placeable`, `GhostRowSpecOk`, `RoDataAt`, & Entry-Guard Glue for `core::str::converts::from_utf8` (`C2RowLayoutFacts.FromUtf8`)

**Checked by Lean. Untrusted (`Role::Proof`).**

Discharges GK6c §19(d) item 1 (`hpl : fromUtf8Block.Placeable (fromUtf8MplPlacement mpl c2FromUtf8TableAddr relax1)`
for `FromUtf8GhostReplays.fromUtf8Ghost_rowSpecOk`, `fromUtf8MplGhost_rowSpecOk`,
`fromUtf8MplGhost_rowReplayOn`, and `fromUtf8MplGhost_rowOk`) plus the per-row `.rodata`
(`UTF8_CHAR_WIDTH`) and `.text.lib2` hull / startup-`lr` entry-guard obligations with zero hex
literals:

1. **Generic $O(1)$ `Placeable` check (`checkFromUtf8Placeable`, `fromUtf8Block_placeable_of_check`,
   `fromUtf8Block_placeable_of_check_allRelax`):** proves `fromUtf8Block.Placeable (fromUtf8Placement fnBase tbl relax1)`
   from 4-byte alignment, 64-bit no-wrap, and `ADRP`/`ADR` range without unfolding `fromUtf8Block.code`
   at consumer call sites. When `tbl` lies within `±1 MiB` of `fnBase + 24`, `Placeable` holds
   simultaneously for **every** linker relaxation predicate `relax1 : Nat → Bool` (including the
   default `fun _ => false` matching the unrelaxed `ADRP + ADD` pair in C2 ELF `50066cbd`).
2. **Concrete C2 `Placeable` & polymorphic-`[LibsignalPlacement]` `GhostRowSpecOk` instances
   (`c2_fromUtf8Block_placeable`, `c2_fromUtf8Block_placeable_unrelaxed`,
   `c2_fromUtf8Ghost_rowSpecOk`, `c2_fromUtf8MplGhost_rowSpecOk`,
   `c2_fromUtf8MplGhost_rowSpecOk_unrelaxed`):** tied to `hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl`
   with explicit `hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr`,
   discharging `Placeable`, `relax1`, and `c2FromUtf8TableAddr`.
3. **C2 `.rodata` (`UTF8_CHAR_WIDTH`) & `.text.lib2` hull / `fromUtf8EntryGuard` helpers
   (`c2CorePlacedData1_eq_corePlacedData1`, `f3CodeInv_roDataAt_coreUtf8Table`,
   `c2_fromUtf8_hRo_of_f3CodeInv`, `keepR_fromUtf8Mpl_sub_keepLib2Text`,
   `f3FromUtf8EntryGuard_of_startupLr`, `c2FromUtf8EntryGuard_of_resolve`):** ready for direct
   assembly into `c2_fromUtf8Ghost_rowOk`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8

open Arm64 Arm64.Obj ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib lsFromUtf8Sym)
open VerifiedLibraries.RustStd (coreFromUtf8Sym corePlacedData1 coreUtf8CharWidthSym)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FromUtf8RowSpec
  (FromUtf8RowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (GhostRowSpecOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock
  (fromUtf8Block fromUtf8Block_code_length fromUtf8Placement)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Ghost (keepFromUtf8Block)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8LrTrap (keepFromUtf8Block_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays
  (fromUtf8EntryGuard fromUtf8EntryGuard_iff fromUtf8Ghost fromUtf8Ghost_fromUtf8RowSpec
   fromUtf8Ghost_rowSpecOk fromUtf8MplGhost fromUtf8MplGhost_rowSpecOk fromUtf8MplPlacement
   keepR_fromUtf8Mpl)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts C2RoSliceFacts c2CorePlacedData1 f3CodeInv_roDataAt_fromUtf8Table
   f3Lib2EntryGuard_of_startupLr f3Lib2_dehookedSym_in_keepLib2Text f3StartupLrVal keepLib2Text)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FromUtf8Addr c2FromUtf8TableAddr c2Lib2DehookedSyms c2Lib2TextHi c2Lib2TextLo)

/-! ## 1. Constant Structural Facts on `fromUtf8Block` -/

private theorem fromUtf8Block_align_eq : fromUtf8Block.align = 4 := by
  decide +kernel

private theorem fromUtf8Block_symbols_eq :
    fromUtf8Block.symbols = [(coreFromUtf8Sym, 0)] := by
  decide +kernel

private def fromUtf8Reloc0 : RelocEntry :=
  { off := 20, kind := .adrpHi21, sym := coreUtf8CharWidthSym, addend := 0 }

private def fromUtf8Reloc1 : RelocEntry :=
  { off := 24, kind := .addLo12, sym := coreUtf8CharWidthSym, addend := 0 }

private theorem fromUtf8Block_relocs_eq :
    fromUtf8Block.relocs = [fromUtf8Reloc0, fromUtf8Reloc1] := by
  decide +kernel

private theorem lookup_table_symbols_none :
    Obj.lookup coreUtf8CharWidthSym [(coreFromUtf8Sym, (0 : Nat))] = none := by
  decide +kernel

private theorem fromUtf8Block_externs_check :
    (fromUtf8Block.externs.all fun e =>
      (Obj.lookup e fromUtf8Block.symbols).isNone && !(e == coreUtf8CharWidthSym)) = true := by
  decide +kernel

private theorem fromUtf8Block_resolve_table (fnBase tbl : BitVec 64) (relax1 : Nat → Bool) :
    fromUtf8Block.resolve (fromUtf8Placement fnBase tbl relax1) coreUtf8CharWidthSym = tbl := by
  unfold CodeBlock.resolve
  rw [fromUtf8Block_symbols_eq, lookup_table_symbols_none]
  simp [fromUtf8Placement]

private theorem fromUtf8Block_relocAt?_some_iff {off : Nat} {r : RelocEntry} :
    fromUtf8Block.relocAt? off = some r ↔
      (off = 20 ∧ r = fromUtf8Reloc0) ∨ (off = 24 ∧ r = fromUtf8Reloc1) := by
  unfold CodeBlock.relocAt?
  rw [fromUtf8Block_relocs_eq]
  simp only [List.find?_cons, List.find?_nil, fromUtf8Reloc0, fromUtf8Reloc1]
  by_cases h20 : off = 20
  · subst h20
    simp [eq_comm]
  · have h20f : (20 == off) = false := beq_false_of_ne (Ne.symm h20)
    rw [h20f]
    by_cases h24 : off = 24
    · subst h24
      simp [eq_comm]
    · have h24f : (24 == off) = false := beq_false_of_ne (Ne.symm h24)
      rw [h24f]
      simp [h20, h24]

/-! ## 2. Generic Address-Free $O(1)$ Decidable `Placeable` Check & Soundness -/

/-- Pure $O(1)$ decidable side condition for `fromUtf8Block.Placeable (fromUtf8Placement fnBase tbl relax1)`:
    - `fnBase` is 4-byte aligned and `[fnBase, fnBase + 624)` does not wrap `2 ^ 64`;
    - `tbl` is within `ADRP` range (`±4 GiB` page offset) of `fnBase + 20`;
    - when `relax20 = true` (`ADRP + ADD` at `+20/+24` relaxed to `NOP + ADR`), `tbl` is also
      within `ADR` range (`±1 MiB`) of `fnBase + 24`. -/
@[expose] def checkFromUtf8Placeable (fnBase tbl : BitVec 64)
    (relax20 : Bool := false) : Bool :=
  Nat.beq (fnBase.toNat % 4) 0 &&
  Nat.ble (fnBase.toNat + 624) (2 ^ 64) &&
  Interned.sInRange (-4294967296) 4294967296
    (pageOf tbl - pageOf (fnBase + BitVec.ofNat 64 20)) &&
  (!relax20 ||
    Interned.sInRange (-1048576) 1048576 (tbl - (fnBase + BitVec.ofNat 64 24)))

/-- Generic soundness of `checkFromUtf8Placeable`: for any `(fnBase, tbl, relax1)` satisfying
    `checkFromUtf8Placeable fnBase tbl (relax1 20) = true`, `fromUtf8Block` is `Placeable` at
    `fromUtf8Placement fnBase tbl relax1`. -/
theorem fromUtf8Block_placeable_of_check {fnBase tbl : BitVec 64}
    {relax1 : Nat → Bool}
    (h : checkFromUtf8Placeable fnBase tbl (relax1 20) = true) :
    fromUtf8Block.Placeable (fromUtf8Placement fnBase tbl relax1) := by
  unfold checkFromUtf8Placeable at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨halign, hnowrap⟩, hadrp⟩, hadr_or⟩
  refine
    { align_pos := by rw [fromUtf8Block_align_eq]; decide
      base_aligned := by rw [fromUtf8Block_align_eq]; exact halign
      no_wrap := by rw [fromUtf8Block_code_length]; exact hnowrap
      len_aligned := by rw [fromUtf8Block_code_length]
      relocs_nodup := by
        rw [fromUtf8Block_relocs_eq]
        decide
      relocs_ok := ?_
      relaxed_ok := ?_
      symbols_ok := ?_
      externs_ok := ?_ }
  · intro r hr
    rw [fromUtf8Block_relocs_eq, List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · refine ⟨by decide, by rw [fromUtf8Block_code_length]; decide, ?_⟩
      have htgt :
          fromUtf8Block.relocTarget (fromUtf8Placement fnBase tbl relax1) 20 fromUtf8Reloc0 = tbl := by
        change addSignedAddr
          (fromUtf8Block.resolve (fromUtf8Placement fnBase tbl relax1) coreUtf8CharWidthSym) 0 = tbl
        rw [fromUtf8Block_resolve_table]
        rfl
      change AdrpInRange (fnBase + BitVec.ofNat 64 20)
        (fromUtf8Block.relocTarget (fromUtf8Placement fnBase tbl relax1) 20 fromUtf8Reloc0)
      rw [htgt]
      exact Interned.codeRelocInRange_of (kind := .adrpHi21) hadrp
    · refine ⟨by decide, by rw [fromUtf8Block_code_length]; decide, ?_⟩
      trivial
  · intro off r hrx hrel4
    unfold CodeBlock.relaxedAt at hrx
    rw [Bool.and_eq_true] at hrx
    rcases hrx with ⟨hrelaxable, hpl_relax⟩
    have hrel0_ex : ∃ r0, fromUtf8Block.relocAt? off = some r0 := by
      unfold CodeBlock.relaxableAt at hrelaxable
      rcases h0 : fromUtf8Block.relocAt? off with _ | r0
      · simp [h0] at hrelaxable
      · exact ⟨r0, rfl⟩
    rcases hrel0_ex with ⟨r0, hrel0⟩
    have h0_cases := (fromUtf8Block_relocAt?_some_iff.mp hrel0)
    have h4_cases := (fromUtf8Block_relocAt?_some_iff.mp hrel4)
    have hoff20 : off = 20 ∧ r = fromUtf8Reloc1 := by
      rcases h0_cases with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
        rcases h4_cases with ⟨h4, hr⟩ | ⟨h4, hr⟩ <;>
        first | exact ⟨rfl, hr⟩ | omega
    rcases hoff20 with ⟨rfl, rfl⟩
    have hrel1_true : relax1 20 = true := hpl_relax
    rcases hadr_or with hrel1_false | hadr
    · cases hrel1_false.symm.trans hrel1_true
    · have htgt :
          fromUtf8Block.target (fromUtf8Placement fnBase tbl relax1) fromUtf8Reloc1 = tbl := by
        change addSignedAddr
          (fromUtf8Block.resolve (fromUtf8Placement fnBase tbl relax1) coreUtf8CharWidthSym) 0 = tbl
        rw [fromUtf8Block_resolve_table]
        rfl
      change AdrInRange (fnBase + BitVec.ofNat 64 24)
        (fromUtf8Block.target (fromUtf8Placement fnBase tbl relax1) fromUtf8Reloc1)
      rw [htgt]
      exact Interned.adrInRange_of hadr
  · intro s hs
    rw [fromUtf8Block_symbols_eq, List.mem_singleton] at hs
    subst hs
    rw [fromUtf8Block_code_length]
    decide
  · intro e he
    have hall := List.all_eq_true.mp fromUtf8Block_externs_check e he
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hall
    refine ⟨hall.1, ?_⟩
    rw [fromUtf8Block_code_length]
    have hρ : (fromUtf8Placement fnBase tbl relax1).ρ e = fnBase + BitVec.ofNat 64 4096 := by
      change (if e == coreUtf8CharWidthSym then tbl else fnBase + BitVec.ofNat 64 4096) =
        fnBase + BitVec.ofNat 64 4096
      rw [hall.2]
      rfl
    have hbase : (fromUtf8Placement fnBase tbl relax1).base = fnBase := rfl
    have hsub : (fnBase + BitVec.ofNat 64 4096) - fnBase = BitVec.ofNat 64 4096 := by
      bv_omega
    rw [hρ, hbase, hsub]
    decide

/-- When `checkFromUtf8Placeable fnBase tbl true = true` (`tbl` within `±1 MiB` of `fnBase + 24`),
    `fromUtf8Block.Placeable (fromUtf8Placement fnBase tbl relax1)` holds universally for **every**
    linker relaxation predicate `relax1 : Nat → Bool` (including default `fun _ => false`). -/
theorem fromUtf8Block_placeable_of_check_allRelax {fnBase tbl : BitVec 64}
    (h : checkFromUtf8Placeable fnBase tbl true = true)
    (relax1 : Nat → Bool := fun _ => false) :
    fromUtf8Block.Placeable (fromUtf8Placement fnBase tbl relax1) := by
  apply fromUtf8Block_placeable_of_check
  unfold checkFromUtf8Placeable at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.false_or] at h ⊢
  exact ⟨h.1, Or.inr h.2⟩

/-- Unrelaxed (`relax1 = fun _ => false`) specialization requiring only `±4 GiB` `ADRP` range. -/
theorem fromUtf8Block_placeable_unrelaxed_of_check {fnBase tbl : BitVec 64}
    (h : checkFromUtf8Placeable fnBase tbl false = true) :
    fromUtf8Block.Placeable (fromUtf8Placement fnBase tbl) :=
  fromUtf8Block_placeable_of_check (relax1 := fun _ => false) h

/-- `MultiPlacedLib.resolve`-indexed bridge: reduces `fromUtf8Placement (lib.resolve mpl sym) tbl relax1`
    to `checkFromUtf8Placeable fnBase tbl true = true` along `lib.resolve mpl sym = fnBase`. -/
theorem fromUtf8Block_placeable_of_resolve_eq
    (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (sym : String)
    {fnBase tbl : BitVec 64}
    (hRes : lib.resolve mpl sym = fnBase)
    (h : checkFromUtf8Placeable fnBase tbl true = true)
    (relax1 : Nat → Bool := fun _ => false) :
    fromUtf8Block.Placeable (fromUtf8Placement (lib.resolve mpl sym) tbl relax1) := by
  rw [hRes]
  exact fromUtf8Block_placeable_of_check_allRelax h relax1

/-- Direct wrapper around engine `CodeBlock.checkPlaceable` for `fromUtf8Placement`. -/
theorem fromUtf8Block_placeable_of_checkPlaceable {fnBase tbl : BitVec 64}
    {relax1 : Nat → Bool}
    (h : fromUtf8Block.checkPlaceable (fromUtf8Placement fnBase tbl relax1) = true) :
    fromUtf8Block.Placeable (fromUtf8Placement fnBase tbl relax1) :=
  CodeBlock.placeable_of_checkPlaceable h

/-! ## 3. Concrete Cutover-2 (`C2`) `Placeable` & `GhostRowSpecOk` Discharges -/

theorem c2_checkFromUtf8Placeable_ok :
    checkFromUtf8Placeable c2FromUtf8Addr c2FromUtf8TableAddr true = true := by
  decide +kernel

/-- Concrete C2 `Placeable` at `(c2FromUtf8Addr, c2FromUtf8TableAddr)` for any `relax1`. -/
theorem c2_fromUtf8Block_placeable_at_c2Addr {relax1 : Nat → Bool} :
    fromUtf8Block.Placeable (fromUtf8Placement c2FromUtf8Addr c2FromUtf8TableAddr relax1) :=
  fromUtf8Block_placeable_of_check_allRelax c2_checkFromUtf8Placeable_ok relax1

/-- **Primary C2 `Placeable` discharge (`GK §19(d)` item 1):** for `mpl` tied to
    `libsignalSessionLib.LinkedAt cliElfBytes mpl` resolving `lsFromUtf8Sym` to `c2FromUtf8Addr`
    (`C2ResolveFacts` premise) and any `relax1 : Nat → Bool` (including the default
    `fun _ => false`), `fromUtf8Block` is `Placeable` at
    `fromUtf8MplPlacement mpl c2FromUtf8TableAddr relax1`. -/
theorem c2_fromUtf8Block_placeable
    {mpl : Obj.MultiPlacement} {relax1 : Nat → Bool}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr) :
    fromUtf8Block.Placeable (fromUtf8MplPlacement mpl c2FromUtf8TableAddr relax1) := by
  let _ := hLs
  unfold fromUtf8MplPlacement
  exact fromUtf8Block_placeable_of_resolve_eq libsignalSessionLib mpl lsFromUtf8Sym
    hRes c2_checkFromUtf8Placeable_ok relax1

/-- Default-`relax1` (`fun _ => false`) spelling of `c2_fromUtf8Block_placeable`. -/
theorem c2_fromUtf8Block_placeable_unrelaxed
    {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr) :
    fromUtf8Block.Placeable (fromUtf8MplPlacement mpl c2FromUtf8TableAddr) :=
  c2_fromUtf8Block_placeable hLs hRes

/-- `FromUtf8RowSpec` at the C2 placement under `LinkedAt cliElfBytes mpl` + `hRes`. -/
theorem c2_fromUtf8Ghost_fromUtf8RowSpec
    {mpl : Obj.MultiPlacement} {relax1 : Nat → Bool}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr) :
    FromUtf8RowSpec (fromUtf8Ghost (fromUtf8MplPlacement mpl c2FromUtf8TableAddr relax1)) :=
  fromUtf8Ghost_fromUtf8RowSpec (c2_fromUtf8Block_placeable hLs hRes)

/-- Polymorphic-`[LibsignalPlacement]` `GhostRowSpecOk` for `fromUtf8Ghost` at C2. -/
theorem c2_fromUtf8Ghost_rowSpecOk [LibsignalPlacement]
    {mpl : Obj.MultiPlacement} {relax1 : Nat → Bool}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr) :
    GhostRowSpecOk lsFromUtf8Sym
      (fromUtf8Ghost (fromUtf8MplPlacement mpl c2FromUtf8TableAddr relax1)) :=
  fromUtf8Ghost_rowSpecOk (c2_fromUtf8Block_placeable hLs hRes)

/-- Polymorphic-`[LibsignalPlacement]` `GhostRowSpecOk` for `fromUtf8MplGhost` at C2. -/
theorem c2_fromUtf8MplGhost_rowSpecOk [LibsignalPlacement]
    {mpl mmpl : Obj.MultiPlacement} {relax1 : Nat → Bool}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr) :
    GhostRowSpecOk lsFromUtf8Sym (fromUtf8MplGhost mpl mmpl c2FromUtf8TableAddr relax1) :=
  fromUtf8MplGhost_rowSpecOk mpl mmpl c2FromUtf8TableAddr relax1
    (c2_fromUtf8Block_placeable hLs hRes)

/-- Default-`relax1` (`fun _ => false`) spelling of `c2_fromUtf8MplGhost_rowSpecOk`. -/
theorem c2_fromUtf8MplGhost_rowSpecOk_unrelaxed [LibsignalPlacement]
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr) :
    GhostRowSpecOk lsFromUtf8Sym (fromUtf8MplGhost mpl mmpl c2FromUtf8TableAddr) :=
  c2_fromUtf8MplGhost_rowSpecOk hLs hRes

/-! ## 4. C2 `.rodata` (`UTF8_CHAR_WIDTH`) & `.text.lib2` Hull / Entry-Guard Bridges -/

/-- Canonical byte identity between `Lib2LayoutFacts.c2CorePlacedData1` and
    `VerifiedLibraries.RustStd.corePlacedData1` (`256`-byte `UTF8_CHAR_WIDTH` table). -/
theorem c2CorePlacedData1_eq_corePlacedData1 :
    c2CorePlacedData1 = corePlacedData1 := by
  rfl_kernel

/-- Memory-level `.rodata` `RoDataAt` bridge at `c2FromUtf8TableAddr` from `F3CodeInv` +
    `LinkedAt cliElfBytes mpl` under `C2RoSliceFacts`. -/
theorem f3CodeInv_roDataAt_coreUtf8Table
    (hRoSlice : C2RoSliceFacts)
    {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    RoDataAt m c2FromUtf8TableAddr corePlacedData1 := by
  have h0 : RoDataAt m c2FromUtf8TableAddr c2CorePlacedData1 :=
    f3CodeInv_roDataAt_fromUtf8Table hRoSlice hLs hInv
  rw [← c2CorePlacedData1_eq_corePlacedData1]
  exact h0

/-- Exact `hRo` premise shape consumed by `FromUtf8GhostReplays.fromUtf8MplGhost_rowReplayOn`
    and `fromUtf8MplGhost_rowOk` at `tbl := c2FromUtf8TableAddr`. -/
theorem c2_fromUtf8_hRo_of_f3CodeInv
    (hRoSlice : C2RoSliceFacts)
    {mpl mmpl : Obj.MultiPlacement}
    {InvS : State → Prop}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, ExecFrozen u.mem → InvS u → RoDataAt u.mem c2FromUtf8TableAddr corePlacedData1 :=
  fun u _ hu => f3CodeInv_roDataAt_coreUtf8Table hRoSlice hLs (hInv u hu)

theorem lsFromUtf8Sym_mem_c2Lib2DehookedSyms :
    lsFromUtf8Sym ∈ c2Lib2DehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

private theorem keepLib2Text_of_sub_lt {base pc : BitVec 64} {len : Nat}
    (hsub : (pc - base).toNat < len)
    (hlo : c2Lib2TextLo.toNat ≤ base.toNat)
    (hhi : base.toNat + len ≤ c2Lib2TextHi.toNat) :
    keepLib2Text pc = true := by
  unfold keepLib2Text
  rw [decide_eq_true_eq]
  have htop : c2Lib2TextHi.toNat < 2 ^ 64 := BitVec.isLt c2Lib2TextHi
  generalize hd : pc - base = d at hsub
  have hpc_eq : pc = base + d := by subst hd; bv_omega
  have htoNat : pc.toNat = base.toNat + d.toNat := by
    rw [hpc_eq, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Unconditional C2 hull inclusion for `keepFromUtf8Block c2FromUtf8Addr`. -/
theorem keepFromUtf8Block_c2_sub_keepLib2Text {pc : BitVec 64}
    (h : keepFromUtf8Block c2FromUtf8Addr pc = true) :
    keepLib2Text pc = true := by
  rw [keepFromUtf8Block_iff] at h
  exact keepLib2Text_of_sub_lt h
    (decide_eq_true_eq.mp (by rfl_kernel))
    (decide_eq_true_eq.mp (by rfl_kernel))

/-- C2 hull inclusion `keepR_fromUtf8Mpl mpl pc = true → keepLib2Text pc = true` for `mpl` tied to
    `LinkedAt cliElfBytes mpl` under `hRes`. -/
theorem keepR_fromUtf8Mpl_sub_keepLib2Text {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr)
    (pc : BitVec 64) (h : keepR_fromUtf8Mpl mpl pc = true) :
    keepLib2Text pc = true := by
  let _ := hLs
  dsimp only [keepR_fromUtf8Mpl] at h
  rw [hRes] at h
  exact keepFromUtf8Block_c2_sub_keepLib2Text h

/-- `fromUtf8EntryGuard mpl s0` from `LinkedAt cliElfBytes mpl` + `C2ExternTableFacts` + `hRes` +
    startup `lr`. -/
theorem f3FromUtf8EntryGuard_of_startupLr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr)
    {s0 : State} (hlr : s0.readReg64 .lr = f3StartupLrVal) :
    fromUtf8EntryGuard mpl s0 :=
  (fromUtf8EntryGuard_iff mpl s0).mpr
    (f3Lib2EntryGuard_of_startupLr hlr
      (f3Lib2_dehookedSym_in_keepLib2Text hExt lsFromUtf8Sym_mem_c2Lib2DehookedSyms)
      (keepR_fromUtf8Mpl_sub_keepLib2Text hLs hRes))

/-- `C2ExternTableFacts`-free companion for `fromUtf8EntryGuard mpl s0` (`keepLib2Text` on entry
    discharged directly from `hRes`). -/
theorem c2FromUtf8EntryGuard_of_resolve {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hRes : libsignalSessionLib.resolve mpl lsFromUtf8Sym = c2FromUtf8Addr)
    {s0 : State} (hlr : s0.readReg64 .lr = f3StartupLrVal) :
    fromUtf8EntryGuard mpl s0 := by
  have hsym : keepLib2Text (libsignalSessionLib.resolve mpl lsFromUtf8Sym) = true := by
    rw [hRes]; exact decide_eq_true_eq.mp (by rfl_kernel)
  exact (fromUtf8EntryGuard_iff mpl s0).mpr
    (f3Lib2EntryGuard_of_startupLr hlr hsym (keepR_fromUtf8Mpl_sub_keepLib2Text hLs hRes))

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.FromUtf8
