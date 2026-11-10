/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen -- proof-setup: allow-public-import
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Cutover-2 (`C2`) `.text.lib2` / `.rodata.lib2` & `.text.b_pre` Layout Bridges (`ElfF3Relink.Lib2LayoutFacts`)

Supplies the untrusted layout and `F3CodeInv` bridges for Cutover-2 (`D-C2f = 2C` + `lib2` de-hook,
reference ELF `50066cbd…98ce`) without adding any fields to `F3CodeInv` or modifying
`StartupStatics.lean`:
1. `.rodata.lib2` `RoDataAt` derivation from `hInv.fromLoad` + `LinkedAt cliElfBytes mpl`
   (`holdsBytes_of_checkSegSlice` at `f3StdLayout.roSegIdx = 0` + `KeepsFrozen` + `holdsBytes_ro`).
2. `rxCode` sub-slice `CodeLoaded` on `stripExecOutside` & contiguous multi-block `hasWords`
   sub-slice projection (covering `bcmp + memcmp`, `duration_since + sub_timespec`,
   `SharedSecret::drop + zeroize32`, and `memcpy .. memmove`).
3. Unified `rxSeg` real & ghost `externAt?` lemmas + `Steps` lift over any `keepR_row ⊆ rxProg`.
4. Unconditional startup `s0.lr` (`ExtraEntryGuard`) and caller `LsRetAddr624` return-address guards
   (covering both `.text.lib2` R0 `β′` / trap-safe rows and `.text.b_pre` Batch L rows, plus K3/K4
   panic-stub exclusion).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliElf_parse cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (cliProgPlacedSig)
open LibsignalBinary.Heap.Fine (f3RxWordCount f3StdLayout)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt externAt?_cliProgExtPlacedSigAt_eq_none patchElfTokensPlacedAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfBlockBases cliElfMultiPlacement cliElf_linkedAt_unique)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn h2fsgen_steps_lift_of_visitedIn_noExtern)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf f3PatchedElf_eq_of_linkedAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BatchLDehookedSyms c2DurationSinceCst16Addr c2FirstExternStubAddr c2FromUtf8TableAddr
   c2Lib2DehookedSyms c2Lib2RoHi c2Lib2RoLo c2Lib2TextHi c2Lib2TextLo c2RxDehookedSyms
   c2StartupLrLit c2TextBPreDehookedSyms c2TextBPreHi c2TextBPreLo)

/-! ## 0. Panic-Stub Symbols & `.rodata.lib2` Byte Constants -/

abbrev lsExpectFailedSymC2 : String := "_RNvNtCskxtBwYRO61I_4core6option13expect_failed"
abbrev lsSliceIndexFailSymC2 : String := "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail"

/-- Canonical 256-byte `core::str::converts::UTF8_CHAR_WIDTH` table (`rfl`-identical to
    `VerifiedLibraries.RustStd.corePlacedData1`). -/
@[expose] def c2CorePlacedData1 : List (BitVec 8) :=
  List.replicate 128 0x01#8 ++
  List.replicate 66 0x00#8 ++
  List.replicate 30 0x02#8 ++
  List.replicate 16 0x03#8 ++
  List.replicate 5 0x04#8 ++
  List.replicate 11 0x00#8

/-- Canonical 16-byte `1_u128` mask in `Timespec::sub_timespec` (`rfl`-identical to
    `VerifiedLibraries.RustStd.timePlacedData0`). -/
@[expose] def c2TimePlacedData0 : List (BitVec 8) :=
  0x01#8 :: List.replicate 15 0x00#8

/-- Definitional (`rfl`) alias matching `HookDischarge.RustStd.Common.RoDataAt`. -/
abbrev RoDataAt (m : Memory) (addr : BitVec 64) (bytes : List (BitVec 8)) : Prop :=
  m.RO addr bytes.length ∧ m.readBytes addr bytes.length = bytes

/-! ## 1. `.text.b_pre` / `.text.lib2` Interval Predicates & Startup `lr` Value -/

/-- Half-open `.text.b_pre` interval `[c2TextBPreLo, c2TextBPreHi)` inside `rxSeg`. -/
@[expose] def keepTextBPre (pc : BitVec 64) : Bool :=
  decide (c2TextBPreLo.toNat ≤ pc.toNat ∧ pc.toNat < c2TextBPreHi.toNat)

/-- Half-open `.text.lib2` interval `[c2Lib2TextLo, c2Lib2TextHi)` inside `rxSeg`.
    Invariant under internal `.text.lib2` symbol reordering and valid for both 7-row and 6-row ELFs. -/
@[expose] def keepLib2Text (pc : BitVec 64) : Bool :=
  decide (c2Lib2TextLo.toNat ≤ pc.toNat ∧ pc.toNat < c2Lib2TextHi.toNat)

/-- Concrete startup return address entering `main` (`block 617`), proved equal to `sm.readReg64 .lr`
    by `StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt`. -/
@[expose] def f3StartupLrVal : BitVec 64 :=
  f3StdLayout.libcStartMainStage2Addr + 56#64

theorem f3StartupLrVal_eq : f3StartupLrVal = c2StartupLrLit := rfl

theorem keepTextBPre_startupLr_false : keepTextBPre f3StartupLrVal = false := by
  decide

theorem keepLib2Text_startupLr_false : keepLib2Text f3StartupLrVal = false := by
  decide

private theorem rxProg_code_len_eq :
    Tie.f3TrialRxProg.code.length = 4 * f3RxWordCount := by
  rw [Tie.f3TrialRxWordTree_eq, WordTree.length_toBytes_of_checkSize? Tie.f3TrialRxWordTree_size]

theorem keepTextBPre_sub_rxProg {pc : BitVec 64} (h : keepTextBPre pc = true) :
    progKeep Tie.f3TrialRxProg pc = true := by
  unfold keepTextBPre at h
  rw [decide_eq_true_eq] at h
  simp only [progKeep, Tie.f3TrialRxProg_base, rxProg_code_len_eq, decide_eq_true_eq]
  have hrx : Tie.f3RxSegBase = c2TextBPreLo := rfl
  have hbound : c2TextBPreHi.toNat - c2TextBPreLo.toNat ≤ 4 * f3RxWordCount := by decide
  have hlo : c2TextBPreLo.toNat ≤ pc.toNat := h.1
  have hhi : pc.toNat < c2TextBPreHi.toNat := h.2
  have hsub : (pc - Tie.f3RxSegBase).toNat = pc.toNat - c2TextBPreLo.toNat := by
    rw [hrx]; bv_omega
  omega

theorem keepLib2Text_sub_rxProg {pc : BitVec 64} (h : keepLib2Text pc = true) :
    progKeep Tie.f3TrialRxProg pc = true := by
  unfold keepLib2Text at h
  rw [decide_eq_true_eq] at h
  simp only [progKeep, Tie.f3TrialRxProg_base, rxProg_code_len_eq, decide_eq_true_eq]
  have hge : Tie.f3RxSegBase.toNat ≤ c2Lib2TextLo.toNat := by decide
  have hbound : c2Lib2TextHi.toNat - Tie.f3RxSegBase.toNat ≤ 4 * f3RxWordCount := by decide
  have hlo : c2Lib2TextLo.toNat ≤ pc.toNat := h.1
  have hhi : pc.toNat < c2Lib2TextHi.toNat := h.2
  have hsub : (pc - Tie.f3RxSegBase).toNat = pc.toNat - Tie.f3RxSegBase.toNat := by
    bv_omega
  omega

/-! ## 2. `.rodata.lib2` `RoDataAt` Bridges from `F3CodeInv` (`0` New Fields) -/

set_option maxRecDepth 4000000 in
theorem f3PatchedElf_wellFormed : f3PatchedElf.WellFormed = true := by
  rfl_kernel

/-- Generic `.rodata` slice bridge from `F3CodeInv` + `LinkedAt` into `RoDataAt`. -/
theorem f3CodeInv_roDataAt_of_checkSegSlice
    {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m)
    (addr : BitVec 64) (bytes : List (BitVec 8))
    (hSlice : ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length addr bytes = true) :
    RoDataAt m addr bytes := by
  obtain ⟨inputs, sLoad, hload, hkf⟩ := hInv.fromLoad
  rw [f3PatchedElf_eq_of_linkedAt hLs] at hload
  obtain ⟨seg, hseg, hperm, hsl⟩ := hSlice
  obtain ⟨hhb0, _, _⟩ :=
    holdsBytes_of_checkSegSlice f3PatchedElf_wellFormed hload hseg hsl
  have hhb_ro0 : Obj.HoldsBytes sLoad.mem addr bytes (fun _ => Perm.ro) := by
    simpa [hperm] using hhb0
  exact holdsBytes_ro (holdsBytes_ro_of_keepsFrozen hhb_ro0 hkf)

/-- Pending 2-field `rfl_kernel` `.rodata.lib2` witness on the C2-pinned `cliElfImage`
    (`50066cbd…98ce`); closed by `⟨⟨_, rfl, rfl, by rfl_kernel⟩, ⟨_, rfl, rfl, by rfl_kernel⟩⟩`
    once C2 rebases onto the C2 ELF. -/
structure C2RoSliceFacts : Prop where
  fromUtf8Slice :
    ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length c2FromUtf8TableAddr c2CorePlacedData1 = true
  durationSinceSlice :
    ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
      seg.perm.rwx = Perm.ro ∧
      checkSegSlice seg seg.bytes.length c2DurationSinceCst16Addr c2TimePlacedData0 = true

theorem f3CodeInv_roDataAt_fromUtf8Table
    (hRo : C2RoSliceFacts)
    {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    RoDataAt m c2FromUtf8TableAddr c2CorePlacedData1 :=
  f3CodeInv_roDataAt_of_checkSegSlice hLs hInv c2FromUtf8TableAddr c2CorePlacedData1
    hRo.fromUtf8Slice

theorem f3CodeInv_roDataAt_durationSinceCst16
    (hRo : C2RoSliceFacts)
    {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    RoDataAt m c2DurationSinceCst16Addr c2TimePlacedData0 :=
  f3CodeInv_roDataAt_of_checkSegSlice hLs hInv c2DurationSinceCst16Addr c2TimePlacedData0
    hRo.durationSinceSlice

/-! ## 3. `rxCode` Sub-Slice `CodeLoaded` on `stripExecOutside` & Multi-Block `hasWords` -/

/-- Restrict `hInv.rxCode` (`Tie.f3TrialRxProg.CodeLoaded m`) to any 4-byte-aligned word slice
    `(addr, words)` inside `Tie.f3TrialRxProg` on `stripExecOutside keepR m`.
    Covers single-block and contiguous multi-block rows across `.text.b_pre` and `.text.lib2`
    (`strlen`, `bcmp + memcmp`, `memcpy .. memmove`, `memrchr`, `from_utf8`, `duration_since +
    sub_timespec`, `black_box`, `SharedSecret::drop + zeroize32`, `StaticSecret::drop`, `add`). -/
theorem f3CodeInv_rxWords_codeLoaded_strip
    {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hInv : F3CodeInv mpl mmpl m)
    (addr : BitVec 64) (words : List (BitVec 32))
    (keepR : BitVec 64 → Bool)
    (hAlign : addr.toNat % 4 = 0)
    (hNoWrap : addr.toNat + 4 * words.length ≤ 2 ^ 64)
    (hSub : ∀ (i : Nat) (hi : i < (pureWordsProg addr words).code.length),
      ∃ (j : Nat) (hj : j < Tie.f3TrialRxProg.code.length),
        addr + BitVec.ofNat 64 i = Tie.f3TrialRxProg.base + BitVec.ofNat 64 j ∧
        (pureWordsProg addr words).code[i] = Tie.f3TrialRxProg.code[j])
    (hKeep : ∀ i < 4 * words.length, keepR (addr + BitVec.ofNat 64 i) = true) :
    (pureWordsProg addr words).CodeLoaded (stripExecOutside keepR m) := by
  have hLen : (pureWordsProg addr words).code.length = 4 * words.length :=
    Program.length_flatMap_wordToBytesLE words
  have hc := hInv.rxCode
  have hNoWrap' : (pureWordsProg addr words).base.toNat +
      (pureWordsProg addr words).code.length ≤ 2 ^ 64 := by
    change addr.toNat + (pureWordsProg addr words).code.length ≤ 2 ^ 64
    rw [hLen]
    exact hNoWrap
  refine Program.CodeLoaded.intro hAlign hNoWrap' ?_
  intro i hi
  obtain ⟨j, hj, haddr_eq, hbyte_eq⟩ := hSub i hi
  have hi4 : i < 4 * words.length := hLen ▸ hi
  have hk_i : keepR (addr + BitVec.ofNat 64 i) = true := hKeep i hi4
  have hr_rx := hc.byte_eq j hj
  have hp_rx := hc.perm_eq j hj
  have hlf_rx := hc.isLazyFree_eq j hj
  change (stripExecOutside keepR m).read8 (addr + BitVec.ofNat 64 i) =
      (pureWordsProg addr words).code[i] ∧
    (stripExecOutside keepR m).perm (addr + BitVec.ofNat 64 i) = some Perm.rx ∧
    (stripExecOutside keepR m).isLazyFree (addr + BitVec.ofNat 64 i) = false
  refine ⟨?_, ?_, ?_⟩
  · rw [strip_read8, haddr_eq, hr_rx, hbyte_eq]
  · rw [strip_perm, hk_i, haddr_eq, hp_rx]
    rfl
  · rw [strip_isLazyFree, haddr_eq, hlf_rx]

private theorem hookFree_subslice {prog : Program} {off len off' len' : Nat}
    (h : prog.hookFree off len) (hlo : off ≤ off') (hhi : off' + len' ≤ off + len) :
    prog.hookFree off' len' := by
  rcases h with ⟨h1, h2⟩
  refine ⟨List.all_eq_true.mpr ?_, List.all_eq_true.mpr ?_⟩
  · intro ⟨n, o⟩ hp
    have hp0 := List.all_eq_true.mp h1 (n, o) hp
    change (!(decide (off ≤ o) && decide (o < off + len)) || (prog.externs n).isNone) = true at hp0
    change (!(decide (off' ≤ o) && decide (o < off' + len')) || (prog.externs n).isNone) = true
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at hp0 ⊢
    rcases hp0 with (hleft | hright) | hpred
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr hpred
  · intro ⟨n, o⟩ hp
    have hp0 := List.all_eq_true.mp h2 (n, o) hp
    change (!(decide (off ≤ o) && decide (o < off + len)) || (prog.overrides n).isNone) = true at hp0
    change (!(decide (off' ≤ o) && decide (o < off' + len')) || (prog.overrides n).isNone) = true
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at hp0 ⊢
    rcases hp0 with (hleft | hright) | hpred
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr hpred

/-- Project `prog.hasWords (base + 4*k) sub` out of a contiguous multi-block `prog.hasWords base words`
    witness (covering `bcmp + memcmp`, `duration_since + sub_timespec`, `SharedSecret::drop +
    zeroize32`, and `memcpy .. memmove`). -/
theorem hasWords_subslice_of_hasWords {prog : Program} {base : BitVec 64}
    {words sub : List (BitVec 32)} {k : Nat}
    (hw : prog.hasWords base words)
    (hk_end : k + sub.length ≤ words.length)
    (hbnd : (base - prog.base).toNat + 4 * k < 2 ^ 64)
    (_hbase_ge : prog.base.toNat ≤ base.toNat)
    (_hbase_k : base.toNat + 4 * k < 2 ^ 64)
    (hsub : ∀ i (hi : i < sub.length), sub[i] = words[k + i]'(by omega)) :
    prog.hasWords (base + BitVec.ofNat 64 (4 * k)) sub := by
  unfold Program.hasWords Program.hasWordsOff at hw ⊢
  obtain ⟨hlen_w, hread_w, hrest⟩ := hw
  have hoff_eq : ((base + BitVec.ofNat 64 (4 * k)) - prog.base).toNat =
      (base - prog.base).toNat + 4 * k := by
    bv_omega
  rw [hoff_eq]
  refine ⟨by omega, fun i hi => ?_, hookFree_subslice hrest (by omega) (by omega)⟩
  have hki : k + i < words.length := by omega
  have hr := hread_w (k + i) hki
  have harr : (base - prog.base).toNat + 4 * k + 4 * i =
      (base - prog.base).toNat + 4 * (k + i) := by omega
  rw [harr, hr]
  exact congrArg some (hsub i hi).symm

/-! ## 4. Unified `rxSeg` Real & Ghost `externAt?` & `Steps` Lift (`T1`, `T2` + `2C`) -/

private def lookupAddrTagNatC2 (tbl : List (Nat × UInt8)) (pc : Nat) : Option UInt8 :=
  match tbl with
  | [] => none
  | (a, t) :: rest => if Nat.beq a pc then some t else lookupAddrTagNatC2 rest pc

private theorem lookupAddrTagNatC2_none_of_all_lt (tbl : List (Nat × UInt8)) (pc : Nat)
    (hall : (tbl.all fun p => Nat.blt p.1 pc) = true) :
    lookupAddrTagNatC2 tbl pc = none := by
  induction tbl with
  | nil => rfl
  | cons hd xs ih =>
    rcases hd with ⟨a, t⟩
    simp only [List.all_cons, Bool.and_eq_true, Nat.blt_eq] at hall
    have hne : Nat.beq a pc = false := by
      rw [Bool.eq_false_iff, Ne, Nat.beq_eq]; omega
    simp only [lookupAddrTagNatC2, hne, Bool.false_eq_true, ↓reduceIte]
    exact ih hall.2

/-- Pending C2 placement/table lookup witnesses on the C2-rekeyed `cliExternsPlaced` /
    `ElfCodeMatchesData` (`50066cbd…98ce`); discharged by `rfl_kernel` at C2 rebase. -/
structure C2ExternTableFacts (mpl : Obj.MultiPlacement) : Prop where
  realRxNoExtern :
    ∀ (mmpl : Obj.MultiPlacement) (W : CliHooks) {pc : BitVec 64},
      progKeep Tie.f3TrialRxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none
  ghostRxNoExternOffEntries :
    ∀ (extFn : CliHooks → String → Option (State → State)) (W : CliHooks) {pc : BitVec 64},
      progKeep Tie.f3TrialRxProg pc = true →
      pc ∉ c2RxDehookedSyms.map (libsignalSessionLib.resolve mpl) →
      (cliProgExtPlacedAt mpl extFn 617 W).externAt? pc = none
  ghostRxEntry :
    ∀ (extFn : CliHooks → String → Option (State → State)) (W : CliHooks) {sym : String},
      sym ∈ c2RxDehookedSyms →
      (cliProgExtPlacedAt mpl extFn 617 W).externAt? (libsignalSessionLib.resolve mpl sym) =
        extFn W sym
  lib2InKeep :
    ∀ {sym : String}, sym ∈ c2Lib2DehookedSyms →
      keepLib2Text (libsignalSessionLib.resolve mpl sym) = true
  batchLInKeep :
    ∀ {sym : String}, sym ∈ c2BatchLDehookedSyms →
      keepTextBPre (libsignalSessionLib.resolve mpl sym) = true

theorem f3RxSeg_realProg617_externAt_none
    {mpl mmpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {pc : BitVec 64}
    (hpc : progKeep Tie.f3TrialRxProg pc = true) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  hExt.realRxNoExtern mmpl W hpc

theorem f3RxSeg_ghostProg617_externAt_none_of_ne_entries
    {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (extFn : CliHooks → String → Option (State → State)) (W : CliHooks)
    {pc : BitVec 64} (hpc : progKeep Tie.f3TrialRxProg pc = true)
    (hne : pc ∉ c2RxDehookedSyms.map (libsignalSessionLib.resolve mpl)) :
    (cliProgExtPlacedAt mpl extFn 617 W).externAt? pc = none :=
  hExt.ghostRxNoExternOffEntries extFn W hpc hne

theorem f3RxSeg_ghostProg617_externAt_entry
    {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (extFn : CliHooks → String → Option (State → State)) (W : CliHooks)
    {sym : String} (hsym : sym ∈ c2RxDehookedSyms) :
    (cliProgExtPlacedAt mpl extFn 617 W).externAt?
      (libsignalSessionLib.resolve mpl sym) = extFn W sym :=
  hExt.ghostRxEntry extFn W hsym

/-- Per-row entry-excluded `externAt? = none` on `P_ghost_W` (`cliProgExtPlacedAt mpl extFn 617 W`):
    for any row `(sym, keepR_row)` inside `rxSeg` whose `keepR_row` avoids other `c2RxDehookedSyms`
    entries (or where `extFn W s = none`, e.g. `"memcpy"`/`"memset"` inside `memmove + memcpy`),
    every non-entry `pc` in `keepR_row` has `externAt? pc = none`. -/
theorem f3Row_ghostProg617_externAt_none_of_ne_entry
    {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (extFn : CliHooks → String → Option (State → State)) (W : CliHooks)
    {sym : String} {keepR_row : BitVec 64 → Bool}
    (hSub : ∀ pc, keepR_row pc = true → progKeep Tie.f3TrialRxProg pc = true)
    (hOther : ∀ s ∈ c2RxDehookedSyms, s ≠ sym →
      keepR_row (libsignalSessionLib.resolve mpl s) = false ∨ extFn W s = none)
    {pc : BitVec 64} (hkeep : keepR_row pc = true)
    (hne : pc ≠ libsignalSessionLib.resolve mpl sym) :
    (cliProgExtPlacedAt mpl extFn 617 W).externAt? pc = none := by
  by_cases hmem : pc ∈ c2RxDehookedSyms.map (libsignalSessionLib.resolve mpl)
  · obtain ⟨s, hs_mem, hs_eq⟩ := List.mem_map.mp hmem
    have hs_ne : s ≠ sym := by
      intro h_eq; subst h_eq; exact hne hs_eq.symm
    rcases hOther s hs_mem hs_ne with hfalse | hnone
    · rw [hs_eq] at hfalse; cases hkeep.symm.trans hfalse
    · rw [← hs_eq, hExt.ghostRxEntry extFn W hs_mem, hnone]
  · exact hExt.ghostRxNoExternOffEntries extFn W (hSub pc hkeep) hmem

/-- Multi-entry generalization of `f3Row_ghostProg617_externAt_none_of_ne_entry` for hulls
    containing multiple active ghost entries (e.g. `rowSyms := ["memmove", "memcpy", "memset"]` on
    `memmove`'s 956 B hull when `g.memcpy`/`g.memset` are simultaneously active in `extFn W`):
    every `pc` in `keepR_row` outside `rowSyms.map (resolve mpl)` has `externAt? pc = none`. -/
theorem f3RowSyms_ghostProg617_externAt_none_of_ne_entries
    {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (extFn : CliHooks → String → Option (State → State)) (W : CliHooks)
    {rowSyms : List String} {keepR_row : BitVec 64 → Bool}
    (hSub : ∀ pc, keepR_row pc = true → progKeep Tie.f3TrialRxProg pc = true)
    (hOther : ∀ s ∈ c2RxDehookedSyms, s ∉ rowSyms →
      keepR_row (libsignalSessionLib.resolve mpl s) = false ∨ extFn W s = none)
    {pc : BitVec 64} (hkeep : keepR_row pc = true)
    (hne : pc ∉ rowSyms.map (libsignalSessionLib.resolve mpl)) :
    (cliProgExtPlacedAt mpl extFn 617 W).externAt? pc = none := by
  by_cases hmem : pc ∈ c2RxDehookedSyms.map (libsignalSessionLib.resolve mpl)
  · obtain ⟨s, hs_mem, hs_eq⟩ := List.mem_map.mp hmem
    have hs_notin : s ∉ rowSyms := by
      intro hs_in
      exact hne (hs_eq ▸ List.mem_map.mpr ⟨s, hs_in, rfl⟩)
    rcases hOther s hs_mem hs_notin with hfalse | hnone
    · rw [hs_eq] at hfalse; cases hkeep.symm.trans hfalse
    · rw [← hs_eq, hExt.ghostRxEntry extFn W hs_mem, hnone]
  · exact hExt.ghostRxNoExternOffEntries extFn W (hSub pc hkeep) hmem

theorem f3Lib2_dehookedSym_in_keepLib2Text
    {mpl : Obj.MultiPlacement} (hExt : C2ExternTableFacts mpl)
    {sym : String} (hsym : sym ∈ c2Lib2DehookedSyms) :
    keepLib2Text (libsignalSessionLib.resolve mpl sym) = true :=
  hExt.lib2InKeep hsym

theorem f3BatchL_dehookedSym_in_keepTextBPre
    {mpl : Obj.MultiPlacement} (hExt : C2ExternTableFacts mpl)
    {sym : String} (hsym : sym ∈ c2BatchLDehookedSyms) :
    keepTextBPre (libsignalSessionLib.resolve mpl sym) = true :=
  hExt.batchLInKeep hsym

/-- Definitional (`rfl`) alias of `ElfSlicesPqOomH2FirstStopGeneric.h2fsgen_StepsVisitedIn`,
    for lifting hook-free `Program.ofSvc Syscall.standard` (`hole2_emptyProg`) runs on `keepR_row`
    to `Steps P_real_W`. -/
abbrev StepsVisitedIn : (BitVec 64 → Bool) → Program → State → State → Prop :=
  h2fsgen_StepsVisitedIn

private theorem ofSvc_standard_svc : (Program.ofSvc Syscall.standard).svc = Syscall.standard :=
  rfl

private theorem realProg617_svc (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard :=
  rfl

private theorem ofSvc_standard_externAt (pc : BitVec 64) :
    (Program.ofSvc Syscall.standard).externAt? pc = none :=
  rfl

/-- Direct `rxSeg` analogue of `H2StepsLiftR2.h2sl_steps_realW_of_visitedIn_keepSub` (`:954`) for
    ANY row predicate `keepR_row ⊆ progKeep Tie.f3TrialRxProg`. -/
theorem f3RxSeg_steps_realW_of_visitedIn
    {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {keepR_row : BitVec 64 → Bool}
    (hSub : ∀ pc, keepR_row pc = true → progKeep Tie.f3TrialRxProg pc = true)
    {s sf : State}
    (hvis : StepsVisitedIn keepR_row (Program.ofSvc Syscall.standard) s sf) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s sf :=
  h2fsgen_steps_lift_of_visitedIn_noExtern
    (P1 := Program.ofSvc Syscall.standard)
    (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
    (ofSvc_standard_svc.trans (realProg617_svc mpl mmpl W).symm)
    (fun pc _ => ofSvc_standard_externAt pc)
    (fun pc hkeep => hExt.realRxNoExtern mmpl W (hSub pc hkeep))
    hvis

/-! ## 5. Unconditional Startup `s0.lr` (`ExtraEntryGuard`) & Caller `LsRetAddr624` Guards -/

/-- Startup `s0.lr` (`ExtraEntryGuard` for `LinkedCallHookG`) on `.text.lib2` rows (`6` or `7` rows,
    order-independent). Unconditional (`0` pending C2 hypotheses). -/
theorem f3Lib2EntryGuard_of_startupLr
    {mpl : Obj.MultiPlacement}
    {s0 : State} (hlr : s0.readReg64 .lr = f3StartupLrVal)
    {sym : String} (hsym : keepLib2Text (libsignalSessionLib.resolve mpl sym) = true)
    {keepR : BitVec 64 → Bool}
    (hsub : ∀ pc, keepR pc = true → keepLib2Text pc = true) :
    keepR (s0.readReg64 .lr) = false ∧
      s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl sym := by
  rw [hlr]
  have hfalse : keepLib2Text f3StartupLrVal = false := keepLib2Text_startupLr_false
  refine ⟨?_, ?_⟩
  · cases hk : keepR f3StartupLrVal
    · rfl
    · cases hfalse.symm.trans (hsub f3StartupLrVal hk)
  · intro heq
    rw [heq] at hfalse
    cases hfalse.symm.trans hsym

/-- Startup `s0.lr` (`ExtraEntryGuard`) on `.text.b_pre` Batch L rows (`memmove + memcpy`,
    `bcmp + memcmp`, `strlen`). Unconditional (`0` pending C2 hypotheses). -/
theorem f3BatchLEntryGuard_of_startupLr
    {mpl : Obj.MultiPlacement}
    {s0 : State} (hlr : s0.readReg64 .lr = f3StartupLrVal)
    {sym : String} (hsym : keepTextBPre (libsignalSessionLib.resolve mpl sym) = true)
    {keepR : BitVec 64 → Bool}
    (hsub : ∀ pc, keepR pc = true → keepTextBPre pc = true) :
    keepR (s0.readReg64 .lr) = false ∧
      s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl sym := by
  rw [hlr]
  have hfalse : keepTextBPre f3StartupLrVal = false := keepTextBPre_startupLr_false
  refine ⟨?_, ?_⟩
  · cases hk : keepR f3StartupLrVal
    · rfl
    · cases hfalse.symm.trans (hsub f3StartupLrVal hk)
  · intro heq
    rw [heq] at hfalse
    cases hfalse.symm.trans hsym

section LsRetAddr624Kernel
set_option maxRecDepth 400000

/-- Kernel check across all `624` crate blocks (`0 .. 623` in `.text.crate`): every block end
    `cliElfBlockBases[j] + lsLen j` sits at or below `c2FirstExternStubAddr`, and the
    two K3/K4 panic stubs sit at or above `c2FirstExternStubAddr`. -/
noncomputable def c2CheckLsRetAddr624BoundsB : Bool :=
  Nat.beq libsignalSessionLib.blocks.length 624 &&
  Nat.beq cliElfBlockBases.length 624 &&
  (List.range 624).all (fun j =>
    Nat.ble ((cliElfBlockBases.getD j 0#64).toNat + lsLen j) c2FirstExternStubAddr.toNat) &&
  Nat.ble c2FirstExternStubAddr.toNat
    (libsignalSessionLib.resolve cliElfMultiPlacement lsExpectFailedSymC2).toNat &&
  Nat.ble c2FirstExternStubAddr.toNat
    (libsignalSessionLib.resolve cliElfMultiPlacement lsSliceIndexFailSymC2).toNat

theorem c2CheckLsRetAddr624Bounds_ok : c2CheckLsRetAddr624BoundsB = true := by
  rfl_kernel

end LsRetAddr624Kernel

/-- Unconditional upper bound for every `LsRetAddr624 lr`: `lr.toNat < c2FirstExternStubAddr.toNat`
    (strictly below all extern/retired stubs in `:text_a`, `.text.b_pre`, and
    `.text.lib2`). Callers bridge `lsmpl ↔ mpl` via
    `ElfCodeMatchesPlaced.f3CliElf_libsignal_linkedAt_unique`. -/
theorem f3LsRetAddr624_lt_firstExternStub [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hRet : LsRetAddr624 lr) :
    lr.toNat < c2FirstExternStubAddr.toNat := by
  rcases hRet with ⟨j, hj, o, ho, rfl⟩
  have hok := c2CheckLsRetAddr624Bounds_ok
  unfold c2CheckLsRetAddr624BoundsB at hok
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hok
  have hjlen : j < libsignalSessionLib.blocks.length := by
    rw [hok.1.1.1.1]; exact hj
  have hbase_eq : lsmpl.base j = cliElfMultiPlacement.base j :=
    (cliElf_linkedAt_unique hLs).1 j hjlen
  have hdef : cliElfMultiPlacement.base j = cliElfBlockBases.getD j 0#64 := rfl
  have hbnd : (cliElfBlockBases.getD j 0#64).toNat + lsLen j ≤ c2FirstExternStubAddr.toNat := by
    have hall := List.all_eq_true.mp hok.1.1.2 j (List.mem_range.mpr hj)
    rwa [Nat.ble_eq] at hall
  rw [hbase_eq, hdef]
  have hstub_lt : c2FirstExternStubAddr.toNat < 2 ^ 64 := BitVec.isLt c2FirstExternStubAddr
  have hadd : ((cliElfBlockBases.getD j 0#64) + BitVec.ofNat 64 o).toNat =
      (cliElfBlockBases.getD j 0#64).toNat + o := by
    have ho' : (BitVec.ofNat 64 o).toNat = o := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, ho', Nat.mod_eq_of_lt (by omega)]
  omega

/-- Unconditional K3/K4 panic-stub exclusion (`expect_failed`, `slice_index_fail`) for any caller
    `LsRetAddr624 lr` (`T6`). -/
theorem f3LsRetAddr624_ne_panicStubs [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hRet : LsRetAddr624 lr) :
    lr ≠ libsignalSessionLib.resolve lsmpl lsExpectFailedSymC2 ∧
      lr ≠ libsignalSessionLib.resolve lsmpl lsSliceIndexFailSymC2 := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hRet
  have hok := c2CheckLsRetAddr624Bounds_ok
  unfold c2CheckLsRetAddr624BoundsB at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  have huniq := cliElf_linkedAt_unique hLs
  rw [huniq.2.1 lsExpectFailedSymC2 (decide_eq_true_eq.mp (by rfl_kernel)),
      huniq.2.1 lsSliceIndexFailSymC2 (decide_eq_true_eq.mp (by rfl_kernel))]
  refine ⟨?_, ?_⟩ <;> intro heq <;> rw [heq] at hlt <;> omega

/-- Unconditional caller `LsRetAddr624` guard for R0 `β′` K-narrowed `lib2` rows (`memrchr`,
    `duration_since`, and `SystemTime::add` in the 7-row layout; `add` stays hooked in the 6-row
    layout) and `.text.b_pre` Batch L rows (`T6`, `T7`). -/
theorem f3LsRetAddr624_rxRegion_guard [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hRet : LsRetAddr624 lr)
    {sym : String}
    (hsym : keepTextBPre (libsignalSessionLib.resolve lsmpl sym) = true ∨
      keepLib2Text (libsignalSessionLib.resolve lsmpl sym) = true)
    {keepR : BitVec 64 → Bool}
    (hsub : ∀ pc, keepR pc = true → keepTextBPre pc = true ∨ keepLib2Text pc = true) :
    keepR lr = false ∧ lr ≠ libsignalSessionLib.resolve lsmpl sym := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hRet
  have hbpre_false : keepTextBPre lr = false := by
    unfold keepTextBPre
    rw [decide_eq_false_iff_not]
    have hlo : c2FirstExternStubAddr.toNat ≤ c2TextBPreLo.toNat := by decide
    omega
  have hlib2_false : keepLib2Text lr = false := by
    unfold keepLib2Text
    rw [decide_eq_false_iff_not]
    have hlo : c2FirstExternStubAddr.toNat ≤ c2Lib2TextLo.toNat := by decide
    omega
  refine ⟨?_, ?_⟩
  · cases hk : keepR lr
    · rfl
    · rcases hsub lr hk with hb | hl
      · cases hbpre_false.symm.trans hb
      · cases hlib2_false.symm.trans hl
  · intro heq
    rw [← heq] at hsym
    rcases hsym with hb | hl
    · cases hbpre_false.symm.trans hb
    · cases hlib2_false.symm.trans hl

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
