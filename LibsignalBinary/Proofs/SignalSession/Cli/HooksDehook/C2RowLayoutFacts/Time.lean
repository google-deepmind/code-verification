/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Multi -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DurCst16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Generic & Cutover-2 (`C2`) `timeMultiLib` Placement and `duration_since` Row Glue (`C2RowLayoutFacts.Time`)

**Checked by Lean. Untrusted (`Role::Proof`).**

Owns the shared Cutover-2 `timeMultiLib` placement `c2TimeMpl : Obj.MultiPlacement` (used by both
`<std::time::SystemTime>::duration_since` and `<SystemTime as Add<Duration>>::add`) and discharges
the GK6c §19(d) `duration_since` row premises from `DurationSinceGhostReplays`:

1. **Generic `mkTimeMpl` & `Placeable` / `checkProgCodeSubslice` Combinators (§1–§2, zero C2 constants):**
   - `mkTimeMpl` constructs an unrelaxed `Obj.MultiPlacement` for `timeMultiLib`'s 3 code blocks
     (`Timespec::sub_timespec`, `SystemTime::duration_since`, `SystemTime::add`), 5 `.rodata`
     symbols, and single panic extern `rustTimeExpectFailedSym`, with `rfl`/decidable projections
     for `base 0..2`, `ρ timeRodataCst16Sym`, and `timeAddExpectFailedStubPc`.
   - `checkProgCodeSubslice rxProg subProg` performs a single linear `O(off + len)` byte-subslice
     comparison `(rxProg.code.drop off).take len`, discharging both direct `subProg.CodeLoaded m`
     and `Lib2LayoutFacts.f3CodeInv_rxWords_codeLoaded_strip` (`hAlign`, `hNoWrap`, `hSub`).
2. **Concrete `c2TimeMpl : Obj.MultiPlacement` & Shared Time Facts (§3):**
   - Keyed by symbol name (`libsignalSessionLib.resolve cliElfMultiPlacement lsExpectFailedSymC2`)
     and generator-emitted `Wp4LayoutGen` constants (`c2SubTimespecAddr`, `c2DurationSinceAddr`,
     `c2TimeAddAddr`, `c2DurationSinceCst16Addr`, `c2FromUtf8TableAddr`, `c2Lib2RoLo`), with a
     single documented block of 4 named `.rodata.lib2` `abbrev`s for local `.Lanon`/`str1.1` data
     symbols not present in `.symtab`.
   - Proves unconditional (`0` pending hypotheses) `c2TimeMpl_placeable`, `c2TimeMpl_hb1`,
     `c2TimeMpl_hRho`, `c2TimeMpl_expectFailedStubPc`, `c2TimeMpl_expectFailedStubPc_of_linkedAt`,
     and `c2_durationSinceGhost_rowSpecOk`.
3. **Concrete `durationSinceGhost_rowOk` Premises & Combined Row Theorem (§4):**
   - Discharges `hTargetEq`, `hCL` (via `Lib2LayoutFacts.f3CodeInv_rxWords_codeLoaded_strip` +
     `durationSinceSubProg_codeLoaded_of_stripExecOutside`), `hRo` (via `DurCst16`), `hInvKeep`
     (via `F3CodeInv.of_keepsFrozen`), `hKeep` (via `f3LsRetAddr624_lt_firstExternStub`), and
     `hRealHullNoExt` (via `f3RxSeg_realProg617_externAt_none` + `keepLib2Text_sub_rxProg`),
     leaving only the T4 `rfl_kernel`-closed premises (`C2RoSliceFacts`, `C2ExternTableFacts`,
     `hRxDur : checkProgCodeSubslice Tie.f3TrialRxProg (durationSinceSubProg c2TimeMpl) = true`,
     and `hResDur : libsignalSessionLib.resolve mpl lsDurationSinceSym = c2DurationSinceAddr`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open VerifiedLibraries.RustStd
  (rustTimeExpectFailedSym timeAddSym timeMultiLib timePlacedData0 timeRodataCst16Sym)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib lsDurationSinceSym lsTimeAddSym)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.DurCst16
  (durationSince_hRo_of_f3CodeInv)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode
  (durationSinceHullProg durationSinceHullWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhost (subTimespecByteLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostReplays
  (durationSinceGhost durationSinceGhost_rowOk durationSinceGhost_rowSpecOk
   durationSinceHullByteLen durationSinceSubProg durationSinceSubProg_base
   durationSinceSubProg_code_length durationSinceSubProg_codeLoaded_of_stripExecOutside
   keepR_durationSince keepR_durationSince_of_code_offset)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays
  (keepR_timeAdd timeAddSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddPanicGhost
  (timeAddEntryAddr_eq_base2 timeAddExpectFailedStubPc)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (GhostRowSpecOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts C2RoSliceFacts f3CodeInv_rxWords_codeLoaded_strip
   f3LsRetAddr624_lt_firstExternStub f3RxSeg_realProg617_externAt_none keepLib2Text
   keepLib2Text_sub_rxProg lsExpectFailedSymC2)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElf_linkedAt_unique lsInternedMultiLib)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2DurationSinceAddr c2DurationSinceCst16Addr c2FirstExternStubAddr c2FromUtf8TableAddr
   c2Lib2DehookedSyms c2Lib2RoLo c2Lib2TextHi c2Lib2TextLo c2SubTimespecAddr c2TimeAddAddr)

/-! ## 1. Generic `timeMultiLib` Placement Constructor & Projections -/

/-- Internal `timeMultiLib` read-only data symbol for `.rodata.str1.1+0x0` (`73` B, `align = 1`). -/
abbrev rustTimeRoStr1Sym : String := "rust_time:.rodata.str1.1+0x0"

/-- Internal `timeMultiLib` read-only data symbol for `.rodata..Lanon.148` (`25` B, `align = 1`). -/
abbrev rustTimeRoLanon148Sym : String := "rust_time:.rodata..Lanon.148"

/-- Internal `timeMultiLib` read-only data symbol for `.data.rel.ro..Lanon.150` (`24` B, `align = 8`). -/
abbrev rustTimeDataRelRoLanon150Sym : String := "rust_time:.data.rel.ro..Lanon.150"

/-- Internal `timeMultiLib` read-only data symbol for `.rodata..Lanon.678` (`45` B, `align = 1`). -/
abbrev rustTimeRoLanon678Sym : String := "rust_time:.rodata..Lanon.678"

/-- Generic unrelaxed `Obj.MultiPlacement` constructor for `VerifiedLibraries.RustStd.timeMultiLib`
    from its 3 block bases (`sub_timespec`, `duration_since`, `SystemTime::add`), 5 RO data symbol
    addresses, and single panic-extern address (`rustTimeExpectFailedSym`). -/
@[expose] def mkTimeMpl
    (subTimespecBase durEntry addEntry : BitVec 64)
    (cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr : BitVec 64)
    (expectFailedAddr : BitVec 64) : Obj.MultiPlacement where
  base i :=
    match i with
    | 0 => subTimespecBase
    | 1 => durEntry
    | 2 => addEntry
    | _ => 0#64
  ρ sym :=
    if sym == timeRodataCst16Sym then cst16Addr
    else if sym == rustTimeRoStr1Sym then roStr1Addr
    else if sym == rustTimeRoLanon148Sym then roLanon148Addr
    else if sym == rustTimeDataRelRoLanon150Sym then dataRelRo150Addr
    else if sym == rustTimeRoLanon678Sym then roLanon678Addr
    else if sym == rustTimeExpectFailedSym then expectFailedAddr
    else 0#64
  relax _ _ := false
  b2b _ _ := false
  undefWeak _ := false

theorem mkTimeMpl_base0
    (subTimespecBase durEntry addEntry : BitVec 64)
    (cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr : BitVec 64)
    (expectFailedAddr : BitVec 64) :
    (mkTimeMpl subTimespecBase durEntry addEntry
      cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr
      expectFailedAddr).base 0 = subTimespecBase :=
  rfl

theorem mkTimeMpl_base1
    (subTimespecBase durEntry addEntry : BitVec 64)
    (cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr : BitVec 64)
    (expectFailedAddr : BitVec 64) :
    (mkTimeMpl subTimespecBase durEntry addEntry
      cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr
      expectFailedAddr).base 1 = durEntry :=
  rfl

theorem mkTimeMpl_base2
    (subTimespecBase durEntry addEntry : BitVec 64)
    (cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr : BitVec 64)
    (expectFailedAddr : BitVec 64) :
    (mkTimeMpl subTimespecBase durEntry addEntry
      cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr
      expectFailedAddr).base 2 = addEntry :=
  rfl

theorem mkTimeMpl_rho_cst16
    (subTimespecBase durEntry addEntry : BitVec 64)
    (cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr : BitVec 64)
    (expectFailedAddr : BitVec 64) :
    (mkTimeMpl subTimespecBase durEntry addEntry
      cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr
      expectFailedAddr).ρ timeRodataCst16Sym = cst16Addr := by
  have h0 : (timeRodataCst16Sym == timeRodataCst16Sym) = true := beq_self_eq_true _
  unfold mkTimeMpl
  dsimp only
  rw [h0]
  simp

theorem mkTimeMpl_rho_expectFailed
    (subTimespecBase durEntry addEntry : BitVec 64)
    (cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr : BitVec 64)
    (expectFailedAddr : BitVec 64) :
    (mkTimeMpl subTimespecBase durEntry addEntry
      cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr
      expectFailedAddr).ρ rustTimeExpectFailedSym = expectFailedAddr := by
  have h0 : (rustTimeExpectFailedSym == timeRodataCst16Sym) = false := by decide +kernel
  have h1 : (rustTimeExpectFailedSym == rustTimeRoStr1Sym) = false := by decide +kernel
  have h2 : (rustTimeExpectFailedSym == rustTimeRoLanon148Sym) = false := by decide +kernel
  have h3 : (rustTimeExpectFailedSym == rustTimeDataRelRoLanon150Sym) = false := by decide +kernel
  have h4 : (rustTimeExpectFailedSym == rustTimeRoLanon678Sym) = false := by decide +kernel
  have h5 : (rustTimeExpectFailedSym == rustTimeExpectFailedSym) = true := beq_self_eq_true _
  unfold mkTimeMpl
  dsimp only
  rw [h0, h1, h2, h3, h4, h5]
  simp

private theorem lookupBlockSym_expectFailed_none :
    Obj.lookupBlockSym rustTimeExpectFailedSym timeMultiLib.blocks = none := by
  decide +kernel

/-- Generic reduction of `timeAddExpectFailedStubPc timeMpl` to `timeMpl.ρ rustTimeExpectFailedSym`
    for **any** `timeMpl : Obj.MultiPlacement` (`rustTimeExpectFailedSym` is external to all 3
    `timeMultiLib` blocks). -/
theorem timeAddExpectFailedStubPc_eq_rho (timeMpl : Obj.MultiPlacement) :
    timeAddExpectFailedStubPc timeMpl = timeMpl.ρ rustTimeExpectFailedSym := by
  unfold timeAddExpectFailedStubPc MultiPlacedLib.blockPlacement MultiPlacedLib.resolve
  dsimp only
  rw [lookupBlockSym_expectFailed_none]

theorem mkTimeMpl_expectFailedStubPc
    (subTimespecBase durEntry addEntry : BitVec 64)
    (cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr : BitVec 64)
    (expectFailedAddr : BitVec 64) :
    timeAddExpectFailedStubPc
      (mkTimeMpl subTimespecBase durEntry addEntry
        cst16Addr roStr1Addr roLanon148Addr dataRelRo150Addr roLanon678Addr
        expectFailedAddr) = expectFailedAddr := by
  rw [timeAddExpectFailedStubPc_eq_rho, mkTimeMpl_rho_expectFailed]

/-! ## 2. Generic `Placeable` and Premise Combinators (`checkProgCodeSubslice` in `CodeSubslice`) -/

/-- Generic decidable `Placeable` bridge for `timeMultiLib`. -/
theorem timeMultiLib_placeable_of_check {timeMpl : Obj.MultiPlacement}
    (hchk : timeMultiLib.checkPlaceable timeMpl = true) :
    timeMultiLib.Placeable timeMpl :=
  MultiPlacedLib.placeable_of_checkPlaceable hchk

/-- Generic `GhostRowSpecOk` bridge for `lsDurationSinceSym` from decidable `checkPlaceable`. -/
theorem durationSinceGhost_rowSpecOk_of_check [LibsignalPlacement]
    (timeMpl : Obj.MultiPlacement)
    (hchk : timeMultiLib.checkPlaceable timeMpl = true)
    (hb1 : timeMpl.base 1 = timeMpl.base 0 + subTimespecByteLen) :
    GhostRowSpecOk lsDurationSinceSym (durationSinceGhost timeMpl) :=
  durationSinceGhost_rowSpecOk timeMpl (timeMultiLib_placeable_of_check hchk) hb1

/-- Generic interval inclusion for `keepR_durationSince timeMpl`. -/
theorem keepR_durationSince_sub_interval {timeMpl : Obj.MultiPlacement}
    {lo hi pc : BitVec 64}
    (hlo : lo.toNat ≤ (timeMpl.base 0).toNat)
    (hhi : (timeMpl.base 0).toNat + durationSinceHullByteLen ≤ hi.toNat)
    (hk : keepR_durationSince timeMpl pc = true) :
    decide (lo.toNat ≤ pc.toNat ∧ pc.toNat < hi.toNat) = true := by
  unfold keepR_durationSince at hk
  rw [decide_eq_true_eq] at hk ⊢
  have htop : hi.toNat < 2 ^ 64 := BitVec.isLt hi
  have hpc_eq : pc = timeMpl.base 0 + (pc - timeMpl.base 0) := by bv_omega
  have htoNat : pc.toNat = (timeMpl.base 0).toNat + (pc - timeMpl.base 0).toNat := by
    conv => lhs; rw [hpc_eq]
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Generic `hInvKeep` combinator for `InvS u := InvMem u.mem`. -/
theorem invS_mem_keepsFrozen {InvMem : Memory → Prop}
    (hMemKeep : ∀ m1 m2 : Memory, InvMem m1 → m1.KeepsFrozen m2 → InvMem m2) :
    ∀ u v : State, InvMem u.mem → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvMem v.mem :=
  fun u v hu hkf _ => hMemKeep u.mem v.mem hu hkf

/-- Generic `hInvKeep` combinator for `InvS u := InvMem u.mem ∧ PredFs u.fs`
    (matching `ExtraGhostReplay.block617TransferFixedG_of_extraRow`). -/
theorem invS_mem_fs_keepsFrozen {InvMem : Memory → Prop} {PredFs : FsState → Prop}
    (hMemKeep : ∀ m1 m2 : Memory, InvMem m1 → m1.KeepsFrozen m2 → InvMem m2) :
    ∀ u v : State, (InvMem u.mem ∧ PredFs u.fs) → u.mem.KeepsFrozen v.mem → v.fs = u.fs →
      (InvMem v.mem ∧ PredFs v.fs) := by
  intro u v ⟨hmem, hfs⟩ hkf hvfs
  exact ⟨hMemKeep u.mem v.mem hmem hkf, hvfs ▸ hfs⟩

/-! ## 3. Concrete Cutover-2 `c2TimeMpl` & Shared `timeMultiLib` Facts -/

/-! ### Cutover-2 `.rodata.lib2` Local Data-Symbol Offsets (Gate ELF `50066cbd…98ce`)

The 4 anonymous/section-local `timeMultiLib` RO data symbols (`str1.1`, `.Lanon.148`,
`.Lanon.150`, `.Lanon.678`) are stripped from `.symtab` by `ld.lld` and therefore expressed
relative to the generator-emitted `.rodata.lib2` anchors (`c2FromUtf8TableAddr`,
`c2DurationSinceCst16Addr`, `c2Lib2RoLo`). Their encoded `adrp + add` / `ldr` words in `.text.lib2`
are kernel-verified against `Tie.f3TrialRxProg` via `checkProgCodeSubslice` (`hRxDur` / `hRxAdd`). -/

/-- `rust_time:.rodata.str1.1+0x0` (`73` B, `align = 1`): placed immediately before
    `c2FromUtf8TableAddr` in `.rodata.lib2` on gate ELF `50066cbd`. Not referenced directly by
    code instructions in blocks `0..2` (referenced only by `.data.rel.ro..Lanon.150` `+0` `abs64`). -/
abbrev c2TimeRoStr1Addr : BitVec 64 := c2FromUtf8TableAddr - 73#64

/-- `rust_time:.rodata..Lanon.148` (`25` B, `align = 1`): placed immediately after the `16`-byte
    `c2DurationSinceCst16Addr` mask in `.rodata.lib2` on gate ELF `50066cbd`. Encoded in block `0`
    (`sub_timespec`, inside `durationSinceSubProg c2TimeMpl`) at `+216` (`adrpHi21`) and `+220`
    (`addLo12`), pinned by `hRxDur`. -/
abbrev c2TimeRoLanon148Addr : BitVec 64 := c2DurationSinceCst16Addr + 16#64

/-- `rust_time:.data.rel.ro..Lanon.150` (`24` B, `align = 8`, `abs64` reloc at `+0` to `str1.1`):
    placed at `c2Lib2RoLo + 48` in `.rodata.lib2` on gate ELF `50066cbd`. Encoded in block `0`
    (`sub_timespec`, inside `durationSinceSubProg c2TimeMpl`) at `+224` (`adrpHi21`) and `+228`
    (`addLo12`), pinned by `hRxDur`. -/
abbrev c2TimeDataRelRoLanon150Addr : BitVec 64 := c2Lib2RoLo + 48#64

/-- `rust_time:.rodata..Lanon.678` (`45` B, `align = 1`): placed immediately after `.Lanon.148`
    (`+16 + 25 = +41` from `c2DurationSinceCst16Addr`, last in `.rodata.lib2`) on gate ELF
    `50066cbd`. Encoded in block `2` (`SystemTime::add`, inside `timeAddSubProg c2TimeMpl`) at
    `+76` (`adrpHi21`) and `+80` (`addLo12`), pinned by `hRxAdd`. -/
abbrev c2TimeRoLanon678Addr : BitVec 64 := c2DurationSinceCst16Addr + 41#64

/-- Concrete Cutover-2 `Obj.MultiPlacement` for `VerifiedLibraries.RustStd.timeMultiLib`
    (blocks: `Timespec::sub_timespec`, `SystemTime::duration_since`, `SystemTime::add`), shared by
    the `duration_since` and `SystemTime::add` C2 glue modules. -/
@[expose] noncomputable def c2TimeMpl : Obj.MultiPlacement :=
  mkTimeMpl
    c2SubTimespecAddr c2DurationSinceAddr c2TimeAddAddr
    c2DurationSinceCst16Addr
    c2TimeRoStr1Addr c2TimeRoLanon148Addr c2TimeDataRelRoLanon150Addr c2TimeRoLanon678Addr
    (libsignalSessionLib.resolve cliElfMultiPlacement lsExpectFailedSymC2)

theorem c2TimeMpl_base0 : c2TimeMpl.base 0 = c2SubTimespecAddr := rfl

theorem c2TimeMpl_base1 : c2TimeMpl.base 1 = c2DurationSinceAddr := rfl

theorem c2TimeMpl_base2 : c2TimeMpl.base 2 = c2TimeAddAddr := rfl

theorem c2TimeMpl_fnAddr_timeAdd :
    timeMultiLib.fnAddr c2TimeMpl timeAddSym = c2TimeAddAddr :=
  timeAddEntryAddr_eq_base2 c2TimeMpl

/-- Exact `hTargetEq` premise of `TimeAddGhostReplays.timeAddGhost_rowOk` at `c2TimeMpl` from
    `hResAdd : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr`. -/
theorem c2_timeAdd_hTargetEq {mpl : Obj.MultiPlacement}
    (hResAdd : libsignalSessionLib.resolve mpl lsTimeAddSym = c2TimeAddAddr) :
    libsignalSessionLib.resolve mpl lsTimeAddSym =
      timeMultiLib.fnAddr c2TimeMpl timeAddSym := by
  rw [hResAdd, c2TimeMpl_fnAddr_timeAdd]

/-- Exact `hRho` premise consumed by `DurCst16.f3CodeInv_roDataAt_timeCst16` and
    `DurCst16.durationSince_hRo_of_f3CodeInv`. -/
theorem c2TimeMpl_hRho :
    c2TimeMpl.ρ timeRodataCst16Sym = c2DurationSinceCst16Addr :=
  mkTimeMpl_rho_cst16 _ _ _ _ _ _ _ _ _

/-- Panic-stub target of `SystemTime::add` under `c2TimeMpl` equals `cliElfMultiPlacement`'s
    resolution of `lsExpectFailedSymC2`. -/
theorem c2TimeMpl_expectFailedStubPc :
    timeAddExpectFailedStubPc c2TimeMpl =
      libsignalSessionLib.resolve cliElfMultiPlacement lsExpectFailedSymC2 :=
  mkTimeMpl_expectFailedStubPc _ _ _ _ _ _ _ _ _

/-- For any `mpl` satisfying `libsignalSessionLib.LinkedAt cliElfBytes mpl`,
    `timeAddExpectFailedStubPc c2TimeMpl` equals `libsignalSessionLib.resolve mpl lsExpectFailedSymC2`
    (`0` pending C2 hypotheses — holds both pre-T4 and post-T4). -/
theorem c2TimeMpl_expectFailedStubPc_of_linkedAt {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    timeAddExpectFailedStubPc c2TimeMpl =
      libsignalSessionLib.resolve mpl lsExpectFailedSymC2 := by
  have huniq := cliElf_linkedAt_unique hLs
  have hmem : lsExpectFailedSymC2 ∈ lsInternedMultiLib.names :=
    decide_eq_true_eq.mp (by rfl_kernel)
  exact c2TimeMpl_expectFailedStubPc.trans (huniq.2.1 lsExpectFailedSymC2 hmem).symm

/-- Kernel-checked `timeMultiLib.checkPlaceable c2TimeMpl = true`. -/
theorem c2TimeMpl_checkPlaceable :
    timeMultiLib.checkPlaceable c2TimeMpl = true := by
  rfl_kernel

/-- Exact `hpl` premise consumed by `durationSinceGhost_rowSpecOk`, `durationSinceGhost_rowOk`,
    `timeAddGhost_rowSpecOk`, and `timeAddGhost_rowOk` (`0` pending hypotheses). -/
theorem c2TimeMpl_placeable :
    timeMultiLib.Placeable c2TimeMpl :=
  timeMultiLib_placeable_of_check c2TimeMpl_checkPlaceable

/-- Exact `hb1` premise consumed by `durationSinceGhost_rowSpecOk` and `durationSinceGhost_rowOk`
    (`0` pending hypotheses). -/
theorem c2TimeMpl_hb1 :
    c2TimeMpl.base 1 = c2TimeMpl.base 0 + subTimespecByteLen := by
  decide +kernel

/-- Unconditional Cutover-2 `GhostRowSpecOk` discharge for `lsDurationSinceSym` at `c2TimeMpl`
    (`0` pending hypotheses). -/
theorem c2_durationSinceGhost_rowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsDurationSinceSym (durationSinceGhost c2TimeMpl) :=
  durationSinceGhost_rowSpecOk c2TimeMpl c2TimeMpl_placeable c2TimeMpl_hb1

/-! ## 4. Concrete Cutover-2 `durationSinceGhost_rowOk` Premises & Combined Row Theorem -/

theorem lsDurationSinceSym_mem_c2Lib2DehookedSyms :
    lsDurationSinceSym ∈ c2Lib2DehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

/-- Exact `hTargetEq` premise of `durationSinceGhost_rowOk` at `c2TimeMpl` from
    `hResDur : libsignalSessionLib.resolve mpl lsDurationSinceSym = c2DurationSinceAddr`. -/
theorem c2_durationSince_hTargetEq {mpl : Obj.MultiPlacement}
    (hResDur : libsignalSessionLib.resolve mpl lsDurationSinceSym = c2DurationSinceAddr) :
    libsignalSessionLib.resolve mpl lsDurationSinceSym =
      c2TimeMpl.base 0 + subTimespecByteLen := by
  rw [hResDur, ← c2TimeMpl_base1, c2TimeMpl_hb1]

/-- Unconditional hull inclusion `keepR_durationSince c2TimeMpl ⊆ keepLib2Text`. -/
theorem keepR_durationSince_c2_sub_keepLib2Text {pc : BitVec 64}
    (h : keepR_durationSince c2TimeMpl pc = true) :
    keepLib2Text pc = true :=
  keepR_durationSince_sub_interval
    (decide_eq_true_eq.mp (by rfl_kernel))
    (decide_eq_true_eq.mp (by rfl_kernel))
    h

/-- Unconditional hull inclusion `keepR_durationSince c2TimeMpl ⊆ progKeep f3TrialRxProg`. -/
theorem keepR_durationSince_c2_sub_rxProg {pc : BitVec 64}
    (h : keepR_durationSince c2TimeMpl pc = true) :
    progKeep f3TrialRxProg pc = true :=
  keepLib2Text_sub_rxProg (keepR_durationSince_c2_sub_keepLib2Text h)

/-- Exact `hCL` premise of `durationSinceGhost_rowOk` at `c2TimeMpl` from `F3CodeInv` and the
    per-row RX byte-slice premise `hRxDur` (closed by `rfl_kernel` at T4). -/
theorem c2_durationSince_hCL
    (hRxDur : checkProgCodeSubslice f3TrialRxProg (durationSinceSubProg c2TimeMpl) = true)
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u → (durationSinceSubProg c2TimeMpl).CodeLoaded u.mem :=
  fun u hu => codeLoaded_of_checkProgCodeSubslice (hInv u hu).rxCode hRxDur

/-- Exact `hCL` premise of `TimeAddGhostReplays.timeAddGhost_rowOk` at `c2TimeMpl` from `F3CodeInv`
    and the per-row RX byte-slice premise `hRxAdd` (closed by `rfl_kernel` at T4). -/
theorem c2_timeAdd_hCL
    (hRxAdd : checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true)
    {mpl mmpl : Obj.MultiPlacement} {InvS : State → Prop}
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u → (timeAddSubProg c2TimeMpl).CodeLoaded u.mem :=
  fun u hu => codeLoaded_of_checkProgCodeSubslice (hInv u hu).rxCode hRxAdd

/-- Exact `hInvKeep` premise of `durationSinceGhost_rowOk` for `InvS u := F3CodeInv mpl mmpl u.mem`. -/
theorem c2_f3CodeInv_hInvKeep (mpl mmpl : Obj.MultiPlacement) :
    ∀ u v : State, F3CodeInv mpl mmpl u.mem → u.mem.KeepsFrozen v.mem → v.fs = u.fs →
      F3CodeInv mpl mmpl v.mem :=
  invS_mem_keepsFrozen (fun _ _ h hkf => h.of_keepsFrozen hkf)

/-- Exact `hInvKeep` premise of `durationSinceGhost_rowOk` for
    `InvS u := F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs`
    (the state invariant shape of `ExtraGhostReplay.block617TransferFixedG_of_extraRow`). -/
theorem c2_f3CodeInv_and_fs_hInvKeep (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop) :
    ∀ u v : State, (F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs) →
      u.mem.KeepsFrozen v.mem → v.fs = u.fs →
      (F3CodeInv mpl mmpl v.mem ∧ PredFs v.fs) :=
  invS_mem_fs_keepsFrozen (fun _ _ h hkf => h.of_keepsFrozen hkf)

/-- Exact `hKeep` premise of `durationSinceGhost_rowOk` at `c2TimeMpl` (`0` pending C2 hypotheses):
    every caller return address `LsRetAddr624 lr` lies strictly below `c2FirstExternStubAddr ≤
    c2Lib2TextLo`, hence outside `keepR_durationSince c2TimeMpl`. -/
theorem c2_durationSince_hKeep [LibsignalPlacement]
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_durationSince c2TimeMpl lr = false := by
  intro lr hRet
  have hlt := f3LsRetAddr624_lt_firstExternStub hLsLsmpl hRet
  have hlo : c2FirstExternStubAddr.toNat ≤ c2Lib2TextLo.toNat :=
    decide_eq_true_eq.mp (by rfl_kernel)
  cases hk : keepR_durationSince c2TimeMpl lr
  · rfl
  · have hlib2 := keepR_durationSince_c2_sub_keepLib2Text hk
    unfold keepLib2Text at hlib2
    rw [decide_eq_true_eq] at hlib2
    omega

/-- Exact `hRealHullNoExt` premise of `durationSinceGhost_rowOk` at `c2TimeMpl` from
    `C2ExternTableFacts mpl`. -/
theorem c2_durationSince_hRealHullNoExt {mpl mmpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_durationSince c2TimeMpl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  fun W _ hkeep =>
    f3RxSeg_realProg617_externAt_none hExt W (keepR_durationSince_c2_sub_rxProg hkeep)

/-- Combined Cutover-2 `GhostRowOk` discharge for `lsDurationSinceSym` at `c2TimeMpl` for any
    `KeepsFrozen`/`fs`-stable `InvS` projecting to `F3CodeInv mpl mmpl u.mem`. -/
theorem c2_durationSinceGhost_rowOk_of_inv [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hRoSlice : C2RoSliceFacts)
    (hExt : C2ExternTableFacts mpl)
    (hRxDur : checkProgCodeSubslice f3TrialRxProg (durationSinceSubProg c2TimeMpl) = true)
    (hResDur : libsignalSessionLib.resolve mpl lsDurationSinceSym = c2DurationSinceAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v) :
    GhostRowOk mpl mmpl InvS EG lsDurationSinceSym (fun _ => True)
      (durationSinceGhost c2TimeMpl) :=
  durationSinceGhost_rowOk mpl mmpl c2TimeMpl InvS EG
    c2TimeMpl_placeable
    c2TimeMpl_hb1
    (c2_durationSince_hTargetEq hResDur)
    (c2_durationSince_hCL hRxDur hInv)
    (durationSince_hRo_of_f3CodeInv hRoSlice hLs c2TimeMpl_hRho hInv)
    hInvKeep
    (c2_durationSince_hKeep hLsLsmpl)
    (c2_durationSince_hRealHullNoExt hExt)

/-- Combined Cutover-2 `GhostRowOk` discharge for `lsDurationSinceSym` at `c2TimeMpl` for
    `InvS := fun u => F3CodeInv mpl mmpl u.mem`. -/
theorem c2_durationSinceGhost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (EG : CliHooks → String → Option (State → State))
    (hRoSlice : C2RoSliceFacts)
    (hExt : C2ExternTableFacts mpl)
    (hRxDur : checkProgCodeSubslice f3TrialRxProg (durationSinceSubProg c2TimeMpl) = true)
    (hResDur : libsignalSessionLib.resolve mpl lsDurationSinceSym = c2DurationSinceAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk mpl mmpl (fun u => F3CodeInv mpl mmpl u.mem) EG lsDurationSinceSym
      (fun _ => True) (durationSinceGhost c2TimeMpl) :=
  c2_durationSinceGhost_rowOk_of_inv mpl mmpl (fun u => F3CodeInv mpl mmpl u.mem) EG
    hRoSlice hExt hRxDur hResDur hLs hLsLsmpl
    (fun _ h => h)
    (c2_f3CodeInv_hInvKeep mpl mmpl)

/-- Combined Cutover-2 `GhostRowOk` discharge for `lsDurationSinceSym` at `c2TimeMpl` for
    `InvS := fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs`
    (matching `ExtraGhostReplay.block617TransferFixedG_of_extraRow`). -/
theorem c2_durationSinceGhost_rowOk_and_fs [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hRoSlice : C2RoSliceFacts)
    (hExt : C2ExternTableFacts mpl)
    (hRxDur : checkProgCodeSubslice f3TrialRxProg (durationSinceSubProg c2TimeMpl) = true)
    (hResDur : libsignalSessionLib.resolve mpl lsDurationSinceSym = c2DurationSinceAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk mpl mmpl (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs) EG lsDurationSinceSym
      (fun _ => True) (durationSinceGhost c2TimeMpl) :=
  c2_durationSinceGhost_rowOk_of_inv mpl mmpl
    (fun u => F3CodeInv mpl mmpl u.mem ∧ PredFs u.fs) EG
    hRoSlice hExt hRxDur hResDur hLs hLsLsmpl
    (fun _ h => h.1)
    (c2_f3CodeInv_and_fs_hInvKeep mpl mmpl PredFs)

/-- Single-`LinkedAt` (`mpl := lsmpl`) specialization of `c2_durationSinceGhost_rowOk` for
    `InvS := fun u => F3CodeInv lsmpl mmpl u.mem`. -/
theorem c2_durationSinceGhost_rowOk_lsmpl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (EG : CliHooks → String → Option (State → State))
    (hRoSlice : C2RoSliceFacts)
    (hExt : C2ExternTableFacts lsmpl)
    (hRxDur : checkProgCodeSubslice f3TrialRxProg (durationSinceSubProg c2TimeMpl) = true)
    (hResDur : libsignalSessionLib.resolve lsmpl lsDurationSinceSym = c2DurationSinceAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem) EG lsDurationSinceSym
      (fun _ => True) (durationSinceGhost c2TimeMpl) :=
  c2_durationSinceGhost_rowOk lsmpl mmpl EG hRoSlice hExt hRxDur hResDur hLs hLs

/-- Single-`LinkedAt` (`mpl := lsmpl`) specialization of `c2_durationSinceGhost_rowOk_and_fs` for
    `InvS := fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs`
    (matching `ExtraOk` / `ExtraGhostReplay.block617TransferFixedG_of_extraRow`). -/
theorem c2_durationSinceGhost_rowOk_lsmpl_and_fs [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hRoSlice : C2RoSliceFacts)
    (hExt : C2ExternTableFacts lsmpl)
    (hRxDur : checkProgCodeSubslice f3TrialRxProg (durationSinceSubProg c2TimeMpl) = true)
    (hResDur : libsignalSessionLib.resolve lsmpl lsDurationSinceSym = c2DurationSinceAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG lsDurationSinceSym
      (fun _ => True) (durationSinceGhost c2TimeMpl) :=
  c2_durationSinceGhost_rowOk_and_fs lsmpl mmpl PredFs EG hRoSlice hExt hRxDur hResDur hLs hLs

/-- `GhostRowReplayOn` projection of `c2_durationSinceGhost_rowOk_lsmpl_and_fs` for direct
    `ExtraListReplaysOn` / `block617TransferFixedG_of_extraRow` consumption. -/
theorem c2_durationSinceGhost_rowReplayOn_lsmpl_and_fs [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hRoSlice : C2RoSliceFacts)
    (hExt : C2ExternTableFacts lsmpl)
    (hRxDur : checkProgCodeSubslice f3TrialRxProg (durationSinceSubProg c2TimeMpl) = true)
    (hResDur : libsignalSessionLib.resolve lsmpl lsDurationSinceSym = c2DurationSinceAddr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowReplayOn lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      lsDurationSinceSym (fun _ => True) (durationSinceGhost c2TimeMpl) :=
  (c2_durationSinceGhost_rowOk_lsmpl_and_fs mmpl PredFs EG hRoSlice hExt hRxDur hResDur hLs).2

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time
