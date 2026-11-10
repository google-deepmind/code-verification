/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.F3LayoutData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks -- proof-setup: allow-public-import
public import ProofLib.ProgramReflection -- proof-setup: allow-public-import

/-!
# Startup `StdMainEntryLr` Dischargers & Guarded-Harness Producer for `F3C2EntryGuard` (`ElfSlicesPqOomC2EntryGuardLr`)

Delivers `api_A.md` §5R.c + H-REV4 `§5R verdict` (`C4`–`C6`) with `0` hex literals and `0` imports
from `C2RowLayoutFacts.Dalek` or `T4Witness` (resolving all 8 external symbols directly from
`ElfCodeMatchesPlaced.f3CliElf_libsignal_linkedAt_unique` and `lsPlacedStubPairs`):

1. `f3FromUtf8EntryGuard_of_stdMainEntryLr` (`C5`): derives `resolve mpl lsFromUtf8Sym` from `hLs`
   and `s0.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64` directly from
   `hlr : StdMainEntryLr f3StdLayout s0`.
2. `c2GuardOf_of_stdMainEntryLr`, `extraEntryGuard_c2GuardOf_of_stdMainEntryLr`,
   `extraEntryGuard_h2k_of_stdMainEntryLr`, and `f3C2EntryGuard_of_stdMainEntryLr`.
3. `cliElf_f3MuslHarness_c2EntryGuard_of_linkedAt` (`C6`): drop-in guarded-harness producer for
   `ElfSlicesPqOomPlacedG.cliElf_f3B2NeedLocksAssumptionsG` (`ElfSlicesPqOomPlacedG.lean:63`),
   ensuring zero new assumptions reach any headline theorem.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomC2EntryGuardLr

open Arm64 Arm64.Obj ProofLib.ProgramReflection
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (
  CliHooks cliElfBytes cliElfImage cliExternsPlaced cliProcessInputs libsignalSessionLib
  lsBlackBoxSym lsFromUtf8Sym lsSharedSecretDropSym lsStaticSecretDropSym
)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3StdLayout fineCostModel)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  MuslHarnessFineNeedLocksGuardedPerInput StdMainEntryLr cliBudgetLimits
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedAt cliStaticsPlacedAt patchElfTokensPlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode (memcmpByteLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap (BcmpEntryGuard keepBcmpHull)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxLrTrap (
  BlackBoxEntryGuard keepBlackBox
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard (
  F3C2EntryGuard c2GuardOf
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (ExtraEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8Ghost (keepFromUtf8Block)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8LrTrap (FromUtf8EntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost (keepBPreHull)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost (keepStrlenRange)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenLrTrap (StrlenEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost (sharedSecretDropEntryOff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap (
  SharedSecretDropEntryGuard StaticSecretDropEntryGuard
  keepSharedSecretDropHull keepStaticSecretDrop
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (
  f3LsSymAddrs lsInternedMultiLib lsPlacedStubPairs lsPlacedStubPairs_eq lsSharedExterns
  ls_idsOk ls_names_nodup ls_sharedExterns_lt ls_toMultiPlacedLib_eq
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced (
  f3CliElf_libsignal_linkedAt_unique f3LsMpl
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (
  F3CodeOk cliElf_f3MuslHarnessLr_of_linkedAt
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard (
  f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)

noncomputable section

private def findStubPosAux (target : String) : List (String × BitVec 64) → Nat → Nat
  | [], acc => acc
  | (nm, _) :: rest, acc =>
    if nm == target then acc else findStubPosAux target rest (acc + 1)

private def stubPosOf (s : String) : Nat :=
  findStubPosAux s lsPlacedStubPairs 0

private def stubAddrOf (s : String) : BitVec 64 :=
  (lsPlacedStubPairs.getD (stubPosOf s) ("", 0#64)).2

private def f3StartupLrVal : BitVec 64 :=
  f3StdLayout.libcStartMainStage2Addr + 56#64

private def checkStubSymB (s : String) : Bool :=
  let pos := stubPosOf s
  let idx := lsSharedExterns.getD pos 0
  let pair := lsPlacedStubPairs.getD pos ("", 0#64)
  Nat.blt pos lsSharedExterns.length &&
  (pair.1 == s) &&
  (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none)

private def checkC2PinsB : Bool :=
  checkStubSymB "memcpy" &&
  checkStubSymB "memmove" &&
  checkStubSymB "bcmp" &&
  checkStubSymB "strlen" &&
  checkStubSymB lsFromUtf8Sym &&
  checkStubSymB lsBlackBoxSym &&
  checkStubSymB lsStaticSecretDropSym &&
  checkStubSymB lsSharedSecretDropSym

private def checkC2LrDisjointB : Bool :=
  (!keepBPreHull (stubAddrOf "memcpy") f3StartupLrVal) &&
  !(f3StartupLrVal == stubAddrOf "memmove") &&
  (!keepBcmpHull (stubAddrOf "bcmp" - memcmpByteLen) f3StartupLrVal) &&
  !(f3StartupLrVal == stubAddrOf "bcmp") &&
  (!keepStrlenRange (stubAddrOf "strlen") f3StartupLrVal) &&
  !(f3StartupLrVal == stubAddrOf "strlen") &&
  (!keepFromUtf8Block (stubAddrOf lsFromUtf8Sym) f3StartupLrVal) &&
  !(f3StartupLrVal == stubAddrOf lsFromUtf8Sym) &&
  (!keepBlackBox (stubAddrOf lsBlackBoxSym) f3StartupLrVal) &&
  !(f3StartupLrVal == stubAddrOf lsBlackBoxSym) &&
  (!keepStaticSecretDrop (stubAddrOf lsStaticSecretDropSym) f3StartupLrVal) &&
  !(f3StartupLrVal == stubAddrOf lsStaticSecretDropSym) &&
  (!keepSharedSecretDropHull (stubAddrOf lsSharedSecretDropSym - sharedSecretDropEntryOff) f3StartupLrVal) &&
  !(f3StartupLrVal == stubAddrOf lsSharedSecretDropSym)

set_option maxRecDepth 400000 in
private theorem checkC2PinsB_ok : checkC2PinsB = true := by
  rfl_kernel

set_option maxRecDepth 400000 in
private theorem checkC2LrDisjointB_ok : checkC2LrDisjointB = true := by
  rfl_kernel

private theorem stubAddrOf_def (s : String) :
    stubAddrOf s = (lsPlacedStubPairs.getD (stubPosOf s) ("", 0#64)).2 :=
  rfl

private theorem toMultiPlacement_rho_eq (mly : Obj.Interned.MultiLayout) (names : List String)
    (s : String) :
    (mly.toMultiPlacement names).ρ s = mly.addrs.getD (names.idxOf s) 0#64 :=
  rfl

private theorem resolve_eq_stubAddrOf {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s : String} (hok : checkStubSymB s = true) :
    libsignalSessionLib.resolve mpl s = stubAddrOf s := by
  have hc :
      (Nat.blt (stubPosOf s) lsSharedExterns.length &&
       ((lsPlacedStubPairs.getD (stubPosOf s) ("", 0#64)).1 == s) &&
       (Obj.Interned.lookupBlockSymId (lsSharedExterns.getD (stubPosOf s) 0)
          lsInternedMultiLib.blocks == none)) = true :=
    hok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
  rcases hc with ⟨⟨hpos_lt, hpair_fst⟩, hblk_none⟩
  set pos := stubPosOf s
  set idx := lsSharedExterns.getD pos 0
  have hidx_eq : idx = lsSharedExterns[pos]'hpos_lt :=
    Obj.Interned.getD_of_lt hpos_lt
  have hidx_lt : idx < lsInternedMultiLib.names.length := by
    have hmem_ext : idx ∈ lsSharedExterns := by
      rw [hidx_eq]
      exact List.getElem_mem hpos_lt
    exact Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hmem_ext)
  have hplen : pos < lsPlacedStubPairs.length := by
    rw [lsPlacedStubPairs_eq, List.length_map]
    exact hpos_lt
  have hpair :
      lsPlacedStubPairs.getD pos ("", 0#64) =
        (lsInternedMultiLib.names.getD idx "", f3LsSymAddrs.getD idx 0#64) := by
    rw [Obj.Interned.getD_of_lt hplen]
    simp only [lsPlacedStubPairs_eq, List.getElem_map, ← hidx_eq]
  have hname_eq : lsInternedMultiLib.names.getD idx "" = s :=
    (congrArg Prod.fst hpair).symm.trans hpair_fst
  have haddr_eq : f3LsSymAddrs.getD idx 0#64 = stubAddrOf s := by
    rw [stubAddrOf_def]
    exact (congrArg Prod.snd hpair).symm
  have hs_mem : s ∈ lsInternedMultiLib.names := by
    rw [← hname_eq, Obj.Interned.getD_of_lt hidx_lt]
    exact List.getElem_mem hidx_lt
  have hnone : Obj.lookupBlockSym s libsignalSessionLib.blocks = none := by
    rw [← hname_eq, ls_toMultiPlacedLib_eq,
      Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hidx_lt]
    exact hblk_none
  have hres_mpl : libsignalSessionLib.resolve mpl s = mpl.ρ s := by
    unfold Obj.MultiPlacedLib.resolve
    rw [hnone]
  have hρ_eq : mpl.ρ s = f3LsMpl.ρ s :=
    (f3CliElf_libsignal_linkedAt_unique hLs).2.2.1 s hs_mem hnone
  have hidxOf : lsInternedMultiLib.names.idxOf s = idx := by
    rw [← hname_eq]
    exact Obj.Interned.idxOf_getD ls_names_nodup hidx_lt
  have hρ_f3 : f3LsMpl.ρ s = f3LsSymAddrs.getD idx 0#64 := by
    unfold f3LsMpl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsMpl
    rw [toMultiPlacement_rho_eq, hidxOf]
    rfl
  exact hres_mpl.trans (hρ_eq.trans (hρ_f3.trans haddr_eq))

private theorem c2Pins_parts :
    checkStubSymB "memcpy" = true ∧
    checkStubSymB "memmove" = true ∧
    checkStubSymB "bcmp" = true ∧
    checkStubSymB "strlen" = true ∧
    checkStubSymB lsFromUtf8Sym = true ∧
    checkStubSymB lsBlackBoxSym = true ∧
    checkStubSymB lsStaticSecretDropSym = true ∧
    checkStubSymB lsSharedSecretDropSym = true := by
  have h :
      (checkStubSymB "memcpy" &&
       checkStubSymB "memmove" &&
       checkStubSymB "bcmp" &&
       checkStubSymB "strlen" &&
       checkStubSymB lsFromUtf8Sym &&
       checkStubSymB lsBlackBoxSym &&
       checkStubSymB lsStaticSecretDropSym &&
       checkStubSymB lsSharedSecretDropSym) = true :=
    checkC2PinsB_ok
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem c2LrDisjoint_parts :
    (keepBPreHull (stubAddrOf "memcpy") f3StartupLrVal = false ∧
      f3StartupLrVal ≠ stubAddrOf "memmove") ∧
    (keepBcmpHull (stubAddrOf "bcmp" - memcmpByteLen) f3StartupLrVal = false ∧
      f3StartupLrVal ≠ stubAddrOf "bcmp") ∧
    (keepStrlenRange (stubAddrOf "strlen") f3StartupLrVal = false ∧
      f3StartupLrVal ≠ stubAddrOf "strlen") ∧
    (keepFromUtf8Block (stubAddrOf lsFromUtf8Sym) f3StartupLrVal = false ∧
      f3StartupLrVal ≠ stubAddrOf lsFromUtf8Sym) ∧
    (keepBlackBox (stubAddrOf lsBlackBoxSym) f3StartupLrVal = false ∧
      f3StartupLrVal ≠ stubAddrOf lsBlackBoxSym) ∧
    (keepStaticSecretDrop (stubAddrOf lsStaticSecretDropSym) f3StartupLrVal = false ∧
      f3StartupLrVal ≠ stubAddrOf lsStaticSecretDropSym) ∧
    (keepSharedSecretDropHull (stubAddrOf lsSharedSecretDropSym - sharedSecretDropEntryOff) f3StartupLrVal = false ∧
      f3StartupLrVal ≠ stubAddrOf lsSharedSecretDropSym) := by
  have h :
      ((!keepBPreHull (stubAddrOf "memcpy") f3StartupLrVal) &&
       !(f3StartupLrVal == stubAddrOf "memmove") &&
       (!keepBcmpHull (stubAddrOf "bcmp" - memcmpByteLen) f3StartupLrVal) &&
       !(f3StartupLrVal == stubAddrOf "bcmp") &&
       (!keepStrlenRange (stubAddrOf "strlen") f3StartupLrVal) &&
       !(f3StartupLrVal == stubAddrOf "strlen") &&
       (!keepFromUtf8Block (stubAddrOf lsFromUtf8Sym) f3StartupLrVal) &&
       !(f3StartupLrVal == stubAddrOf lsFromUtf8Sym) &&
       (!keepBlackBox (stubAddrOf lsBlackBoxSym) f3StartupLrVal) &&
       !(f3StartupLrVal == stubAddrOf lsBlackBoxSym) &&
       (!keepStaticSecretDrop (stubAddrOf lsStaticSecretDropSym) f3StartupLrVal) &&
       !(f3StartupLrVal == stubAddrOf lsStaticSecretDropSym) &&
       (!keepSharedSecretDropHull (stubAddrOf lsSharedSecretDropSym - sharedSecretDropEntryOff) f3StartupLrVal) &&
       !(f3StartupLrVal == stubAddrOf lsSharedSecretDropSym)) = true :=
    checkC2LrDisjointB_ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact ⟨⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.1.1.2⟩,
    ⟨h.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.2⟩,
    ⟨h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2⟩,
    ⟨h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2⟩,
    ⟨h.1.1.1.1.1.2, h.1.1.1.1.2⟩,
    ⟨h.1.1.1.2, h.1.1.2⟩,
    ⟨h.1.2, h.2⟩⟩

attribute [local irreducible] stubPosOf stubAddrOf

private theorem hlr_eq_startupLrVal {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    s0.readReg64 .lr = f3StartupLrVal :=
  hlr

/-- Explicit `(C5)` discharger: derives `libsignalSessionLib.resolve mpl lsFromUtf8Sym = stubAddrOf lsFromUtf8Sym`
    from `hLs` (`f3CliElf_libsignal_linkedAt_unique`) and `s0.readReg64 .lr = stage2 + 56#64`
    directly from `hlr : StdMainEntryLr f3StdLayout s0`, closing `FromUtf8GhostReplays.fromUtf8EntryGuard`. -/
theorem f3FromUtf8EntryGuard_of_stdMainEntryLr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays.fromUtf8EntryGuard
      mpl s0 := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays.fromUtf8EntryGuard
    FromUtf8EntryGuard
  rw [resolve_eq_stubAddrOf hLs c2Pins_parts.2.2.2.2.1, hlr_eq_startupLrVal hlr]
  exact c2LrDisjoint_parts.2.2.2.1

/-- Every `cliExtraGhostSyms` entry guard holds at `StdMainEntryLr f3StdLayout s0`. -/
theorem c2GuardOf_of_stdMainEntryLr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {sym : String} {s0 : State}
    (hlr : StdMainEntryLr f3StdLayout s0) :
    c2GuardOf mpl sym s0 := by
  unfold c2GuardOf
  split
  · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays.memmoveEntryGuard
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays.keepR_memmove
      LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays.memcpyEntry
    rw [resolve_eq_stubAddrOf hLs c2Pins_parts.1,
      resolve_eq_stubAddrOf hLs c2Pins_parts.2.1,
      hlr_eq_startupLrVal hlr]
    exact c2LrDisjoint_parts.1
  · split
    · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays.bcmpEntryGuard
        LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays.bcmpHullBase
        BcmpEntryGuard
      rw [resolve_eq_stubAddrOf hLs c2Pins_parts.2.2.1, hlr_eq_startupLrVal hlr]
      exact c2LrDisjoint_parts.2.1
    · split
      · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays.strlenEntryGuard
          LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays.strlenEntry
          StrlenEntryGuard
        rw [resolve_eq_stubAddrOf hLs c2Pins_parts.2.2.2.1, hlr_eq_startupLrVal hlr]
        exact c2LrDisjoint_parts.2.2.1
      · split
        · trivial
        · split
          · exact f3FromUtf8EntryGuard_of_stdMainEntryLr hLs hlr
          · split
            · trivial
            · split
              · trivial
              · split
                · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays.blackBoxEntryGuard
                    BlackBoxEntryGuard
                  rw [resolve_eq_stubAddrOf hLs c2Pins_parts.2.2.2.2.2.1, hlr_eq_startupLrVal hlr]
                  exact c2LrDisjoint_parts.2.2.2.2.1
                · split
                  · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays.staticSecretDropEntryGuard
                      StaticSecretDropEntryGuard
                    rw [resolve_eq_stubAddrOf hLs c2Pins_parts.2.2.2.2.2.2.1, hlr_eq_startupLrVal hlr]
                    exact c2LrDisjoint_parts.2.2.2.2.2.1
                  · split
                    · unfold LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays.sharedSecretDropEntryGuard
                        LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays.sharedSecretDropHullBase
                        SharedSecretDropEntryGuard
                      rw [resolve_eq_stubAddrOf hLs c2Pins_parts.2.2.2.2.2.2.2, hlr_eq_startupLrVal hlr]
                      exact c2LrDisjoint_parts.2.2.2.2.2.2
                    · trivial

/-- Generic `ExtraEntryGuard (c2GuardOf mpl) gh s0` startup discharge for ANY `gh : CliGhostHooks`. -/
theorem extraEntryGuard_c2GuardOf_of_stdMainEntryLr {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (gh : CliGhostHooks) {s0 : State}
    (hlr : StdMainEntryLr f3StdLayout s0) :
    ExtraEntryGuard (c2GuardOf mpl) gh s0 :=
  fun _sym _f _hDom _hLook => c2GuardOf_of_stdMainEntryLr hLs hlr

/-- Exact H-REV4 requested specialization at `gh := h2k_ghFixedK mpl mmpl`. -/
theorem extraEntryGuard_h2k_of_stdMainEntryLr [LibsignalPlacement]
    {mpl : Obj.MultiPlacement} (mmpl : Obj.MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    ExtraEntryGuard (c2GuardOf mpl) (h2k_ghFixedK mpl mmpl) s0 :=
  extraEntryGuard_c2GuardOf_of_stdMainEntryLr hLs (h2k_ghFixedK mpl mmpl) hlr

/-- Combined `F3C2EntryGuard mpl mmpl s0` startup discharge (drop-in replacement at every
    `f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr` call site). -/
theorem f3C2EntryGuard_of_stdMainEntryLr {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    F3C2EntryGuard mpl mmpl s0 :=
  ⟨f3MemsetMemcpyEntryLrFalse_of_stdMainEntryLr hMm hlr,
   fun _sym _hDom => c2GuardOf_of_stdMainEntryLr hLs hlr⟩

/-- `(C6)` `W`-independent `F3C2EntryGuard mpl mmpl` guarded harness directly from
    `StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt` (drop-in producer replacement for
    `ElfMemsetEntryGuard.cliElf_f3MuslHarness_memsetMemcpyLrFalse_of_linkedAt` at
    `ElfSlicesPqOomPlacedG.lean:63`). -/
theorem cliElf_f3MuslHarness_c2EntryGuard_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hmng : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks) :
    MuslHarnessFineNeedLocksGuardedPerInput 80
      (mallocngAddrsOfPlacement mmpl).libc
      (patchElfTokensPlacedAt mpl cliElfImage)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
      (mpl.base 617) cliProcessInputs mmpl cliBudgetLimits fineCostModel.init cliMainStk
      (F3CodeOk mpl mmpl) (cliStaticsPlacedAt mpl)
      (F3C2EntryGuard mpl mmpl) :=
  (cliElf_f3MuslHarnessLr_of_linkedAt hls hmng W).mono_guard
    (fun _ hlr => f3C2EntryGuard_of_stdMainEntryLr hls hmng hlr)

end

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomC2EntryGuardLr
