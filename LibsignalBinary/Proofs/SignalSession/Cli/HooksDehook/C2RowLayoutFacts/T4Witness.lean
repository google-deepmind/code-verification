/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8
import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop
import LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl4
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Cutover-2 (`C2`) T4 Kernel-Closed Layout Witnesses (`C2RowLayoutFacts.T4Witness`)

**Checked by Lean. Untrusted (`Role::Proof`, `CliElfLib`).**

Closes all four Cutover-2 (`C2`, `37 → 27` hooks, `9 → 19` de-hooked symbols, `D-C2f = 2C`,
`50066cbd…98ce`) layout-fact bundles on `cliElfBytes`:
1. **`c2RoSliceFacts : C2RoSliceFacts`:** `rfl_kernel` `.rodata.lib2` segment-slice checks for
   `c2FromUtf8TableAddr` (`UTF8_CHAR_WIDTH`, `256` B) and `c2DurationSinceCst16Addr`
   (`1_u128`, `16` B) on `f3PatchedElf`.
2. **`c2ResolveFacts_of_linkedAt` / `_cliElf` / `_lsmpl`:** Symbol-resolved entry equalities across
   all `10` de-hooked C2 rows under `libsignalSessionLib.LinkedAt cliElfBytes mpl`.
3. **`c2Lib2RxSliceFacts_of_linkedAt` / `_cliElf` / `_lsmpl`:** `rfl_kernel` linear byte-subslice
   checks `checkProgCodeSubslice f3TrialRxProg <rowSubProg> = true` across all `10` de-hooked C2
   rows.
4. **`c2ExternTableFacts_of_linkedAt` / `_cliElf` / `_lsmpl`:** Block-`617` real & ghost `externAt?`
   identities and `.text.lib2` / `.text.b_pre` hull memberships across `c2RxDehookedSyms`.
5. **Bundle-free per-row `GhostRowOk` corollaries (`c2_<row>Ghost_rowOk[_guardOf]_of_linkedAt`):**
   Direct `LinkedAt`-only `GhostRowOk` instantiations across all `10` de-hooked C2 rows at
   `mpl := lsmpl`, eliminating every `C2*Facts` binder from consumer call sites.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open VerifiedLibraries.Musl (memmoveLibcaCalls memmoveLibcaWords)
open CryptoVerification (LibsignalPlacement libsignalSessionExterns lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib lsBlackBoxSym lsDurationSinceSym
   lsFromUtf8Sym lsMemrchrSym lsSharedSecretDropSym lsStaticSecretDropSym lsTimeAddSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3RxWordCount f3StdLayout)
open LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8 (blackBoxU8Words)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (zeroize32Words)
open LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO (coreMemrchrWords)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode (bcmpHullWords memcmpByteLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays
  (bcmpEntryGuard bcmpGhost bcmpHullBase bcmpSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays
  (blackBoxEntryGuard blackBoxGhost blackBoxSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts
  (C2Lib2RxSliceFacts C2ResolveFacts
   c2_bcmpGhost_rowOk c2_bcmpGhost_rowOk_guardOf
   c2_blackBoxGhost_rowOk c2_blackBoxGhost_rowOk_guardOf
   c2_durationSinceGhost_rowOk c2_durationSinceGhost_rowOk_guardOf
   c2_fromUtf8Ghost_rowOk c2_fromUtf8Ghost_rowOk_guardOf
   c2_memmoveGhost_rowOk c2_memmoveGhost_rowOk_guardOf
   c2_memrchrGhost_rowOk c2_memrchrGhost_rowOk_guardOf
   c2_sharedSecretDropGhost_rowOk c2_sharedSecretDropGhost_rowOk_guardOf
   c2_staticSecretDropGhost_rowOk c2_staticSecretDropGhost_rowOk_guardOf
   c2_strlenGhost_rowOk c2_strlenGhost_rowOk_guardOf
   c2_timeAddGhost_rowOk c2_timeAddGhost_rowOk_guardOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (libsignalSessionExterns_resolve_eq_rho resolve_c2RxSym_eq_cliElf_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time (c2TimeMpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
  (externAt?_cliProgExtPlacedAt_617 externAt?_cliProgExtPlacedAt_617_of_nodup_resolve
   ls_block617_externs_eq_libsignalSessionExterns)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostReplays
  (durationSinceEntryGuard durationSinceGhost durationSinceSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays
  (fromUtf8EntryGuard fromUtf8MplGhost fromUtf8SubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8SingleBlock (fromUtf8Placement)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode
  (bPreHullWords bPreMemmoveByteOff bPrePadWord)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays
  (memcpyEntry memmoveEntryGuard memmoveGhost memmoveHullWords memmoveSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrExtraReplays
  (memrchrEntryGuard memrchrGhost memrchrSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
  (f3EmptyMemcpyGhostHookNarrow f3EmptyMemsetGhostHookNarrow)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays
  (sharedSecretDropEntryGuard sharedSecretDropGhost sharedSecretDropHullBase
   sharedSecretDropSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays
  (staticSecretDropEntryGuard staticSecretDropGhost staticSecretDropSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays
  (strlenEntry strlenEntryGuard strlenGhost strlenSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays
  (timeAddEntryGuard timeAddGhost timeAddSubProg)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode (sharedSecretDropHullWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost (sharedSecretDropEntryOff)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData (ls_idsOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts C2RoSliceFacts c2CorePlacedData1 c2TimePlacedData0 keepLib2Text keepTextBPre)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree_eq f3TrialRxWordTree_size)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElf_externs_nodup_of_linkedAt cliElf_linkedAt cliElf_linkedAt_unique
   lsInternedMultiLib lsSharedExterns ls_names_nodup ls_toMultiPlacedLib_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2
  (h2sl_realW_noExtern_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst (hole2_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BatchLDehookedSyms c2BcmpAddr c2BlackBoxAddr c2DurationSinceAddr c2DurationSinceCst16Addr
   c2FromUtf8Addr c2FromUtf8TableAddr c2Lib2DehookedSyms c2MemmoveAddr c2MemrchrAddr
   c2RxDehookedSyms c2SharedSecretDropAddr c2StaticSecretDropAddr c2StrlenAddr c2TimeAddAddr
   wp4MemcpyRealAddr)

/-! ## 1. `.rodata.lib2` Slice Witness (`c2RoSliceFacts`) -/

set_option maxRecDepth 4000000 in
private theorem f3PatchedElf_roSegIdx_lt_bool :
    Nat.blt f3StdLayout.roSegIdx f3PatchedElf.segments.length = true := by
  rfl_kernel

private theorem f3PatchedElf_roSegIdx_lt :
    f3StdLayout.roSegIdx < f3PatchedElf.segments.length :=
  Nat.blt_eq.mp f3PatchedElf_roSegIdx_lt_bool

private noncomputable def f3RoSeg :=
  f3PatchedElf.segments[f3StdLayout.roSegIdx]'f3PatchedElf_roSegIdx_lt

set_option maxRecDepth 4000000 in
private theorem f3RoSeg_perm_eq : f3RoSeg.perm.rwx = Perm.ro := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem f3RoSeg_fromUtf8_ok :
    checkSegSlice f3RoSeg f3RoSeg.bytes.length c2FromUtf8TableAddr c2CorePlacedData1 = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem f3RoSeg_durationSince_ok :
    checkSegSlice f3RoSeg f3RoSeg.bytes.length c2DurationSinceCst16Addr c2TimePlacedData0 = true := by
  rfl_kernel

theorem c2RoSliceFacts : C2RoSliceFacts where
  fromUtf8Slice :=
    ⟨f3RoSeg, List.getElem?_eq_getElem f3PatchedElf_roSegIdx_lt,
      f3RoSeg_perm_eq, f3RoSeg_fromUtf8_ok⟩
  durationSinceSlice :=
    ⟨f3RoSeg, List.getElem?_eq_getElem f3PatchedElf_roSegIdx_lt,
      f3RoSeg_perm_eq, f3RoSeg_durationSince_ok⟩

/-! ## 2. Symbol-Resolution Witness (`c2ResolveFacts_*`) -/

theorem c2ResolveFacts_of_linkedAt {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    C2ResolveFacts mpl where
  fromUtf8_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  durationSince_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  timeAdd_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  memrchr_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  strlen_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  bcmp_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  memmove_eq :=
    (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
      (by rfl_kernel)
  dalek :=
    { blackBox_eq :=
        (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
          (by rfl_kernel)
      sharedSecretDrop_eq :=
        (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
          (by rfl_kernel)
      staticSecretDrop_eq :=
        (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
          (by rfl_kernel) }

theorem c2ResolveFacts_cliElf : C2ResolveFacts cliElfMultiPlacement :=
  c2ResolveFacts_of_linkedAt cliElf_linkedAt

theorem c2ResolveFacts_lsmpl [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    C2ResolveFacts lsmpl :=
  c2ResolveFacts_of_linkedAt hLs

private theorem resolve_memcpy_eq_of_linkedAt {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    libsignalSessionLib.resolve mpl "memcpy" = wp4MemcpyRealAddr :=
  (resolve_c2RxSym_eq_cliElf_rho hLs (decide_eq_true_eq.mp (by rfl_kernel))).trans
    (by rfl_kernel)

/-! ## 3. RX Byte-Subslice Witness (`c2Lib2RxSliceFacts_*`) -/

private theorem patchCalls_memmoveLibcaCalls_congr
    (words : List (BitVec 32)) (a : BitVec 64)
    (r1 r2 : String → BitVec 64) (h : r1 "memcpy" = r2 "memcpy") :
    Obj.patchCalls memmoveLibcaCalls words a r1 =
      Obj.patchCalls memmoveLibcaCalls words a r2 := by
  unfold Obj.patchCalls
  refine congrArg (fun fn => words.mapIdx fn) (funext fun j => funext fun w => ?_)
  cases hp : ((104 : Nat) == 4 * j)
  · simp [List.find?, hp]
  · simp [List.find?, hp, h]

private theorem memmoveSubProg_eq_closed {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    memmoveSubProg mpl =
      pureWordsProg wp4MemcpyRealAddr
        (bPreHullWords wp4MemcpyRealAddr (fun _ => wp4MemcpyRealAddr) bPrePadWord) := by
  have hm : libsignalSessionLib.resolve mpl "memcpy" = wp4MemcpyRealAddr :=
    resolve_memcpy_eq_of_linkedAt hLs
  unfold memmoveSubProg memmoveHullWords memcpyEntry bPreHullWords
  rw [hm, patchCalls_memmoveLibcaCalls_congr memmoveLibcaWords
    (wp4MemcpyRealAddr + bPreMemmoveByteOff) (libsignalSessionLib.resolve mpl)
    (fun _ => wp4MemcpyRealAddr) hm]

set_option maxRecDepth 4000000 in
private theorem c2_rxSlice_fromUtf8_ok :
    checkProgCodeSubslice f3TrialRxProg
      (fromUtf8SubProg (fromUtf8Placement c2FromUtf8Addr c2FromUtf8TableAddr)) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_rxSlice_durationSince_ok :
    checkProgCodeSubslice f3TrialRxProg (durationSinceSubProg c2TimeMpl) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_rxSlice_timeAdd_ok :
    checkProgCodeSubslice f3TrialRxProg (timeAddSubProg c2TimeMpl) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_rxSlice_blackBox_ok :
    checkProgCodeSubslice f3TrialRxProg (pureWordsProg c2BlackBoxAddr blackBoxU8Words) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_rxSlice_sharedSecretDrop_ok :
    checkProgCodeSubslice f3TrialRxProg
      (pureWordsProg (c2SharedSecretDropAddr - sharedSecretDropEntryOff)
        sharedSecretDropHullWords) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_rxSlice_staticSecretDrop_ok :
    checkProgCodeSubslice f3TrialRxProg
      (pureWordsProg c2StaticSecretDropAddr zeroize32Words) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_rxSlice_memrchr_ok :
    checkProgCodeSubslice f3TrialRxProg
      (pureWordsProg c2MemrchrAddr coreMemrchrWords) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_rxSlice_strlen_ok :
    checkProgCodeSubslice f3TrialRxProg
      (pureWordsProg c2StrlenAddr muslStrlenWords) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_rxSlice_bcmp_ok :
    checkProgCodeSubslice f3TrialRxProg
      (pureWordsProg (c2BcmpAddr - memcmpByteLen)
        (bcmpHullWords (c2BcmpAddr - memcmpByteLen))) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2_rxSlice_memmove_ok :
    checkProgCodeSubslice f3TrialRxProg
      (pureWordsProg wp4MemcpyRealAddr
        (bPreHullWords wp4MemcpyRealAddr (fun _ => wp4MemcpyRealAddr) bPrePadWord)) = true := by
  rfl_kernel

theorem c2Lib2RxSliceFacts_of_linkedAt {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    C2Lib2RxSliceFacts mpl := by
  have hRes := c2ResolveFacts_of_linkedAt hLs
  refine
    { fromUtf8 := c2_rxSlice_fromUtf8_ok
      durationSince := c2_rxSlice_durationSince_ok
      timeAdd := c2_rxSlice_timeAdd_ok
      blackBox := ?_
      sharedSecretDrop := ?_
      staticSecretDrop := ?_
      memrchr := ?_
      strlen := ?_
      bcmp := ?_
      memmove := ?_ }
  · unfold blackBoxSubProg; rw [hRes.blackBox_eq]; exact c2_rxSlice_blackBox_ok
  · unfold sharedSecretDropSubProg sharedSecretDropHullBase
    rw [hRes.sharedSecretDrop_eq]; exact c2_rxSlice_sharedSecretDrop_ok
  · unfold staticSecretDropSubProg; rw [hRes.staticSecretDrop_eq]; exact c2_rxSlice_staticSecretDrop_ok
  · unfold memrchrSubProg; rw [hRes.memrchr_eq]; exact c2_rxSlice_memrchr_ok
  · unfold strlenSubProg strlenEntry; rw [hRes.strlen_eq]; exact c2_rxSlice_strlen_ok
  · unfold bcmpSubProg bcmpHullBase; rw [hRes.bcmp_eq]; exact c2_rxSlice_bcmp_ok
  · rw [memmoveSubProg_eq_closed hLs]; exact c2_rxSlice_memmove_ok

theorem c2Lib2RxSliceFacts_cliElf : C2Lib2RxSliceFacts cliElfMultiPlacement :=
  c2Lib2RxSliceFacts_of_linkedAt cliElf_linkedAt

theorem c2Lib2RxSliceFacts_lsmpl [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    C2Lib2RxSliceFacts lsmpl :=
  c2Lib2RxSliceFacts_of_linkedAt hLs

/-! ## 4. Block-`617` Extern-Table & Hull Membership Witness (`c2ExternTableFacts_*`) -/

private theorem rxProg_code_len_eq :
    f3TrialRxProg.code.length = 4 * f3RxWordCount := by
  rw [f3TrialRxWordTree_eq, WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size]

private theorem progKeep_f3TrialRxProg_imp_hole2_keepSub {pc : BitVec 64}
    (h : progKeep f3TrialRxProg pc = true) :
    hole2_keepSub pc = true := by
  unfold progKeep at h
  rw [f3TrialRxProg_base, rxProg_code_len_eq, decide_eq_true_eq] at h
  unfold hole2_keepSub
  rw [decide_eq_true_eq]
  have hbase : f3RxSegBase = 0x469000#64 := rfl
  have hlen : 4 * f3RxWordCount = 0x6000 := rfl
  rw [hbase, hlen] at h
  generalize hd : pc - 0x469000#64 = d at h
  have hpc_eq : pc = 0x469000#64 + d := by subst hd; bv_omega
  have h9000 : (0x469000#64 : BitVec 64).toNat = 0x469000 := rfl
  have htoNat : pc.toNat = 0x469000 + d.toNat := by
    rw [hpc_eq, BitVec.toNat_add, h9000, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem findSome?_eq_none_of_forall_ne {α β γ : Type} [BEq β] [LawfulBEq β]
    {xs : List α} {f : α → β} (g : α → Option γ) {v : β}
    (hne : ∀ e ∈ xs, f e ≠ v) :
    (xs.findSome? fun e => if f e == v then g e else none) = none := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have ha : (f a == v) = false := beq_eq_false_iff_ne.mpr (hne a (.head _))
    simp only [List.findSome?_cons, ha, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun e he => hne e (.tail _ he))

set_option maxRecDepth 4000000 in
private theorem sharedExterns_lookup_ok :
    libsignalSessionExterns =
        lsSharedExterns.map (fun idx => lsInternedMultiLib.names.getD idx "") ∧
      (lsSharedExterns.all fun idx =>
        Nat.blt idx lsInternedMultiLib.names.length &&
          (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none)) = true :=
  ⟨by rfl_kernel, by rfl_kernel⟩

private theorem resolve_extern_eq_cliElf_rho {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {e : String} (he : e ∈ libsignalSessionExterns) :
    libsignalSessionLib.resolve mpl e = cliElfMultiPlacement.ρ e := by
  have hres_rho := libsignalSessionExterns_resolve_eq_rho mpl e he
  have huniq := (cliElf_linkedAt_unique hLs).2.2.1
  rw [sharedExterns_lookup_ok.1, List.mem_map] at he
  rcases he with ⟨idx, hidx, rfl⟩
  have hall := List.all_eq_true.mp sharedExterns_lookup_ok.2 idx hidx
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hall
  have hmem : lsInternedMultiLib.names.getD idx "" ∈ lsInternedMultiLib.names := by
    rw [Obj.Interned.getD_of_lt hall.1]
    exact List.getElem_mem hall.1
  have hnone :
      Obj.lookupBlockSym (lsInternedMultiLib.names.getD idx "") libsignalSessionLib.blocks =
        none := by
    rw [ls_toMultiPlacedLib_eq,
      Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hall.1]
    exact hall.2
  exact hres_rho.trans (huniq _ hmem hnone)

set_option maxRecDepth 4000000 in
private theorem externs_in_rx_sub_c2RxDehooked :
    (libsignalSessionExterns.all fun e =>
      let a := (cliElfMultiPlacement.ρ e).toNat
      !(Nat.ble 0x469000 a && Nat.blt a 0x46f000) || c2RxDehookedSyms.contains e) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2RxDehookedSyms_sub_externs :
    (c2RxDehookedSyms.all fun s => libsignalSessionExterns.contains s) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2Lib2DehookedSyms_in_keepLib2Text :
    (c2Lib2DehookedSyms.all fun s =>
      c2RxDehookedSyms.contains s && keepLib2Text (cliElfMultiPlacement.ρ s)) = true := by
  rfl_kernel

set_option maxRecDepth 4000000 in
private theorem c2BatchLDehookedSyms_in_keepTextBPre :
    (c2BatchLDehookedSyms.all fun s =>
      c2RxDehookedSyms.contains s && keepTextBPre (cliElfMultiPlacement.ρ s)) = true := by
  rfl_kernel

theorem c2ExternTableFacts_of_linkedAt {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    C2ExternTableFacts mpl where
  realRxNoExtern mmpl W {pc} hpc :=
    h2sl_realW_noExtern_keepSub hLs mmpl W pc (progKeep_f3TrialRxProg_imp_hole2_keepSub hpc)
  ghostRxNoExternOffEntries extFn W {pc} hpc hnotin := by
    have hk := progKeep_f3TrialRxProg_imp_hole2_keepSub hpc
    unfold hole2_keepSub at hk
    rw [decide_eq_true_eq] at hk
    rw [externAt?_cliProgExtPlacedAt_617, ls_block617_externs_eq_libsignalSessionExterns]
    refine findSome?_eq_none_of_forall_ne (extFn W) fun e he hres_eq => ?_
    have hrho : cliElfMultiPlacement.ρ e = pc :=
      (resolve_extern_eq_cliElf_rho hLs he).symm.trans hres_eq
    have hall := List.all_eq_true.mp externs_in_rx_sub_c2RxDehooked e he
    dsimp only at hall
    rw [hrho, Nat.ble_eq.mpr hk.1, Nat.blt_eq.mpr hk.2] at hall
    simp only [Bool.true_and, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hall
    exact hnotin (hres_eq ▸ List.mem_map_of_mem hall)
  ghostRxEntry extFn W {sym} hsym := by
    have hMemExt : sym ∈ libsignalSessionExterns :=
      List.contains_iff_mem.mp (List.all_eq_true.mp c2RxDehookedSyms_sub_externs sym hsym)
    have hMem617 : sym ∈ (libsignalSessionLib.blockLib 617).text.externs := by
      rwa [ls_block617_externs_eq_libsignalSessionExterns]
    have hMapEq :
        (libsignalSessionLib.blockLib 617).text.externs.map (libsignalSessionLib.resolve mpl) =
          libsignalSessionExterns.map mpl.ρ := by
      rw [ls_block617_externs_eq_libsignalSessionExterns]
      exact List.map_congr_left (libsignalSessionExterns_resolve_eq_rho mpl)
    have hNodup :
        ((libsignalSessionLib.blockLib 617).text.externs.map
          (libsignalSessionLib.resolve mpl)).Nodup := by
      rw [hMapEq]
      exact cliElf_externs_nodup_of_linkedAt hLs
    exact externAt?_cliProgExtPlacedAt_617_of_nodup_resolve hMem617 hNodup W
  lib2InKeep {sym} hsym := by
    have hall := Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp c2Lib2DehookedSyms_in_keepLib2Text sym hsym)
    have hmem : sym ∈ c2RxDehookedSyms := List.contains_iff_mem.mp hall.1
    rw [resolve_c2RxSym_eq_cliElf_rho hLs hmem]
    exact hall.2
  batchLInKeep {sym} hsym := by
    have hall := Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp c2BatchLDehookedSyms_in_keepTextBPre sym hsym)
    have hmem : sym ∈ c2RxDehookedSyms := List.contains_iff_mem.mp hall.1
    rw [resolve_c2RxSym_eq_cliElf_rho hLs hmem]
    exact hall.2

theorem c2ExternTableFacts_cliElf : C2ExternTableFacts cliElfMultiPlacement :=
  c2ExternTableFacts_of_linkedAt cliElf_linkedAt

theorem c2ExternTableFacts_lsmpl [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    C2ExternTableFacts lsmpl :=
  c2ExternTableFacts_of_linkedAt hLs

/-! ## 5. Bundle-Free Per-Row `GhostRowOk` Corollaries at `mpl := lsmpl` -/

theorem c2_fromUtf8Ghost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsFromUtf8Sym =
      some (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsFromUtf8Sym
      (fromUtf8EntryGuard lsmpl)
      (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr) :=
  c2_fromUtf8Ghost_rowOk mmpl PredFs g extra hLook
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs) c2RoSliceFacts
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_fromUtf8Ghost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsFromUtf8Sym =
      some (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr))
    (hGuard : ∀ s0 : State, guardOf lsFromUtf8Sym s0 → fromUtf8EntryGuard lsmpl s0)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsFromUtf8Sym
      (guardOf lsFromUtf8Sym)
      (fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr) :=
  c2_fromUtf8Ghost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs) c2RoSliceFacts
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_durationSinceGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsDurationSinceSym
      (durationSinceEntryGuard lsmpl)
      (durationSinceGhost c2TimeMpl) :=
  c2_durationSinceGhost_rowOk mmpl PredFs g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs) c2RoSliceFacts
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_durationSinceGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsDurationSinceSym
      (guardOf lsDurationSinceSym)
      (durationSinceGhost c2TimeMpl) :=
  c2_durationSinceGhost_rowOk_guardOf mmpl PredFs guardOf g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs) c2RoSliceFacts
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_timeAddGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsTimeAddSym
      (timeAddEntryGuard lsmpl)
      (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk mmpl PredFs g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_timeAddGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsTimeAddSym
      (guardOf lsTimeAddSym)
      (timeAddGhost c2TimeMpl) :=
  c2_timeAddGhost_rowOk_guardOf mmpl PredFs guardOf g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_blackBoxGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsBlackBoxSym = some (blackBoxGhost lsmpl mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsBlackBoxSym
      (blackBoxEntryGuard lsmpl)
      (blackBoxGhost lsmpl mmpl) :=
  c2_blackBoxGhost_rowOk mmpl PredFs g extra hLook
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_blackBoxGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsBlackBoxSym = some (blackBoxGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf lsBlackBoxSym s0 → blackBoxEntryGuard lsmpl s0)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsBlackBoxSym
      (guardOf lsBlackBoxSym)
      (blackBoxGhost lsmpl mmpl) :=
  c2_blackBoxGhost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_sharedSecretDropGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsSharedSecretDropSym = some (sharedSecretDropGhost lsmpl mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsSharedSecretDropSym
      (sharedSecretDropEntryGuard lsmpl)
      (sharedSecretDropGhost lsmpl mmpl) :=
  c2_sharedSecretDropGhost_rowOk mmpl PredFs g extra hLook
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_sharedSecretDropGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsSharedSecretDropSym = some (sharedSecretDropGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf lsSharedSecretDropSym s0 → sharedSecretDropEntryGuard lsmpl s0)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsSharedSecretDropSym
      (guardOf lsSharedSecretDropSym)
      (sharedSecretDropGhost lsmpl mmpl) :=
  c2_sharedSecretDropGhost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_staticSecretDropGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsStaticSecretDropSym = some (staticSecretDropGhost lsmpl mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsStaticSecretDropSym
      (staticSecretDropEntryGuard lsmpl)
      (staticSecretDropGhost lsmpl mmpl) :=
  c2_staticSecretDropGhost_rowOk mmpl PredFs g extra hLook
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_staticSecretDropGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup lsStaticSecretDropSym = some (staticSecretDropGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf lsStaticSecretDropSym s0 → staticSecretDropEntryGuard lsmpl s0)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsStaticSecretDropSym
      (guardOf lsStaticSecretDropSym)
      (staticSecretDropGhost lsmpl mmpl) :=
  c2_staticSecretDropGhost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_memrchrGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsMemrchrSym
      (memrchrEntryGuard lsmpl)
      (memrchrGhost lsmpl mmpl) :=
  c2_memrchrGhost_rowOk mmpl PredFs g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_memrchrGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      lsMemrchrSym
      (guardOf lsMemrchrSym)
      (memrchrGhost lsmpl mmpl) :=
  c2_memrchrGhost_rowOk_guardOf mmpl PredFs guardOf g extra
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_strlenGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "strlen" = some (strlenGhost lsmpl mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "strlen"
      (strlenEntryGuard lsmpl)
      (strlenGhost lsmpl mmpl) :=
  c2_strlenGhost_rowOk mmpl PredFs g extra hLook
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_strlenGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "strlen" = some (strlenGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "strlen" s0 → strlenEntryGuard lsmpl s0)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "strlen"
      (guardOf "strlen")
      (strlenGhost lsmpl mmpl) :=
  c2_strlenGhost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_bcmpGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "bcmp" = some (bcmpGhost lsmpl mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "bcmp"
      (bcmpEntryGuard lsmpl)
      (bcmpGhost lsmpl mmpl) :=
  c2_bcmpGhost_rowOk mmpl PredFs g extra hLook
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_bcmpGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "bcmp" = some (bcmpGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "bcmp" s0 → bcmpEntryGuard lsmpl s0)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "bcmp"
      (guardOf "bcmp")
      (bcmpGhost lsmpl mmpl) :=
  c2_bcmpGhost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_memmoveGhost_rowOk_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "memmove" = some (memmoveGhost lsmpl mmpl))
    (hGMemcpy : g.memcpy = none ∨ g.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : g.memset = none ∨ g.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "memmove"
      (memmoveEntryGuard lsmpl)
      (memmoveGhost lsmpl mmpl) :=
  c2_memmoveGhost_rowOk mmpl PredFs g extra hLook hGMemcpy hGMemset
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

theorem c2_memmoveGhost_rowOk_guardOf_of_linkedAt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (guardOf : String → State → Prop)
    (g : CliGhostHooks) (extra : ExtraGhostTable)
    (hLook : extra.lookup "memmove" = some (memmoveGhost lsmpl mmpl))
    (hGuard : ∀ s0 : State, guardOf "memmove" s0 → memmoveEntryGuard lsmpl s0)
    (hGMemcpy : g.memcpy = none ∨ g.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : g.memset = none ∨ g.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs)
      (fun W' => cliGhostExternsWithExtra g extra (cliExternsPlaced mmpl W'))
      "memmove"
      (guardOf "memmove")
      (memmoveGhost lsmpl mmpl) :=
  c2_memmoveGhost_rowOk_guardOf mmpl PredFs guardOf g extra hLook hGuard hGMemcpy hGMemset
    (c2ResolveFacts_lsmpl hLs) (c2Lib2RxSliceFacts_lsmpl hLs)
    (c2ExternTableFacts_lsmpl hLs) hLs

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness
