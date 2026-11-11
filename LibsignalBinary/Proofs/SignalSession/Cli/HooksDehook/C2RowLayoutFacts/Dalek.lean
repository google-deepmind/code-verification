/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import

/-!
# Cutover-2 (`C2`) `.text.lib2` Dalek Entry-Guard Discharges (`C2RowLayoutFacts.Dalek`)

Discharges GK6c §19(d) for the three `.text.lib2` Dalek/generics rows (`lsBlackBoxSym`,
`lsSharedSecretDropSym`, `lsStaticSecretDropSym`):
1. Keyed strictly by symbol name (`libsignalSessionLib.resolve mpl <sym>`) and generator-emitted
   `Wp4LayoutGen` / `Lib2LayoutFacts` constants (`c2BlackBoxAddr`, `c2SharedSecretDropAddr`,
   `c2StaticSecretDropAddr`, `c2Lib2TextLo`, `c2Lib2TextHi`, `f3StartupLrVal`), with zero hex
   address literals.
2. Proves per-row hull inclusion `keepR_<row> mpl pc = true → keepLib2Text pc = true` on the C2
   placement (`C2DalekResolveFacts mpl`), then routes through unconditional
   `Lib2LayoutFacts.f3Lib2EntryGuard_of_startupLr` + `C2ExternTableFacts.lib2InKeep` (and direct
   `C2DalekResolveFacts`-only corollaries) to yield `blackBoxEntryGuard mpl s0`,
   `sharedSecretDropEntryGuard mpl s0`, and `staticSecretDropEntryGuard mpl s0` in the exact shapes
   consumed by `extraEntryGuard_{blackBox,sharedSecretDrop,staticSecretDrop}_arm` and
   `extraEntryGuard_singleton_{blackBox,sharedSecretDrop,staticSecretDrop}`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Dalek

open Arm64 Arm64.Obj ProofLib.ProgramReflection
open CryptoVerification.SignalSession
  (libsignalSessionLib lsBlackBoxSym lsSharedSecretDropSym lsStaticSecretDropSym)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (StdMainEntryLr)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (ExtraEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxLrTrap
  (blackBoxByteLen keepBlackBox keepBlackBox_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays
  (blackBoxEntryGuard blackBoxEntryGuard_iff blackBoxGhost extraEntryGuard_blackBox_arm
   extraEntryGuard_singleton_blackBox keepR_blackBox)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost (sharedSecretDropEntryOff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap
  (keepSharedSecretDropHull keepSharedSecretDropHull_iff keepStaticSecretDrop
   keepStaticSecretDrop_iff sharedSecretDropHullByteLen staticSecretDropByteLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays
  (extraEntryGuard_sharedSecretDrop_arm extraEntryGuard_singleton_sharedSecretDrop
   keepR_sharedSecretDrop sharedSecretDropEntryGuard sharedSecretDropEntryGuard_iff
   sharedSecretDropGhost sharedSecretDropHullBase)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays
  (extraEntryGuard_singleton_staticSecretDrop extraEntryGuard_staticSecretDrop_arm
   keepR_staticSecretDrop staticSecretDropEntryGuard staticSecretDropEntryGuard_iff
   staticSecretDropGhost)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3Lib2EntryGuard_of_startupLr f3Lib2_dehookedSym_in_keepLib2Text
   f3StartupLrVal keepLib2Text)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2BlackBoxAddr c2Lib2DehookedSyms c2Lib2TextHi c2Lib2TextLo c2SharedSecretDropAddr
   c2StaticSecretDropAddr)

/-! ## 1. C2 Resolved-Address Witness & Symbol Membership in `c2Lib2DehookedSyms` -/

/-- C2 resolved-address witness for the 3 `.text.lib2` Dalek rows; closed at T4 on the C2-pinned
    `cliElfBytes` from `cliElf_linkedAt_unique` + `rfl`. -/
structure C2DalekResolveFacts (mpl : Obj.MultiPlacement) : Prop where
  blackBox_eq : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr
  sharedSecretDrop_eq :
    libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr
  staticSecretDrop_eq :
    libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr

theorem lsBlackBoxSym_mem_c2Lib2DehookedSyms :
    lsBlackBoxSym ∈ c2Lib2DehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

theorem lsSharedSecretDropSym_mem_c2Lib2DehookedSyms :
    lsSharedSecretDropSym ∈ c2Lib2DehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

theorem lsStaticSecretDropSym_mem_c2Lib2DehookedSyms :
    lsStaticSecretDropSym ∈ c2Lib2DehookedSyms :=
  decide_eq_true_eq.mp (by rfl_kernel)

/-! ## 2. Per-Row Hull Inclusion `keepR_<row> mpl pc = true → keepLib2Text pc = true` -/

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

/-- Unconditional C2 hull inclusion for `keepBlackBox c2BlackBoxAddr`. -/
theorem keepBlackBox_c2_sub_keepLib2Text {pc : BitVec 64}
    (h : keepBlackBox c2BlackBoxAddr pc = true) :
    keepLib2Text pc = true := by
  rw [keepBlackBox_iff] at h
  exact keepLib2Text_of_sub_lt h
    (decide_eq_true_eq.mp (by rfl_kernel))
    (decide_eq_true_eq.mp (by rfl_kernel))

/-- Unconditional C2 hull inclusion for `keepSharedSecretDropHull (c2SharedSecretDropAddr - sharedSecretDropEntryOff)`. -/
theorem keepSharedSecretDrop_c2_sub_keepLib2Text {pc : BitVec 64}
    (h : keepSharedSecretDropHull (c2SharedSecretDropAddr - sharedSecretDropEntryOff) pc = true) :
    keepLib2Text pc = true := by
  rw [keepSharedSecretDropHull_iff] at h
  exact keepLib2Text_of_sub_lt h
    (decide_eq_true_eq.mp (by rfl_kernel))
    (decide_eq_true_eq.mp (by rfl_kernel))

/-- Unconditional C2 hull inclusion for `keepStaticSecretDrop c2StaticSecretDropAddr`. -/
theorem keepStaticSecretDrop_c2_sub_keepLib2Text {pc : BitVec 64}
    (h : keepStaticSecretDrop c2StaticSecretDropAddr pc = true) :
    keepLib2Text pc = true := by
  rw [keepStaticSecretDrop_iff] at h
  exact keepLib2Text_of_sub_lt h
    (decide_eq_true_eq.mp (by rfl_kernel))
    (decide_eq_true_eq.mp (by rfl_kernel))

theorem keepR_blackBox_sub_keepLib2Text {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr)
    (pc : BitVec 64) (h : keepR_blackBox mpl pc = true) :
    keepLib2Text pc = true := by
  dsimp only [keepR_blackBox] at h
  rw [hRes] at h
  exact keepBlackBox_c2_sub_keepLib2Text h

theorem keepR_sharedSecretDrop_sub_keepLib2Text {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr)
    (pc : BitVec 64) (h : keepR_sharedSecretDrop mpl pc = true) :
    keepLib2Text pc = true := by
  dsimp only [keepR_sharedSecretDrop, sharedSecretDropHullBase] at h
  rw [hRes] at h
  exact keepSharedSecretDrop_c2_sub_keepLib2Text h

theorem keepR_staticSecretDrop_sub_keepLib2Text {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr)
    (pc : BitVec 64) (h : keepR_staticSecretDrop mpl pc = true) :
    keepLib2Text pc = true := by
  dsimp only [keepR_staticSecretDrop] at h
  rw [hRes] at h
  exact keepStaticSecretDrop_c2_sub_keepLib2Text h

/-! ## 3. Per-Row Entry Guards (`blackBoxEntryGuard`, `sharedSecretDropEntryGuard`, `staticSecretDropEntryGuard`) -/

/-- `blackBoxEntryGuard mpl s0` from `C2ExternTableFacts` + `resolve = c2BlackBoxAddr` + startup `lr`,
    routing directly through `Lib2LayoutFacts.f3Lib2EntryGuard_of_startupLr`. -/
theorem f3BlackBoxEntryGuard_of_startupLr {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr)
    {s0 : State} (hlr : s0.readReg64 .lr = f3StartupLrVal) :
    blackBoxEntryGuard mpl s0 :=
  (blackBoxEntryGuard_iff mpl s0).mpr
    (f3Lib2EntryGuard_of_startupLr hlr
      (f3Lib2_dehookedSym_in_keepLib2Text hExt lsBlackBoxSym_mem_c2Lib2DehookedSyms)
      (keepR_blackBox_sub_keepLib2Text hRes))

/-- `sharedSecretDropEntryGuard mpl s0` from `C2ExternTableFacts` + `resolve = c2SharedSecretDropAddr`
    + startup `lr`, routing directly through `Lib2LayoutFacts.f3Lib2EntryGuard_of_startupLr`. -/
theorem f3SharedSecretDropEntryGuard_of_startupLr {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr)
    {s0 : State} (hlr : s0.readReg64 .lr = f3StartupLrVal) :
    sharedSecretDropEntryGuard mpl s0 :=
  (sharedSecretDropEntryGuard_iff mpl s0).mpr
    (f3Lib2EntryGuard_of_startupLr hlr
      (f3Lib2_dehookedSym_in_keepLib2Text hExt lsSharedSecretDropSym_mem_c2Lib2DehookedSyms)
      (keepR_sharedSecretDrop_sub_keepLib2Text hRes))

/-- `staticSecretDropEntryGuard mpl s0` from `C2ExternTableFacts` + `resolve = c2StaticSecretDropAddr`
    + startup `lr`, routing directly through `Lib2LayoutFacts.f3Lib2EntryGuard_of_startupLr`. -/
theorem f3StaticSecretDropEntryGuard_of_startupLr {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr)
    {s0 : State} (hlr : s0.readReg64 .lr = f3StartupLrVal) :
    staticSecretDropEntryGuard mpl s0 :=
  (staticSecretDropEntryGuard_iff mpl s0).mpr
    (f3Lib2EntryGuard_of_startupLr hlr
      (f3Lib2_dehookedSym_in_keepLib2Text hExt lsStaticSecretDropSym_mem_c2Lib2DehookedSyms)
      (keepR_staticSecretDrop_sub_keepLib2Text hRes))

/-- `C2ExternTableFacts`-free companion for `blackBoxEntryGuard mpl s0` (`keepLib2Text` on entry
    discharged directly from `hRes`). -/
theorem c2BlackBoxEntryGuard_of_resolve {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr)
    {s0 : State} (hlr : s0.readReg64 .lr = f3StartupLrVal) :
    blackBoxEntryGuard mpl s0 := by
  have hsym : keepLib2Text (libsignalSessionLib.resolve mpl lsBlackBoxSym) = true := by
    rw [hRes]; exact decide_eq_true_eq.mp (by rfl_kernel)
  exact (blackBoxEntryGuard_iff mpl s0).mpr
    (f3Lib2EntryGuard_of_startupLr hlr hsym (keepR_blackBox_sub_keepLib2Text hRes))

/-- `C2ExternTableFacts`-free companion for `sharedSecretDropEntryGuard mpl s0`. -/
theorem c2SharedSecretDropEntryGuard_of_resolve {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr)
    {s0 : State} (hlr : s0.readReg64 .lr = f3StartupLrVal) :
    sharedSecretDropEntryGuard mpl s0 := by
  have hsym : keepLib2Text (libsignalSessionLib.resolve mpl lsSharedSecretDropSym) = true := by
    rw [hRes]; exact decide_eq_true_eq.mp (by rfl_kernel)
  exact (sharedSecretDropEntryGuard_iff mpl s0).mpr
    (f3Lib2EntryGuard_of_startupLr hlr hsym (keepR_sharedSecretDrop_sub_keepLib2Text hRes))

/-- `C2ExternTableFacts`-free companion for `staticSecretDropEntryGuard mpl s0`. -/
theorem c2StaticSecretDropEntryGuard_of_resolve {mpl : Obj.MultiPlacement}
    (hRes : libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr)
    {s0 : State} (hlr : s0.readReg64 .lr = f3StartupLrVal) :
    staticSecretDropEntryGuard mpl s0 := by
  have hsym : keepLib2Text (libsignalSessionLib.resolve mpl lsStaticSecretDropSym) = true := by
    rw [hRes]; exact decide_eq_true_eq.mp (by rfl_kernel)
  exact (staticSecretDropEntryGuard_iff mpl s0).mpr
    (f3Lib2EntryGuard_of_startupLr hlr hsym (keepR_staticSecretDrop_sub_keepLib2Text hRes))

/-- `StdMainEntryLr f3StdLayout s0` bundle yielding all 3 Dalek entry guards simultaneously. -/
theorem f3DalekEntryGuards_of_stdMainEntryLr {mpl : Obj.MultiPlacement}
    (hExt : C2ExternTableFacts mpl)
    (hDalek : C2DalekResolveFacts mpl)
    {s0 : State} (hlr : StdMainEntryLr f3StdLayout s0) :
    blackBoxEntryGuard mpl s0 ∧
      sharedSecretDropEntryGuard mpl s0 ∧
      staticSecretDropEntryGuard mpl s0 :=
  ⟨f3BlackBoxEntryGuard_of_startupLr hExt hDalek.blackBox_eq hlr,
   f3SharedSecretDropEntryGuard_of_startupLr hExt hDalek.sharedSecretDrop_eq hlr,
   f3StaticSecretDropEntryGuard_of_startupLr hExt hDalek.staticSecretDrop_eq hlr⟩

/-! ## 4. Direct Instantiations of `extraEntryGuard_*_arm` & `extraEntryGuard_singleton_*` -/

theorem c2_extraEntryGuard_blackBox_arm {mpl : Obj.MultiPlacement}
    {guardOf : String → State → Prop} {s0 : State}
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr)
    (hlr : StdMainEntryLr f3StdLayout s0)
    (hGuardEq : guardOf lsBlackBoxSym s0 ↔ blackBoxEntryGuard mpl s0) :
    guardOf lsBlackBoxSym s0 :=
  extraEntryGuard_blackBox_arm hGuardEq (f3BlackBoxEntryGuard_of_startupLr hExt hRes hlr)

theorem c2_extraEntryGuard_sharedSecretDrop_arm {mpl : Obj.MultiPlacement}
    {guardOf : String → State → Prop} {s0 : State}
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr)
    (hlr : StdMainEntryLr f3StdLayout s0)
    (hGuardEq : guardOf lsSharedSecretDropSym s0 ↔ sharedSecretDropEntryGuard mpl s0) :
    guardOf lsSharedSecretDropSym s0 :=
  extraEntryGuard_sharedSecretDrop_arm hGuardEq
    (f3SharedSecretDropEntryGuard_of_startupLr hExt hRes hlr)

theorem c2_extraEntryGuard_staticSecretDrop_arm {mpl : Obj.MultiPlacement}
    {guardOf : String → State → Prop} {s0 : State}
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr)
    (hlr : StdMainEntryLr f3StdLayout s0)
    (hGuardEq : guardOf lsStaticSecretDropSym s0 ↔ staticSecretDropEntryGuard mpl s0) :
    guardOf lsStaticSecretDropSym s0 :=
  extraEntryGuard_staticSecretDrop_arm hGuardEq
    (f3StaticSecretDropEntryGuard_of_startupLr hExt hRes hlr)

theorem c2_extraEntryGuard_singleton_blackBox {mpl mmpl : Obj.MultiPlacement}
    {guardOf : String → State → Prop} {g : CliGhostHooks} {s0 : State}
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsBlackBoxSym = c2BlackBoxAddr)
    (hlr : StdMainEntryLr f3StdLayout s0)
    (hg : g.extra = [(lsBlackBoxSym, blackBoxGhost mpl mmpl)])
    (hGuardEq : guardOf lsBlackBoxSym s0 ↔ blackBoxEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 :=
  extraEntryGuard_singleton_blackBox hg hGuardEq
    (f3BlackBoxEntryGuard_of_startupLr hExt hRes hlr)

theorem c2_extraEntryGuard_singleton_sharedSecretDrop {mpl mmpl : Obj.MultiPlacement}
    {guardOf : String → State → Prop} {g : CliGhostHooks} {s0 : State}
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsSharedSecretDropSym = c2SharedSecretDropAddr)
    (hlr : StdMainEntryLr f3StdLayout s0)
    (hg : g.extra = [(lsSharedSecretDropSym, sharedSecretDropGhost mpl mmpl)])
    (hGuardEq : guardOf lsSharedSecretDropSym s0 ↔ sharedSecretDropEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 :=
  extraEntryGuard_singleton_sharedSecretDrop hg hGuardEq
    (f3SharedSecretDropEntryGuard_of_startupLr hExt hRes hlr)

theorem c2_extraEntryGuard_singleton_staticSecretDrop {mpl mmpl : Obj.MultiPlacement}
    {guardOf : String → State → Prop} {g : CliGhostHooks} {s0 : State}
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsStaticSecretDropSym = c2StaticSecretDropAddr)
    (hlr : StdMainEntryLr f3StdLayout s0)
    (hg : g.extra = [(lsStaticSecretDropSym, staticSecretDropGhost mpl mmpl)])
    (hGuardEq : guardOf lsStaticSecretDropSym s0 ↔ staticSecretDropEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 :=
  extraEntryGuard_singleton_staticSecretDrop hg hGuardEq
    (f3StaticSecretDropEntryGuard_of_startupLr hExt hRes hlr)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Dalek
