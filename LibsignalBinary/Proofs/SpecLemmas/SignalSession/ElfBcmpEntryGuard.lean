/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.F3LayoutData -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays -- proof-setup: allow-public-import

/-!
# Card L1-c Pilot — `F3CodeInv` / `rxProg` Replay Wrappers & Block-`617` `"bcmp"` Entry Guards (`ElfBcmpEntryGuard`)

Pilot card **`c`** (`L1-c`) companion to `Cli.HooksDehook.BcmpGhostReplays` (parallel to
`ElfMemsetEntryGuard`, while staying in the default `LibsignalBinary` target with `0` `CliElfLib`,
C2, or trusted imports):

1. **Artifact 2b — `F3CodeInv` / `rxProg` `GhostRowReplayOn` Wrappers (`§1`):**
   - Parameterized over `(CodeInv : Memory → Prop)` (`:= StartupStatics.F3CodeInv mpl mmpl` at C2)
     and `(rxProg : Program)` (`:= Tie.f3TrialRxProg` at C2), taking STARTUP's stock-side facts as
     verbatim premises matching `Lib2LayoutFacts.lean` (`origin/stock-lld/c2-startup-dnm` @
     `a230f2671b`: `:114`, `:203`, `:271`, `:316`, `:317`, `:326`, `:338`, `:355`, `:368`, `:374`,
     `:428`, `:444`) so C2 assembly discharges every premise with plain `exact`.
   - Provides both `bcmpGhost_rowReplayOn_f3CodeInv_of_strip` (taking `hStripCL` verbatim from
     `f3CodeInv_rxWords_codeLoaded_strip` `:203–215`) and `bcmpGhost_rowReplayOn_f3CodeInv` (taking
     the 3 slice premises `hAlign`/`hNoWrap`/`hSubSlice` `:208–213` directly on `rxProg` — with
     `hAlign : (bcmpHullBase mpl).toNat % 4 = 0` matching `Program.CodeLoaded.intro` — and
     discharging `hKeep` `:214` automatically via `keepR_bcmp_of_code_offset`).
2. **Artifact 3 — Block-`617` Startup `lr` (`bcmpEntryGuard` / `ExtraEntryGuard`) Discharge (`§2`):**
   - Parameterized over `(keepBPre : BitVec 64 → Bool)` (`:= Lib2LayoutFacts.keepTextBPre` at C2),
     taking `keepTextBPre_startupLr_false` (`:104`), `C2ExternTableFacts.batchLInKeep` (`:334` / `:419`),
     and hull inclusion (`:485` `f3BatchLEntryGuard_of_startupLr`) as verbatim premises at the
     concrete startup return address `f3StdLayout.libcStartMainStage2Addr + 56#64` (`= StdMainEntryLr
     f3StdLayout s0`, `rfl`-equal to `Lib2LayoutFacts.f3StartupLrVal` `:99`).
   - Supplies table-level `ExtraEntryGuard` arm helpers (`extraEntryGuard_bcmp_arm` and
     `extraEntryGuard_singleton_bcmp`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfBcmpEntryGuard

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (StdMainEntryLr)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode (bcmpHullWords)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (
  ExtraEntryGuard GhostRowReplayOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays (
  bcmpHullBase keepR_bcmp bcmpSubProg bcmpSubProg_base bcmpSubProg_code_length
  keepR_bcmp_of_code_offset bcmpSubProg_codeLoaded_of_stripExecOutside
  bcmpGhost bcmpGhostK bcmpEntryGuard bcmpEntryGuard_iff
  bcmpGhost_rowReplayOn bcmpGhostK_rowReplayOn
)

/-! ## 1. Artifact 2b — `F3CodeInv` / `rxProg` `GhostRowReplayOn` Wrappers (Verbatim C2 Premises) -/

/-- Default-target sub-slice `CodeLoaded (stripExecOutside (keepR_bcmp mpl) m)` projection from
    `rxProg.CodeLoaded m` (`:= hInv.rxCode` at `rxProg := Tie.f3TrialRxProg`), mirroring
    `Lib2LayoutFacts.lean @a230f2671b:203-215` (`f3CodeInv_rxWords_codeLoaded_strip`; cf. `:271`
    `hasWords_subslice_of_hasWords` for contiguous multi-block `hasWords` sub-slices) while
    discharging `:214` (`hKeep`) automatically via `keepR_bcmp_of_code_offset`. -/
theorem bcmpSubProg_codeLoaded_strip_of_rxProg
    {mpl : Obj.MultiPlacement} {rxProg : Program} {m : Memory}
    (hRx : rxProg.CodeLoaded m)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :208] f3CodeInv_rxWords_codeLoaded_strip:
    (hAlign : (bcmpHullBase mpl).toNat % 4 = 0)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :209] f3CodeInv_rxWords_codeLoaded_strip:
    (hNoWrap :
      (bcmpHullBase mpl).toNat + 4 * (bcmpHullWords (bcmpHullBase mpl)).length ≤ 2 ^ 64)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :210-213] f3CodeInv_rxWords_codeLoaded_strip
    -- (cf. Lib2LayoutFacts.lean @a230f2671b:271 hasWords_subslice_of_hasWords):
    (hSubSlice : ∀ (i : Nat) (hi : i < (bcmpSubProg mpl).code.length),
      ∃ (j : Nat) (hj : j < rxProg.code.length),
        bcmpHullBase mpl + BitVec.ofNat 64 i = rxProg.base + BitVec.ofNat 64 j ∧
        (bcmpSubProg mpl).code[i] = rxProg.code[j]) :
    (bcmpSubProg mpl).CodeLoaded (stripExecOutside (keepR_bcmp mpl) m) := by
  have hLen4 : 4 * (bcmpHullWords (bcmpHullBase mpl)).length = (bcmpSubProg mpl).code.length := by
    rw [bcmpSubProg_code_length]
    exact LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap.four_mul_bcmpHullWords_length
      (bcmpHullBase mpl) (fun _ => bcmpHullBase mpl)
  have hAlignBase : (bcmpSubProg mpl).base.toNat % 4 = 0 := hAlign
  refine Program.CodeLoaded.intro hAlignBase (by rw [bcmpSubProg_base, ← hLen4]; exact hNoWrap) ?_
  intro i hi
  obtain ⟨j, hj, haddr_eq, hbyte_eq⟩ := hSubSlice i hi
  have hk_i : keepR_bcmp mpl ((bcmpSubProg mpl).base + BitVec.ofNat 64 i) = true :=
    keepR_bcmp_of_code_offset mpl hi
  dsimp only [bcmpSubProg_base] at hk_i ⊢
  have hr_rx := hRx.byte_eq j hj
  have hp_rx := hRx.perm_eq j hj
  have hlf_rx := hRx.isLazyFree_eq j hj
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hk_i, ProofLib.strip_isLazyFree]
  rw [haddr_eq, hr_rx, hbyte_eq, hp_rx, hlf_rx]
  exact ⟨rfl, rfl, rfl⟩

/-- **Artifact 2b (direct `hStripCL` form):** `GhostRowReplayOn` over
    `(fun u => CodeInv u.mem ∧ PredFs u.fs)` (`CodeInv := StartupStatics.F3CodeInv mpl mmpl`,
    `rxProg := Tie.f3TrialRxProg`), consuming `f3CodeInv_rxWords_codeLoaded_strip`'s conclusion
    (`Lib2LayoutFacts.lean @a230f2671b:203-215`) directly alongside `:114`, `:316`/`:317`/`:338`
    (cf. `:428` `StepsVisitedIn`, `:444` `f3RxSeg_steps_realW_of_visitedIn`), `:326`/`:355`, and
    `:368`/`:374`. -/
theorem bcmpGhost_rowReplayOn_f3CodeInv_of_strip
    (mpl mmpl : Obj.MultiPlacement)
    (CodeInv : Memory → Prop)
    (PredFs : FsState → Prop)
    (rxProg : Program)
    (EG : CliHooks → String → Option (State → State))
    (hInvKf : ∀ m m' : Memory, CodeInv m → m.KeepsFrozen m' → CodeInv m')
    -- [Lib2LayoutFacts.lean @a230f2671b:203-215] f3CodeInv_rxWords_codeLoaded_strip
    -- (cf. Lib2LayoutFacts.lean @a230f2671b:271 hasWords_subslice_of_hasWords):
    (hStripCL : ∀ m : Memory, CodeInv m →
      (bcmpSubProg mpl).CodeLoaded (stripExecOutside (keepR_bcmp mpl) m))
    -- [Lib2LayoutFacts.lean @a230f2671b:114] keepTextBPre_sub_rxProg (composed with keepR_bcmp ⊆ keepTextBPre):
    (hSubRx : ∀ {pc : BitVec 64}, keepR_bcmp mpl pc = true → progKeep rxProg pc = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :317, :338] C2ExternTableFacts.realRxNoExtern /
    -- f3RxSeg_realProg617_externAt_none (cf. :428 StepsVisitedIn, :444 f3RxSeg_steps_realW_of_visitedIn):
    (hRealRxNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      progKeep rxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :326, :355] C2ExternTableFacts.ghostRxEntry /
    -- f3RxSeg_ghostProg617_externAt_entry:
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "bcmp") =
        some (bcmpGhost mpl mmpl))
    -- [Lib2LayoutFacts.lean @a230f2671b:368, :374] f3Row_ghostProg617_externAt_none_of_ne_entry
    -- (sym = "bcmp", with hOther :374: memmove ends at m, strlen starts at m + 56):
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_bcmp mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "bcmp" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs)
      EG "bcmp" (bcmpEntryGuard mpl) (bcmpGhost mpl mmpl) :=
  bcmpGhost_rowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs) EG
    (fun u ⟨hCode, _⟩ => bcmpSubProg_codeLoaded_of_stripExecOutside (hStripCL u.mem hCode))
    (fun u v ⟨hCode, hFs⟩ hkf hfs => ⟨hInvKf u.mem v.mem hCode hkf, hfs ▸ hFs⟩)
    hGhostAt
    (fun W {_} hk => hRealRxNoExt W (hSubRx hk))
    hGhostNoExtNe

/-- **Artifact 2b (slice-premise form):** `GhostRowReplayOn` over
    `(fun u => CodeInv u.mem ∧ PredFs u.fs)` (`CodeInv := StartupStatics.F3CodeInv mpl mmpl`,
    `rxProg := Tie.f3TrialRxProg`), taking the verbatim slice premises (`:208–213`) of
    `Lib2LayoutFacts.f3CodeInv_rxWords_codeLoaded_strip` (`:203`) + `hInvRx : ∀ m, CodeInv m →
    rxProg.CodeLoaded m` (`:= fun _ h => h.rxCode`). -/
theorem bcmpGhost_rowReplayOn_f3CodeInv
    (mpl mmpl : Obj.MultiPlacement)
    (CodeInv : Memory → Prop)
    (PredFs : FsState → Prop)
    (rxProg : Program)
    (EG : CliHooks → String → Option (State → State))
    (hInvRx : ∀ m : Memory, CodeInv m → rxProg.CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, CodeInv m → m.KeepsFrozen m' → CodeInv m')
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :208] f3CodeInv_rxWords_codeLoaded_strip:
    (hAlign : (bcmpHullBase mpl).toNat % 4 = 0)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :209] f3CodeInv_rxWords_codeLoaded_strip:
    (hNoWrap :
      (bcmpHullBase mpl).toNat + 4 * (bcmpHullWords (bcmpHullBase mpl)).length ≤ 2 ^ 64)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :210-213] f3CodeInv_rxWords_codeLoaded_strip
    -- (cf. Lib2LayoutFacts.lean @a230f2671b:271 hasWords_subslice_of_hasWords):
    (hSubSlice : ∀ (i : Nat) (hi : i < (bcmpSubProg mpl).code.length),
      ∃ (j : Nat) (hj : j < rxProg.code.length),
        bcmpHullBase mpl + BitVec.ofNat 64 i = rxProg.base + BitVec.ofNat 64 j ∧
        (bcmpSubProg mpl).code[i] = rxProg.code[j])
    -- [Lib2LayoutFacts.lean @a230f2671b:114] keepTextBPre_sub_rxProg (composed with keepR_bcmp ⊆ keepTextBPre):
    (hSubRx : ∀ {pc : BitVec 64}, keepR_bcmp mpl pc = true → progKeep rxProg pc = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :317, :338] C2ExternTableFacts.realRxNoExtern /
    -- f3RxSeg_realProg617_externAt_none (cf. :428 StepsVisitedIn, :444 f3RxSeg_steps_realW_of_visitedIn):
    (hRealRxNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      progKeep rxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :326, :355] C2ExternTableFacts.ghostRxEntry /
    -- f3RxSeg_ghostProg617_externAt_entry:
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "bcmp") =
        some (bcmpGhost mpl mmpl))
    -- [Lib2LayoutFacts.lean @a230f2671b:368, :374] f3Row_ghostProg617_externAt_none_of_ne_entry
    -- (sym = "bcmp", with hOther :374: memmove ends at m, strlen starts at m + 56):
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_bcmp mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "bcmp" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs)
      EG "bcmp" (bcmpEntryGuard mpl) (bcmpGhost mpl mmpl) :=
  bcmpGhost_rowReplayOn_f3CodeInv_of_strip mpl mmpl CodeInv PredFs rxProg EG hInvKf
    (fun m hCode =>
      bcmpSubProg_codeLoaded_strip_of_rxProg (hInvRx m hCode) hAlign hNoWrap hSubSlice)
    hSubRx hRealRxNoExt hGhostAt hGhostNoExtNe

/-- `K`-narrowed companion to `bcmpGhost_rowReplayOn_f3CodeInv_of_strip` (requiring zero ghost-table
    or entry-`lr` premises). -/
theorem bcmpGhostK_rowReplayOn_f3CodeInv_of_strip
    (mpl mmpl : Obj.MultiPlacement)
    (CodeInv : Memory → Prop)
    (PredFs : FsState → Prop)
    (rxProg : Program)
    (EG : CliHooks → String → Option (State → State))
    (hInvKf : ∀ m m' : Memory, CodeInv m → m.KeepsFrozen m' → CodeInv m')
    -- [Lib2LayoutFacts.lean @a230f2671b:203-215] f3CodeInv_rxWords_codeLoaded_strip:
    (hStripCL : ∀ m : Memory, CodeInv m →
      (bcmpSubProg mpl).CodeLoaded (stripExecOutside (keepR_bcmp mpl) m))
    -- [Lib2LayoutFacts.lean @a230f2671b:114] keepTextBPre_sub_rxProg:
    (hSubRx : ∀ {pc : BitVec 64}, keepR_bcmp mpl pc = true → progKeep rxProg pc = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :317, :338] C2ExternTableFacts.realRxNoExtern /
    -- f3RxSeg_realProg617_externAt_none:
    (hRealRxNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      progKeep rxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs)
      EG "bcmp" (fun _ => True) (bcmpGhostK mpl mmpl) :=
  bcmpGhostK_rowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs) EG
    (fun u ⟨hCode, _⟩ => bcmpSubProg_codeLoaded_of_stripExecOutside (hStripCL u.mem hCode))
    (fun u v ⟨hCode, hFs⟩ hkf hfs => ⟨hInvKf u.mem v.mem hCode hkf, hfs ▸ hFs⟩)
    (fun W {_} hk => hRealRxNoExt W (hSubRx hk))

/-! ## 2. Artifact 3 — Block-`617` Startup `lr` (`bcmpEntryGuard` / `ExtraEntryGuard`) Discharge -/

/-- Concrete startup return address entering `main` (`block 617`), `rfl`-identical to
    `Lib2LayoutFacts.f3StartupLrVal` (`Lib2LayoutFacts.lean @a230f2671b:99`) and proved equal to
    `sm.readReg64 .lr` by `StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt`. -/
@[expose] def f3StartupLrVal : BitVec 64 :=
  f3StdLayout.libcStartMainStage2Addr + 56#64

/-- Direct adapter from `Lib2LayoutFacts.f3BatchLEntryGuard_of_startupLr`
    (`Lib2LayoutFacts.lean @a230f2671b:485-492`) into `bcmpEntryGuard mpl s0` (`Iff.rfl`). -/
theorem f3BcmpEntryGuard_of_batchLEntryGuard
    {mpl : Obj.MultiPlacement} {s0 : State}
    -- [Lib2LayoutFacts.lean @a230f2671b:485-492] f3BatchLEntryGuard_of_startupLr:
    (hGuard : keepR_bcmp mpl (s0.readReg64 .lr) = false ∧
      s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl "bcmp") :
    bcmpEntryGuard mpl s0 :=
  (bcmpEntryGuard_iff mpl s0).mpr hGuard

/-- **Artifact 3 (`C11` §6.3):** Block-`617` `bcmpEntryGuard mpl s0` discharge from startup `lr`
    (`s0.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64`), parameterized over
    `keepBPre : BitVec 64 → Bool` (`:= Lib2LayoutFacts.keepTextBPre` at C2) so zero C2-only
    constants are imported while every premise matches `Lib2LayoutFacts.lean @a230f2671b` verbatim. -/
theorem f3BcmpEntryGuard_of_startupLr
    {mpl : Obj.MultiPlacement} {s0 : State}
    (keepBPre : BitVec 64 → Bool)
    -- [StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt; rfl-equal to Lib2LayoutFacts.f3StartupLrVal @a230f2671b:99]:
    (hlr : s0.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64)
    -- [Lib2LayoutFacts.lean @a230f2671b:104] keepTextBPre_startupLr_false:
    (hLrOut : keepBPre (f3StdLayout.libcStartMainStage2Addr + 56#64) = false)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :334, :419] C2ExternTableFacts.batchLInKeep /
    -- f3BatchL_dehookedSym_in_keepTextBPre (at sym = "bcmp"):
    (hSymIn : keepBPre (libsignalSessionLib.resolve mpl "bcmp") = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:485, :490] f3BatchLEntryGuard_of_startupLr (`hsub` premise):
    (hHullSub : ∀ pc : BitVec 64, keepR_bcmp mpl pc = true → keepBPre pc = true) :
    bcmpEntryGuard mpl s0 := by
  rw [bcmpEntryGuard_iff, hlr]
  refine ⟨?_, ?_⟩
  · cases hk : keepR_bcmp mpl (f3StdLayout.libcStartMainStage2Addr + 56#64)
    · rfl
    · cases hLrOut.symm.trans (hHullSub _ hk)
  · intro hEq
    rw [hEq] at hLrOut
    cases hLrOut.symm.trans hSymIn

/-- `StdMainEntryLr f3StdLayout s0` wrapper around `f3BcmpEntryGuard_of_startupLr` (matching
    `ElfMemsetEntryGuard.f3MemsetEntryGuard_of_startupLr` / `StartupStatics`). -/
theorem f3BcmpEntryGuard_of_stdMainEntryLr
    {mpl : Obj.MultiPlacement} {s0 : State}
    (keepBPre : BitVec 64 → Bool)
    (hlr : StdMainEntryLr f3StdLayout s0)
    -- [Lib2LayoutFacts.lean @a230f2671b:104] keepTextBPre_startupLr_false:
    (hLrOut : keepBPre (f3StdLayout.libcStartMainStage2Addr + 56#64) = false)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :334, :419] C2ExternTableFacts.batchLInKeep /
    -- f3BatchL_dehookedSym_in_keepTextBPre (at sym = "bcmp"):
    (hSymIn : keepBPre (libsignalSessionLib.resolve mpl "bcmp") = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:485, :490] f3BatchLEntryGuard_of_startupLr (`hsub` premise):
    (hHullSub : ∀ pc : BitVec 64, keepR_bcmp mpl pc = true → keepBPre pc = true) :
    bcmpEntryGuard mpl s0 :=
  f3BcmpEntryGuard_of_startupLr keepBPre hlr hLrOut hSymIn hHullSub

/-- Per-arm `"bcmp"` discharge for any `guardOf : String → State → Prop` agreeing with
    `bcmpEntryGuard mpl` on `"bcmp"`. -/
theorem extraEntryGuard_bcmp_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf "bcmp" s0 ↔ bcmpEntryGuard mpl s0)
    (hBcmpGuard : bcmpEntryGuard mpl s0) :
    guardOf "bcmp" s0 :=
  hGuardEq.mpr hBcmpGuard

/-- Table-level `ExtraEntryGuard guardOf g s0` discharge when `g.extra` carries the singleton
    `"bcmp"` row `[("bcmp", bcmpGhost mpl mmpl)]`. -/
theorem extraEntryGuard_singleton_bcmp
    {mpl mmpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hg : g.extra = [("bcmp", bcmpGhost mpl mmpl)])
    (hGuardEq : guardOf "bcmp" s0 ↔ bcmpEntryGuard mpl s0)
    (hBcmpGuard : bcmpEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 := by
  intro sym f _ hLook
  rw [hg] at hLook
  simp only [List.lookup] at hLook
  by_cases hSym : (sym == "bcmp") = true
  · have hEq : sym = "bcmp" := eq_of_beq hSym
    subst hEq
    exact hGuardEq.mpr hBcmpGuard
  · simp [hSym] at hLook

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfBcmpEntryGuard
