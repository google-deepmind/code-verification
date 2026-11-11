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
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords -- proof-setup: allow-public-import

/-!
# Card CC-MEMMOVE (`memmove`) — `F3CodeInv` / `rxProg` Replay Wrappers & Block-`617` `"memmove"` Entry Guards (`ElfMemmoveEntryGuard`)

Cutover-2 `c`-card companion to `Cli.HooksDehook.MemmoveExtraReplays` (modeled on
`ElfBcmpEntryGuard` @ `1583e332c6` and `ElfStrlenEntryGuard` @ `138b2e4236`, staying in the default
`LibsignalBinary` target with `0` `CliElfLib`, C2, or trusted imports):

1. **Artifact 2b — `F3CodeInv` / `rxProg` `GhostRowReplayOn` Wrappers (`§1`):**
   - Parameterized over `(CodeInv : Memory → Prop)` (`:= StartupStatics.F3CodeInv mpl mmpl` at C2)
     and `(rxProg : Program)` (`:= Tie.f3TrialRxProg` at C2), taking STARTUP's stock-side facts as
     verbatim premises matching `Lib2LayoutFacts.lean` (`origin/stock-lld/c2-startup-dnm` @
     `a230f2671b`: `:114`, `:203`, `:208–215`, `:271`, `:316`, `:317`, `:338`, `:355–362`,
     `:392–402`, `:428`, `:444`) so C2 assembly discharges every premise with plain `exact`.
   - Uses the 3-entry `.text.b_pre` hull (`rowSyms := ["memmove", "memcpy", "memset"]`,
     `Lib2LayoutFacts.lean @ a230f2671b:392-402` `f3RowSyms_ghostProg617_externAt_none_of_ne_entries`
     + `:355-362` `f3RxSeg_ghostProg617_externAt_entry`) so Stage A `"memcpy"` and `"memset"` ghosts
     may remain simultaneously active in `EG W` (`hother`-free L3-d multi-ghost route).
2. **Artifact 3 — Block-`617` Startup `lr` (`memmoveEntryGuard` / `ExtraEntryGuard`) Discharge (`§2`):**
   - Parameterized over `(keepBPre : BitVec 64 → Bool)` (`:= Lib2LayoutFacts.keepTextBPre` at C2),
     taking `keepTextBPre_startupLr_false` (`:104`), `C2ExternTableFacts.batchLInKeep` (`:334` / `:419`
     at `sym = "memmove"`), and hull inclusion (`:485` `f3BatchLEntryGuard_of_startupLr`) as verbatim
     premises at `f3StdLayout.libcStartMainStage2Addr + 56#64` (`= StdMainEntryLr f3StdLayout s0`,
     `rfl`-equal to `Lib2LayoutFacts.f3StartupLrVal` `:99`).
   - Supplies table-level `ExtraEntryGuard` arm helpers (`extraEntryGuard_memmove_arm` and
     `extraEntryGuard_singleton_memmove`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemmoveEntryGuard

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (StdMainEntryLr)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (
  ExtraEntryGuard GhostRowReplayOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode (bPreMemmoveByteOff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays (
  keepR_memmove keepR_memmove_of_code_offset
  memcpyEntry memmoveEntry memmoveEntryGuard memmoveEntryGuard_iff
  memmoveGhost memmoveGhost_rowReplayOn memmoveGhostK memmoveGhostK_rowReplayOn
  memmoveHullWords memmoveHullWords_length
  memmoveSubProg memmoveSubProg_base memmoveSubProg_code_length
  memmoveSubProg_codeLoaded_of_stripExecOutside
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (TrapHook)

/-! ## 1. Artifact 2b — `F3CodeInv` / `rxProg` `GhostRowReplayOn` Wrappers (Verbatim C2 Premises) -/

/-- Default-target sub-slice `CodeLoaded (stripExecOutside (keepR_memmove mpl) m)` projection from
    `rxProg.CodeLoaded m` (`:= hInv.rxCode` at `rxProg := Tie.f3TrialRxProg`), mirroring
    `Lib2LayoutFacts.lean @a230f2671b:203-215` (`f3CodeInv_rxWords_codeLoaded_strip`; cf. `:271`
    `hasWords_subslice_of_hasWords`) while discharging `:214` (`hKeep`) automatically via
    `keepR_memmove_of_code_offset`. -/
theorem memmoveSubProg_codeLoaded_strip_of_rxProg
    {mpl : Obj.MultiPlacement} {rxProg : Program} {m : Memory}
    (hRx : rxProg.CodeLoaded m)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :208] f3CodeInv_rxWords_codeLoaded_strip:
    (hAlign : (memcpyEntry mpl).toNat % 4 = 0)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :209] f3CodeInv_rxWords_codeLoaded_strip:
    (hNoWrap : (memcpyEntry mpl).toNat + 4 * (memmoveHullWords mpl).length ≤ 2 ^ 64)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :210-213] f3CodeInv_rxWords_codeLoaded_strip
    -- (cf. Lib2LayoutFacts.lean @a230f2671b:271 hasWords_subslice_of_hasWords):
    (hSubSlice : ∀ (i : Nat) (hi : i < (memmoveSubProg mpl).code.length),
      ∃ (j : Nat) (hj : j < rxProg.code.length),
        memcpyEntry mpl + BitVec.ofNat 64 i = rxProg.base + BitVec.ofNat 64 j ∧
        (memmoveSubProg mpl).code[i] = rxProg.code[j]) :
    (memmoveSubProg mpl).CodeLoaded (stripExecOutside (keepR_memmove mpl) m) := by
  have hLen4 : 4 * (memmoveHullWords mpl).length = (memmoveSubProg mpl).code.length := by
    rw [memmoveHullWords_length, memmoveSubProg_code_length]
    rfl
  have hAlignBase : (memmoveSubProg mpl).base.toNat % 4 = 0 := by
    rw [memmoveSubProg_base]
    exact hAlign
  refine Program.CodeLoaded.intro hAlignBase (by rw [memmoveSubProg_base, ← hLen4]; exact hNoWrap) ?_
  intro i hi
  obtain ⟨j, hj, haddr_eq, hbyte_eq⟩ := hSubSlice i hi
  have hk_i : keepR_memmove mpl ((memmoveSubProg mpl).base + BitVec.ofNat 64 i) = true :=
    keepR_memmove_of_code_offset hi
  rw [memmoveSubProg_base] at hk_i ⊢
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
    (cf. `:428` `StepsVisitedIn`, `:444` `f3RxSeg_steps_realW_of_visitedIn`), `:355–362`, and
    `:392–402` (`rowSyms := ["memmove", "memcpy", "memset"]`). -/
theorem memmoveGhost_rowReplayOn_f3CodeInv_of_strip
    (mpl mmpl : Obj.MultiPlacement)
    (CodeInv : Memory → Prop)
    (PredFs : FsState → Prop)
    (rxProg : Program)
    (EG : CliHooks → String → Option (State → State))
    (hMemmoveOff : memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff)
    (hInvKf : ∀ m m' : Memory, CodeInv m → m.KeepsFrozen m' → CodeInv m')
    -- [Lib2LayoutFacts.lean @a230f2671b:203-215] f3CodeInv_rxWords_codeLoaded_strip
    -- (cf. Lib2LayoutFacts.lean @a230f2671b:271 hasWords_subslice_of_hasWords):
    (hStripCL : ∀ m : Memory, CodeInv m →
      (memmoveSubProg mpl).CodeLoaded (stripExecOutside (keepR_memmove mpl) m))
    -- [Lib2LayoutFacts.lean @a230f2671b:114] keepTextBPre_sub_rxProg (composed with keepR_memmove ⊆ keepTextBPre):
    (hSubRx : ∀ {pc : BitVec 64}, keepR_memmove mpl pc = true → progKeep rxProg pc = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :317, :338] C2ExternTableFacts.realRxNoExtern /
    -- f3RxSeg_realProg617_externAt_none (cf. :428 StepsVisitedIn, :444 f3RxSeg_steps_realW_of_visitedIn):
    (hRealRxNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      progKeep rxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    -- [Lib2LayoutFacts.lean @a230f2671b:392-402] f3RowSyms_ghostProg617_externAt_none_of_ne_entries
    -- (rowSyms := ["memmove", "memcpy", "memset"]):
    (hGhostOffEntries : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map (libsignalSessionLib.resolve mpl) →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none)
    -- [Lib2LayoutFacts.lean @a230f2671b:355-362] f3RxSeg_ghostProg617_externAt_entry:
    (hGhostEntry : ∀ (W : CliHooks) {sym : String},
      sym ∈ ["memmove", "memcpy", "memset"] →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl sym) = EG W sym)
    (hMemmoveExt : ∀ W : CliHooks,
      EG W "memmove" = none ∨ EG W "memmove" = some (memmoveGhost mpl mmpl))
    (hMemcpyTrap : ∀ (W : CliHooks) (f : State → State),
      EG W "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ (W : CliHooks) (f : State → State),
      EG W "memset" = some f → ∀ L, TrapHook L f) :
    GhostRowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs)
      EG "memmove" (memmoveEntryGuard mpl) (memmoveGhost mpl mmpl) :=
  memmoveGhost_rowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs) EG
    hMemmoveOff
    (fun u ⟨hCode, _⟩ => memmoveSubProg_codeLoaded_of_stripExecOutside (hStripCL u.mem hCode))
    (fun u v ⟨hCode, hFs⟩ hkf hfs => ⟨hInvKf u.mem v.mem hCode hkf, hfs ▸ hFs⟩)
    (fun W {_} hk => hRealRxNoExt W (hSubRx hk))
    hGhostOffEntries
    hGhostEntry
    hMemmoveExt
    hMemcpyTrap
    hMemsetTrap

/-- **Artifact 2b (slice-premise form):** `GhostRowReplayOn` over
    `(fun u => CodeInv u.mem ∧ PredFs u.fs)` (`CodeInv := StartupStatics.F3CodeInv mpl mmpl`,
    `rxProg := Tie.f3TrialRxProg`), taking the verbatim slice premises (`:208–213`) of
    `Lib2LayoutFacts.f3CodeInv_rxWords_codeLoaded_strip` (`:203`) + `hInvRx : ∀ m, CodeInv m →
    rxProg.CodeLoaded m` (`:= fun _ h => h.rxCode`). -/
theorem memmoveGhost_rowReplayOn_f3CodeInv
    (mpl mmpl : Obj.MultiPlacement)
    (CodeInv : Memory → Prop)
    (PredFs : FsState → Prop)
    (rxProg : Program)
    (EG : CliHooks → String → Option (State → State))
    (hMemmoveOff : memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff)
    (hInvRx : ∀ m : Memory, CodeInv m → rxProg.CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, CodeInv m → m.KeepsFrozen m' → CodeInv m')
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :208] f3CodeInv_rxWords_codeLoaded_strip:
    (hAlign : (memcpyEntry mpl).toNat % 4 = 0)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :209] f3CodeInv_rxWords_codeLoaded_strip:
    (hNoWrap : (memcpyEntry mpl).toNat + 4 * (memmoveHullWords mpl).length ≤ 2 ^ 64)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :210-213] f3CodeInv_rxWords_codeLoaded_strip
    -- (cf. Lib2LayoutFacts.lean @a230f2671b:271 hasWords_subslice_of_hasWords):
    (hSubSlice : ∀ (i : Nat) (hi : i < (memmoveSubProg mpl).code.length),
      ∃ (j : Nat) (hj : j < rxProg.code.length),
        memcpyEntry mpl + BitVec.ofNat 64 i = rxProg.base + BitVec.ofNat 64 j ∧
        (memmoveSubProg mpl).code[i] = rxProg.code[j])
    -- [Lib2LayoutFacts.lean @a230f2671b:114] keepTextBPre_sub_rxProg (composed with keepR_memmove ⊆ keepTextBPre):
    (hSubRx : ∀ {pc : BitVec 64}, keepR_memmove mpl pc = true → progKeep rxProg pc = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :317, :338] C2ExternTableFacts.realRxNoExtern /
    -- f3RxSeg_realProg617_externAt_none (cf. :428 StepsVisitedIn, :444 f3RxSeg_steps_realW_of_visitedIn):
    (hRealRxNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      progKeep rxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    -- [Lib2LayoutFacts.lean @a230f2671b:392-402] f3RowSyms_ghostProg617_externAt_none_of_ne_entries:
    (hGhostOffEntries : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_memmove mpl pc = true →
      pc ∉ ["memmove", "memcpy", "memset"].map (libsignalSessionLib.resolve mpl) →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none)
    -- [Lib2LayoutFacts.lean @a230f2671b:355-362] f3RxSeg_ghostProg617_externAt_entry:
    (hGhostEntry : ∀ (W : CliHooks) {sym : String},
      sym ∈ ["memmove", "memcpy", "memset"] →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl sym) = EG W sym)
    (hMemmoveExt : ∀ W : CliHooks,
      EG W "memmove" = none ∨ EG W "memmove" = some (memmoveGhost mpl mmpl))
    (hMemcpyTrap : ∀ (W : CliHooks) (f : State → State),
      EG W "memcpy" = some f → ∀ L, TrapHook L f)
    (hMemsetTrap : ∀ (W : CliHooks) (f : State → State),
      EG W "memset" = some f → ∀ L, TrapHook L f) :
    GhostRowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs)
      EG "memmove" (memmoveEntryGuard mpl) (memmoveGhost mpl mmpl) :=
  memmoveGhost_rowReplayOn_f3CodeInv_of_strip mpl mmpl CodeInv PredFs rxProg EG
    hMemmoveOff hInvKf
    (fun m hCode =>
      memmoveSubProg_codeLoaded_strip_of_rxProg (hInvRx m hCode) hAlign hNoWrap hSubSlice)
    hSubRx hRealRxNoExt hGhostOffEntries hGhostEntry hMemmoveExt hMemcpyTrap hMemsetTrap

/-- `K`-narrowed companion to `memmoveGhost_rowReplayOn_f3CodeInv_of_strip` (requiring zero
    ghost-table or entry-`lr` premises). -/
theorem memmoveGhostK_rowReplayOn_f3CodeInv_of_strip
    (mpl mmpl : Obj.MultiPlacement)
    (CodeInv : Memory → Prop)
    (PredFs : FsState → Prop)
    (rxProg : Program)
    (EG : CliHooks → String → Option (State → State))
    (hMemmoveOff : memmoveEntry mpl = memcpyEntry mpl + bPreMemmoveByteOff)
    (hInvKf : ∀ m m' : Memory, CodeInv m → m.KeepsFrozen m' → CodeInv m')
    -- [Lib2LayoutFacts.lean @a230f2671b:203-215] f3CodeInv_rxWords_codeLoaded_strip:
    (hStripCL : ∀ m : Memory, CodeInv m →
      (memmoveSubProg mpl).CodeLoaded (stripExecOutside (keepR_memmove mpl) m))
    -- [Lib2LayoutFacts.lean @a230f2671b:114] keepTextBPre_sub_rxProg:
    (hSubRx : ∀ {pc : BitVec 64}, keepR_memmove mpl pc = true → progKeep rxProg pc = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :317, :338] C2ExternTableFacts.realRxNoExtern /
    -- f3RxSeg_realProg617_externAt_none:
    (hRealRxNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      progKeep rxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs)
      EG "memmove" (fun _ => True) (memmoveGhostK mpl mmpl) :=
  memmoveGhostK_rowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs) EG
    hMemmoveOff
    (fun u ⟨hCode, _⟩ => memmoveSubProg_codeLoaded_of_stripExecOutside (hStripCL u.mem hCode))
    (fun u v ⟨hCode, hFs⟩ hkf hfs => ⟨hInvKf u.mem v.mem hCode hkf, hfs ▸ hFs⟩)
    (fun W {_} hk => hRealRxNoExt W (hSubRx hk))

/-! ## 2. Artifact 3 — Block-`617` Startup `lr` (`memmoveEntryGuard` / `ExtraEntryGuard`) Discharge -/

/-- Concrete startup return address entering `main` (`block 617`), `rfl`-identical to
    `Lib2LayoutFacts.f3StartupLrVal` (`Lib2LayoutFacts.lean @a230f2671b:99`) and proved equal to
    `sm.readReg64 .lr` by `StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt`. -/
@[expose] def f3StartupLrVal : BitVec 64 :=
  f3StdLayout.libcStartMainStage2Addr + 56#64

/-- Direct adapter from `Lib2LayoutFacts.f3BatchLEntryGuard_of_startupLr`
    (`Lib2LayoutFacts.lean @a230f2671b:485-492`) into `memmoveEntryGuard mpl s0` (`Iff.rfl`). -/
theorem f3MemmoveEntryGuard_of_batchLEntryGuard
    {mpl : Obj.MultiPlacement} {s0 : State}
    -- [Lib2LayoutFacts.lean @a230f2671b:485-492] f3BatchLEntryGuard_of_startupLr:
    (hGuard : keepR_memmove mpl (s0.readReg64 .lr) = false ∧
      s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl "memmove") :
    memmoveEntryGuard mpl s0 :=
  (memmoveEntryGuard_iff mpl s0).mpr hGuard

/-- **Artifact 3 (`C11` §6.3):** Block-`617` `memmoveEntryGuard mpl s0` discharge from startup `lr`
    (`s0.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64`), parameterized over
    `keepBPre : BitVec 64 → Bool` (`:= Lib2LayoutFacts.keepTextBPre` at C2) so zero C2-only
    constants are imported while every premise matches `Lib2LayoutFacts.lean @a230f2671b` verbatim. -/
theorem f3MemmoveEntryGuard_of_startupLr
    {mpl : Obj.MultiPlacement} {s0 : State}
    (keepBPre : BitVec 64 → Bool)
    -- [StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt; rfl-equal to Lib2LayoutFacts.f3StartupLrVal @a230f2671b:99]:
    (hlr : s0.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64)
    -- [Lib2LayoutFacts.lean @a230f2671b:104] keepTextBPre_startupLr_false:
    (hLrOut : keepBPre (f3StdLayout.libcStartMainStage2Addr + 56#64) = false)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :334, :419] C2ExternTableFacts.batchLInKeep /
    -- f3BatchL_dehookedSym_in_keepTextBPre (at sym = "memmove"):
    (hSymIn : keepBPre (libsignalSessionLib.resolve mpl "memmove") = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:485, :490] f3BatchLEntryGuard_of_startupLr (`hsub` premise):
    (hHullSub : ∀ pc : BitVec 64, keepR_memmove mpl pc = true → keepBPre pc = true) :
    memmoveEntryGuard mpl s0 := by
  rw [memmoveEntryGuard_iff, hlr]
  refine ⟨?_, ?_⟩
  · cases hk : keepR_memmove mpl (f3StdLayout.libcStartMainStage2Addr + 56#64)
    · rfl
    · cases hLrOut.symm.trans (hHullSub _ hk)
  · intro hEq
    rw [hEq] at hLrOut
    cases hLrOut.symm.trans hSymIn

/-- `StdMainEntryLr f3StdLayout s0` wrapper around `f3MemmoveEntryGuard_of_startupLr` (matching
    `ElfMemsetEntryGuard.f3MemsetEntryGuard_of_startupLr` / `StartupStatics`). -/
theorem f3MemmoveEntryGuard_of_stdMainEntryLr
    {mpl : Obj.MultiPlacement} {s0 : State}
    (keepBPre : BitVec 64 → Bool)
    (hlr : StdMainEntryLr f3StdLayout s0)
    -- [Lib2LayoutFacts.lean @a230f2671b:104] keepTextBPre_startupLr_false:
    (hLrOut : keepBPre (f3StdLayout.libcStartMainStage2Addr + 56#64) = false)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :334, :419] C2ExternTableFacts.batchLInKeep /
    -- f3BatchL_dehookedSym_in_keepTextBPre (at sym = "memmove"):
    (hSymIn : keepBPre (libsignalSessionLib.resolve mpl "memmove") = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:485, :490] f3BatchLEntryGuard_of_startupLr (`hsub` premise):
    (hHullSub : ∀ pc : BitVec 64, keepR_memmove mpl pc = true → keepBPre pc = true) :
    memmoveEntryGuard mpl s0 :=
  f3MemmoveEntryGuard_of_startupLr keepBPre hlr hLrOut hSymIn hHullSub

/-- Per-arm `"memmove"` discharge for any `guardOf : String → State → Prop` agreeing with
    `memmoveEntryGuard mpl` on `"memmove"`. -/
theorem extraEntryGuard_memmove_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf "memmove" s0 ↔ memmoveEntryGuard mpl s0)
    (hMemmoveGuard : memmoveEntryGuard mpl s0) :
    guardOf "memmove" s0 :=
  hGuardEq.mpr hMemmoveGuard

/-- Table-level `ExtraEntryGuard guardOf g s0` discharge when `g.extra` carries the singleton
    `"memmove"` row `[("memmove", memmoveGhost mpl mmpl)]`. -/
theorem extraEntryGuard_singleton_memmove
    {mpl mmpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hg : g.extra = [("memmove", memmoveGhost mpl mmpl)])
    (hGuardEq : guardOf "memmove" s0 ↔ memmoveEntryGuard mpl s0)
    (hMemmoveGuard : memmoveEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 := by
  intro sym f _ hLook
  rw [hg] at hLook
  simp only [List.lookup] at hLook
  by_cases hSym : (sym == "memmove") = true
  · have hEq : sym = "memmove" := eq_of_beq hSym
    subst hEq
    exact hGuardEq.mpr hMemmoveGuard
  · simp [hSym] at hLook

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemmoveEntryGuard
