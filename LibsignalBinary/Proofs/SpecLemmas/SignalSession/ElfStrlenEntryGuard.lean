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
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays -- proof-setup: allow-public-import

/-!
# Card CC-LIBC (`strlen`) — `F3CodeInv` / `rxProg` Replay Wrappers & Block-`617` `"strlen"` Entry Guards (`ElfStrlenEntryGuard`)

Cutover-2 `c`-card companion to `Cli.HooksDehook.StrlenGhostReplays` (modeled on
`ElfBcmpEntryGuard` @ `1583e332c6`, staying in the default `LibsignalBinary` target with `0`
`CliElfLib`, C2, or trusted imports):

1. **Artifact 2b — `F3CodeInv` / `rxProg` `GhostRowReplayOn` Wrappers (`§1`):**
   - Parameterized over `(CodeInv : Memory → Prop)` (`:= StartupStatics.F3CodeInv mpl mmpl` at C2)
     and `(rxProg : Program)` (`:= Tie.f3TrialRxProg` at C2), taking STARTUP's stock-side facts as
     verbatim premises matching `Lib2LayoutFacts.lean` (`origin/stock-lld/c2-startup-dnm` @
     `a230f2671b`: `:114`, `:203`, `:271`, `:316`, `:317`, `:326`, `:338`, `:355`, `:368`, `:374`,
     `:428`, `:444`) so C2 assembly discharges every premise with plain `exact`.
   - Provides both `strlenGhost_rowReplayOn_f3CodeInv_of_strip` (consuming `hStripCL` verbatim from
     `f3CodeInv_rxWords_codeLoaded_strip` `:203–215`) and `strlenGhost_rowReplayOn_f3CodeInv`
     (consuming the 3 slice premises `hAlign`/`hNoWrap`/`hSubSlice` `:208–213` directly on `rxProg`
     with `hAlign : (strlenEntry mpl).toNat % 4 = 0` and discharging `hKeep` `:214` automatically
     via `keepR_strlen_of_code_offset`).
2. **Artifact 3 — Block-`617` Startup `lr` (`strlenEntryGuard` / `ExtraEntryGuard`) Discharge (`§2`):**
   - Parameterized over `(keepBPre : BitVec 64 → Bool)` (`:= Lib2LayoutFacts.keepTextBPre` at C2),
     taking `keepTextBPre_startupLr_false` (`:104`), `C2ExternTableFacts.batchLInKeep` (`:334` / `:419`),
     and hull inclusion (`:485` `f3BatchLEntryGuard_of_startupLr`) as verbatim premises at the
     concrete startup return address `f3StdLayout.libcStartMainStage2Addr + 56#64` (`= StdMainEntryLr
     f3StdLayout s0`, `rfl`-equal to `Lib2LayoutFacts.f3StartupLrVal` `:99`).
   - Supplies table-level `ExtraEntryGuard` arm helpers (`extraEntryGuard_strlen_arm` and
     `extraEntryGuard_singleton_strlen`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStrlenEntryGuard

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (StdMainEntryLr)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (
  ExtraEntryGuard GhostRowOk GhostRowReplayOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays (
  strlenEntry keepR_strlen strlenSubProg strlenSubProg_base strlenSubProg_code_length
  keepR_strlen_of_code_offset strlenSubProg_codeLoaded_of_stripExecOutside
  strlenGhost strlenGhostK strlenEntryGuard strlenEntryGuard_iff
  strlenGhost_rowReplayOn strlenGhost_rowSpecOk strlenGhostK_rowReplayOn
)

/-! ## 1. Artifact 2b — `F3CodeInv` / `rxProg` `GhostRowReplayOn` Wrappers (Verbatim C2 Premises) -/

/-- Default-target sub-slice `CodeLoaded (stripExecOutside (keepR_strlen mpl) m)` projection from
    `rxProg.CodeLoaded m` (`:= hInv.rxCode` at `rxProg := Tie.f3TrialRxProg`), mirroring
    `Lib2LayoutFacts.lean @a230f2671b:203-215` (`f3CodeInv_rxWords_codeLoaded_strip`; cf. `:271`
    `hasWords_subslice_of_hasWords`) while discharging `:214` (`hKeep`) automatically via
    `keepR_strlen_of_code_offset`. -/
theorem strlenSubProg_codeLoaded_strip_of_rxProg
    {mpl : Obj.MultiPlacement} {rxProg : Program} {m : Memory}
    (hRx : rxProg.CodeLoaded m)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :208] f3CodeInv_rxWords_codeLoaded_strip:
    (hAlign : (strlenEntry mpl).toNat % 4 = 0)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :209] f3CodeInv_rxWords_codeLoaded_strip:
    (hNoWrap : (strlenEntry mpl).toNat + 4 * muslStrlenWords.length ≤ 2 ^ 64)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :210-213] f3CodeInv_rxWords_codeLoaded_strip
    -- (cf. Lib2LayoutFacts.lean @a230f2671b:271 hasWords_subslice_of_hasWords):
    (hSubSlice : ∀ (i : Nat) (hi : i < (strlenSubProg mpl).code.length),
      ∃ (j : Nat) (hj : j < rxProg.code.length),
        strlenEntry mpl + BitVec.ofNat 64 i = rxProg.base + BitVec.ofNat 64 j ∧
        (strlenSubProg mpl).code[i] = rxProg.code[j]) :
    (strlenSubProg mpl).CodeLoaded (stripExecOutside (keepR_strlen mpl) m) := by
  have hLen4 : 4 * muslStrlenWords.length = (strlenSubProg mpl).code.length := by
    rw [strlenSubProg_code_length]
    rfl
  have hAlignBase : (strlenSubProg mpl).base.toNat % 4 = 0 := by
    rw [strlenSubProg_base]
    exact hAlign
  refine Program.CodeLoaded.intro hAlignBase (by rw [strlenSubProg_base, ← hLen4]; exact hNoWrap) ?_
  intro i hi
  obtain ⟨j, hj, haddr_eq, hbyte_eq⟩ := hSubSlice i hi
  have hk_i : keepR_strlen mpl ((strlenSubProg mpl).base + BitVec.ofNat 64 i) = true :=
    keepR_strlen_of_code_offset mpl hi
  rw [strlenSubProg_base] at hk_i ⊢
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
theorem strlenGhost_rowReplayOn_f3CodeInv_of_strip
    (mpl mmpl : Obj.MultiPlacement)
    (CodeInv : Memory → Prop)
    (PredFs : FsState → Prop)
    (rxProg : Program)
    (EG : CliHooks → String → Option (State → State))
    (hInvKf : ∀ m m' : Memory, CodeInv m → m.KeepsFrozen m' → CodeInv m')
    -- [Lib2LayoutFacts.lean @a230f2671b:203-215] f3CodeInv_rxWords_codeLoaded_strip
    -- (cf. Lib2LayoutFacts.lean @a230f2671b:271 hasWords_subslice_of_hasWords):
    (hStripCL : ∀ m : Memory, CodeInv m →
      (strlenSubProg mpl).CodeLoaded (stripExecOutside (keepR_strlen mpl) m))
    -- [Lib2LayoutFacts.lean @a230f2671b:114] keepTextBPre_sub_rxProg (composed with keepR_strlen ⊆ keepTextBPre):
    (hSubRx : ∀ {pc : BitVec 64}, keepR_strlen mpl pc = true → progKeep rxProg pc = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :317, :338] C2ExternTableFacts.realRxNoExtern /
    -- f3RxSeg_realProg617_externAt_none (cf. :428 StepsVisitedIn, :444 f3RxSeg_steps_realW_of_visitedIn):
    (hRealRxNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      progKeep rxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :326, :355] C2ExternTableFacts.ghostRxEntry /
    -- f3RxSeg_ghostProg617_externAt_entry:
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "strlen") =
        some (strlenGhost mpl mmpl))
    -- [Lib2LayoutFacts.lean @a230f2671b:368, :374] f3Row_ghostProg617_externAt_none_of_ne_entry
    -- (sym = "strlen", with hOther :374):
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_strlen mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "strlen" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs)
      EG "strlen" (strlenEntryGuard mpl) (strlenGhost mpl mmpl) :=
  strlenGhost_rowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs) EG
    (fun u ⟨hCode, _⟩ => strlenSubProg_codeLoaded_of_stripExecOutside (hStripCL u.mem hCode))
    (fun u v ⟨hCode, hFs⟩ hkf hfs => ⟨hInvKf u.mem v.mem hCode hkf, hfs ▸ hFs⟩)
    hGhostAt
    (fun W {_} hk => hRealRxNoExt W (hSubRx hk))
    hGhostNoExtNe

/-- **Artifact 2b (slice-premise form):** `GhostRowReplayOn` over
    `(fun u => CodeInv u.mem ∧ PredFs u.fs)` (`CodeInv := StartupStatics.F3CodeInv mpl mmpl`,
    `rxProg := Tie.f3TrialRxProg`), taking the verbatim slice premises (`:208–213`) of
    `Lib2LayoutFacts.f3CodeInv_rxWords_codeLoaded_strip` (`:203`) + `hInvRx : ∀ m, CodeInv m →
    rxProg.CodeLoaded m` (`:= fun _ h => h.rxCode`). -/
theorem strlenGhost_rowReplayOn_f3CodeInv
    (mpl mmpl : Obj.MultiPlacement)
    (CodeInv : Memory → Prop)
    (PredFs : FsState → Prop)
    (rxProg : Program)
    (EG : CliHooks → String → Option (State → State))
    (hInvRx : ∀ m : Memory, CodeInv m → rxProg.CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, CodeInv m → m.KeepsFrozen m' → CodeInv m')
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :208] f3CodeInv_rxWords_codeLoaded_strip:
    (hAlign : (strlenEntry mpl).toNat % 4 = 0)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :209] f3CodeInv_rxWords_codeLoaded_strip:
    (hNoWrap : (strlenEntry mpl).toNat + 4 * muslStrlenWords.length ≤ 2 ^ 64)
    -- [Lib2LayoutFacts.lean @a230f2671b:203, :210-213] f3CodeInv_rxWords_codeLoaded_strip
    -- (cf. Lib2LayoutFacts.lean @a230f2671b:271 hasWords_subslice_of_hasWords):
    (hSubSlice : ∀ (i : Nat) (hi : i < (strlenSubProg mpl).code.length),
      ∃ (j : Nat) (hj : j < rxProg.code.length),
        strlenEntry mpl + BitVec.ofNat 64 i = rxProg.base + BitVec.ofNat 64 j ∧
        (strlenSubProg mpl).code[i] = rxProg.code[j])
    -- [Lib2LayoutFacts.lean @a230f2671b:114] keepTextBPre_sub_rxProg (composed with keepR_strlen ⊆ keepTextBPre):
    (hSubRx : ∀ {pc : BitVec 64}, keepR_strlen mpl pc = true → progKeep rxProg pc = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :317, :338] C2ExternTableFacts.realRxNoExtern /
    -- f3RxSeg_realProg617_externAt_none (cf. :428 StepsVisitedIn, :444 f3RxSeg_steps_realW_of_visitedIn):
    (hRealRxNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      progKeep rxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :326, :355] C2ExternTableFacts.ghostRxEntry /
    -- f3RxSeg_ghostProg617_externAt_entry:
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "strlen") =
        some (strlenGhost mpl mmpl))
    -- [Lib2LayoutFacts.lean @a230f2671b:368, :374] f3Row_ghostProg617_externAt_none_of_ne_entry:
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_strlen mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "strlen" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs)
      EG "strlen" (strlenEntryGuard mpl) (strlenGhost mpl mmpl) :=
  strlenGhost_rowReplayOn_f3CodeInv_of_strip mpl mmpl CodeInv PredFs rxProg EG hInvKf
    (fun m hCode =>
      strlenSubProg_codeLoaded_strip_of_rxProg (hInvRx m hCode) hAlign hNoWrap hSubSlice)
    hSubRx hRealRxNoExt hGhostAt hGhostNoExtNe

/-- Combined `GhostRowOk` (`hStripCL` form) over `(fun u => CodeInv u.mem ∧ PredFs u.fs)`. -/
theorem strlenGhost_rowOk_f3CodeInv_of_strip [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (CodeInv : Memory → Prop)
    (PredFs : FsState → Prop)
    (rxProg : Program)
    (EG : CliHooks → String → Option (State → State))
    (hInvKf : ∀ m m' : Memory, CodeInv m → m.KeepsFrozen m' → CodeInv m')
    (hStripCL : ∀ m : Memory, CodeInv m →
      (strlenSubProg mpl).CodeLoaded (stripExecOutside (keepR_strlen mpl) m))
    (hSubRx : ∀ {pc : BitVec 64}, keepR_strlen mpl pc = true → progKeep rxProg pc = true)
    (hRealRxNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      progKeep rxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "strlen") =
        some (strlenGhost mpl mmpl))
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_strlen mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "strlen" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs)
      EG "strlen" (strlenEntryGuard mpl) (strlenGhost mpl mmpl) :=
  ⟨strlenGhost_rowSpecOk mpl mmpl,
   strlenGhost_rowReplayOn_f3CodeInv_of_strip mpl mmpl CodeInv PredFs rxProg EG hInvKf hStripCL
     hSubRx hRealRxNoExt hGhostAt hGhostNoExtNe⟩

/-- Combined `GhostRowOk` (slice-premise form) over `(fun u => CodeInv u.mem ∧ PredFs u.fs)`. -/
theorem strlenGhost_rowOk_f3CodeInv [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (CodeInv : Memory → Prop)
    (PredFs : FsState → Prop)
    (rxProg : Program)
    (EG : CliHooks → String → Option (State → State))
    (hInvRx : ∀ m : Memory, CodeInv m → rxProg.CodeLoaded m)
    (hInvKf : ∀ m m' : Memory, CodeInv m → m.KeepsFrozen m' → CodeInv m')
    (hAlign : (strlenEntry mpl).toNat % 4 = 0)
    (hNoWrap : (strlenEntry mpl).toNat + 4 * muslStrlenWords.length ≤ 2 ^ 64)
    (hSubSlice : ∀ (i : Nat) (hi : i < (strlenSubProg mpl).code.length),
      ∃ (j : Nat) (hj : j < rxProg.code.length),
        strlenEntry mpl + BitVec.ofNat 64 i = rxProg.base + BitVec.ofNat 64 j ∧
        (strlenSubProg mpl).code[i] = rxProg.code[j])
    (hSubRx : ∀ {pc : BitVec 64}, keepR_strlen mpl pc = true → progKeep rxProg pc = true)
    (hRealRxNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      progKeep rxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hGhostAt : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl EG 617 W).externAt? (libsignalSessionLib.resolve mpl "strlen") =
        some (strlenGhost mpl mmpl))
    (hGhostNoExtNe : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_strlen mpl pc = true →
      pc ≠ libsignalSessionLib.resolve mpl "strlen" →
      (cliProgExtPlacedAt mpl EG 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs)
      EG "strlen" (strlenEntryGuard mpl) (strlenGhost mpl mmpl) :=
  ⟨strlenGhost_rowSpecOk mpl mmpl,
   strlenGhost_rowReplayOn_f3CodeInv mpl mmpl CodeInv PredFs rxProg EG hInvRx hInvKf hAlign
     hNoWrap hSubSlice hSubRx hRealRxNoExt hGhostAt hGhostNoExtNe⟩

/-- `K`-narrowed companion to `strlenGhost_rowReplayOn_f3CodeInv_of_strip` (requiring zero
    ghost-table or entry-`lr` premises). -/
theorem strlenGhostK_rowReplayOn_f3CodeInv_of_strip
    (mpl mmpl : Obj.MultiPlacement)
    (CodeInv : Memory → Prop)
    (PredFs : FsState → Prop)
    (rxProg : Program)
    (EG : CliHooks → String → Option (State → State))
    (hInvKf : ∀ m m' : Memory, CodeInv m → m.KeepsFrozen m' → CodeInv m')
    -- [Lib2LayoutFacts.lean @a230f2671b:203-215] f3CodeInv_rxWords_codeLoaded_strip:
    (hStripCL : ∀ m : Memory, CodeInv m →
      (strlenSubProg mpl).CodeLoaded (stripExecOutside (keepR_strlen mpl) m))
    -- [Lib2LayoutFacts.lean @a230f2671b:114] keepTextBPre_sub_rxProg:
    (hSubRx : ∀ {pc : BitVec 64}, keepR_strlen mpl pc = true → progKeep rxProg pc = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :317, :338] C2ExternTableFacts.realRxNoExtern /
    -- f3RxSeg_realProg617_externAt_none:
    (hRealRxNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      progKeep rxProg pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs)
      EG "strlen" (fun _ => True) (strlenGhostK mpl mmpl) :=
  strlenGhostK_rowReplayOn mpl mmpl (fun u => CodeInv u.mem ∧ PredFs u.fs) EG
    (fun u ⟨hCode, _⟩ => strlenSubProg_codeLoaded_of_stripExecOutside (hStripCL u.mem hCode))
    (fun u v ⟨hCode, hFs⟩ hkf hfs => ⟨hInvKf u.mem v.mem hCode hkf, hfs ▸ hFs⟩)
    (fun W {_} hk => hRealRxNoExt W (hSubRx hk))

/-! ## 2. Artifact 3 — Block-`617` Startup `lr` (`strlenEntryGuard` / `ExtraEntryGuard`) Discharge -/

/-- Concrete startup return address entering `main` (`block 617`), `rfl`-identical to
    `Lib2LayoutFacts.f3StartupLrVal` (`Lib2LayoutFacts.lean @a230f2671b:99`) and proved equal to
    `sm.readReg64 .lr` by `StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt`. -/
@[expose] def f3StartupLrVal : BitVec 64 :=
  f3StdLayout.libcStartMainStage2Addr + 56#64

/-- Direct adapter from `Lib2LayoutFacts.f3BatchLEntryGuard_of_startupLr`
    (`Lib2LayoutFacts.lean @a230f2671b:485-492`) into `strlenEntryGuard mpl s0` (`Iff.rfl`). -/
theorem f3StrlenEntryGuard_of_batchLEntryGuard
    {mpl : Obj.MultiPlacement} {s0 : State}
    -- [Lib2LayoutFacts.lean @a230f2671b:485-492] f3BatchLEntryGuard_of_startupLr:
    (hGuard : keepR_strlen mpl (s0.readReg64 .lr) = false ∧
      s0.readReg64 .lr ≠ libsignalSessionLib.resolve mpl "strlen") :
    strlenEntryGuard mpl s0 :=
  (strlenEntryGuard_iff mpl s0).mpr hGuard

/-- **Artifact 3 (`C11` §6.3):** Block-`617` `strlenEntryGuard mpl s0` discharge from startup `lr`
    (`s0.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64`), parameterized over
    `keepBPre : BitVec 64 → Bool` (`:= Lib2LayoutFacts.keepTextBPre` at C2) so zero C2-only
    constants are imported while every premise matches `Lib2LayoutFacts.lean @a230f2671b` verbatim. -/
theorem f3StrlenEntryGuard_of_startupLr
    {mpl : Obj.MultiPlacement} {s0 : State}
    (keepBPre : BitVec 64 → Bool)
    -- [StartupStatics.cliElf_f3MuslHarnessLr_of_linkedAt; rfl-equal to Lib2LayoutFacts.f3StartupLrVal @a230f2671b:99]:
    (hlr : s0.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64)
    -- [Lib2LayoutFacts.lean @a230f2671b:104] keepTextBPre_startupLr_false:
    (hLrOut : keepBPre (f3StdLayout.libcStartMainStage2Addr + 56#64) = false)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :334, :419] C2ExternTableFacts.batchLInKeep /
    -- f3BatchL_dehookedSym_in_keepTextBPre (at sym = "strlen"):
    (hSymIn : keepBPre (libsignalSessionLib.resolve mpl "strlen") = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:485, :490] f3BatchLEntryGuard_of_startupLr (`hsub` premise):
    (hHullSub : ∀ pc : BitVec 64, keepR_strlen mpl pc = true → keepBPre pc = true) :
    strlenEntryGuard mpl s0 := by
  rw [strlenEntryGuard_iff, hlr]
  refine ⟨?_, ?_⟩
  · cases hk : keepR_strlen mpl (f3StdLayout.libcStartMainStage2Addr + 56#64)
    · rfl
    · cases hLrOut.symm.trans (hHullSub _ hk)
  · intro hEq
    rw [hEq] at hLrOut
    cases hLrOut.symm.trans hSymIn

/-- `StdMainEntryLr f3StdLayout s0` wrapper around `f3StrlenEntryGuard_of_startupLr` (matching
    `ElfMemsetEntryGuard.f3MemsetEntryGuard_of_startupLr` / `StartupStatics`). -/
theorem f3StrlenEntryGuard_of_stdMainEntryLr
    {mpl : Obj.MultiPlacement} {s0 : State}
    (keepBPre : BitVec 64 → Bool)
    (hlr : StdMainEntryLr f3StdLayout s0)
    -- [Lib2LayoutFacts.lean @a230f2671b:104] keepTextBPre_startupLr_false:
    (hLrOut : keepBPre (f3StdLayout.libcStartMainStage2Addr + 56#64) = false)
    -- [Lib2LayoutFacts.lean @a230f2671b:316, :334, :419] C2ExternTableFacts.batchLInKeep /
    -- f3BatchL_dehookedSym_in_keepTextBPre (at sym = "strlen"):
    (hSymIn : keepBPre (libsignalSessionLib.resolve mpl "strlen") = true)
    -- [Lib2LayoutFacts.lean @a230f2671b:485, :490] f3BatchLEntryGuard_of_startupLr (`hsub` premise):
    (hHullSub : ∀ pc : BitVec 64, keepR_strlen mpl pc = true → keepBPre pc = true) :
    strlenEntryGuard mpl s0 :=
  f3StrlenEntryGuard_of_startupLr keepBPre hlr hLrOut hSymIn hHullSub

/-- Per-arm `"strlen"` discharge for any `guardOf : String → State → Prop` agreeing with
    `strlenEntryGuard mpl` on `"strlen"`. -/
theorem extraEntryGuard_strlen_arm
    {mpl : Obj.MultiPlacement} {guardOf : String → State → Prop} {s0 : State}
    (hGuardEq : guardOf "strlen" s0 ↔ strlenEntryGuard mpl s0)
    (hStrlenGuard : strlenEntryGuard mpl s0) :
    guardOf "strlen" s0 :=
  hGuardEq.mpr hStrlenGuard

/-- Table-level `ExtraEntryGuard guardOf g s0` discharge when `g.extra` carries the singleton
    `"strlen"` row `[("strlen", strlenGhost mpl mmpl)]`. -/
theorem extraEntryGuard_singleton_strlen
    {mpl mmpl : Obj.MultiPlacement} {guardOf : String → State → Prop}
    {g : CliGhostHooks} {s0 : State}
    (hg : g.extra = [("strlen", strlenGhost mpl mmpl)])
    (hGuardEq : guardOf "strlen" s0 ↔ strlenEntryGuard mpl s0)
    (hStrlenGuard : strlenEntryGuard mpl s0) :
    ExtraEntryGuard guardOf g s0 := by
  intro sym f _ hLook
  rw [hg] at hLook
  simp only [List.lookup] at hLook
  by_cases hSym : (sym == "strlen") = true
  · have hEq : sym = "strlen" := eq_of_beq hSym
    subst hEq
    exact hGuardEq.mpr hStrlenGuard
  · simp [hSym] at hLook

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfStrlenEntryGuard
