/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWire -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen -- proof-setup: allow-public-import

/-!
# Multi-Ghost `codeOnly` Block-`617` Transfer (`ElfSlicesPqOomH2ExecFrozenWireExtra`)

Implements frozen **R5.3** (`block617TransferFixedG_replaysOn_false_codeOnly_withExtra`,
`scratch/2b/api_A.md` §5R.b & `rev_api_A.md` §5R GO) plus `cliExtraGhostSyms_sub_c2Rx`:

1. `cliExtraGhostSyms_sub_c2Rx`: `∀ s ∈ cliExtraGhostSyms, s ∈ c2RxDehookedSyms`.
2. `block617TransferFixedG_replaysOn_false_codeOnly_extraList` (arbitrary `extra : ExtraGhostTable`)
   and `block617TransferFixedG_replaysOn_false_codeOnly_withExtra` (exact §5R.b L930–999 signature,
   using `ElfSlicesPqOomH2ExecFrozenWire.h2ef_h2k_ghFixedK_withExtra_preserves_execFrozen`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWireExtra

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.SepLogic
open CryptoVerification (LibsignalFrozen LibsignalPlacement)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced libsignalSessionLib lsMemcpySym lsMemsetSym lsReadFileSym
   lsRustNoAllocShimSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns cliGhostExterns_eq_withExtra)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (cliExternsPlaced_preserves_execFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG block617TransferFixedG_of_replaysOn
   noNewHooks_cliProgExtPlacedAt_of_ext_none_imp)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (ExtraEntryGuard ExtraListEntryGuard ExtraListReplaysOn ExtraReplaysOn GhostSymActiveNamed
   GhostSymActiveWithExtra GhostSymActiveWithExtra_iff_named_or_extra
   cliGhostExternsWithExtra_eq_some_of_active cliGhostExternsWithExtra_nil_of_named
   cliGhostExternsWithExtra_none_imp cliGhostExternsWithExtra_some_cases extraListReplaysOn_arm)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (keepMemcpyBlk20)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyLrTrapRet
  (Blk20TrapHook blk20_lr_trap_after_hook_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (keepMemsetBlk21)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetLrTrapRet
  (Blk21TrapHook blk21_lr_trap_after_hook_ret)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraGhostTable cliExtraGhostSyms cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (f3LsBlocksLen libsignalBlocks_len)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard
  (F3MemsetMemcpyEntryLrFalse)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWire
  (h2ef_h2k_ghFixedK_withExtra_preserves_execFrozen h2ef_strClone_not_mem_ext617)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst (hole2_keepSub)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen (c2RxDehookedSyms)
open VerifiedLibraries (mallocngLib)

/-- Domain inclusion discharging `hSymRx` of `C2RowLayoutFacts.RowCommon.c2_ghostAt_of_extraLookup`. -/
theorem cliExtraGhostSyms_sub_c2Rx :
    ∀ s ∈ cliExtraGhostSyms, s ∈ c2RxDehookedSyms := by decide

/-! ### Internal `externAt?` & `CodeLoaded` Helpers -/

private theorem findSome?_const_none {α β : Type} (l : List α) :
    (l.findSome? fun _ => (none : Option β)) = none := by
  induction l with
  | nil => rfl
  | cons _ tl ih => exact ih

private theorem findSome?_table_exists (tbl : List (String × Nat))
    {ext : String → Option (State → State)} (off : Nat) {f : State → State}
    (h : (tbl.findSome? fun (n, o) => if o == off then ext n else none) = some f) :
    ∃ sym : String, ext sym = some f := by
  induction tbl with
  | nil => simp at h
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    simp only [List.findSome?_cons] at h
    cases hoo : (o == off) with
    | false =>
      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h
      exact ih h
    | true =>
      simp only [hoo, ↓reduceIte] at h
      cases he : ext n with
      | none => rw [he] at h; exact ih h
      | some g =>
        rw [he] at h
        injection h with hgf
        subst hgf
        exact ⟨n, he⟩

private theorem blockProgram_externAt?_some_exists
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {idx : Nat}
    {ext : String → Option (State → State)} {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram mpl idx ext).externAt? pc = some f) :
    ∃ sym : String, ext sym = some f := by
  unfold Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program Program.externAt? Program.hookAtOff? at h
  simp only [ite_self] at h
  rw [findSome?_const_none, Option.or_none] at h
  exact findSome?_table_exists _ _ h

private theorem findSome?_stubs_cliGhostExternsWithExtra_mem_cases
    (exts : List String) (ρ : String → BitVec 64) (base pc : BitVec 64)
    (ghFixed : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State)) {f : State → State}
    (h : ((exts.map fun e => (e, (ρ e - base).toNat)).findSome?
      fun (n, o) =>
        if o == (pc - base).toNat then cliGhostExternsWithExtra ghFixed extra baseExt n
        else none) = some f) :
    ((exts.map fun e => (e, (ρ e - base).toNat)).findSome?
      fun (n, o) => if o == (pc - base).toNat then baseExt n else none) = some f ∨
    ∃ sym : String, sym ∈ exts ∧ GhostSymActiveWithExtra ghFixed extra sym f ∧ pc = ρ sym := by
  induction exts with
  | nil => simp at h
  | cons e tl ih =>
    simp only [List.map_cons, List.findSome?_cons] at h ⊢
    cases hoo : ((ρ e - base).toNat == (pc - base).toNat) with
    | false =>
      simp only [hoo, Bool.false_eq_true, ↓reduceIte] at h ⊢
      rcases ih h with hL | ⟨sym, hmem, hAct, hpc⟩
      · exact Or.inl hL
      · exact Or.inr ⟨sym, List.mem_cons_of_mem _ hmem, hAct, hpc⟩
    | true =>
      simp only [hoo, ↓reduceIte] at h ⊢
      cases he : cliGhostExternsWithExtra ghFixed extra baseExt e with
      | none =>
        rw [he] at h
        rw [cliGhostExternsWithExtra_none_imp ghFixed extra baseExt he]
        rcases ih h with hL | ⟨sym, hmem, hAct, hpc⟩
        · exact Or.inl hL
        · exact Or.inr ⟨sym, List.mem_cons_of_mem _ hmem, hAct, hpc⟩
      | some g =>
        rw [he] at h
        injection h with hgf
        subst hgf
        rcases cliGhostExternsWithExtra_some_cases ghFixed extra baseExt he with hAct | hBase
        · have heq : ρ e - base = pc - base := BitVec.eq_of_toNat_eq (beq_iff_eq.mp hoo)
          have hpc_eq : pc = ρ e := by
            have h1 := congrArg (· + base) heq.symm
            simpa only [BitVec.sub_add_cancel] using h1
          exact Or.inr ⟨e, List.Mem.head _, hAct, hpc_eq⟩
        · rw [hBase]
          exact Or.inl rfl

private theorem blockProgram_cliGhostExternsWithExtra_externAt?_mem_cases
    {lib : Obj.MultiPlacedLib} {mpl : Obj.MultiPlacement} {idx : Nat}
    (ghFixed : CliGhostHooks) (extra : ExtraGhostTable)
    (baseExt : String → Option (State → State))
    {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram mpl idx (cliGhostExternsWithExtra ghFixed extra baseExt)).externAt? pc =
      some f) :
    (lib.blockProgram mpl idx baseExt).externAt? pc = some f ∨
      ∃ sym : String, sym ∈ (lib.blockLib idx).text.externs ∧
        GhostSymActiveWithExtra ghFixed extra sym f ∧ pc = lib.resolve mpl sym := by
  unfold Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program Program.externAt? Program.hookAtOff? at h ⊢
  simp only [ite_self] at h ⊢
  rw [findSome?_const_none, Option.or_none] at h ⊢
  exact findSome?_stubs_cliGhostExternsWithExtra_mem_cases
    (lib.blockLib idx).text.externs (lib.blockPlacement mpl idx).ρ
    (lib.blockPlacement mpl idx).base pc ghFixed extra baseExt h

private theorem pGhost617_codeLoaded_of_libsignalFrozen_anyExt
    (mpl : Obj.MultiPlacement) (EG : CliHooks → String → Option (State → State))
    (W : CliHooks) (m : Memory) (hFrz : LibsignalFrozen mpl m) :
    (cliProgExtPlacedAt mpl EG 617 W).CodeLoaded m := by
  have h617 : 617 < libsignalSessionLib.blocks.length := by
    have hlen := Nat.beq_eq.mp libsignalBlocks_len
    have hge : 618 ≤ f3LsBlocksLen := by decide
    omega
  have hc := hFrz.2 617 h617
  exact Arm64.Program.CodeLoaded.intro hc.aligned hc.no_wrap fun i hi =>
    ⟨hc.byte_eq i hi, hc.perm_eq i hi, hc.isLazyFree_eq i hi⟩

/-! ### (R5.3) Combined 10-Named + 10-Extra `codeOnly` Transfer at `h2k_ghFixedK` -/

/-- Table-parametric core of **R5.3** over arbitrary `extra : ExtraGhostTable`. -/
theorem block617TransferFixedG_replaysOn_false_codeOnly_extraList [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (extra : ExtraGhostTable)
    (guardOf : String → State → Prop)
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hRealNone : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActiveNamed (h2k_ghFixedK mpl mmpl) sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActiveNamed (h2k_ghFixedK mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        (sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
          hole2_keepSub (u.readReg64 .lr) = false) →
        (sym = lsMemsetSym → keepMemsetBlk21 mmpl (u.readReg64 .lr) = false) →
        (sym = lsMemcpySym → keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false) →
        F3CodeInv mpl mmpl u.mem →
        (sym = lsReadFileSym → FdsGe3Closed u.fs) →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u))
    (hNoExLr : ∀ {sym : String} {f : State → State} {a : State},
      cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) [] (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      (∀ msg, (f a).status ≠ .Exception msg) →
      sym ≠ lsMemsetSym →
      sym ≠ lsMemcpySym →
      hole2_keepSub (a.readReg64 .lr) = false)
    (hNoExFds : ∀ {baseExt : String → Option (State → State)} {f : State → State} {a : State},
      cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) extra baseExt lsReadFileSym = some f →
      (∀ msg, (f a).status ≠ .Exception msg) →
      FdsGe3Closed a.fs)
    (hTrap21 : ∀ {sym : String} {f : State → State},
      cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) [] (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hTrap20 : ∀ {sym : String} {f : State → State},
      cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) [] (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hBlk21Ext : ∀ (W : CliHooks) (pc : BitVec 64), keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) extra (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) extra (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hBlk20Ext : ∀ (W : CliHooks) (pc : BitVec 64), keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) extra (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) extra (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hExtraReplays : ExtraListReplaysOn mpl mmpl
      (fun u : State => F3CodeInv mpl mmpl u.mem ∧ True) guardOf (h2k_ghFixedK mpl mmpl) extra) :
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) extra (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl)
      (fun s0 => F3MemsetMemcpyEntryLrFalse mmpl s0 ∧ ExtraListEntryGuard guardOf extra s0)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk := by
  have hmng20 : (20 : Nat) < mallocngLib.blocks.length := by decide
  have hmng21 : (21 : Nat) < mallocngLib.blocks.length := by decide
  refine block617TransferFixedG_of_replaysOn
    (fun _ => false) (F3CodeInv mpl mmpl) (fun _ => True)
    (noNewHooks_cliProgExtPlacedAt_of_ext_none_imp mpl 617
      (fun W _sym h =>
        cliGhostExternsWithExtra_none_imp (h2k_ghFixedK mpl mmpl) extra (cliExternsPlaced mmpl W) h))
    hF3Frozen
    (pGhost617_codeLoaded_of_libsignalFrozen_anyExt mpl _)
    (fun _ h => h.2) (fun _ h => h.1) (fun _ _ h hkf => h.of_keepsFrozen hkf)
    (fun _ => trivial) ?_
  intro W _i s0 sf
  dsimp only
  intro hGuard0 _hReal0 _hpc0 _hfs0 _htr0 _hsteps hret_pc hnoex hnhalt
  have hrun_sf21 : sf.status = .Running → keepMemsetBlk21 mmpl sf.pc = false :=
    fun hrs => hret_pc hrs ▸ hGuard0.1.1
  have hrun_sf20 : sf.status = .Running → keepMemcpyBlk20 mmpl sf.pc = false :=
    fun hrs => hret_pc hrs ▸ hGuard0.1.2
  refine ⟨?_, fun _ _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ => rfl⟩
  intro pc f heg
  rcases blockProgram_cliGhostExternsWithExtra_externAt?_mem_cases
      (h2k_ghFixedK mpl mmpl) extra (cliExternsPlaced mmpl W) heg with
    her | ⟨sym, hsym_ext, hAct, hpc_eq⟩
  · obtain ⟨sym, hsym⟩ := blockProgram_externAt?_some_exists her
    refine Or.inl ⟨her, fun u _ _ _ _ _ hkf hfr ⟨hinv, _⟩ => ?_⟩
    exact ⟨cliExternsPlaced_preserves_execFrozen mmpl W hsym u hfr,
      hinv.of_keepsFrozen hkf, trivial⟩
  · rcases (GhostSymActiveWithExtra_iff_named_or_extra _ _ _ _).mp hAct with
      hActNamed | ⟨hDom, hLook⟩
    · refine Or.inr ⟨hpc_eq ▸ hRealNone W sym f hsym_ext hActNamed,
        fun u _ hrest hpc hrun hnoex_fu hkf hfr _ ⟨hinv, _⟩ => ?_⟩
      have hne_sc : sym ≠ lsStringCloneSym := fun heq =>
        h2ef_strClone_not_mem_ext617 (heq ▸ hsym_ext)
      have hext_nil :
          cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) [] (fun _ => none) sym = some f :=
        cliGhostExternsWithExtra_nil_of_named (h2k_ghFixedK mpl mmpl) (fun _ => none) hActNamed
      have hext_extra :
          cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) extra (fun _ => none) sym = some f :=
        cliGhostExternsWithExtra_eq_some_of_active (h2k_ghFixedK mpl mmpl) extra (fun _ => none) hAct
      have hinv_fu : F3CodeInv mpl mmpl (f u).mem := hinv.of_keepsFrozen hkf
      have hlr_sub : sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
          hole2_keepSub (u.readReg64 .lr) = false :=
        fun hnoShim hnoMs hnoMc => hNoExLr hext_nil hnoShim hnoex_fu hnoMs hnoMc
      have hlr_blk21 : sym = lsMemsetSym → keepMemsetBlk21 mmpl (u.readReg64 .lr) = false :=
        fun hms => blk21_lr_trap_after_hook_ret
          (hTrap21 hext_nil (by subst hms; decide)) (hBlk21Ext W)
          (hinv_fu.mngBlockCodeLoaded 21 hmng21 _ _ Syscall.standard)
          hrest hrun hrun_sf21 hnoex hnhalt
      have hlr_blk20 : sym = lsMemcpySym → keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false :=
        fun hmc => blk20_lr_trap_after_hook_ret
          (hTrap20 hext_nil (by subst hmc; decide)) (hBlk20Ext W)
          (hinv_fu.mngBlockCodeLoaded 20 hmng20 _ _ Syscall.standard)
          hrest hrun hrun_sf20 hnoex hnhalt
      have hread_fds : sym = lsReadFileSym → FdsGe3Closed u.fs :=
        fun hrd => hNoExFds (hrd ▸ hext_extra) hnoex_fu
      have hst_r : Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) :=
        hGhostReplay W sym f hsym_ext hne_sc hActNamed u (hpc.trans hpc_eq) hrun hnoex_fu hkf hfr
          hlr_sub hlr_blk21 hlr_blk20 hinv hread_fds
      exact ⟨hst_r,
        h2ef_h2k_ghFixedK_withExtra_preserves_execFrozen mpl mmpl hExtraReplays hAct u hrun hnoex_fu hfr,
        hinv_fu, trivial⟩
    · exact extraListReplaysOn_arm (W := W) (fun _ => false) hExtraReplays hGuard0.2
        hDom hLook hpc_eq hret_pc hnoex hnhalt

/-- **(R5.3)** Direct Cutover-2 generalization of
    `H2ExecFrozenWire.h2ef_block617TransferFixedG_replaysOn_false_codeOnly`
    (`ElfSlicesPqOomH2ExecFrozenWire.lean:2325–2390`), following H-REV4 `rev_api_A.md` steps 1–6
    and `api_A.md` §5R.b L930–999 verbatim (`keep := fun _ => false`, `PredFs := fun _ => True`). -/
theorem block617TransferFixedG_replaysOn_false_codeOnly_withExtra [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    {libcAddr brkStart : BitVec 64} {stk : Nat}
    (guardOf : String → State → Prop)
    (hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (hRealNone : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      GhostSymActiveNamed (h2k_ghFixedK mpl mmpl) sym f →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) = none)
    (hGhostReplay : ∀ (W : CliHooks) (sym : String) (f : State → State),
      sym ∈ (libsignalSessionLib.blockLib 617).text.externs →
      sym ≠ lsStringCloneSym →
      GhostSymActiveNamed (h2k_ghFixedK mpl mmpl) sym f →
      ∀ u : State,
        u.pc = libsignalSessionLib.resolve mpl sym →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        u.mem.KeepsFrozen (f u).mem →
        ExecFrozen u.mem →
        (sym ≠ lsRustNoAllocShimSymCli → sym ≠ lsMemsetSym → sym ≠ lsMemcpySym →
          hole2_keepSub (u.readReg64 .lr) = false) →
        (sym = lsMemsetSym → keepMemsetBlk21 mmpl (u.readReg64 .lr) = false) →
        (sym = lsMemcpySym → keepMemcpyBlk20 mmpl (u.readReg64 .lr) = false) →
        F3CodeInv mpl mmpl u.mem →
        (sym = lsReadFileSym → FdsGe3Closed u.fs) →
        Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u))
    (hNoExLr : ∀ {sym : String} {f : State → State} {a : State},
      cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) [] (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      (∀ msg, (f a).status ≠ .Exception msg) →
      sym ≠ lsMemsetSym →
      sym ≠ lsMemcpySym →
      hole2_keepSub (a.readReg64 .lr) = false)
    (hNoExFds : ∀ {baseExt : String → Option (State → State)} {f : State → State} {a : State},
      cliGhostExterns (h2k_ghFixedK mpl mmpl) baseExt lsReadFileSym = some f →
      (∀ msg, (f a).status ≠ .Exception msg) →
      FdsGe3Closed a.fs)
    (hTrap21 : ∀ {sym : String} {f : State → State},
      cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) [] (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hTrap20 : ∀ {sym : String} {f : State → State},
      cliGhostExternsWithExtra (h2k_ghFixedK mpl mmpl) [] (fun _ => none) sym = some f →
      sym ≠ lsRustNoAllocShimSymCli →
      ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hBlk21Ext : ∀ (W : CliHooks) (pc : BitVec 64), keepMemsetBlk21 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemsetBlk21 mmpl L = true → Blk21TrapHook L f)
    (hBlk20Ext : ∀ (W : CliHooks) (pc : BitVec 64), keepMemcpyBlk20 mmpl pc = true →
      (cliProgExtPlacedAt mpl
        (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
        617 W).externAt? pc = none ∨
        ∃ f, (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W'))
          617 W).externAt? pc = some f ∧
          ∀ L : BitVec 64, keepMemcpyBlk20 mmpl L = true → Blk20TrapHook L f)
    (hExtraReplays : ExtraReplaysOn mpl mmpl
      (fun u : State => F3CodeInv mpl mmpl u.mem ∧ True) guardOf (h2k_ghFixedK mpl mmpl)) :
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl)
      (fun s0 => F3MemsetMemcpyEntryLrFalse mmpl s0 ∧
        ExtraEntryGuard guardOf (h2k_ghFixedK mpl mmpl) s0)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl) libcAddr brkStart stk := by
  rw [cliGhostExterns_eq_withExtra (h2k_ghFixedK mpl mmpl)] at hNoExFds hBlk21Ext hBlk20Ext ⊢
  exact block617TransferFixedG_replaysOn_false_codeOnly_extraList
    mpl mmpl (h2k_ghFixedK mpl mmpl).extra guardOf hF3Frozen hRealNone hGhostReplay
    hNoExLr hNoExFds hTrap21 hTrap20 hBlk21Ext hBlk20Ext hExtraReplays

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWireExtra
