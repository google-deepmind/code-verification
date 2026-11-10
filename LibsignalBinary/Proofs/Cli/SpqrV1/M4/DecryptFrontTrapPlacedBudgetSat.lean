/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart3Sat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetPart4Sat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexBudgetSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplayBudget
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget

/-!
# `HookSat` Sibling of `DecryptFrontTrapPlacedBudget` (`DecryptFrontTrapPlacedBudgetSat`)

Re-proves the `memset`-dependent Block `433` segment seams (`s6_433_cli`, `dhStep_pinned_433_cli`,
`dhStep_433_cli`, `s4_433_cli_ofEnv`, `s4_433_cli`, and `s7_433_cli`) parameterized by
`HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec`,
while preserving the remaining `memset`-free Block `433` seams (`errTail_433_cli`,
`pqRecv_433_cli_ofEnv`, `pqRecv_433_cli`, `aesDecrypt_433_cli`, `s1_pinned_433_cli`, `s1_433_cli`,
`s9_433_cli`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetSat

open Arm64 ProofLib
open CryptoVerification
  (LibsignalPlacement blkPC_69 blkPl_69 ls_hook_ok_ultra_of_mem
   ls_subroutine_ok_of_block lsmpl subroutine_ok_withLsCodeLoaded_of_plain)
open CryptoVerification.E2E (aesDecHookMallocng fmtWriteHook0)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (lsMemcpySym lsMemsetSym)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet
  (SendCall SpqrModel keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro
   sessionMemsetRegionSpec subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (blkPC_434 blkPl_434 instIsLsBlockProg_434)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced cliHookTablePlaced lsFmtWriteSym lsFormatInnerSym
   lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
   lsRustReallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_panic_all cliGhostExterns_sat_of_cliExternsPlaced
   compress256_row_placed fmtWrite_row_placed)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fmtWriteHook0_budget_ok)
open LibsignalBinary.Heap.SpecBudget
  (FormatInnerEnv aesDecBudgetSpec fmtWriteBudgetEnvSpec formatInnerBudgetEnvSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget
  (CmkSeg4Env consumeMsgKey_433_placed_ok_ofEnv s4DefaultEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget (s8Env s9Env)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrRecvTrapV1PlacedBudget (deriveKeys_433_placed_ok)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (s7Env)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS1ErrPlacedBudget
  (S1TightSeamFreePlaced S1TightSeamPinnedFreePlaced)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
  (ErrTailTightSeamPlaced S3TightSeamPinnedPlaced S3TightSeamPlaced
   S4SeamPlaced S5WTSeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkAllocHooks)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
  (expand_multi_info_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (extract_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_exactMemcpy_sat cliExternsPlaced_realloc_budget_sat
   cliExternsPlaced_sessionMemsetRegion_budget_sat cliExternsPlaced_shim_budget_sat
   cliGhostExterns_blackBoxSat_budget_sat cliGhostExterns_sessionMemmove_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
  (SpqrRecvBytesEnv SpqrV1PlacedSeams SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (HkdfPlacedHooksExactSat hookSat_sessionMemsetRegion_of_budget)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplayBudget
  (addrDisplay_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget
  (generateKeys_placed_ok_of_contracts)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

section CmkBbSat

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (IsLsBlockProg LibsignalCodeLoaded blkPC_24 blkPl_24 extract_withLsCodeLoaded lsBlackBoxU8Sym lsRustReallocSym withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet (extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (ls_subroutine_ok_transfer_of_plain)
open LibsignalBinary.Heap (rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkEnv cmkPlacedSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetSat (grow_one_placed_ok_at_cmk_sat hmac_sha256_placed_ro_ok_at_cmk_sat)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexBudgetSat (find_receiver_chain_index_placed_ok_at_cmk_sat)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat)
open LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget (cmkPlacedRoSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudgetSat (consume_message_key_placed_ro_run_of_sat)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (sessionMemmoveBoundedBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (cmkRawSpecPlaced)

attribute [local irreducible]
  CryptoVerification.LibsignalSession.cmkDummyImg
  CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptPlacedImg

private theorem cmkPlacedSpec_pre_eq_raw [LibsignalPlacement] (F : ShaCompress)
    (A' : CryptoVerification.RustHeap.RustAlloc)
    (x : CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost) (s : State) :
    (CryptoVerification.LibsignalSession.cmkPlacedSpec F A').pre x s =
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced F A').pre x s ∗
        ⌜LibsignalCodeLoaded lsmpl s.mem⌝ := by
  dsimp only [CryptoVerification.LibsignalSession.cmkPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced,
    withLsCodeLoaded]
  rw [CryptoVerification.LibsignalTripleRatchet.Decrypt.logOff_tryDecryptPlacedImg]

private theorem cmkPlacedSpec_post_eq_raw [LibsignalPlacement] (F : ShaCompress)
    (A' : CryptoVerification.RustHeap.RustAlloc)
    (x : CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost) (s0 sf : State) :
    (CryptoVerification.LibsignalSession.cmkPlacedSpec F A').post x s0 sf =
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced
        F A').post x s0 sf := by
  dsimp only [CryptoVerification.LibsignalSession.cmkPlacedSpec,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.cmkRawSpecPlaced,
    withLsCodeLoaded]
  rw [CryptoVerification.LibsignalTripleRatchet.Decrypt.logOff_tryDecryptPlacedImg]

private theorem cmk_raw_placed_cro_ok_at_block_bb_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    (F : ShaCompress) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : HookSatExactMemcpy H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym)
    (h_ms : HookSat H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 24)
      (withLsCodeRoLoaded lsmpl (cmkRawSpecPlaced F A lim CmkEnv)) := by
  have hcmk0 : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (blkPl_24).base
      (cmkPlacedRoSpec F A lim) :=
    consume_message_key_placed_ro_run_of_sat F A lim H
      (find_receiver_chain_index_placed_ok_at_cmk_sat A h_bb)
      (hmac_sha256_placed_ro_ok_at_cmk_sat F h_mc h_ms h_c256)
      (grow_one_placed_ok_at_cmk_sat hA h_realloc) hA hmm
  have htr : subroutine_ok callerProg (lsmpl.base 24)
      (withLsCodeLoaded lsmpl (cmkPlacedRoSpec F A lim)) :=
    ls_subroutine_ok_transfer_of_plain hcmk0 hi
  refine subroutine_ok_outcome_intro fun ⟨x, st_init⟩ R s0 hpc hrun hpre hsp => ?_
  have ⟨⟨hcl, hro⟩, hp⟩ := extract_withLsCodeRoLoaded hpre
  refine htr.mono_outcome (x, st_init) R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [cmkRawSpecPlaced] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    dsimp only [withLsCodeLoaded, cmkPlacedRoSpec, cmkPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [cmkPlacedSpec_pre_eq_raw, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hp.1, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hro, hp.2⟩
  · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [cmkPlacedRoSpec, cmkPlacedSpec, cmkRawSpecPlaced, withLsCodeRoLoaded] at hq ⊢
      simp only [cmkPlacedSpec_post_eq_raw] at hq
      exact hq
    · exact Or.inr (Or.inl ⟨hpan, hq⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

end CmkBbSat

private theorem cliGhost_row (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide) (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide) (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide) (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ CryptoVerification.SignalSession.lsReadFileSym := by decide)
    (h8 : sym ≠ CryptoVerification.SignalSession.lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide) (h10 : sym ≠ lsMemcpySym := by decide)
    (hExtra : CryptoVerification.SignalSession.Cli.RunGlue.cliExtraGhostSyms.contains sym = false := by decide) :
    cliGhostExterns g (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (Or.inl hExtra)).trans (cliExternsPlaced_row mmpl W hrow)

private theorem mkHkdfPlacedHooksExactSat_cli [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  { memset := hookSat_sessionMemsetRegion_of_budget
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
    memcpy := cliExternsPlaced_exactMemcpy_sat mmpl g W hG
    compress256 := cliGhost_row mmpl g W (compress256_row_placed mmpl W) }

theorem blk433_s3_entry_eq [LibsignalPlacement] : (blkPl_434).base = lsmpl.base 434 := rfl

theorem errTail_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    ErrTailTightSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S tdEnv :=
  DecryptFrontTrapPlacedBudget.errTail_433_cli mmpl g W hG ctl S tdEnv

theorem pqRecv_433_cli_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SendEnv : SendCall → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hSpqr : SpqrV1PlacedSeamsOfEnv M A lim mmpl g W InitEnv
      (fun st msg => RecvBytesEnv st.bytes msg.bytes) SendEnv)
    (hFmtInner : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFormatInnerSym
      (formatInnerBudgetEnvSpec M A lim fmtEnv))
    (ctl : BitVec 64) :
    S5WTSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) RecvBytesEnv fmtEnv) :=
  DecryptFrontTrapPlacedBudget.pqRecv_433_cli_ofEnv mmpl g W hG hSpqr hFmtInner ctl

theorem pqRecv_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl g W) (ctl : BitVec 64) :
    S5WTSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base tokenInitPlacedAt W.C A lim ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (PqRecvEnv (spqrV1 W.C.F W.Q.K) SpqrRecvBytesEnv FormatInnerEnv) :=
  DecryptFrontTrapPlacedBudget.pqRecv_433_cli mmpl g W hG hSpqr ctl

theorem aesDecrypt_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hAesDec : HookOk (aesDecHookMallocng mmpl W.C.D) (aesDecBudgetSpec W.C.D M A lim))
    (ctl : BitVec 64) (S : SpqrModel) :
    S8SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S s8Env :=
  DecryptFrontTrapPlacedBudget.aesDecrypt_433_cli mmpl g W hG hAesDec ctl S

theorem s1_pinned_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S1TightSeamPinnedFreePlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S tdEnv (fun _ => FreeOnlyEvs) :=
  DecryptFrontTrapPlacedBudget.s1_pinned_433_cli mmpl g W hG ctl S tdEnv

theorem s1_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S1TightSeamFreePlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S tdEnv (fun _ => FreeOnlyEvs) :=
  DecryptFrontTrapPlacedBudget.s1_433_cli mmpl g W hG ctl S tdEnv

/-- `S6SeamPlaced` on Block `433` at `cliGhostExterns g (cliExternsPlaced mmpl W)`
under `HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem s6_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (ctl : BitVec 64) :
    S6SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl s6FreeOnlyEnv := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_434 H
  have _ : HkdfPlacedHooksExactSat W.C.F H := mkHkdfPlacedHooksExactSat_cli mmpl g W hG
  have _ : HkdfPlacedHooksExactBudgetSat W.C.F H := HkdfPlacedHooksExactBudgetSat.of_exactSat hMs
  have hgk69 := generateKeys_placed_ok_of_contracts
    (extract_placed_vm_ok_of_other_block_sat W.C
      (callerProg := (blkPC_69).rebase (blkPl_69).base H) H)
    (expand_multi_info_placed_vm_ok_of_other_block_sat W.C
      (callerProg := (blkPC_69).rebase (blkPl_69).base H) H)
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))
  exact deriveKeys_433_placed_ok W.C A lim ctl H
    (keys_ls_subroutine_ok_of_block_cro
      (callerProg := (blkPC_434).rebase (blkPl_434).base H) hgk69)

theorem s9_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S9SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S tdEnv s9Env :=
  DecryptFrontTrapPlacedBudget.s9_433_cli mmpl g W hG ctl S tdEnv

/-- Pinned `S3TightSeamPinnedPlaced` on Block `433`
under `HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem dhStep_pinned_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (ctl : BitVec 64) (S : SpqrModel) :
    S3TightSeamPinnedPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 434) W.C A lim ctl uuidTryParse S (s3DefaultEnv W.C) :=
  DecryptFrontTrapPlacedBudgetPart4Sat.dhStep_pinned_433_cli mmpl g W hG hMs ctl S

/-- Unpinned `S3TightSeamPlaced` on Block `433`
under `HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem dhStep_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (ctl : BitVec 64) (S : SpqrModel) :
    S3TightSeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 434) W.C A lim ctl uuidTryParse S (s3DefaultEnv W.C) :=
  (dhStep_pinned_433_cli mmpl g W hG hMs ctl S).toUnpinned

/-- Envelope-parametric `S4SeamPlaced` on Block `433`
under `HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem s4_433_cli_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {fmtWriteEnv : List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (hFmtWrite : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsFmtWriteSym
      (fmtWriteBudgetEnvSpec M A lim fmtWriteEnv))
    (ctl : BitVec 64) (S : SpqrModel) :
    S4SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S (CmkSeg4Env fmtWriteEnv) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_434 H
  have hH_cmk : HkdfPlacedHooksExactSat W.C.F H := mkHkdfPlacedHooksExactSat_cli mmpl g W hG
  have hA_cmk : CmkAllocHooks A lim H :=
    ⟨cliExternsPlaced_alloc_budget_sat mmpl g W hG,
     cliExternsPlaced_dealloc_budget_sat mmpl g W hG,
     cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq,
     cliGhostExterns_panic_all mmpl g W _ (by decide),
     cliGhostExterns_panic_all mmpl g W _ (by decide),
     cliGhostExterns_panic_all mmpl g W _ (by decide)⟩
  have h215 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (addrDisplay_placed_ok hFmtWrite)
  exact consumeMsgKey_433_placed_ok_ofEnv W.C A lim ctl S fmtWriteEnv H
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block
        (callerProg := (blkPC_434).rebase (blkPl_434).base H) h215))
    (cmk_raw_placed_cro_ok_at_block_bb_sat
      (callerProg := (blkPC_434).rebase (blkPl_434).base H)
      W.C.F A lim hA_cmk
      (cliGhostExterns_sessionMemmove_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk 4096)
      (cliGhostExterns_blackBoxSat_budget_sat g (cliExternsPlaced mmpl W) hG.extraOk)
      (cliExternsPlaced_realloc_budget_sat mmpl g W hG)
      hH_cmk.memcpy
      hMs
      hH_cmk.compress256)
    (ls_hook_ok_ultra_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

/-- Default `s4DefaultEnv` `S4SeamPlaced` on Block `433`
under `HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem s4_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (ctl : BitVec 64) (S : SpqrModel) :
    S4SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S s4DefaultEnv :=
  s4_433_cli_ofEnv mmpl g W hG hMs
    ⟨fmtWriteHook0, cliGhost_row mmpl g W (fmtWrite_row_placed mmpl W),
      fmtWriteHook0_budget_ok M A lim⟩
    ctl S

/-- `S7SeamPlaced` on Block `433`
under `HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem s7_433_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (ctl : BitVec 64) (S : SpqrModel) :
    S7SeamPlaced
      ((blkPC_434).rebase (blkPl_434).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_434).base W.C A lim ctl uuidTryParse S (s7Env W.C.F uuidTryParse) :=
  DecryptFrontTrapPlacedBudgetPart3Sat.s7_433_cli_of_hMs mmpl g W hG hMs ctl S

end LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptFrontTrapPlacedBudgetSat
