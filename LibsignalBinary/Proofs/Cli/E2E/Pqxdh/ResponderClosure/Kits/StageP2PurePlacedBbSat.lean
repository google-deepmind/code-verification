/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedSat -- proof-setup: allow-public-import

/-!
# `HookSat` `black_box` Sibling of `StageP2PurePlaced` (`Kits/StageP2PurePlacedBbSat.lean`)

Provides `isSameAccount_placed_ok_on_stageP1_sat` and `isSameAccount_4k_placed_ok_on_stageP1_sat`
on `stageP1ProgPlaced ext` from `HookSat ext lsBlackBoxU8Sym blackBoxSpecSat` (replacing
`ext lsBlackBoxU8Sym = some blackBoxHook` in `StageP2PurePlaced.lean:455, 466`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBbSat

open Arm64 ProofLib
open CryptoVerification
  (LibsignalPlacement blkPC_252 blkPl_252 lsBlackBoxU8Sym lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (uuidTryParseCodeSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.E2E.Pqxdh.WireEntries (isSameAccountDistinctSpec)
open CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq (isSameAccountDistinctSpecExt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
  (isSameAccountDistinctSpec_lscl_to_ext stageP1ProgPlaced)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedSat
  (isSameAccountEqDistinct_placed_ok_at_sat)

/-- `<IdentityKey>::is_same_account` (`lsmpl.base 17`) on `stageP1ProgPlaced ext` from
`HookSat ext lsBlackBoxU8Sym blackBoxSpecSat`. -/
theorem isSameAccount_placed_ok_on_stageP1_sat [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hBb : HookSat ext lsBlackBoxU8Sym blackBoxSpecSat)
    (hUuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base ext) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse))) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)) :=
  isSameAccountEqDistinct_placed_ok_at_sat A hBb hUuid (by decide)

/-- 4K/`Ext` `<IdentityKey>::is_same_account` (`lsmpl.base 17`) on `stageP1ProgPlaced ext` from
`HookSat ext lsBlackBoxU8Sym blackBoxSpecSat`. -/
theorem isSameAccount_4k_placed_ok_on_stageP1_sat [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hBb : HookSat ext lsBlackBoxU8Sym blackBoxSpecSat)
    (hUuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base ext) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse))) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A uuidTryParse)) :=
  isSameAccountDistinctSpec_lscl_to_ext (isSameAccount_placed_ok_on_stageP1_sat hBb hUuid)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBbSat
