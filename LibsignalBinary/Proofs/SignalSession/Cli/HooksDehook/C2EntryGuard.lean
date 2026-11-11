/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrExtraReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.SharedSecretDropGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays -- proof-setup: allow-public-import

/-!
# Canonical Cutover-2 Entry Guard Leaf (`HooksDehook.C2EntryGuard`)

`CliElf`-free, `[LibsignalPlacement]`-free, `ghFixed`-free Cutover-2 entry-guard definitions
(`api_A.md` §5R.c + H-REV4 `§5R verdict` `C1`–`C3`):

1. `c2GuardOf mpl sym s0`: canonical per-symbol entry guard over all 10 `cliExtraGhostSyms` rows.
2. `F3C2EntryGuard mpl mmpl s0`: conjoins the raw `keepMemsetBlk21` / `keepMemcpyBlk20` entry-`lr`
   conjunct (`rfl`-equal to `F3MemsetMemcpyEntryLrFalse mmpl s0`, avoiding `CliStrictPlaced2G`
   import cycles and `CliElf` closure bloat) with `c2GuardOf mpl sym s0` across `cliExtraGhostSyms`.
3. `f3C2EntryGuard_imp_and_extraEntryGuard`: contravariant `Block617TransferFixedHypG.mono_guard`
   adapter into `ExtraEntryGuard (c2GuardOf mpl) gh s0` for arbitrary `gh : CliGhostHooks`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard

open Arm64 Arm64.Obj
open CryptoVerification.SignalSession (
  lsBlackBoxSym lsDurationSinceSym lsFromUtf8Sym lsMemrchrSym
  lsSharedSecretDropSym lsStaticSecretDropSym lsTimeAddSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (cliExtraGhostSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (ExtraEntryGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (keepMemcpyBlk20)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (keepMemsetBlk21)

/-- Canonical per-symbol Cutover-2 entry guard over the 10 `cliExtraGhostSyms` rows. -/
@[expose] def c2GuardOf (mpl : Obj.MultiPlacement) (sym : String) (s0 : State) : Prop :=
  if sym == "memmove" then MemmoveExtraReplays.memmoveEntryGuard mpl s0
  else if sym == "bcmp" then BcmpGhostReplays.bcmpEntryGuard mpl s0
  else if sym == "strlen" then StrlenGhostReplays.strlenEntryGuard mpl s0
  else if sym == lsMemrchrSym then MemrchrExtraReplays.memrchrEntryGuard mpl s0
  else if sym == lsFromUtf8Sym then FromUtf8GhostReplays.fromUtf8EntryGuard mpl s0
  else if sym == lsDurationSinceSym then DurationSinceGhostReplays.durationSinceEntryGuard mpl s0
  else if sym == lsTimeAddSym then TimeAddGhostReplays.timeAddEntryGuard mpl s0
  else if sym == lsBlackBoxSym then BlackBoxGhostReplays.blackBoxEntryGuard mpl s0
  else if sym == lsStaticSecretDropSym then StaticSecretDropGhostReplays.staticSecretDropEntryGuard mpl s0
  else if sym == lsSharedSecretDropSym then SharedSecretDropGhostReplays.sharedSecretDropEntryGuard mpl s0
  else True

/-- `ghFixed`-free, `[LibsignalPlacement]`-free, `CliElf`-free Cutover-2 real-side entry guard for
    F3 / Hole-2: conjoins raw `keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧ keepMemcpyBlk20 mmpl
    (s0.readReg64 .lr) = false` (`rfl`-equal to `F3MemsetMemcpyEntryLrFalse mmpl s0`) with
    `c2GuardOf mpl sym s0` across all 10 `cliExtraGhostSyms`. -/
@[expose] def F3C2EntryGuard (mpl mmpl : Obj.MultiPlacement) (s0 : State) : Prop :=
  (keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧
    keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false) ∧
    ∀ sym : String, cliExtraGhostSyms.contains sym = true → c2GuardOf mpl sym s0

theorem f3C2EntryGuard_imp_and_extraEntryGuard
    (mpl mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (s0 : State)
    (h : F3C2EntryGuard mpl mmpl s0) :
    (keepMemsetBlk21 mmpl (s0.readReg64 .lr) = false ∧
      keepMemcpyBlk20 mmpl (s0.readReg64 .lr) = false) ∧
      ExtraEntryGuard (c2GuardOf mpl) gh s0 :=
  ⟨h.1, fun sym _f hDom _hLook => h.2 sym hDom⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard
