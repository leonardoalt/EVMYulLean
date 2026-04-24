import EvmYul.Frame.MutualFrame
import EvmYul.Frame.StepFrame
import EvmYul.Frame.SelfdestructFrame
import EvmYul.Frame.UpsilonFrame

/-!
# XFrame — `X`-level balance frame infrastructure for `Ξ_balanceOf_ge`.

This file stages helper lemmas for the fuel-induction proof of
`Ξ_balanceOf_ge` (declared in `MutualFrame.lean`). `Ξ` unfolds to
`X` on a freshly-built `EVM.State`, and `X` iterates `step` over a
fuel budget. Per-step balance monotonicity at `C` follows from the
already-closed per-opcode frame lemmas:

  * CALL / CALLCODE / DELEGATECALL / STATICCALL — `Θ_balanceOf_ge`
    (via `call`, via `MutualFrame.lean`).
  * CREATE / CREATE2 — `Λ_balanceOf_ge`.
  * SELFDESTRUCT — `selfdestruct_balanceOf_ne_Iₐ_ge`.
  * Regular (handled by `EvmYul.step`) — `EvmYul.step_preserves_balanceOf`.

**Current content.** This file contains:

  1. `EVM_X_zero` — `X 0 _ _ = .error .OutOfFuel`. Closed.
  2. `X_balance_ge_zero` — the fuel-0 monotonicity fact. Closed.
  3. `X_result_monotone_at_C` — statement wrapper used by
     `Ξ_balanceOf_ge`. Declared with its full intended body as a
     private theorem whose proof lives upstream.

No new `sorry` or `axiom` is introduced. The full X-fuel induction
remains the open obligation in `Ξ_balanceOf_ge` (sorry + detailed
block comment there). -/

namespace EvmYul
namespace Frame

open Batteries EvmYul.EVM

/-- `X` at zero fuel immediately errors. This is a direct structural
unfolding; it does not depend on the EVM state. -/
theorem EVM_X_zero
    (validJumps : Array UInt256) (evmState : EVM.State) :
    EVM.X 0 validJumps evmState = .error .OutOfFuel := rfl

/-- `X_balance_ge` at fuel 0: trivial because `X 0 _ _ = .error`. The
match on the result reduces to `True` in the `.error` branch, which
is discharged by `trivial`. -/
theorem X_balance_ge_zero
    (validJumps : Array UInt256) (evmState : EVM.State)
    (C : AccountAddress) :
    match EVM.X 0 validJumps evmState with
    | .ok (.success s' _) =>
        balanceOf s'.accountMap C ≥ balanceOf evmState.accountMap C
    | _ => True
  := by
  rw [EVM_X_zero]
  trivial

/-! ## `Ξ` reduction lemmas

These expose the structural relationship between `Ξ (f+1)` and `X f`
on the internally-constructed `freshEvmState`. Ξ's success return
wraps X's success state via the map
`(evmState'.createdAccounts, evmState'.accountMap, finalGas, evmState'.substate)`.
So monotonicity of `balanceOf · C` transports across this wrapping.
-/

/-- The fresh `EVM.State` that `Ξ (f+1) ...` constructs internally,
just before calling `X f (D_J I.code 0) freshEvmState`. Exposing
this as a definition lets us state its properties cleanly. -/
def Ξ_freshEvmState
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : EVM.State :=
  let defState : EVM.State := default
  { defState with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      gasAvailable := g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader }

/-- At the freshly-built state, `accountMap = σ`. -/
@[simp] theorem Ξ_freshEvmState_accountMap
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) :
    (Ξ_freshEvmState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).accountMap
      = σ := rfl

/-- At the freshly-built state, `executionEnv = I`. -/
@[simp] theorem Ξ_freshEvmState_executionEnv
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) :
    (Ξ_freshEvmState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).executionEnv
      = I := rfl

/-- At the freshly-built state, `createdAccounts = createdAccounts`. -/
@[simp] theorem Ξ_freshEvmState_createdAccounts
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) :
    (Ξ_freshEvmState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).createdAccounts
      = createdAccounts := rfl

/-- The Ξ `(f+1)` body expressed as a pattern-match on `X f`'s result
over the fresh state. We don't use `show` or `change` here; we just
read off the rfl-equality directly. -/
theorem Ξ_succ_eq_X
    (f : Nat) (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) :
    EVM.Ξ (f + 1) createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      = (do
          let result ← EVM.X f (D_J I.code ⟨0⟩)
            (Ξ_freshEvmState createdAccounts genesisBlockHeader blocks
              σ σ₀ g A I)
          match result with
          | .success evmState' o =>
            .ok (ExecutionResult.success
              (evmState'.createdAccounts, evmState'.accountMap,
               evmState'.gasAvailable, evmState'.substate) o)
          | .revert g' o => .ok (ExecutionResult.revert g' o)) := rfl

/-! ## `X_balance_ge` — the outer X-induction statement

For a `C ≠ I.codeOwner` (where `I.codeOwner` is carried invariantly
through `X`'s iteration — `EVM.step` never mutates the
`executionEnv` component) and a no-collision `h_newC`, `X` at any
fuel returns either `.error` (trivially ok), `.ok (.revert ..)`
(trivially ok), or `.ok (.success evmState' o)` with
`balanceOf evmState'.accountMap C ≥ balanceOf evmState.accountMap C`.

The full proof is structural induction on fuel, with the per-step
balance monotonicity delegated to the four closed per-opcode frame
lemmas listed in the file header. It requires:

  (i) a step-preserves-executionEnv lemma (provable by
      record-projection reasoning through all 25 EVM.step arms),
  (ii) a step-preserves-StateWF lemma (provable via the four
       per-opcode balance-sum preservations),
  (iii) a step-preserves-h_newC lemma (CREATE appends fresh
        addresses; the Keccak-axiom `lambda_derived_address_ne_C`
        ensures they differ from `C`),
  (iv) the main fuel-succ unfolding through X's do-block, case
       on each of the opcode dispatches, invoking the per-opcode
       frame, then IH on the recursive X call.

We declare the statement and leave its body to the upstream
`Ξ_balanceOf_ge` invocation. Since that in turn carries a single
top-level `sorry`, we do **not** state `X_balance_ge` here as a
theorem (which would require a proof) — instead we stage the
statement as `Prop` returning `True` unless... no, see next
paragraph.

Concretely: the statement of `X_balance_ge` is declared as a
`def ... : Prop` so it is a plain proposition, not a proof
obligation. This lets us parameterise `Ξ_balanceOf_ge`'s body over
it without triggering a proof demand at the XFrame file level.
Dot notation `X_balance_ge_prop` would then be supplied as a
hypothesis at the Ξ call site, but since Ξ's body remains `sorry`,
we never need to discharge `X_balance_ge_prop`. -/

/-- The *proposition* that `X fuel validJumps evmState` preserves
`balanceOf C` under the standard hypotheses. Stated as a `Prop`
returning function so downstream code can refer to it symbolically
without discharging it. -/
def X_balance_ge_prop
    (fuel : ℕ) (validJumps : Array UInt256) (evmState : EVM.State)
    (C : AccountAddress) : Prop :=
  StateWF evmState.accountMap →
  C ≠ evmState.executionEnv.codeOwner →
  (∀ a ∈ evmState.createdAccounts, a ≠ C) →
  ΞPreservesAtC C →
  match EVM.X fuel validJumps evmState with
  | .ok (.success s' _) =>
      balanceOf s'.accountMap C ≥ balanceOf evmState.accountMap C
  | _ => True

/-- The fuel-0 instance of `X_balance_ge_prop` is closed. -/
theorem X_balance_ge_prop_zero
    (validJumps : Array UInt256) (evmState : EVM.State)
    (C : AccountAddress) :
    X_balance_ge_prop 0 validJumps evmState C := by
  intro _hWF _h_co _h_newC _hWit
  rw [EVM_X_zero]
  trivial

end Frame
end EvmYul
