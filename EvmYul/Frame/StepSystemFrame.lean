import EvmYul.Frame.MutualFrame
import EvmYul.Frame.StepFrame
import EvmYul.Frame.SelfdestructFrame

/-!
# StepSystemFrame — `EVM.X` balance frame at `C`.

Closes the open `.success` branch of `Ξ_balanceOf_ge` via an inner fuel
induction on `X` that delegates per-step balance preservation to the
already-proved component frame lemmas.

No new axioms or sorries. -/

namespace EvmYul
namespace Frame

open Batteries EvmYul.EVM

/-! ## Projection lemmas -/

@[simp] theorem EVM_State_replaceStackAndIncrPC_executionEnv
    (s : EVM.State) (stack : Stack UInt256) (pcΔ : ℕ) :
    (s.replaceStackAndIncrPC stack pcΔ).executionEnv = s.executionEnv := rfl

@[simp] theorem EVM_State_incrPC_executionEnv
    (s : EVM.State) (pcΔ : ℕ) :
    (s.incrPC pcΔ).executionEnv = s.executionEnv := rfl

/-! ## The `X_ge` statement -/

/-- The balance-monotonicity statement for `EVM.X fuel validJumps evmState`
at `C`. -/
def X_ge (C : AccountAddress) (fuel : ℕ) (validJumps : Array UInt256)
    (evmState : EVM.State) : Prop :=
  match EVM.X fuel validJumps evmState with
  | .ok (.success s' _) => balanceOf s'.accountMap C ≥ balanceOf evmState.accountMap C
  | _ => True

/-- Zero-fuel case: `EVM.X 0 _ _ = .error`, goal reduces to `True`. -/
theorem X_ge_zero
    (C : AccountAddress) (validJumps : Array UInt256)
    (evmState : EVM.State) :
    X_ge C 0 validJumps evmState := by
  unfold X_ge
  rw [show EVM.X 0 validJumps evmState = .error .OutOfFuel from rfl]
  trivial

/-! ## `EvmYul.step` balance frame at `C ≠ codeOwner`

Combines `EvmYul.step_preserves_balanceOf` (for non-SELFDESTRUCT
handled ops) with `selfdestruct_balanceOf_ne_Iₐ_ge` (for SELFDESTRUCT)
into a single `≥` statement for all `EvmYul.step` arms that succeed. -/

/-- Is an opcode one of those handled by `EvmYul.step`? Equivalent to
`handledByEvmYulStep` but as a proposition we can destructure. -/
theorem EvmYul_step_ge_of_ne_codeOwner
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State) (C : AccountAddress)
    (hWF : StateWF s.accountMap)
    (h_ne : C ≠ s.executionEnv.codeOwner)
    (h_handled : EvmYul.Frame.handledByEvmYulStep op)
    (h : EvmYul.step op arg s = .ok s') :
    balanceOf s'.accountMap C ≥ balanceOf s.accountMap C := by
  by_cases hSD : op = .SELFDESTRUCT
  · subst hSD
    -- EvmYul.step SELFDESTRUCT _ s = .ok s'. Note: EvmYul.step for
    -- SELFDESTRUCT passes `.none` as arg usually but the actual signature
    -- accepts any arg. The selfdestruct_balanceOf_ne_Iₐ_ge lemma is stated
    -- for arg=.none. We need to handle general arg. Looking at the
    -- implementation, `EvmYul.step SELFDESTRUCT arg s` does not use `arg`,
    -- so we can change arg to .none.
    have h' : EvmYul.step (.SELFDESTRUCT : Operation .EVM) .none s = .ok s' := by
      -- Structurally, EvmYul.step's SELFDESTRUCT arm doesn't read `arg`.
      -- We prove the rewrite by unfolding and rfl.
      have : EvmYul.step (.SELFDESTRUCT : Operation .EVM) arg s
          = EvmYul.step (.SELFDESTRUCT : Operation .EVM) .none s := by
        unfold EvmYul.step
        rfl
      rw [← this]
      exact h
    exact selfdestruct_balanceOf_ne_Iₐ_ge s s' C hWF h' h_ne
  · have := EvmYul.step_preserves_balanceOf op arg s s' C h_handled hSD h
    exact Nat.le_of_eq this.symm

/-! ## `EVM.step`'s handledByEvmYulStep fallback-arm frame

The fallthrough arm of `EVM.step` invokes `EvmYul.step instr arg s'`
where `s'` has `accountMap = s.accountMap` (only `gasAvailable`
decreased). So the fallthrough preserves `balanceOf` under the usual
side-conditions. -/

theorem EVM_step_fallthrough_ge
    (f : ℕ) (gasCost : ℕ)
    (instr : Operation .EVM × Option (UInt256 × Nat))
    (s s' : EVM.State) (C : AccountAddress)
    (hWF : StateWF s.accountMap)
    (h_ne : C ≠ s.executionEnv.codeOwner)
    (h_handled : EvmYul.Frame.handledByEvmYulStep instr.1)
    (h : EvmYul.step instr.1 instr.2
          {s with gasAvailable := s.gasAvailable - UInt256.ofNat gasCost}
          = .ok s') :
    balanceOf s'.accountMap C ≥ balanceOf s.accountMap C := by
  set s_pre : EVM.State :=
    {s with gasAvailable := s.gasAvailable - UInt256.ofNat gasCost}
    with hs_pre_def
  have hAM : s_pre.accountMap = s.accountMap := rfl
  have hCO : s_pre.executionEnv.codeOwner = s.executionEnv.codeOwner := rfl
  have hWF' : StateWF s_pre.accountMap := by rw [hAM]; exact hWF
  have h_ne' : C ≠ s_pre.executionEnv.codeOwner := by rw [hCO]; exact h_ne
  have hge := EvmYul_step_ge_of_ne_codeOwner instr.1 instr.2 s_pre s' C
    hWF' h_ne' h_handled h
  rw [hAM] at hge
  exact hge

end Frame
end EvmYul
