import EvmYul.Frame.Projection
import EvmYul.Frame.MutualFrame
import EvmYul.EVM.Semantics

/-!
# A6 — Υ's transaction-level balance frame

Statements use the real-world assumption set (T1/T2/T4/T5). The
`ΞPreservesAtC C` witness is defined in `MutualFrame.lean` and threaded
through to `Θ_balanceOf_ge` / `Λ_balanceOf_ge` / `Ξ_balanceOf_ge` via
their own hypotheses.
-/

namespace EvmYul
namespace Frame

open Batteries EvmYul.EVM

/-- Υ's balance frame. -/
theorem Υ_balanceOf_ge
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) (b₀ : ℕ)
    (hWF : StateWF σ)
    (hBal : b₀ ≤ balanceOf σ C)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (hWitness : ΞPreservesAtC C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => b₀ ≤ balanceOf σ' C
    | .error _ => True := by
  sorry

end Frame
end EvmYul
