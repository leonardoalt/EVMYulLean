import EvmYul.Frame.Projection
import EvmYul.Frame.StorageSum
import EvmYul.Frame.StepFrame
import EvmYul.Frame.SelfdestructFrame
import EvmYul.Frame.MutualFrame
import EvmYul.Frame.StepSystemFrame
import EvmYul.Frame.UpsilonFrame
import EvmYul.Frame.XFrame
import EvmYul.Frame.StepShapes
import EvmYul.Frame.PcWalk

/-!
# Frame library (upstream A1–A6)

Re-exports the reusable frame lemmas for `EvmYul.step`, SELFDESTRUCT,
Θ, Λ, Ξ, and Υ. Any downstream proof about an EVM invariant under
reentrancy starts here.

Status (2026-04-22):

* `Projection`          — projection operators `balanceOf`, `codeOf` and
                          basic `find?_insert_ne` lemma. **Closed.**
* `StepFrame` (A1)      — `EvmYul.step_preserves_balanceOf` for every
                          handled EVM opcode except SELFDESTRUCT.
                          **Closed.**
* `SelfdestructFrame` (A2) — SELFDESTRUCT balance monotonicity at
                          addresses other than the executing code-owner.
                          **Open** (one `sorry`).
* `MutualFrame` (A3+A4+A5) — `Θ`, `Λ`, `Ξ` balance frames, joint fuel
                          induction through the `mutual` block.
                          Ξ's sorry is now narrowed to just the
                          X-success branch (the `.error`/`.revert`
                          branches are discharged). **Open** (one
                          `sorry`, narrowed).
* `UpsilonFrame` (A6)   — `Υ` transaction-level balance frame with
                          parameterised code-preservation witness.
                          **Open** (one `sorry`).
* `XFrame`              — infrastructure for the outer `X` fuel
                          induction used by `Ξ_balanceOf_ge`'s +1
                          case: `Ξ_freshEvmState` definition and
                          rfl-equalities, `Ξ_succ_eq_X` reduction,
                          `X_balance_ge_prop` proposition statement,
                          `X_balance_ge_prop_zero` fuel-0 closure.
                          **No new sorrys or axioms.**
-/
