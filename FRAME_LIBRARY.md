# Frame Library: Balance-Frame Reasoning for EVMYulLean

This document describes the Frame library additions carried by
[`leonardoalt/EVMYulLean@main`](https://github.com/leonardoalt/EVMYulLean) on
top of the `NethermindEth/EVMYulLean` upstream.
It is intended for downstream provers who want to reason about per-account
invariants — most importantly **balance monotonicity at a fixed address `C`** —
across an entire Ethereum transaction (`Υ`), in the presence of arbitrary
reentrancy, nested CREATEs, and self-destructs.

The branch adds **~8,700 lines** of new proof infrastructure in
`EvmYul/Frame/`, with no new sorries and only three real-world
axioms (T2 precompile purity, T5 Keccak collision, and a strengthened
totalETH-bound that lives inside `StateWF`).

## Why these changes

EVMYulLean ships an executable formal model of the EVM but no facilities
for proving invariants of a *contract* across the whole call graph
spawned by a transaction. To prove "Register's balance never decreases
during a Υ run", a downstream caller needs frame-style preservation
results at every layer of the spec:

```
Υ
└── (sender debit, optional CREATE) → Λ / Θ-dispatch
    └── Ξ (interpreter)
        └── X (instruction loop)
            └── step (single opcode dispatch)
                ├── EvmYul.step (non-CREATE/CALL ops)
                ├── EVM.call    (CALL family)
                ├── EVM.Lambda  (CREATE family)
                └── selfdestruct
```

Before this branch, only the operational semantics existed. The frame
library closes balance-monotonicity at every layer and exposes it as a
small set of theorems with crisp preconditions.

## What was added

### `EvmYul/Frame.lean`
Top-level umbrella that re-exports the framework so a downstream
`import EvmYul.Frame` makes everything visible.

### `EvmYul/Frame/Projection.lean` (251 LoC)
Foundational lemmas about `balanceOf`, `totalETH`, account-map find/insert
behaviour, and the **`StateWF`** predicate.

* `StateWF σ` is `totalETH σ < UInt256.size / 2` — half-bound on the total
  ETH supply. This is strictly stronger than "no UInt256 wraparound on
  any single balance" but it's exactly the strength needed to prove
  no-wrap on a self-call: `acc.balance + value ≤ totalETH ≤ totalETH +
  totalETH = 2·totalETH < UInt256.size`.
* `boundedTotalDouble` — `2 · totalETH σ < UInt256.size`, the form used
  inside CALL/CALLCODE.
* `balanceOf_of_find?_eq`, `find?_insert_self`, `find?_insert_ne`,
  `find?_erase_rbset_foldl_ne`, etc. — the workhorses for reasoning
  about account-map updates pointwise.

### `EvmYul/Frame/StepFrame.lean` (1,690 LoC)
Per-opcode step preservation lemmas for `EvmYul.step`. The big results:

* `EvmYul.step_preserves_balanceOf` — for any non-CREATE/CALL,
  non-SELFDESTRUCT op, `balanceOf σ' a = balanceOf σ a` for *every* address `a`.
  Proved via an `opRow` row-vector argument enumerating all dispatch shapes.
* `EvmYul.step_preserves_eEnv_cA` — executionEnv and createdAccounts
  unchanged for non-CALL/CREATE ops.
* `EvmYul_step_preserves_StateWF` (in `MutualFrame.lean`, but relies
  on StepFrame helpers) — `StateWF` is preserved across any `EvmYul.step`.

### `EvmYul/Frame/SelfdestructFrame.lean` (292 LoC)
SELFDESTRUCT-specific frame:

* `selfdestruct_balanceOf_ne_Iₐ_ge` — at any address `≠ Iₐ` (the
  self-destructing account), balance is preserved. (Funds flow to a
  beneficiary, decreasing balance only at `Iₐ`.)
* `selfdestruct_preserves_executionEnv`, `selfdestruct_preserves_createdAccounts`,
  `selfdestruct_preserves_StateWF`.

### `EvmYul/Frame/XFrame.lean` (198 LoC)
The X-instruction-loop frame:

* `Ξ_freshEvmState` — exposes the initial `EVM.State` that `Ξ` builds
  before invoking `X`.
* `Ξ_succ_eq_X` — reduces `EVM.Ξ (n+1) cA gbh blocks σ σ₀ g A I` to
  `X n validJumps freshState`. This is the lift from the interpreter
  layer to the X-loop layer.
* `X_balance_ge_zero` — trivial 0-fuel base case.

### `EvmYul/Frame/StepSystemFrame.lean` (116 LoC)
Aggregator for the system-arm dispatchers (CREATE/CREATE2/CALL/CALLCODE/
DELEGATECALL/STATICCALL).

### `EvmYul/Frame/UpsilonFrame.lean` (918 LoC)
The transaction-level frame `Υ`:

* `Υ_balanceOf_ge` — *the consumer-facing entry point*. Given:
  - `StateWF σ`,
  - `b₀ ≤ balanceOf σ C`,
  - `C ≠ S_T` (Register isn't the tx sender),
  - `C ≠ H.beneficiary` (Register isn't the miner),
  - `ΞPreservesAtC C` (the bytecode witness),
  - `ΥTailInvariant σ … C` (post-dispatch SD-set / dead-filter excludes C),
  - `ΥBodyFactors σ … C` (Υ's body factors as Θ/Λ-dispatch composed with the tail),

  concludes `b₀ ≤ balanceOf σ' C` for the post-Υ state.
* `Υ_output_balance_ge` — uncluttered version returning `≥ balanceOf σ C`.
* `Υ_tail_balanceOf_ge` — pure post-dispatch tail (gas refund + SD sweep
  + dead-account sweep + tstorage wipe) preserves balance at C.
* The `TxValid` predicate (a strengthened upfront-cost validity claim
  with three structural consequences pre-packaged: no underflow on
  `S_T`, value-fundability, recipient no-wrap). **No longer a global
  axiom** — consumers thread it as a hypothesis.

### `EvmYul/Frame/MutualFrame.lean` (5,117 LoC, the bulk of the work)

This is the joint mutual-recursion closure of `Θ`, `Λ`, and `Ξ`. The EVM
spec is mutually recursive (Θ calls Ξ, Ξ contains CALL which calls Θ
again, Λ contains an inner Ξ run for the constructor body). To prove
balance preservation at one of these layers, you need the result at
*all* of them simultaneously, with a unified fuel-induction.

Highlights:

* **`ΞPreservesAtC C`** — universal-fuel witness that Ξ at codeOwner = C
  preserves balance at C. This is what a smart-contract author proves
  for their bytecode.
* **`ΞFrameAtC C maxFuel`** — fuel-bounded variant of *the C ≠ codeOwner
  case*. This is the IH form that the strong-fuel induction produces.
* **`ΞAtCFrame C maxFuel`** — fuel-bounded variant of `ΞPreservesAtC C`,
  for the at-C case. This is the genuinely new contribution that
  separates "the unbounded result we want to prove" from "the bounded
  IH we have access to inside the strong induction".
* **`Θ_balanceOf_ge` / `Θ_balanceOf_ge_bdd`** — Θ's balance frame. The
  bdd-suffix variants take fuel-bounded witnesses; the public versions
  take the unbounded form (and are derivable from `_bdd` + an
  unwrapping step).
* **`Λ_balanceOf_ge` / `Λ_balanceOf_ge_bdd`** — Λ's balance frame.
* **`Ξ_balanceOf_ge_bundled` / `Ξ_balanceOf_ge_bundled_bdd`** — the joint
  closure: Ξ preserves balance at C, plus `StateWF`, plus `cA-exclusion`.
  Closed via strong induction on fuel (`Nat.strong_induction_on`) feeding
  bounded witnesses for both arms (at-C and ≠-C) of the mutual recursion.
* **The "at_C / v=0" chain**: `step_CALL_arm_at_C_v0`,
  `step_bundled_invariant_at_C_v0`, `X_inv_at_C_v0`, `X_inv_at_C_v0_holds` —
  step-bundle and X-loop invariants for the case `codeOwner = C` and
  the running CALL has `value = 0` at stack position 2. This is the
  shape needed for any contract whose own bytecode emits only zero-value
  CALLs out (Register, simple read-only routers, etc.).
* **`ΞPreservesAtC_of_Reachable`** — the parameterised entry point
  smart-contract authors use. Given a `Reachable : EVM.State → Prop`
  predicate that captures the contract's bytecode trace + a stack-shape
  invariant, plus six closure lemmas (`Z`-stability, step-stability,
  `decodeSome`, `op-in-allowed-set`, `v0-at-CALL`, initial-state),
  this theorem produces `ΞPreservesAtC C` directly.

## Other touches in the EVM model

### `EvmYul/EVM/Semantics.lean` (52 LoC delta)
* CREATE/CREATE2 failure semantics fix: when an inner Λ fails, the
  parent's `accountMap` was being wiped to `∅`. Fixed to preserve the
  pre-CREATE state. (Yellow Paper conformance.)
* Per-precompile dispatch in `Θ` was refactored from a single 10-way
  match into a linear if-cascade (`applyPrecompile`) to bypass a
  Lean-kernel deep-recursion limit.

### `EvmYul/Semantics.lean` (42 LoC delta)
* `EvmYul.step` dispatch helpers (`dispatchUnary`, `dispatchBinary`,
  `dispatchTernary`, `dispatchQuartiary`, `dispatchExecutionEnvOp`,
  `dispatchUnaryStateOp`, `dispatchTernaryCopyOp`, etc.) un-privated
  and changed from `def` to `abbrev`, so frame lemmas can `unfold`
  them at proof-time.

## How this enables `evm-smith` proofs

The Register balance-monotonicity proof in
`evm-smith/EvmSmith/Demos/Register/` consumes the framework via:

1. **`Υ_balanceOf_ge`** — the top-level `register_balance_mono`
   theorem invokes this with five preconditions (`StateWF`, `b₀ ≤ …`,
   `C ≠ S_T`, `C ≠ H.beneficiary`) plus three witnesses
   (`ΞPreservesAtC C`, `ΥTailInvariant`, `ΥBodyFactors`).
2. **`ΞPreservesAtC_of_Reachable`** — discharges the `ΞPreservesAtC C`
   witness from a contract-specific `RegisterTrace` predicate plus six
   bytecode-walk closure lemmas.
3. **`Θ_balanceOf_ge` / `Λ_balanceOf_ge`** — used inside the body
   factorisation helpers to bound `balanceOf σ_P C` at the post-debit
   state σ₀.
4. **`StateWF`** + **`tx_validity` (now a hypothesis, not an axiom)** —
   discharge the no-wrap and funds-strict preconditions of Θ/Λ at σ₀.

Because every layer is parameterised by `(C : AccountAddress)` and a
uniform `ΞPreservesAtC` witness, the same framework supports any
single-contract balance invariant a downstream prover wants to state.

## Axiom audit

After this branch, EVMYulLean contains exactly **two** axioms:

* `precompile_preserves_accountMap` — T2: precompiles do not modify the
  account map (purity of cryptographic primitives at the contract-state
  level).
* `lambda_derived_address_ne_C` — T5: under Keccak collision-resistance
  for fixed `C`, no CREATE/CREATE2-derived address equals `C`.

Both are well-understood real-world ground assumptions; both are
declared at the top of `MutualFrame.lean` with full motivation.

The previously-extant `tx_validity` global axiom was **removed**;
it is now an explicit hypothesis on consumer theorems.

## Partial Phase A: substate / SD-set tracking (paused)

A follow-up effort to derive the consumer-side `*SDExclusion` and
`*DeadAtσP` boundary hypotheses inside Lean (eliminating them from
the API surface of consumer theorems like `register_balance_mono`)
landed leaf infrastructure but **paused** before the full closure
rewrite. What's available today:

* `SubstateSDExclude A C : Prop` — substate-level SD-set exclusion.
* `ΞPreservesAtCStrong C` — 4-conjunct sibling of `ΞPreservesAtC`
  including SD-exclusion in the post-condition.
* `ΞFrameAtCStrong C maxFuel` and `ΞAtCFrameStrong C maxFuel` —
  fuel-bounded variants of the strong predicates (parallels of
  `ΞFrameAtC` / `ΞAtCFrame`).
* `ΞAtCFrameStrong_of_witness`, `ΞFrameAtC_of_Strong`,
  monotonicity lemmas — projections / fuel-bound monotonicity.
* `selfdestruct_preserves_SD_exclude_C` (in `SelfdestructFrame.lean`)
  — leaf step lemma: SELFDESTRUCT at `Iₐ ≠ C` preserves SD-exclusion
  at C.
* Nine per-precompile substate-purity lemmas + bundled
  `applyPrecompile_substate_eq_when_in_range` — for the precompile
  branch of Θ.

What's open: the parallel rewrite of `Θ_body_*`, `Θ_balanceOf_ge_bdd`,
`Λ_balanceOf_ge_bdd`, the six `step_*_arm` helpers,
`step_bundled_invariant_at_C`, `X_inv_succ_content` / `X_inv_holds`,
`X_inv_at_C_v0_holds`, and the closing
`Ξ_balanceOf_ge_bundled_strong` + `ΞPreservesAtC_of_Reachable_strong`
— roughly 1500 LoC of cross-referencing tactic proof that needs to
land in lockstep. See evm-smith's `GENERALIZATION_PLAN.md` Step 5
for the full plan.

Until that lands, downstream consumers (e.g. `register_balance_mono`)
still take `*SDExclusion` and `*DeadAtσP` as caller-supplied
hypotheses (not axioms).

---

## Phase B: Account-Presence Preservation and Universal Ξ

A second wave of framework additions, motivated by the WETH solvency
proof, lifts the framework from "balance frame" to a more general
"per-account state-shape frame". The headline result is a **fully
universal Ξ-preservation theorem** (`Ξ_preserves_account_at_a_universal :
∀ a, ΞPreservesAccountAt a`), discharged via mutual fuel induction
over Ξ ↔ Θ ↔ Λ ↔ X ↔ EVM.step.

This unblocks any contract proof that needs to reason about cross-call
σ-account presence (whether the contract's own account survives across
nested CALL / CREATE recursion). It also closes a substantial chunk of
the structural-fact assumptions previously exposed at the consumer
level.

Total added: **~5,000 LoC** of new framework infrastructure across
`MutualFrame.lean`, `StepShapes.lean`, `PcWalk.lean`, `StorageSum.lean`,
and `UpsilonFrame.lean`.

### §I — Θ-side preservation

Layer 1: leaf lemmas about account-presence under specific σ
manipulations.

| Theorem | What it says |
|---|---|
| `accountPresentAt σ a` | `∃ acc, σ.find? a = some acc` — the predicate. |
| `accountPresentAt_insert` | `insert k v` preserves presence at any address. |
| `theta_σ'₁_preserves_present` | Θ's value-credit prefix preserves presence. |
| `theta_σ₁_preserves_present` | Θ's value-debit prefix preserves presence. |
| `theta_σ'_clamp_preserves_present` | Θ's σ'-clamp preserves presence. |
| `Θ_preserves_account_at_a` | **Full Θ** preserves presence (witness-driven). |
| `EVM_call_preserves_account_at_a` | `EVM.call` wrapper of Θ preservation. |

### §J — Universal mutual-induction discharge

#### §J.1–J.4: per-step preservation

| Theorem | What it says |
|---|---|
| `evmYul_step_SSTORE_preserves_present` | SSTORE step preserves presence. |
| `evmYul_step_TSTORE_preserves_present` | Same for TSTORE. |
| `selfDestruct_preserves_present` | SELFDESTRUCT step (within Θ frame). |
| `binaryStateOp_preserves_present` | Generic binary state-op preservation. |
| `evmYul_step_preserves_present` | **Master** per-op lemma for `EvmYul.step`. |
| `EVM_step_handled_preserves_present` | `EVM.step` for "handled" (non-CALL) ops. |
| `EVM_step_CALL_preserves_present` | CALL family (CALL / CALLCODE / DELEGATECALL / STATICCALL). |
| `EVM_step_preserves_present_no_create` | Universal `EVM.step` dispatcher (CREATE excluded). |

#### §J.5: bounded variants for fuel induction

The mutual induction needs fuel-parameterized predicates:

| Predicate | What it says |
|---|---|
| `ΞPreservesAccountAtBdd a f` | Ξ preserves presence at `a` for fuels `≤ f`. |

Plus matching bounded variants of all the per-step / Θ / X / EVM.call
preservation theorems (`Θ_preserves_account_at_a_bdd`,
`EVM_call_preserves_account_at_a_bdd`, `X_preserves_account_at_a_bdd`,
etc.).

#### §J.5b: CREATE/CREATE2 preservation (Λ-side)

The hardest single piece. Requires unfolding `EVM.Lambda`'s nested
do-block (which has `MonadLift Option (Except _)` complications and a
`Id.run` for the F-condition).

| Theorem | What it says |
|---|---|
| `Λ_preserves_account_at_a` | Λ preserves presence (witness-driven). |
| `EVM_step_CREATE_preserves_present` | Λ-using EVM.step CREATE arm. |
| `EVM_step_CREATE2_preserves_present` | Same for CREATE2. |
| `EVM_step_preserves_present` | Universal EVM.step (no no-create constraint). |

#### §J.5c–J.6: universal closures

| Theorem | What it says |
|---|---|
| `X_preserves_account_at_a_bdd_universal` | X-loop preservation handling `decode = none` via STOP arm. |
| **`Ξ_preserves_account_at_a_universal`** | **The fully universal Ξ preservation. The headline result.** |

#### §J.7: Reachable-closure wrappers

Convenience entries for consumers using a `Reachable` predicate:

| Theorem | What it says |
|---|---|
| `Θ_preserves_account_at_a_of_Reachable` | Θ preservation with Reachable closure. |
| `EVM_call_preserves_account_at_a_of_Reachable` | Same for EVM.call. |
| `Ξ_preserves_account_at_a_of_Reachable_for_C` | Restricted to `I.codeOwner = C` (for contract-specific Reachable predicates). |

#### §J.6.6/.6.7 — `_inv_aware` variants

The framework's `hReach_step` callback didn't expose `WethInvFr s'.accountMap C`
to consumers, even though the X-loop's induction has it locally. This
caused a chicken-and-egg circularity for any contract whose Reachable
predicate depends on the invariant.

The `_inv_aware` variants thread the post-step invariant through:

| Theorem | What it says |
|---|---|
| `X_preserves_account_at_a_bdd_op_conditional_with_pres_step` | X-loop variant with σ-presence in step closure. |
| `Ξ_preserves_account_at_a_of_Reachable_for_C_with_pres_step` | Same at Ξ-level. |
| `ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch_inv_aware` | Slack-dispatch variant exposing `WethInvFr s'.accountMap C` to `hReach_step`. |

This is the canonical pattern for any contract proof whose Reachable
predicate carries an X-loop invariant.

### Strong shape lemmas

Per-opcode shape lemmas in `StepShapes.lean` (and `_at_pc` wrappers in
`PcWalk.lean`) that additionally expose `s'.accountMap = s.accountMap`.
Used by per-PC cascade-threading work to propagate storage-equality
facts through non-storage ops.

| Opcode | Strong shape lemma |
|---|---|
| `SLOAD` | `step_SLOAD_shape_strong` (with codeOwner-storage lookup) |
| `LT` | `step_LT_shape_strong` |
| `SUB` | `step_SUB_shape_strong` |
| `DUP1` / `DUP2` / `DUP3` / `DUP5` | `step_DUP{1,2,3,5}_shape_strong` |
| `SWAP1` | `step_SWAP1_shape_strong` |
| `PUSH` (generic n≥1) | `step_PUSH_shape_strong` |
| `PUSH1` | `step_PUSH1_shape_strong` |
| `JUMPI` | `step_JUMPI_shape_strong` |
| `JUMPDEST` | `step_JUMPDEST_shape_strong` |
| `POP` | `step_POP_shape_strong` |
| `CALLER` | `step_CALLER_shape_strong` |
| `CALLVALUE` | `step_CALLVALUE_shape_strong` |
| `ADD` | `step_ADD_shape_strong` |
| `GAS` | `step_GAS_shape_strong` |

Each ships with a `_at_pc_strong` wrapper combining the strong shape
with PC equality.

### StorageSum helpers

In `StorageSum.lean`:

| Theorem | What it says |
|---|---|
| `storageSum_sstore_replace_eq_findD` | findD-flavored `≤`-bridge: SSTORE-replace inequality on storageSum. |
| `storageSum_storage_insert_absent_eq` | Inserting into an absent slot. |
| `storageSum_storage_erase_eq_of_find?_none` (exposed) | Public visibility of erase-of-absent. |

### UpsilonFrame simplification

`Υ_invariant_preserved` previously took a `ΞPreservesInvariantAtC C`
parameter that was structurally unused (passed through to
`Υ_output_invariant_preserves` as `_hWitness`, never consumed). Drop
the parameter to simplify the consumer interface.

### Θ-pre-credit framework lemma

| Theorem | What it says |
|---|---|
| `theta_σ'₁_pre_credit_slack_at_C` | Given `WethInvFr σ C` and balance no-wrap, post-credit state σ'₁ satisfies `v + storageSum σ'₁ C ≤ balanceOf σ'₁ C`. |

Composes the existing `theta_σ'₁_storageSum_eq` (storage unchanged at
C through credit) with balance-delta arithmetic
(`balanceOf σ'₁ C = balanceOf σ C + v` at recipient = C). Backs the
Θ-pre-credit fact for any consumer that needs it (e.g. WETH's
`deposit` slack).

### How Phase B enables WETH's solvency proof

The WETH solvency proof in `evm-smith/EvmSmith/Demos/Weth/` discharges
*every bytecode-derivable assumption* using Phase B:

* `weth_account_at_C : WethAccountAtC C` — projected from the new
  `accountPresentAt s.accountMap C` conjunct in `WethReachable`,
  preserved across all 61 per-PC walks via `EVM_step_preserves_present_no_create`.
* `weth_xi_preserves_C_other` — universal Ξ-preservation via
  `Ξ_preserves_account_at_a_universal`.
* `weth_call_inv_step_pres` — CALL-step `WethInvFr` preservation via
  the `_inv_aware` slack-dispatch variant.

The remaining `WethAssumptions` fields are 4 Register-shape boundary
facts plus 1 chain-state bound (`call_no_wrap`) — none about WETH's
bytecode behavior.

### Axioms unchanged

Phase B introduces zero new axioms. The framework still has exactly
the two axioms documented in the audit above (`precompile_preserves_accountMap`,
`lambda_derived_address_ne_C`).
