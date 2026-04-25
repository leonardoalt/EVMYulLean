# Frame Library: Balance-Frame Reasoning for EVMYulLean

This document describes the additions on the `evm-smith-frame-library` branch.
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
