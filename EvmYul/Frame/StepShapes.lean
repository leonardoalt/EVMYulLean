import EvmYul.Frame.StepFrame
import EvmYul.Frame.MutualFrame

/-!
# Per-opcode step shape lemmas

For each opcode, a single-step lemma describing the post-state shape
in terms of `s.pc`, `s.stack`, and `s.executionEnv`. These are the
building blocks any contract proof uses inside its
`Reachable_step_preserves` walk: each PC case applies the shape
lemma matching the decoded opcode, then reads off the next-PC
disjunct.

All lemmas have signature pattern:
```
theorem step_OP_shape (s s' : EVM.State) (f' cost : ℕ) (...inputs...) :
    s'.pc = s.pc + UInt256.ofNat Δ ∧
    (...stack-shape claim...) ∧
    s'.executionEnv = s.executionEnv
```

Coverage so far (the eight opcodes that appear in Register's bytecode):
PUSH1, CALLDATALOAD, CALLER, SSTORE, GAS, POP, STOP, CALL.

Future work: extend to DUP*, SWAP*, JUMP, JUMPI, JUMPDEST, ADD, SUB,
MUL, DIV, MOD, LT, GT, EQ, ISZERO, AND, OR, XOR, NOT, SHL, SHR,
KECCAK256, MLOAD, MSTORE, MSTORE8, SLOAD, RETURN, REVERT,
RETURNDATACOPY, etc. (cf. `GENERALIZATION_PLAN.md` step 2).
-/

namespace EvmYul.Frame

open EvmYul EvmYul.EVM

/-! ## Push / arithmetic-stack opcodes -/

/-- PUSH1 with arg `(v, 1)`: pushes `v`, advances `pc` by 2. -/
theorem step_PUSH1_shape
    (s s' : EVM.State) (f' cost : ℕ) (v : UInt256)
    (hStep : EVM.step (f' + 1) cost (some (.Push .PUSH1, some (v, 1))) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 2 ∧
    s'.stack = v :: s.stack ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run, Option.some_bind] at hStep
  injection hStep with hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- PUSH0: pushes 0, advances `pc` by 1. -/
theorem step_PUSH0_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.Push .PUSH0, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = ⟨0⟩ :: s.stack ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  injection hStep with hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- Generic PUSH (`PUSHn` for `n ≥ 1`) with arg `(v, n)`: pushes `v`, advances
`pc` by `n + 1`. Covers PUSH2..PUSH32. -/
theorem step_PUSH_shape
    (s s' : EVM.State) (f' cost : ℕ) (op : Operation.POp)
    (hOpNeq : op ≠ .PUSH0)
    (v : UInt256) (n : Nat)
    (hStep : EVM.step (f' + 1) cost (some (.Push op, some (v, n))) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat (n + 1) ∧
    s'.stack = v :: s.stack ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  cases op
  · exact absurd rfl hOpNeq
  all_goals (
    simp only [Id.run, Option.some_bind] at hStep
    injection hStep with hStep
    subst hStep
    refine ⟨rfl, rfl, rfl⟩)

/-- JUMPDEST: pc += 1, stack unchanged. -/
theorem step_JUMPDEST_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.JUMPDEST, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = s.stack ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  injection hStep with hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- PC: pushes the current pc, advances pc by 1. -/
theorem step_PC_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.PC, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  injection hStep with hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-! ## Stack-data opcodes -/

/-- CALLDATALOAD: pops 1, pushes 1, `pc += 1`. The pushed value is
abstracted (`∃ v`) since it depends on `s`'s calldata. -/
theorem step_CALLDATALOAD_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.CALLDATALOAD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnaryStateOp EVM.unaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- CALLER: pushes 1 (the caller address), `pc += 1`. -/
theorem step_CALLER_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.CALLER, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- GAS: pushes 1 (the remaining gas), `pc += 1`. -/
theorem step_GAS_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.GAS, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchMachineStateOp EVM.machineStateOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- ADDRESS: pushes 1 (the contract's address), `pc += 1`. -/
theorem step_ADDRESS_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.ADDRESS, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- ORIGIN: pushes 1 (the tx origin), `pc += 1`. -/
theorem step_ORIGIN_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.ORIGIN, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- CALLVALUE: pushes 1 (the call's wei value), `pc += 1`. -/
theorem step_CALLVALUE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.CALLVALUE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- CALLDATASIZE: pushes 1 (the calldata size), `pc += 1`. -/
theorem step_CALLDATASIZE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.CALLDATASIZE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- CODESIZE: pushes 1 (the code size), `pc += 1`. -/
theorem step_CODESIZE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.CODESIZE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- GASPRICE: pushes 1 (the gas price), `pc += 1`. -/
theorem step_GASPRICE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.GASPRICE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- BASEFEE: pushes 1 (the basefee), `pc += 1`. -/
theorem step_BASEFEE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.BASEFEE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- RETURNDATASIZE: pushes 1, `pc += 1`. -/
theorem step_RETURNDATASIZE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.RETURNDATASIZE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchMachineStateOp EVM.machineStateOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- MSIZE: pushes 1, `pc += 1`. -/
theorem step_MSIZE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.MSIZE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchMachineStateOp EVM.machineStateOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- COINBASE: pushes 1, `pc += 1`. -/
theorem step_COINBASE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.COINBASE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchStateOp EVM.stateOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- TIMESTAMP: pushes 1, `pc += 1`. -/
theorem step_TIMESTAMP_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.TIMESTAMP, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchStateOp EVM.stateOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- NUMBER: pushes 1, `pc += 1`. -/
theorem step_NUMBER_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.NUMBER, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchStateOp EVM.stateOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- GASLIMIT: pushes 1, `pc += 1`. -/
theorem step_GASLIMIT_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.GASLIMIT, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchStateOp EVM.stateOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- CHAINID: pushes 1, `pc += 1`. -/
theorem step_CHAINID_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.CHAINID, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchStateOp EVM.stateOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- SELFBALANCE: pushes 1, `pc += 1`. -/
theorem step_SELFBALANCE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.SELFBALANCE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchStateOp EVM.stateOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- POP: pops 1, no push, `pc += 1`. -/
theorem step_POP_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.POP, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-! ## Unary / binary primops -/

/-- ISZERO: pops 1, pushes 1, `pc += 1`. -/
theorem step_ISZERO_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.ISZERO, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnary EVM.execUnOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- NOT: pops 1, pushes 1, `pc += 1`. -/
theorem step_NOT_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.NOT, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnary EVM.execUnOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- BALANCE: pops 1, pushes 1, `pc += 1`. -/
theorem step_BALANCE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.BALANCE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnaryStateOp EVM.unaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- BLOCKHASH: pops 1, pushes 1, `pc += 1`. -/
theorem step_BLOCKHASH_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.BLOCKHASH, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnaryStateOp EVM.unaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- EXTCODESIZE: pops 1, pushes 1, `pc += 1`. -/
theorem step_EXTCODESIZE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.EXTCODESIZE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnaryStateOp EVM.unaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- EXTCODEHASH: pops 1, pushes 1, `pc += 1`. -/
theorem step_EXTCODEHASH_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.EXTCODEHASH, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnaryStateOp EVM.unaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, ?_⟩
  show (EvmYul.State.extCodeHash s.toState hd).1.executionEnv = s.executionEnv
  rw [extCodeHash_preserves_executionEnv]

/-- SLOAD: pops 1, pushes 1, `pc += 1`. -/
theorem step_SLOAD_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SLOAD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnaryStateOp EVM.unaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- MLOAD: pops 1, pushes 1, `pc += 1`. -/
theorem step_MLOAD_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MLOAD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-! ## Storage / control-flow opcodes -/

/-- SSTORE: pops 2, no push, `pc += 1`. The two popped values are
discarded (storage is updated, but executionEnv is preserved). -/
theorem step_SSTORE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SSTORE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryStateOp EVM.binaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, ?_⟩
  show (EvmYul.State.sstore _ _ _).executionEnv = s.executionEnv
  rw [sstore_preserves_executionEnv]

/-- STOP: pc, stack, and executionEnv all unchanged. -/
theorem step_STOP_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.STOP, arg)) s = .ok s') :
    s'.pc = s.pc ∧
    s'.stack = s.stack ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  exact ⟨rfl, rfl, rfl⟩

/-! ## CALL family -/

/-- `EVM.call` preserves the input's `pc` and `executionEnv` — both gate
branches (gate-pass-with-Θ-success and gate-fail-with-state-passthrough)
return states identical to the input on these projections. Used by
`step_CALL_shape` to derive the post-CALL frame. -/
theorem EVM_call_preserves_pc
    (f' cost : ℕ) (bvh : List ByteArray)
    (g src rcp t v v' io is oo os : UInt256) (perm : Bool)
    (es : EVM.State) (xv : UInt256) (es' : EVM.State)
    (h : EVM.call f' cost bvh g src rcp t v v' io is oo os perm es = .ok (xv, es')) :
    es'.pc = es.pc ∧ es'.executionEnv = es.executionEnv := by
  unfold EVM.call at h
  match f' with
  | 0 => exact absurd h (by simp)
  | n + 1 =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · split at h
      · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, hes⟩ := h
        rw [← hes]
        exact ⟨rfl, rfl⟩
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hes⟩ := h
      rw [← hes]
      exact ⟨rfl, rfl⟩

/-- CALL: pops 7, pushes 1 (the success flag), `pc += 1`. The pushed
value is abstracted (`∃ v`) since it's the dynamic call-success flag.
The pre-call stack must have at least 7 elements. -/
theorem step_CALL_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 hd4 hd5 hd6 hd7 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: hd7 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.CALL, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  simp only [EVM.step, Operation.CALL, bind, Except.bind, pure, Except.pure] at hStep
  rw [hStk] at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · rename_i p hpop7
    obtain ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ := p
    have hStack : stack' = tl := by
      simp only [Stack.pop7] at hpop7
      injection hpop7 with h
      injection h with h
      exact h.symm
    split at hStep
    · exact absurd hStep (by simp)
    · rename_i p_call hCall
      injection hStep with hEq
      have hCallPres := EVM_call_preserves_pc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hCall
      obtain ⟨hPC, hEE⟩ := hCallPres
      rw [← hEq]
      refine ⟨?_, ⟨p_call.1, ?_⟩, ?_⟩
      · show (p_call.2.replaceStackAndIncrPC (stack'.push p_call.1)).pc = s.pc + UInt256.ofNat 1
        show p_call.2.pc + UInt256.ofNat 1 = s.pc + UInt256.ofNat 1
        rw [hPC]
      · show (p_call.2.replaceStackAndIncrPC (stack'.push p_call.1)).stack = p_call.1 :: tl
        show stack'.push p_call.1 = p_call.1 :: tl
        rw [hStack]; rfl
      · show p_call.2.executionEnv = s.executionEnv
        rw [hEE]

end EvmYul.Frame
