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
  simp only [Id.run] at hStep
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
    simp only [Id.run] at hStep
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

/-! ## Binary primops (ADD, SUB, MUL, ...) -/

/-- ADD: pops 2, pushes 1, `pc += 1`. -/
theorem step_ADD_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.ADD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- SUB: pops 2, pushes 1, `pc += 1`. -/
theorem step_SUB_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SUB, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- MUL: pops 2, pushes 1, `pc += 1`. -/
theorem step_MUL_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MUL, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- DIV: pops 2, pushes 1, `pc += 1`. -/
theorem step_DIV_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DIV, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- MOD: pops 2, pushes 1, `pc += 1`. -/
theorem step_MOD_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MOD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- LT: pops 2, pushes 1, `pc += 1`. -/
theorem step_LT_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.LT, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- GT: pops 2, pushes 1, `pc += 1`. -/
theorem step_GT_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.GT, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- SLT: pops 2, pushes 1, `pc += 1`. -/
theorem step_SLT_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SLT, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- SGT: pops 2, pushes 1, `pc += 1`. -/
theorem step_SGT_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SGT, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- EQ: pops 2, pushes 1, `pc += 1`. -/
theorem step_EQ_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.EQ, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- AND: pops 2, pushes 1, `pc += 1`. -/
theorem step_AND_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.AND, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- OR: pops 2, pushes 1, `pc += 1`. -/
theorem step_OR_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.OR, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- XOR: pops 2, pushes 1, `pc += 1`. -/
theorem step_XOR_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.XOR, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- SHL: pops 2, pushes 1, `pc += 1`. -/
theorem step_SHL_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SHL, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- SHR: pops 2, pushes 1, `pc += 1`. -/
theorem step_SHR_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SHR, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- SDIV: pops 2, pushes 1, `pc += 1`. -/
theorem step_SDIV_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SDIV, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- SMOD: pops 2, pushes 1, `pc += 1`. -/
theorem step_SMOD_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SMOD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- EXP: pops 2, pushes 1, `pc += 1`. -/
theorem step_EXP_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.EXP, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- SIGNEXTEND: pops 2, pushes 1, `pc += 1`. -/
theorem step_SIGNEXTEND_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SIGNEXTEND, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- BYTE: pops 2, pushes 1, `pc += 1`. -/
theorem step_BYTE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.BYTE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- SAR: pops 2, pushes 1, `pc += 1`. -/
theorem step_SAR_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SAR, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-! ## Ternary primops -/

/-- ADDMOD: pops 3, pushes 1, `pc += 1`. -/
theorem step_ADDMOD_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.ADDMOD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchTernary EVM.execTriOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop3, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- MULMOD: pops 3, pushes 1, `pc += 1`. -/
theorem step_MULMOD_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MULMOD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchTernary EVM.execTriOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop3, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-! ## Transient storage / extra env opcodes -/

/-- TLOAD: pops 1, pushes 1, `pc += 1`. -/
theorem step_TLOAD_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.TLOAD, arg)) s = .ok s') :
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

/-- TSTORE: pops 2, no push, `pc += 1`. -/
theorem step_TSTORE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.TSTORE, arg)) s = .ok s') :
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
  show (EvmYul.State.tstore s.toState hd1 hd2).executionEnv = s.executionEnv
  rw [tstore_preserves_executionEnv]

/-- PREVRANDAO: pushes 1, `pc += 1`. -/
theorem step_PREVRANDAO_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.PREVRANDAO, arg)) s = .ok s') :
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

/-- BLOBBASEFEE: pushes 1, `pc += 1`. -/
theorem step_BLOBBASEFEE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.BLOBBASEFEE, arg)) s = .ok s') :
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

/-! ## Memory / hashing two-pop opcodes -/

/-- KECCAK256: pops 2, pushes 1 (the hash), `pc += 1`. -/
theorem step_KECCAK256_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.KECCAK256, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryMachineStateOp' EVM.binaryMachineStateOp' at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- MSTORE: pops 2, no push, `pc += 1`. -/
theorem step_MSTORE_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MSTORE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryMachineStateOp EVM.binaryMachineStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- MSTORE8: pops 2, no push, `pc += 1`. -/
theorem step_MSTORE8_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.MSTORE8, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryMachineStateOp EVM.binaryMachineStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-! ## JUMP family -/

/-- JUMP: pops 1, pc replaced by popped value. -/
theorem step_JUMP_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.JUMP, arg)) s = .ok s') :
    s'.pc = hd ∧
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

/-- JUMPI: pops 2, pc set to first popped value if second is non-zero, else pc+1. -/
theorem step_JUMPI_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.JUMPI, arg)) s = .ok s') :
    s'.pc = (if hd2 != ⟨0⟩ then hd1 else s.pc + ⟨1⟩) ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-! ## RETURN / REVERT -/

/-- RETURN: pops 2 (the return-data offset and length); the result has stack
without those two elements, `pc += 1` and `executionEnv` preserved. -/
theorem step_RETURN_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.RETURN, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryMachineStateOp EVM.binaryMachineStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- REVERT: same shape as RETURN at the EVM-step level (the X loop catches
the actual halt by inspecting the operation kind). -/
theorem step_REVERT_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.REVERT, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryMachineStateOp EVM.binaryMachineStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-! ## Copy ops (CALLDATACOPY, CODECOPY, RETURNDATACOPY, EXTCODECOPY) -/

/-- CALLDATACOPY: pops 3, no push, `pc += 1`. -/
theorem step_CALLDATACOPY_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.CALLDATACOPY, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchTernaryCopyOp EVM.ternaryCopyOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop3, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- CODECOPY: pops 3, no push, `pc += 1`. -/
theorem step_CODECOPY_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.CODECOPY, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchTernaryCopyOp EVM.ternaryCopyOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop3, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- RETURNDATACOPY: pops 3, no push, `pc += 1`. Implemented inline in
`EvmYul.step` (does not go through a generic dispatcher). -/
theorem step_RETURNDATACOPY_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.RETURNDATACOPY, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  rw [hStk] at hStep
  simp only [Stack.pop3, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- EXTCODECOPY: pops 4, no push, `pc += 1`. -/
theorem step_EXTCODECOPY_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 hd4 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: hd4 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.EXTCODECOPY, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchQuaternaryCopyOp EVM.quaternaryCopyOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop4, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-! ## DUP1 / SWAP1 -/

/-- DUP1: pops 0, pushes a copy of the top, `pc += 1`. -/
theorem step_DUP1_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DUP1, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd :: s.stack ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 1 (hd :: tl) = [hd] from rfl,
             List.length_singleton, ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ?_, rfl⟩
  show [hd].getLast! :: (hd :: tl) = hd :: s.stack
  rw [hStk]; rfl

/-- DUP2: duplicates the second-from-top, `pc += 1`. -/
theorem step_DUP2_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DUP2, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd2 :: s.stack ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 2 (hd1 :: hd2 :: tl) = [hd1, hd2] from rfl,
             show ([hd1, hd2] : List UInt256).length = 2 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ?_, rfl⟩
  show [hd1, hd2].getLast! :: (hd1 :: hd2 :: tl) = hd2 :: s.stack
  rw [hStk]; rfl

/-- DUP3: duplicates the third-from-top, `pc += 1`. -/
theorem step_DUP3_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DUP3, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd3 :: s.stack ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 3 (hd1 :: hd2 :: hd3 :: tl) = [hd1, hd2, hd3] from rfl,
             show ([hd1, hd2, hd3] : List UInt256).length = 3 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ?_, rfl⟩
  show [hd1, hd2, hd3].getLast! :: (hd1 :: hd2 :: hd3 :: tl) = hd3 :: s.stack
  rw [hStk]; rfl

/-- DUP4: duplicates the fourth-from-top, `pc += 1`. -/
theorem step_DUP4_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 hd4 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: hd4 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.DUP4, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd4 :: s.stack ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dup at hStep
  rw [hStk] at hStep
  simp only [show List.take 4 (hd1 :: hd2 :: hd3 :: hd4 :: tl) = [hd1, hd2, hd3, hd4] from rfl,
             show ([hd1, hd2, hd3, hd4] : List UInt256).length = 4 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, ?_, rfl⟩
  show [hd1, hd2, hd3, hd4].getLast! :: (hd1 :: hd2 :: hd3 :: hd4 :: tl) = hd4 :: s.stack
  rw [hStk]; rfl

/-- SWAP1: swaps the top two stack elements, `pc += 1`. -/
theorem step_SWAP1_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SWAP1, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd2 :: hd1 :: tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold swap at hStep
  rw [hStk] at hStep
  simp only [show List.take (1 + 1) (hd1 :: hd2 :: tl) = [hd1, hd2] from rfl,
             show List.drop (1 + 1) (hd1 :: hd2 :: tl) = tl from rfl,
             show ([hd1, hd2] : List UInt256).length = 1 + 1 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- SWAP2: swaps element 1 (top) with element 3 (count from 1), `pc += 1`. -/
theorem step_SWAP2_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SWAP2, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd3 :: hd2 :: hd1 :: tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold swap at hStep
  rw [hStk] at hStep
  simp only [show List.take (2 + 1) (hd1 :: hd2 :: hd3 :: tl) = [hd1, hd2, hd3] from rfl,
             show List.drop (2 + 1) (hd1 :: hd2 :: hd3 :: tl) = tl from rfl,
             show ([hd1, hd2, hd3] : List UInt256).length = 2 + 1 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- SWAP3: swaps top with the 4th element, `pc += 1`. -/
theorem step_SWAP3_shape
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 hd4 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: hd4 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SWAP3, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd4 :: hd2 :: hd3 :: hd1 :: tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold swap at hStep
  rw [hStk] at hStep
  simp only [show List.take (3 + 1) (hd1 :: hd2 :: hd3 :: hd4 :: tl) = [hd1, hd2, hd3, hd4] from rfl,
             show List.drop (3 + 1) (hd1 :: hd2 :: hd3 :: hd4 :: tl) = tl from rfl,
             show ([hd1, hd2, hd3, hd4] : List UInt256).length = 3 + 1 from rfl,
             ↓reduceIte, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

end EvmYul.Frame
