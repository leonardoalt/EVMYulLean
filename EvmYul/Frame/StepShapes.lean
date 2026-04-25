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
