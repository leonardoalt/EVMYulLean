import EvmYul.Frame.StepShapes

/-!
# Per-PC bytecode-walk helpers

When a contract proof walks its bytecode case-by-case (one PC at a
time), each case opens with the same boilerplate:

  1. Convert a hypothesis `s.pc.toNat = N` (extracted from the trace
     predicate) into `s.pc = UInt256.ofNat N`.
  2. From `fetchInstr s.executionEnv s.pc = .ok (op, arg)` plus the
     known decode at `UInt256.ofNat N`, derive equalities for `op`
     and `arg`, then `subst` them.
  3. Apply the matching `step_OP_shape` lemma with the substituted
     concrete operation.

This file factors steps 1 and 2 into reusable helpers
(`pc_eq_ofNat_of_toNat`, `op_arg_eq_of_fetchInstr_decode`) and step 3
into per-opcode `step_OP_at_pc` wrappers that take the contract
context (`hFetch`, `hCode`, `hpc`, `hDecode`) directly. Each wrapper
delivers the same shape conclusion as its underlying `_shape` lemma.

Wrappers are provided for the commonly walked opcodes Register and
similar contract proofs need:
  - PUSH1, PUSH0, PUSH (generic), JUMPDEST, PC
  - CALLDATALOAD, CALLER, GAS, ADDRESS, ORIGIN, CALLVALUE,
    CALLDATASIZE, CODESIZE, GASPRICE, BASEFEE, RETURNDATASIZE, MSIZE,
    COINBASE, TIMESTAMP, NUMBER, GASLIMIT, CHAINID, SELFBALANCE,
    PREVRANDAO, BLOBBASEFEE
  - POP, ISZERO, NOT, BALANCE, BLOCKHASH, EXTCODESIZE, EXTCODEHASH,
    SLOAD, MLOAD, TLOAD, JUMP, DUP1
  - SSTORE, ADD, SUB, MUL, DIV, MOD, LT, GT, SLT, SGT, EQ, AND, OR,
    XOR, SHL, SHR, SDIV, SMOD, EXP, SIGNEXTEND, BYTE, SAR,
    KECCAK256, MSTORE, MSTORE8, JUMPI, RETURN, REVERT, TSTORE,
    DUP2, SWAP1
  - ADDMOD, MULMOD, CALLDATACOPY, CODECOPY, RETURNDATACOPY, DUP3,
    SWAP2
  - EXTCODECOPY, DUP4, SWAP3
  - CALL
  - STOP

Each `step_OP_at_pc` collapses what was previously ~6 lines of
boilerplate (decode lookup, op/arg extraction, two `subst`s, and the
shape-lemma call) to a single `obtain` invocation.
-/

namespace EvmYul.Frame

open EvmYul EvmYul.EVM

/-! ## Lifted helpers (previously local to per-contract proofs) -/

/-- For a `UInt256` whose `toNat` equals some natural `n < UInt256.size`,
the `UInt256` equals `UInt256.ofNat n`. Used to convert PC hypotheses
of the form `s.pc.toNat = N` (drawn from a trace disjunct) into
`s.pc = UInt256.ofNat N`, which the decode lemmas need. -/
theorem pc_eq_ofNat_of_toNat
    (s : EVM.State) (n : ℕ) (hn : n < UInt256.size)
    (h : s.pc.toNat = n) :
    s.pc = UInt256.ofNat n := by
  rcases hpc : s.pc with ⟨v⟩
  apply congrArg UInt256.mk
  apply Fin.ext
  show v.val = (UInt256.ofNat n).val.val
  have : v.val = n := by rw [hpc] at h; exact h
  rw [this]
  show n = (UInt256.ofNat n).val.val
  unfold UInt256.ofNat Fin.ofNat
  simp only [Id.run]
  rw [Nat.mod_eq_of_lt hn]

/-- Derive `op = op_dec` from a successful `fetchInstr` against a known
`decode` result. -/
theorem op_eq_of_fetchInstr_decode
    {I : ExecutionEnv .EVM} {pc : UInt256}
    {op_dec : Operation .EVM} {arg_dec : Option (UInt256 × Nat)}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hDec : decode I.code pc = some (op_dec, arg_dec))
    (hFetch : fetchInstr I pc = .ok (op, arg)) :
    op = op_dec := by
  unfold fetchInstr at hFetch
  rw [hDec] at hFetch
  injection hFetch with h
  injection h with h _
  exact h.symm

/-- Stronger: derive both `op = op_dec` and `arg = arg_dec`. -/
theorem op_arg_eq_of_fetchInstr_decode
    {I : ExecutionEnv .EVM} {pc : UInt256}
    {op_dec : Operation .EVM} {arg_dec : Option (UInt256 × Nat)}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hDec : decode I.code pc = some (op_dec, arg_dec))
    (hFetch : fetchInstr I pc = .ok (op, arg)) :
    op = op_dec ∧ arg = arg_dec := by
  unfold fetchInstr at hFetch
  rw [hDec] at hFetch
  injection hFetch with h
  injection h with h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-! ## Per-opcode `_at_pc` wrappers

Each wrapper takes the per-PC contract context — `hFetch`, `hCode`,
`hpc` (the PC equality), `hDecode` (the decoded instruction at that
PC) — together with whatever stack inputs the underlying shape lemma
needs, and yields the same shape conclusion. Internally it uses
`op_arg_eq_of_fetchInstr_decode` to align the `op`/`arg` parameters
of `hStep` with the decoded ones, then applies the matching
`step_OP_shape`. -/

section AtPcWrappers

variable {code : ByteArray} {N : ℕ}

/-! ### Push / control-flow / no-stack-input ops -/

/-- `step_PUSH1_shape` lifted to a known PC. -/
theorem step_PUSH1_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (v : UInt256)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N)
                 = some (.Push .PUSH1, some (v, 1)))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 2 ∧
    s'.stack = v :: s.stack ∧
    s'.executionEnv = s.executionEnv := by
  have hDec : decode s.executionEnv.code s.pc
                = some (.Push .PUSH1, some (v, 1)) := by
    rw [hCode, hpc]; exact hDecode
  obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
  subst hOp; subst hArg
  exact step_PUSH1_shape s s' f' cost v hStep

/-- `step_PUSH0_shape` at a known PC. -/
theorem step_PUSH0_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.Push .PUSH0, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = ⟨0⟩ :: s.stack ∧
    s'.executionEnv = s.executionEnv := by
  have hDec : decode s.executionEnv.code s.pc = some (.Push .PUSH0, expArg) := by
    rw [hCode, hpc]; exact hDecode
  obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
  subst hOp; subst hArg
  exact step_PUSH0_shape s s' f' cost arg hStep

/-- `step_PUSH_shape` (PUSHn for `n ≥ 1`) at a known PC. -/
theorem step_PUSH_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (pop : Operation.POp) (hOpNeq : pop ≠ .PUSH0)
    (v : UInt256) (n : Nat)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.Push pop, some (v, n)))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat (n + 1) ∧
    s'.stack = v :: s.stack ∧
    s'.executionEnv = s.executionEnv := by
  have hDec : decode s.executionEnv.code s.pc = some (.Push pop, some (v, n)) := by
    rw [hCode, hpc]; exact hDecode
  obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
  subst hOp; subst hArg
  exact step_PUSH_shape s s' f' cost pop hOpNeq v n hStep

/-! ### A shared schema for all "no-stack-input" ops

`mkNoStackAtPc` would force higher-order tactic plumbing; we just
write each wrapper out explicitly. The pattern is identical: rebuild
`hDec`, derive op/arg, subst, apply the underlying shape lemma. -/

/-- Helper: package the decode rewrite + `op_arg_eq` once. Returns the
op/arg equalities the per-opcode wrappers then `subst`. -/
private theorem aligned_step
    {s : EVM.State}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {op_dec : Operation .EVM} {arg_dec : Option (UInt256 × Nat)}
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (op_dec, arg_dec)) :
    op = op_dec ∧ arg = arg_dec := by
  have hDec : decode s.executionEnv.code s.pc = some (op_dec, arg_dec) := by
    rw [hCode, hpc]; exact hDecode
  exact op_arg_eq_of_fetchInstr_decode hDec hFetch

/-- `step_JUMPDEST_shape` at a known PC. -/
theorem step_JUMPDEST_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.JUMPDEST, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = s.stack ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_JUMPDEST_shape s s' f' cost arg hStep

/-- `step_PC_shape` at a known PC. -/
theorem step_PC_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.PC, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_PC_shape s s' f' cost arg hStep

/-! ### `executionEnvOp`-flavoured pushers (CALLER, GAS, ADDRESS, ...) -/

/-- `step_CALLER_shape` at a known PC. -/
theorem step_CALLER_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.CALLER, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_CALLER_shape s s' f' cost arg hStep

/-- `step_GAS_shape` at a known PC. -/
theorem step_GAS_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.GAS, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_GAS_shape s s' f' cost arg hStep

/-- `step_ADDRESS_shape` at a known PC. -/
theorem step_ADDRESS_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.ADDRESS, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_ADDRESS_shape s s' f' cost arg hStep

/-- `step_ORIGIN_shape` at a known PC. -/
theorem step_ORIGIN_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.ORIGIN, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_ORIGIN_shape s s' f' cost arg hStep

/-- `step_CALLVALUE_shape` at a known PC. -/
theorem step_CALLVALUE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.CALLVALUE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_CALLVALUE_shape s s' f' cost arg hStep

/-- `step_CALLDATASIZE_shape` at a known PC. -/
theorem step_CALLDATASIZE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.CALLDATASIZE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_CALLDATASIZE_shape s s' f' cost arg hStep

/-- `step_CODESIZE_shape` at a known PC. -/
theorem step_CODESIZE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.CODESIZE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_CODESIZE_shape s s' f' cost arg hStep

/-- `step_GASPRICE_shape` at a known PC. -/
theorem step_GASPRICE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.GASPRICE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_GASPRICE_shape s s' f' cost arg hStep

/-- `step_BASEFEE_shape` at a known PC. -/
theorem step_BASEFEE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.BASEFEE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_BASEFEE_shape s s' f' cost arg hStep

/-- `step_RETURNDATASIZE_shape` at a known PC. -/
theorem step_RETURNDATASIZE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.RETURNDATASIZE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_RETURNDATASIZE_shape s s' f' cost arg hStep

/-- `step_MSIZE_shape` at a known PC. -/
theorem step_MSIZE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.MSIZE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_MSIZE_shape s s' f' cost arg hStep

/-- `step_COINBASE_shape` at a known PC. -/
theorem step_COINBASE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.COINBASE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_COINBASE_shape s s' f' cost arg hStep

/-- `step_TIMESTAMP_shape` at a known PC. -/
theorem step_TIMESTAMP_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.TIMESTAMP, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_TIMESTAMP_shape s s' f' cost arg hStep

/-- `step_NUMBER_shape` at a known PC. -/
theorem step_NUMBER_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.NUMBER, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_NUMBER_shape s s' f' cost arg hStep

/-- `step_GASLIMIT_shape` at a known PC. -/
theorem step_GASLIMIT_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.GASLIMIT, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_GASLIMIT_shape s s' f' cost arg hStep

/-- `step_CHAINID_shape` at a known PC. -/
theorem step_CHAINID_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.CHAINID, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_CHAINID_shape s s' f' cost arg hStep

/-- `step_SELFBALANCE_shape` at a known PC. -/
theorem step_SELFBALANCE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.SELFBALANCE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_SELFBALANCE_shape s s' f' cost arg hStep

/-- `step_PREVRANDAO_shape` at a known PC. -/
theorem step_PREVRANDAO_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.PREVRANDAO, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_PREVRANDAO_shape s s' f' cost arg hStep

/-- `step_BLOBBASEFEE_shape` at a known PC. -/
theorem step_BLOBBASEFEE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.BLOBBASEFEE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: s.stack) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_BLOBBASEFEE_shape s s' f' cost arg hStep

/-! ### STOP -/

/-- `step_STOP_shape` at a known PC. -/
theorem step_STOP_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.STOP, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc ∧
    s'.stack = s.stack ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_STOP_shape s s' f' cost arg hStep

/-! ### 1-pop ops -/

/-- `step_CALLDATALOAD_shape` at a known PC. -/
theorem step_CALLDATALOAD_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.CALLDATALOAD, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_CALLDATALOAD_shape s s' f' cost arg hd tl hStk hStep

/-- `step_POP_shape` at a known PC. -/
theorem step_POP_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.POP, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_POP_shape s s' f' cost arg hd tl hStk hStep

/-- `step_ISZERO_shape` at a known PC. -/
theorem step_ISZERO_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.ISZERO, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_ISZERO_shape s s' f' cost arg hd tl hStk hStep

/-- `step_NOT_shape` at a known PC. -/
theorem step_NOT_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.NOT, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_NOT_shape s s' f' cost arg hd tl hStk hStep

/-- `step_BALANCE_shape` at a known PC. -/
theorem step_BALANCE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.BALANCE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_BALANCE_shape s s' f' cost arg hd tl hStk hStep

/-- `step_BLOCKHASH_shape` at a known PC. -/
theorem step_BLOCKHASH_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.BLOCKHASH, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_BLOCKHASH_shape s s' f' cost arg hd tl hStk hStep

/-- `step_EXTCODESIZE_shape` at a known PC. -/
theorem step_EXTCODESIZE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.EXTCODESIZE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_EXTCODESIZE_shape s s' f' cost arg hd tl hStk hStep

/-- `step_EXTCODEHASH_shape` at a known PC. -/
theorem step_EXTCODEHASH_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.EXTCODEHASH, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_EXTCODEHASH_shape s s' f' cost arg hd tl hStk hStep

/-- `step_SLOAD_shape` at a known PC. -/
theorem step_SLOAD_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.SLOAD, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_SLOAD_shape s s' f' cost arg hd tl hStk hStep

/-- `step_MLOAD_shape` at a known PC. -/
theorem step_MLOAD_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.MLOAD, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_MLOAD_shape s s' f' cost arg hd tl hStk hStep

/-- `step_TLOAD_shape` at a known PC. -/
theorem step_TLOAD_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.TLOAD, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_TLOAD_shape s s' f' cost arg hd tl hStk hStep

/-- `step_JUMP_shape` at a known PC. -/
theorem step_JUMP_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.JUMP, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = hd ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_JUMP_shape s s' f' cost arg hd tl hStk hStep

/-- `step_DUP1_shape` at a known PC. -/
theorem step_DUP1_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.DUP1, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd :: s.stack ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_DUP1_shape s s' f' cost arg hd tl hStk hStep

/-! ### 2-pop ops -/

/-- `step_SSTORE_shape` at a known PC. -/
theorem step_SSTORE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.SSTORE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_SSTORE_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_ADD_shape` at a known PC. -/
theorem step_ADD_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.ADD, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_ADD_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_SUB_shape` at a known PC. -/
theorem step_SUB_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.SUB, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_SUB_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_MUL_shape` at a known PC. -/
theorem step_MUL_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.MUL, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_MUL_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_EQ_shape` at a known PC. -/
theorem step_EQ_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.EQ, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_EQ_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_AND_shape` at a known PC. -/
theorem step_AND_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.AND, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_AND_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_OR_shape` at a known PC. -/
theorem step_OR_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.OR, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_OR_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_LT_shape` at a known PC. -/
theorem step_LT_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.LT, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_LT_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_GT_shape` at a known PC. -/
theorem step_GT_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.GT, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_GT_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_DIV_shape` at a known PC. -/
theorem step_DIV_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.DIV, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_DIV_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_MOD_shape` at a known PC. -/
theorem step_MOD_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.MOD, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_MOD_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_KECCAK256_shape` at a known PC. -/
theorem step_KECCAK256_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.KECCAK256, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_KECCAK256_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_MSTORE_shape` at a known PC. -/
theorem step_MSTORE_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.MSTORE, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_MSTORE_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_MSTORE8_shape` at a known PC. -/
theorem step_MSTORE8_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.MSTORE8, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_MSTORE8_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-- `step_JUMPI_shape` at a known PC. -/
theorem step_JUMPI_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.JUMPI, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = (if hd2 != ⟨0⟩ then hd1 else s.pc + ⟨1⟩) ∧
    s'.stack = tl ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_JUMPI_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-! ### CALL (7-pop) -/

/-- `step_CALL_shape` at a known PC. -/
theorem step_CALL_at_pc
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 hd3 hd4 hd5 hd6 hd7 : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: hd7 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.CALL, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    (∃ v, s'.stack = v :: tl) ∧
    s'.executionEnv = s.executionEnv := by
  obtain ⟨hOp, hArg⟩ := aligned_step (code := code) (N := N) hFetch hCode hpc hDecode
  subst hOp; subst hArg
  exact step_CALL_shape s s' f' cost arg hd1 hd2 hd3 hd4 hd5 hd6 hd7 tl hStk hStep

end AtPcWrappers

end EvmYul.Frame
