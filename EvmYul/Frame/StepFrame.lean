import EvmYul.Frame.Projection
import EvmYul.Semantics
import EvmYul.EVM.PrimOps
import EvmYul.EVM.StateOps

/-!
# `EvmYul.step` frame lemmas (A1)

The key upstream lemma for any balance/code invariant on EVM bytecode:
`EvmYul.step op arg s = .ok s'` with `op ≠ SELFDESTRUCT` preserves
`balanceOf s.accountMap` and `codeOf s.accountMap` at every address.

Organisation:
1. Per-dispatch-helper lemmas: most helpers preserve `accountMap`
   literally; `binaryStateOp`/`unaryStateOp` preserve it projected to
   balance+code.
2. Main theorem by case-split on `op` (EVM case only — Yul out of scope).

SELFDESTRUCT is excluded by hypothesis and handled in A2.
-/

namespace EvmYul
namespace Frame

open Batteries EvmYul.EVM EvmYul.EVM.State

/-! ## Helper frames — `accountMap` literally preserved

Pattern: each dispatch helper is
`match ... with | some ⟨...⟩ => Id.run do .ok <some state construction> | _ => .error _`.
We unfold, split on the pop match, rewrite `Id.run (.ok x) = .ok x`, and
read off `s'` from the resulting `.ok ... = .ok s'`. `accountMap` follows
by `rfl` because `replaceStackAndIncrPC` and `{s with stack := …}` do not
touch the `toState.toSharedState.toState.accountMap` field. -/

@[simp] theorem Id_run_ok {ε α} (x : Except ε α) : Id.run x = x := rfl

/-- `replaceStackAndIncrPC` only touches `pc` and `stack`. -/
@[simp] theorem accountMap_replaceStackAndIncrPC
    (s : EVM.State) (stack : Stack UInt256) (pcΔ : ℕ) :
    (s.replaceStackAndIncrPC stack pcΔ).accountMap = s.accountMap := rfl

/-- `incrPC` only touches `pc`. -/
@[simp] theorem accountMap_incrPC (s : EVM.State) (pcΔ : ℕ) :
    (s.incrPC pcΔ).accountMap = s.accountMap := rfl

theorem execUnOp_preserves_accountMap
    {f : Primop.Unary} {s s' : EVM.State}
    (h : EVM.execUnOp f s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.execUnOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem execBinOp_preserves_accountMap
    {f : Primop.Binary} {s s' : EVM.State}
    (h : EVM.execBinOp f s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.execBinOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem execTriOp_preserves_accountMap
    {f : Primop.Ternary} {s s' : EVM.State}
    (h : EVM.execTriOp f s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.execTriOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem execQuadOp_preserves_accountMap
    {f : Primop.Quaternary} {s s' : EVM.State}
    (h : EVM.execQuadOp f s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.execQuadOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem executionEnvOp_preserves_accountMap
    {op : ExecutionEnv .EVM → UInt256} {s s' : EVM.State}
    (h : EVM.executionEnvOp op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.executionEnvOp at h
  simp only [Id_run_ok, Except.ok.injEq] at h
  subst h; rfl

theorem unaryExecutionEnvOp_preserves_accountMap
    {op : ExecutionEnv .EVM → UInt256 → UInt256} {s s' : EVM.State}
    (h : EVM.unaryExecutionEnvOp op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.unaryExecutionEnvOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem machineStateOp_preserves_accountMap
    {op : MachineState → UInt256} {s s' : EVM.State}
    (h : EVM.machineStateOp op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.machineStateOp at h
  simp only [Id_run_ok, Except.ok.injEq] at h
  subst h; rfl

theorem stateOp_preserves_accountMap
    {op : EvmYul.State .EVM → UInt256} {s s' : EVM.State}
    (h : EVM.stateOp op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.stateOp at h
  simp only [Id_run_ok, Except.ok.injEq] at h
  subst h; rfl

theorem binaryMachineStateOp_preserves_accountMap
    {op : MachineState → UInt256 → UInt256 → MachineState} {s s' : EVM.State}
    (h : EVM.binaryMachineStateOp op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.binaryMachineStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem binaryMachineStateOp'_preserves_accountMap
    {op : MachineState → UInt256 → UInt256 → UInt256 × MachineState}
    {s s' : EVM.State}
    (h : EVM.binaryMachineStateOp' op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.binaryMachineStateOp' at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem ternaryMachineStateOp_preserves_accountMap
    {op : MachineState → UInt256 → UInt256 → UInt256 → MachineState}
    {s s' : EVM.State}
    (h : EVM.ternaryMachineStateOp op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.ternaryMachineStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem dup_preserves_accountMap
    {n : ℕ} {s s' : EVM.State}
    (h : EvmYul.dup n s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EvmYul.dup at h
  simp only [] at h
  by_cases hlen : (s.stack.take n).length = n
  · rw [if_pos hlen] at h
    injection h with h; subst h; rfl
  · rw [if_neg hlen] at h
    exact absurd h (by simp)

theorem swap_preserves_accountMap
    {n : ℕ} {s s' : EVM.State}
    (h : EvmYul.swap n s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EvmYul.swap at h
  simp only [] at h
  by_cases hlen : (s.stack.take (n + 1)).length = n + 1
  · rw [if_pos hlen] at h
    injection h with h; subst h; rfl
  · rw [if_neg hlen] at h
    exact absurd h (by simp)

/-! ## Helper frames — `accountMap` untouched even though a bigger field is rewritten -/

theorem calldatacopy_preserves_accountMap
    {τ} (self : SharedState τ) (mstart datastart size : UInt256) :
    (SharedState.calldatacopy self mstart datastart size).toState.accountMap
      = self.toState.accountMap := rfl

theorem codeCopy_preserves_accountMap
    (self : SharedState .EVM) (mstart cstart size : UInt256) :
    (SharedState.codeCopy self mstart cstart size).toState.accountMap
      = self.toState.accountMap := rfl

theorem extCodeCopy'_preserves_accountMap
    (self : SharedState .EVM) (acc mstart cstart size : UInt256) :
    (SharedState.extCodeCopy' self acc mstart cstart size).toState.accountMap
      = self.toState.accountMap := by
  unfold SharedState.extCodeCopy'
  rfl

theorem ternaryCopyOp_preserves_accountMap
    {op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM}
    {s s' : EVM.State}
    (hOp : ∀ ss a b c, (op ss a b c).toState.accountMap = ss.toState.accountMap)
    (h : EVM.ternaryCopyOp op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.ternaryCopyOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h
    exact hOp _ _ _ _
  · exact absurd h (by simp)

theorem quaternaryCopyOp_preserves_accountMap
    {op : SharedState .EVM → UInt256 → UInt256 → UInt256 → UInt256 → SharedState .EVM}
    {s s' : EVM.State}
    (hOp : ∀ ss a b c d, (op ss a b c d).toState.accountMap = ss.toState.accountMap)
    (h : EVM.quaternaryCopyOp op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.quaternaryCopyOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h
    exact hOp _ _ _ _ _
  · exact absurd h (by simp)

theorem logOp_preserves_accountMap
    {τ} (μ₀ μ₁ : UInt256) (t : Array UInt256) (self : SharedState τ) :
    (SharedState.logOp μ₀ μ₁ t self).toState.accountMap
      = self.toState.accountMap := rfl

theorem evmLogOp_preserves_accountMap
    (s : EVM.State) (μ₀ μ₁ : UInt256) (t : Array UInt256) :
    (EVM.evmLogOp s μ₀ μ₁ t).accountMap = s.accountMap := rfl

theorem log0Op_preserves_accountMap
    {s s' : EVM.State} (h : EVM.log0Op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.log0Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem log1Op_preserves_accountMap
    {s s' : EVM.State} (h : EVM.log1Op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.log1Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem log2Op_preserves_accountMap
    {s s' : EVM.State} (h : EVM.log2Op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.log2Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem log3Op_preserves_accountMap
    {s s' : EVM.State} (h : EVM.log3Op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.log3Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

theorem log4Op_preserves_accountMap
    {s s' : EVM.State} (h : EVM.log4Op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.log4Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp)

/-! ## `State`-touching helpers — `unaryStateOp` / `binaryStateOp`

These take an arbitrary `op : State → ... → State × ...` and apply it to
`evmState.toState`. Whether `accountMap` is preserved depends on the specific
`op`. We factor this by taking a hypothesis that `op` itself preserves
`accountMap`, and then prove individual `op` lemmas below. -/

theorem unaryStateOp_preserves_accountMap
    {op : EvmYul.State .EVM → UInt256 → EvmYul.State .EVM × UInt256}
    {s s' : EVM.State}
    (hOp : ∀ st u, (op st u).1.accountMap = st.accountMap)
    (h : EVM.unaryStateOp op s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.unaryStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h
    show (op s.toState _).1.accountMap = s.accountMap
    exact hOp _ _
  · exact absurd h (by simp)

/-- Weaker form for `binaryStateOp`: the passed `op` may only change fields
other than `accountMap`, but may change accountMap at specific addresses.
Here we take the strong hypothesis that `op` itself preserves balance/code
projections at every address. -/
theorem binaryStateOp_preserves_balanceOf
    {op : EvmYul.State .EVM → UInt256 → UInt256 → EvmYul.State .EVM}
    {s s' : EVM.State} {a : AccountAddress}
    (hOp : ∀ st u v, Frame.balanceOf (op st u v).accountMap a
                      = Frame.balanceOf st.accountMap a)
    (h : EVM.binaryStateOp op s = .ok s') :
    Frame.balanceOf s'.accountMap a = Frame.balanceOf s.accountMap a := by
  unfold EVM.binaryStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h
    show Frame.balanceOf (op s.toState _ _).accountMap a
           = Frame.balanceOf s.accountMap a
    exact hOp _ _ _
  · exact absurd h (by simp)

theorem binaryStateOp_preserves_codeOf
    {op : EvmYul.State .EVM → UInt256 → UInt256 → EvmYul.State .EVM}
    {s s' : EVM.State} {a : AccountAddress}
    (hOp : ∀ st u v, Frame.codeOf (op st u v).accountMap a
                      = Frame.codeOf st.accountMap a)
    (h : EVM.binaryStateOp op s = .ok s') :
    Frame.codeOf s'.accountMap a = Frame.codeOf s.accountMap a := by
  unfold EVM.binaryStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h
    show Frame.codeOf (op s.toState _ _).accountMap a
           = Frame.codeOf s.accountMap a
    exact hOp _ _ _
  · exact absurd h (by simp)

/-! ## Individual `State`-op preservation lemmas -/

theorem addAccessedAccount_preserves_accountMap
    {τ} (self : EvmYul.State τ) (addr : AccountAddress) :
    (self.addAccessedAccount addr).accountMap = self.accountMap := rfl

theorem addAccessedStorageKey_preserves_accountMap
    {τ} (self : EvmYul.State τ) (sk : AccountAddress × UInt256) :
    (self.addAccessedStorageKey sk).accountMap = self.accountMap := rfl

theorem balance_preserves_accountMap
    {τ} (self : EvmYul.State τ) (k : UInt256) :
    (EvmYul.State.balance self k).1.accountMap = self.accountMap := rfl

theorem sload_preserves_accountMap
    {τ} (self : EvmYul.State τ) (spos : UInt256) :
    (EvmYul.State.sload self spos).1.accountMap = self.accountMap := rfl

theorem tload_preserves_accountMap
    {τ} (self : EvmYul.State τ) (spos : UInt256) :
    (EvmYul.State.tload self spos).1.accountMap = self.accountMap := rfl

theorem extCodeSize_preserves_accountMap
    (self : EvmYul.State .EVM) (a : UInt256) :
    (EvmYul.State.extCodeSize self a).1.accountMap = self.accountMap := rfl

theorem extCodeHash_preserves_accountMap
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.extCodeHash self v).1.accountMap = self.accountMap := by
  dsimp only [EvmYul.State.extCodeHash]
  split_ifs <;> rfl

/-! ## SSTORE / TSTORE preserve balance and code at every address

The strategy: the result `accountMap` is either `self.accountMap` (Iₐ
absent) or `self.accountMap.insert Iₐ (acc.updateStorage spos sval)` where
`acc = self.accountMap.find? Iₐ |>.get`. Storage-only updates preserve
balance and code on the account. -/

/-- `Account.updateStorage` doesn't touch balance. -/
theorem Account_updateStorage_balance {τ} (a : Account τ) (k v : UInt256) :
    (a.updateStorage k v).balance = a.balance := by
  unfold Account.updateStorage
  split_ifs <;> rfl

/-- `Account.updateStorage` doesn't touch code. -/
theorem Account_updateStorage_code {τ} (a : Account τ) (k v : UInt256) :
    (a.updateStorage k v).code = a.code := by
  unfold Account.updateStorage
  split_ifs <;> rfl

/-- `Account.updateTransientStorage` doesn't touch balance. -/
theorem Account_updateTransientStorage_balance {τ} (a : Account τ) (k v : UInt256) :
    (a.updateTransientStorage k v).balance = a.balance := by
  unfold Account.updateTransientStorage
  split_ifs <;> rfl

/-- `Account.updateTransientStorage` doesn't touch code. -/
theorem Account_updateTransientStorage_code {τ} (a : Account τ) (k v : UInt256) :
    (a.updateTransientStorage k v).code = a.code := by
  unfold Account.updateTransientStorage
  split_ifs <;> rfl

/-- A generic insert-at-`k`-with-same-balance-and-code lemma. If the new
account matches the old account's balance (or 0 if no old account) at `k`,
then inserting it preserves `balanceOf` at every `a`. -/
theorem balanceOf_insert_preserve_of_eq
    (σ : AccountMap .EVM) (k : AccountAddress) (acc_old acc_new : Account .EVM)
    (hFind : σ.find? k = some acc_old) (hB : acc_new.balance = acc_old.balance)
    (a : AccountAddress) :
    Frame.balanceOf (σ.insert k acc_new) a = Frame.balanceOf σ a := by
  by_cases hne : k = a
  · subst hne
    unfold Frame.balanceOf
    rw [Frame.find?_insert_self, hFind]
    simp [hB]
  · apply Frame.balanceOf_of_find?_eq
    exact Frame.find?_insert_ne σ k a acc_new hne

theorem codeOf_insert_preserve_of_eq
    (σ : AccountMap .EVM) (k : AccountAddress) (acc_old acc_new : Account .EVM)
    (hFind : σ.find? k = some acc_old) (hC : acc_new.code = acc_old.code)
    (a : AccountAddress) :
    Frame.codeOf (σ.insert k acc_new) a = Frame.codeOf σ a := by
  by_cases hne : k = a
  · subst hne
    unfold Frame.codeOf
    rw [Frame.find?_insert_self, hFind]
    simp [hC]
  · apply Frame.codeOf_of_find?_eq
    exact Frame.find?_insert_ne σ k a acc_new hne

open Frame in
theorem sstore_preserves_balanceOf
    (self : EvmYul.State .EVM) (spos sval : UInt256) (a : AccountAddress) :
    balanceOf (EvmYul.State.sstore self spos sval).accountMap a
      = balanceOf self.accountMap a := by
  unfold EvmYul.State.sstore
  simp only [EvmYul.State.lookupAccount]
  match hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => simp [Option.option, hFind]
  | some acc =>
    simp only [Option.option, hFind]
    change balanceOf (self.accountMap.insert self.executionEnv.codeOwner
                       (acc.updateStorage spos sval)) a
         = balanceOf self.accountMap a
    exact balanceOf_insert_preserve_of_eq _ _ _ _ hFind
      (Account_updateStorage_balance _ _ _) _

open Frame in
theorem sstore_preserves_codeOf
    (self : EvmYul.State .EVM) (spos sval : UInt256) (a : AccountAddress) :
    codeOf (EvmYul.State.sstore self spos sval).accountMap a
      = codeOf self.accountMap a := by
  unfold EvmYul.State.sstore
  simp only [EvmYul.State.lookupAccount]
  match hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => simp [Option.option, hFind]
  | some acc =>
    simp only [Option.option, hFind]
    change codeOf (self.accountMap.insert self.executionEnv.codeOwner
                     (acc.updateStorage spos sval)) a
         = codeOf self.accountMap a
    exact codeOf_insert_preserve_of_eq _ _ _ _ hFind
      (Account_updateStorage_code _ _ _) _

open Frame in
theorem tstore_preserves_balanceOf
    (self : EvmYul.State .EVM) (spos sval : UInt256) (a : AccountAddress) :
    balanceOf (EvmYul.State.tstore self spos sval).accountMap a
      = balanceOf self.accountMap a := by
  unfold EvmYul.State.tstore
  simp only [EvmYul.State.lookupAccount]
  match hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => simp [Option.option, hFind]
  | some acc =>
    simp only [Option.option, hFind]
    change balanceOf (self.accountMap.insert self.executionEnv.codeOwner
                       (acc.updateTransientStorage spos sval)) a
         = balanceOf self.accountMap a
    exact balanceOf_insert_preserve_of_eq _ _ _ _ hFind
      (Account_updateTransientStorage_balance _ _ _) _

open Frame in
theorem tstore_preserves_codeOf
    (self : EvmYul.State .EVM) (spos sval : UInt256) (a : AccountAddress) :
    codeOf (EvmYul.State.tstore self spos sval).accountMap a
      = codeOf self.accountMap a := by
  unfold EvmYul.State.tstore
  simp only [EvmYul.State.lookupAccount]
  match hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => simp [Option.option, hFind]
  | some acc =>
    simp only [Option.option, hFind]
    change codeOf (self.accountMap.insert self.executionEnv.codeOwner
                     (acc.updateTransientStorage spos sval)) a
         = codeOf self.accountMap a
    exact codeOf_insert_preserve_of_eq _ _ _ _ hFind
      (Account_updateTransientStorage_code _ _ _) _

/-! ## Main theorem — `EvmYul.step` balance/code frame

`EvmYul.step` for the **EVM** branch is a big opcode match. For a
correct Yellow-Paper dispatch, `EVM.step` pre-intercepts CALL / CREATE
family opcodes and routes them to `call` / `Lambda`; `EvmYul.step` is
never called with those. But `EvmYul.step` *does* have a fall-through
`| .EVM, _ => λ _ ↦ default` that returns a pristine `default` state
whose `accountMap` is empty. So we restrict the frame claim with a
whitelist predicate: every EVM opcode that `EvmYul.step` *actually*
handles (everything except CREATE / CREATE2 / CALL / CALLCODE /
DELEGATECALL / STATICCALL).

SELFDESTRUCT is excluded separately (balance-only exception): that case
is handled in `SelfdestructFrame.lean`.

Code is preserved by every handled opcode (SELFDESTRUCT included — it
only changes balances, not codes). -/

/-- `EvmYul.step` "handles" an EVM opcode iff its arm is not a
fall-through to `default`. Equivalently: `op` is not a message-call or
contract-creation opcode, because those are routed by `EVM.step` before
we ever reach `EvmYul.step`. -/
def handledByEvmYulStep (op : Operation .EVM) : Prop :=
  op ≠ .CREATE ∧ op ≠ .CREATE2 ∧ op ≠ .CALL ∧ op ≠ .CALLCODE
    ∧ op ≠ .DELEGATECALL ∧ op ≠ .STATICCALL

private def opRow (s s' : EVM.State) : Prop :=
  ∀ a, Frame.balanceOf s'.accountMap a = Frame.balanceOf s.accountMap a

private theorem opRow_of_accountMap_eq {s s' : EVM.State}
    (h : s'.accountMap = s.accountMap) : opRow s s' := by
  intro a; unfold Frame.balanceOf; rw [h]

private def codeRow (s s' : EVM.State) : Prop :=
  ∀ a, Frame.codeOf s'.accountMap a = Frame.codeOf s.accountMap a

private theorem codeRow_of_accountMap_eq {s s' : EVM.State}
    (h : s'.accountMap = s.accountMap) : codeRow s s' := by
  intro a; unfold Frame.codeOf; rw [h]

/-! The `dispatchXXX` helpers upstream (in `EvmYul.Semantics`) are now
declared `abbrev`, so they're transparent to the elaborator. Hypotheses
of shape `dispatchXXX .EVM op s = .ok s'` unify with `EVM.* op s = .ok s'`
by reduction. -/

@[simp] theorem dispatchUnary_EVM (f : Primop.Unary) :
    EvmYul.dispatchUnary .EVM f = EVM.execUnOp f := rfl
@[simp] theorem dispatchBinary_EVM (f : Primop.Binary) :
    EvmYul.dispatchBinary .EVM f = EVM.execBinOp f := rfl
@[simp] theorem dispatchTernary_EVM (f : Primop.Ternary) :
    EvmYul.dispatchTernary .EVM f = EVM.execTriOp f := rfl
@[simp] theorem dispatchQuartiary_EVM (f : Primop.Quaternary) :
    EvmYul.dispatchQuartiary .EVM f = EVM.execQuadOp f := rfl
@[simp] theorem dispatchExecutionEnvOp_EVM (op : ExecutionEnv .EVM → UInt256) :
    EvmYul.dispatchExecutionEnvOp .EVM op = EVM.executionEnvOp op := rfl
@[simp] theorem dispatchUnaryExecutionEnvOp_EVM
    (op : ExecutionEnv .EVM → UInt256 → UInt256) :
    EvmYul.dispatchUnaryExecutionEnvOp .EVM op = EVM.unaryExecutionEnvOp op := rfl
@[simp] theorem dispatchMachineStateOp_EVM (op : MachineState → UInt256) :
    EvmYul.dispatchMachineStateOp .EVM op = EVM.machineStateOp op := rfl
@[simp] theorem dispatchUnaryStateOp_EVM
    (op : EvmYul.State .EVM → UInt256 → EvmYul.State .EVM × UInt256) :
    EvmYul.dispatchUnaryStateOp .EVM op = EVM.unaryStateOp op := rfl
@[simp] theorem dispatchTernaryCopyOp_EVM
    (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM) :
    EvmYul.dispatchTernaryCopyOp .EVM op = EVM.ternaryCopyOp op := rfl
@[simp] theorem dispatchQuaternaryCopyOp_EVM
    (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → UInt256 → SharedState .EVM) :
    EvmYul.dispatchQuaternaryCopyOp .EVM op = EVM.quaternaryCopyOp op := rfl
@[simp] theorem dispatchBinaryMachineStateOp_EVM
    (op : MachineState → UInt256 → UInt256 → MachineState) :
    EvmYul.dispatchBinaryMachineStateOp .EVM op = EVM.binaryMachineStateOp op := rfl
@[simp] theorem dispatchBinaryMachineStateOp'_EVM
    (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) :
    EvmYul.dispatchBinaryMachineStateOp' .EVM op = EVM.binaryMachineStateOp' op := rfl
@[simp] theorem dispatchTernaryMachineStateOp_EVM
    (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) :
    EvmYul.dispatchTernaryMachineStateOp .EVM op = EVM.ternaryMachineStateOp op := rfl
@[simp] theorem dispatchBinaryStateOp_EVM
    (op : EvmYul.State .EVM → UInt256 → UInt256 → EvmYul.State .EVM) :
    EvmYul.dispatchBinaryStateOp .EVM op = EVM.binaryStateOp op := rfl
@[simp] theorem dispatchStateOp_EVM (op : EvmYul.State .EVM → UInt256) :
    EvmYul.dispatchStateOp .EVM op = EVM.stateOp op := rfl
@[simp] theorem dispatchLog0_EVM : EvmYul.dispatchLog0 .EVM = EVM.log0Op := rfl
@[simp] theorem dispatchLog1_EVM : EvmYul.dispatchLog1 .EVM = EVM.log1Op := rfl
@[simp] theorem dispatchLog2_EVM : EvmYul.dispatchLog2 .EVM = EVM.log2Op := rfl
@[simp] theorem dispatchLog3_EVM : EvmYul.dispatchLog3 .EVM = EVM.log3Op := rfl
@[simp] theorem dispatchLog4_EVM : EvmYul.dispatchLog4 .EVM = EVM.log4Op := rfl

open Frame in
/-- `opRow` holds for StopArith opcodes. -/
theorem EvmYul.step_opRow_StopArith
    (o : Operation.SAOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.StopArith o : Operation .EVM) arg s = .ok s') :
    opRow s s' := by
  apply opRow_of_accountMap_eq
  cases o
  all_goals (
    unfold EvmYul.step at h
    simp only [Id.run] at h)
  -- STOP, ADD, MUL, SUB, DIV, SDIV, MOD, SMOD, ADDMOD, MULMOD, EXP, SIGNEXTEND
  · injection h with h; subst h; rfl
  all_goals first
    | exact execBinOp_preserves_accountMap h
    | exact execTriOp_preserves_accountMap h

open Frame in
theorem EvmYul.step_opRow_CompBit
    (o : Operation.CBLOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.CompBit o : Operation .EVM) arg s = .ok s') :
    opRow s s' := by
  apply opRow_of_accountMap_eq
  cases o
  all_goals (
    unfold EvmYul.step at h
    simp only [Id.run] at h)
  all_goals first
    | exact execBinOp_preserves_accountMap h
    | exact execUnOp_preserves_accountMap h

open Frame in
theorem EvmYul.step_opRow_Keccak
    (o : Operation.KOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Keccak o : Operation .EVM) arg s = .ok s') :
    opRow s s' := by
  apply opRow_of_accountMap_eq
  cases o
  unfold EvmYul.step at h
  simp only [Id.run] at h
  exact binaryMachineStateOp'_preserves_accountMap h

open Frame in
theorem EvmYul.step_opRow_Env
    (o : Operation.EOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Env o : Operation .EVM) arg s = .ok s') :
    opRow s s' := by
  apply opRow_of_accountMap_eq
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  -- ADDRESS, BALANCE, ORIGIN, CALLER, CALLVALUE, CALLDATALOAD, CALLDATASIZE,
  -- CALLDATACOPY, CODESIZE, CODECOPY, GASPRICE, EXTCODESIZE, EXTCODECOPY,
  -- RETURNDATASIZE, RETURNDATACOPY, EXTCODEHASH
  · exact executionEnvOp_preserves_accountMap h       -- ADDRESS
  · exact unaryStateOp_preserves_accountMap
      (fun st v => balance_preserves_accountMap st v) h                 -- BALANCE
  · exact executionEnvOp_preserves_accountMap h       -- ORIGIN
  · exact executionEnvOp_preserves_accountMap h       -- CALLER
  · exact executionEnvOp_preserves_accountMap h       -- CALLVALUE
  · exact unaryStateOp_preserves_accountMap (fun _ _ => rfl) h  -- CALLDATALOAD
  · exact executionEnvOp_preserves_accountMap h       -- CALLDATASIZE
  · exact ternaryCopyOp_preserves_accountMap
      (fun ss a b c => calldatacopy_preserves_accountMap ss a b c) h    -- CALLDATACOPY
  · exact executionEnvOp_preserves_accountMap h       -- GASPRICE (9th in EOp)
  · exact executionEnvOp_preserves_accountMap h       -- CODESIZE (10th in EOp)
  · exact ternaryCopyOp_preserves_accountMap
      (fun ss a b c => codeCopy_preserves_accountMap ss a b c) h        -- CODECOPY (11th)
  · exact unaryStateOp_preserves_accountMap
      (fun st v => extCodeSize_preserves_accountMap st v) h             -- EXTCODESIZE
  · exact quaternaryCopyOp_preserves_accountMap
      (fun ss a b c d => extCodeCopy'_preserves_accountMap ss a b c d) h -- EXTCODECOPY
  · exact machineStateOp_preserves_accountMap h       -- RETURNDATASIZE
  · -- RETURNDATACOPY — inline
    split at h
    · simp only [Id_run_ok, Except.ok.injEq] at h
      subst h; rfl
    · exact absurd h (by simp)
  · exact unaryStateOp_preserves_accountMap
      (fun st v => extCodeHash_preserves_accountMap st v) h             -- EXTCODEHASH

open Frame in
theorem EvmYul.step_opRow_Block
    (o : Operation.BOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Block o : Operation .EVM) arg s = .ok s') :
    opRow s s' := by
  apply opRow_of_accountMap_eq
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  -- BLOCKHASH, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT, CHAINID,
  -- SELFBALANCE, BASEFEE, BLOBHASH, BLOBBASEFEE
  · exact unaryStateOp_preserves_accountMap (fun _ _ => rfl) h  -- BLOCKHASH
  · exact stateOp_preserves_accountMap h              -- COINBASE
  · exact stateOp_preserves_accountMap h              -- TIMESTAMP
  · exact stateOp_preserves_accountMap h              -- NUMBER
  · exact executionEnvOp_preserves_accountMap h       -- PREVRANDAO
  · exact stateOp_preserves_accountMap h              -- GASLIMIT
  · exact stateOp_preserves_accountMap h              -- CHAINID
  · exact stateOp_preserves_accountMap h              -- SELFBALANCE
  · exact executionEnvOp_preserves_accountMap h       -- BASEFEE
  · exact unaryExecutionEnvOp_preserves_accountMap h  -- BLOBHASH
  · exact executionEnvOp_preserves_accountMap h       -- BLOBBASEFEE

open Frame in
theorem EvmYul.step_opRow_StackMemFlow
    (o : Operation.SMSFOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.StackMemFlow o : Operation .EVM) arg s = .ok s') :
    opRow s s' := by
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  -- POP, MLOAD, MSTORE, SLOAD, SSTORE, MSTORE8, JUMP, JUMPI, PC, MSIZE, GAS,
  -- JUMPDEST, TLOAD, TSTORE, MCOPY
  · -- POP inline
    apply opRow_of_accountMap_eq
    split at h
    · injection h with h; subst h; rfl
    · exact absurd h (by simp)
  · -- MLOAD inline
    apply opRow_of_accountMap_eq
    split at h
    · simp only [Id_run_ok, Except.ok.injEq] at h
      subst h; rfl
    · exact absurd h (by simp)
  · -- MSTORE
    exact opRow_of_accountMap_eq (binaryMachineStateOp_preserves_accountMap h)
  · -- SLOAD
    exact opRow_of_accountMap_eq
      (unaryStateOp_preserves_accountMap
        (fun st v => sload_preserves_accountMap st v) h)
  · -- SSTORE
    intro a'
    exact binaryStateOp_preserves_balanceOf
      (fun st s' s'' => sstore_preserves_balanceOf st s' s'' a') h
  · -- MSTORE8
    exact opRow_of_accountMap_eq (binaryMachineStateOp_preserves_accountMap h)
  · -- JUMP inline
    apply opRow_of_accountMap_eq
    split at h
    · injection h with h; subst h; rfl
    · exact absurd h (by simp)
  · -- JUMPI inline
    apply opRow_of_accountMap_eq
    split at h
    · injection h with h; subst h; rfl
    · exact absurd h (by simp)
  · -- PC inline
    apply opRow_of_accountMap_eq
    injection h with h; subst h; rfl
  · -- MSIZE
    exact opRow_of_accountMap_eq (machineStateOp_preserves_accountMap h)
  · -- GAS
    exact opRow_of_accountMap_eq (machineStateOp_preserves_accountMap h)
  · -- JUMPDEST inline
    apply opRow_of_accountMap_eq
    injection h with h; subst h; rfl
  · -- TLOAD
    exact opRow_of_accountMap_eq
      (unaryStateOp_preserves_accountMap
        (fun st v => tload_preserves_accountMap st v) h)
  · -- TSTORE
    intro a'
    exact binaryStateOp_preserves_balanceOf
      (fun st s' s'' => tstore_preserves_balanceOf st s' s'' a') h
  · -- MCOPY
    exact opRow_of_accountMap_eq (ternaryMachineStateOp_preserves_accountMap h)

open Frame in
theorem EvmYul.step_opRow_Push
    (o : Operation.POp) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Push o : Operation .EVM) arg s = .ok s') :
    opRow s s' := by
  apply opRow_of_accountMap_eq
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  · -- PUSH0: .ok <| s.replaceStackAndIncrPC (s.stack.push ⟨0⟩)
    injection h with h; subst h; rfl
  all_goals (
    -- PUSHn: match arg | none => err | some (a,w) => ok (s.replaceStackAndIncrPC ...)
    cases harg : arg with
    | none => simp [harg] at h
    | some p =>
      obtain ⟨a', w'⟩ := p
      simp [harg] at h
      subst h; rfl)

open Frame in
theorem EvmYul.step_opRow_Dup
    (o : Operation.DOp) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Dup o : Operation .EVM) arg s = .ok s') :
    opRow s s' := by
  apply opRow_of_accountMap_eq
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  all_goals exact dup_preserves_accountMap h

open Frame in
theorem EvmYul.step_opRow_Exchange
    (o : Operation.ExOp) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Exchange o : Operation .EVM) arg s = .ok s') :
    opRow s s' := by
  apply opRow_of_accountMap_eq
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  all_goals exact swap_preserves_accountMap h

open Frame in
theorem EvmYul.step_opRow_Log
    (o : Operation.LOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Log o : Operation .EVM) arg s = .ok s') :
    opRow s s' := by
  apply opRow_of_accountMap_eq
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  · exact log0Op_preserves_accountMap h
  · exact log1Op_preserves_accountMap h
  · exact log2Op_preserves_accountMap h
  · exact log3Op_preserves_accountMap h
  · exact log4Op_preserves_accountMap h

open Frame in
theorem EvmYul.step_opRow_System
    (o : Operation.SOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h_handled : handledByEvmYulStep (.System o : Operation .EVM))
    (h_ne : (.System o : Operation .EVM) ≠ .SELFDESTRUCT)
    (h : EvmYul.step (.System o : Operation .EVM) arg s = .ok s') :
    opRow s s' := by
  obtain ⟨hne1, hne2, hne3, hne4, hne5, hne6⟩ := h_handled
  cases o
  all_goals (try unfold EvmYul.step at h; try simp only [Id.run] at h)
  · exact absurd rfl hne1  -- CREATE
  · exact absurd rfl hne3  -- CALL
  · exact absurd rfl hne4  -- CALLCODE
  · -- RETURN
    apply opRow_of_accountMap_eq
    exact binaryMachineStateOp_preserves_accountMap h
  · exact absurd rfl hne5  -- DELEGATECALL
  · exact absurd rfl hne2  -- CREATE2
  · exact absurd rfl hne6  -- STATICCALL
  · -- REVERT
    apply opRow_of_accountMap_eq
    exact binaryMachineStateOp_preserves_accountMap h
  · -- INVALID → dispatchInvalid → .error
    exact absurd h (by simp [dispatchInvalid])
  · exact absurd rfl h_ne  -- SELFDESTRUCT

open Frame in
/-- Main theorem. -/
theorem EvmYul.step_preserves_balanceOf
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State) (a : AccountAddress)
    (h_handled : handledByEvmYulStep op)
    (h_ne : op ≠ .SELFDESTRUCT)
    (h : EvmYul.step op arg s = .ok s') :
    balanceOf s'.accountMap a = balanceOf s.accountMap a := by
  have h' : opRow s s' := by
    cases op with
    | StopArith o    => exact EvmYul.step_opRow_StopArith o arg s s' h
    | CompBit o      => exact EvmYul.step_opRow_CompBit o arg s s' h
    | Keccak o       => exact EvmYul.step_opRow_Keccak o arg s s' h
    | Env o          => exact EvmYul.step_opRow_Env o arg s s' h
    | Block o        => exact EvmYul.step_opRow_Block o arg s s' h
    | StackMemFlow o => exact EvmYul.step_opRow_StackMemFlow o arg s s' h
    | Push o         => exact EvmYul.step_opRow_Push o arg s s' h
    | Dup o          => exact EvmYul.step_opRow_Dup o arg s s' h
    | Exchange o     => exact EvmYul.step_opRow_Exchange o arg s s' h
    | Log o          => exact EvmYul.step_opRow_Log o arg s s' h
    | System o       => exact EvmYul.step_opRow_System o arg s s' h_handled h_ne h
  exact h' a

end Frame
end EvmYul
