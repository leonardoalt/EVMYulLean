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

/-- `replaceStackAndIncrPC` only touches `pc` and `stack`. -/
@[simp] theorem executionEnv_replaceStackAndIncrPC
    (s : EVM.State) (stack : Stack UInt256) (pcΔ : ℕ) :
    (s.replaceStackAndIncrPC stack pcΔ).executionEnv = s.executionEnv := rfl

/-- `replaceStackAndIncrPC` only touches `pc` and `stack`. -/
@[simp] theorem createdAccounts_replaceStackAndIncrPC
    (s : EVM.State) (stack : Stack UInt256) (pcΔ : ℕ) :
    (s.replaceStackAndIncrPC stack pcΔ).createdAccounts = s.createdAccounts := rfl

/-- `incrPC` only touches `pc`. -/
@[simp] theorem accountMap_incrPC (s : EVM.State) (pcΔ : ℕ) :
    (s.incrPC pcΔ).accountMap = s.accountMap := rfl

@[simp] theorem executionEnv_incrPC (s : EVM.State) (pcΔ : ℕ) :
    (s.incrPC pcΔ).executionEnv = s.executionEnv := rfl

@[simp] theorem createdAccounts_incrPC (s : EVM.State) (pcΔ : ℕ) :
    (s.incrPC pcΔ).createdAccounts = s.createdAccounts := rfl


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
  | none => simp [Option.option]
  | some acc =>
    simp only [Option.option]
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
  | none => simp [Option.option]
  | some acc =>
    simp only [Option.option]
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
  | none => simp [Option.option]
  | some acc =>
    simp only [Option.option]
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
  | none => simp [Option.option]
  | some acc =>
    simp only [Option.option]
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
    · simp only [Except.ok.injEq] at h
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
    · simp only [Except.ok.injEq] at h
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

/-! ## executionEnv / createdAccounts preservation

Every handled EVM op leaves these two fields untouched. We prove this in
one pair of uniform theorems. The key observation: for each helper `H`
in PrimOps.lean (and each inline `.ok` in Semantics.lean), the result
state is of the form `evmState'.replaceStackAndIncrPC stk` where
`evmState'` is obtained from `evmState` by a record update that touches
neither `executionEnv` nor `createdAccounts` (only `toMachineState`,
`accountMap`, `substate`, or `toState` are modified — and `toState`
itself, when modified via `sstore`/`tstore`/`balance`/`sload`/`tload`,
leaves `executionEnv` and `createdAccounts` alone). -/

-- ExecutionEnv preservation helpers (each mirrors a `_preserves_accountMap` helper).

theorem execUnOp_preserves_eEnv_cA
    {f : Primop.Unary} {s s' : EVM.State}
    (h : EVM.execUnOp f s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.execUnOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

theorem execBinOp_preserves_eEnv_cA
    {f : Primop.Binary} {s s' : EVM.State}
    (h : EVM.execBinOp f s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.execBinOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

theorem execTriOp_preserves_eEnv_cA
    {f : Primop.Ternary} {s s' : EVM.State}
    (h : EVM.execTriOp f s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.execTriOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

theorem execQuadOp_preserves_eEnv_cA
    {f : Primop.Quaternary} {s s' : EVM.State}
    (h : EVM.execQuadOp f s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.execQuadOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

theorem executionEnvOp_preserves_eEnv_cA
    {op : ExecutionEnv .EVM → UInt256} {s s' : EVM.State}
    (h : EVM.executionEnvOp op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.executionEnvOp at h
  simp only [Id_run_ok, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem unaryExecutionEnvOp_preserves_eEnv_cA
    {op : ExecutionEnv .EVM → UInt256 → UInt256} {s s' : EVM.State}
    (h : EVM.unaryExecutionEnvOp op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.unaryExecutionEnvOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

theorem machineStateOp_preserves_eEnv_cA
    {op : MachineState → UInt256} {s s' : EVM.State}
    (h : EVM.machineStateOp op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.machineStateOp at h
  simp only [Id_run_ok, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem stateOp_preserves_eEnv_cA
    {op : EvmYul.State .EVM → UInt256} {s s' : EVM.State}
    (h : EVM.stateOp op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.stateOp at h
  simp only [Id_run_ok, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem binaryMachineStateOp_preserves_eEnv_cA
    {op : MachineState → UInt256 → UInt256 → MachineState} {s s' : EVM.State}
    (h : EVM.binaryMachineStateOp op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.binaryMachineStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

theorem binaryMachineStateOp'_preserves_eEnv_cA
    {op : MachineState → UInt256 → UInt256 → UInt256 × MachineState}
    {s s' : EVM.State}
    (h : EVM.binaryMachineStateOp' op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.binaryMachineStateOp' at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

theorem ternaryMachineStateOp_preserves_eEnv_cA
    {op : MachineState → UInt256 → UInt256 → UInt256 → MachineState}
    {s s' : EVM.State}
    (h : EVM.ternaryMachineStateOp op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.ternaryMachineStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

theorem dup_preserves_eEnv_cA
    {n : ℕ} {s s' : EVM.State}
    (h : EvmYul.dup n s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EvmYul.dup at h
  simp only [] at h
  by_cases hlen : (s.stack.take n).length = n
  · rw [if_pos hlen] at h
    injection h with h; subst h; exact ⟨rfl, rfl⟩
  · rw [if_neg hlen] at h
    exact absurd h (by simp)

theorem swap_preserves_eEnv_cA
    {n : ℕ} {s s' : EVM.State}
    (h : EvmYul.swap n s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EvmYul.swap at h
  simp only [] at h
  by_cases hlen : (s.stack.take (n + 1)).length = n + 1
  · rw [if_pos hlen] at h
    injection h with h; subst h; exact ⟨rfl, rfl⟩
  · rw [if_neg hlen] at h
    exact absurd h (by simp)

theorem ternaryCopyOp_preserves_eEnv_cA
    {op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM}
    {s s' : EVM.State}
    (hOpEnv : ∀ ss a b c,
      (op ss a b c).toState.executionEnv = ss.toState.executionEnv)
    (hOpCA : ∀ ss a b c,
      (op ss a b c).toState.createdAccounts = ss.toState.createdAccounts)
    (h : EVM.ternaryCopyOp op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.ternaryCopyOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h
    refine ⟨?_, ?_⟩
    · show (op s.toSharedState _ _ _).toState.executionEnv = s.executionEnv
      exact hOpEnv _ _ _ _
    · show (op s.toSharedState _ _ _).toState.createdAccounts = s.createdAccounts
      exact hOpCA _ _ _ _
  · exact absurd h (by simp)

theorem quaternaryCopyOp_preserves_eEnv_cA
    {op : SharedState .EVM → UInt256 → UInt256 → UInt256 → UInt256 → SharedState .EVM}
    {s s' : EVM.State}
    (hOpEnv : ∀ ss a b c d,
      (op ss a b c d).toState.executionEnv = ss.toState.executionEnv)
    (hOpCA : ∀ ss a b c d,
      (op ss a b c d).toState.createdAccounts = ss.toState.createdAccounts)
    (h : EVM.quaternaryCopyOp op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.quaternaryCopyOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h
    refine ⟨?_, ?_⟩
    · show (op s.toSharedState _ _ _ _).toState.executionEnv = s.executionEnv
      exact hOpEnv _ _ _ _ _
    · show (op s.toSharedState _ _ _ _).toState.createdAccounts = s.createdAccounts
      exact hOpCA _ _ _ _ _
  · exact absurd h (by simp)

-- Per-op eEnv/cA preservation for shared-state helpers:

theorem calldatacopy_preserves_eEnv
    {τ} (self : SharedState τ) (a b c : UInt256) :
    (SharedState.calldatacopy self a b c).toState.executionEnv
      = self.toState.executionEnv := rfl

theorem calldatacopy_preserves_cA
    {τ} (self : SharedState τ) (a b c : UInt256) :
    (SharedState.calldatacopy self a b c).toState.createdAccounts
      = self.toState.createdAccounts := rfl

theorem codeCopy_preserves_eEnv
    (self : SharedState .EVM) (a b c : UInt256) :
    (SharedState.codeCopy self a b c).toState.executionEnv
      = self.toState.executionEnv := rfl

theorem codeCopy_preserves_cA
    (self : SharedState .EVM) (a b c : UInt256) :
    (SharedState.codeCopy self a b c).toState.createdAccounts
      = self.toState.createdAccounts := rfl

theorem extCodeCopy'_preserves_eEnv
    (self : SharedState .EVM) (acc a b c : UInt256) :
    (SharedState.extCodeCopy' self acc a b c).toState.executionEnv
      = self.toState.executionEnv := by
  unfold SharedState.extCodeCopy'; rfl

theorem extCodeCopy'_preserves_cA
    (self : SharedState .EVM) (acc a b c : UInt256) :
    (SharedState.extCodeCopy' self acc a b c).toState.createdAccounts
      = self.toState.createdAccounts := by
  unfold SharedState.extCodeCopy'; rfl

theorem evmLogOp_preserves_eEnv
    (s : EVM.State) (μ₀ μ₁ : UInt256) (t : Array UInt256) :
    (EVM.evmLogOp s μ₀ μ₁ t).executionEnv = s.executionEnv := rfl

theorem evmLogOp_preserves_cA
    (s : EVM.State) (μ₀ μ₁ : UInt256) (t : Array UInt256) :
    (EVM.evmLogOp s μ₀ μ₁ t).createdAccounts = s.createdAccounts := rfl

theorem log0Op_preserves_eEnv_cA
    {s s' : EVM.State} (h : EVM.log0Op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.log0Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h
    refine ⟨?_, ?_⟩ <;> rfl
  · exact absurd h (by simp)

theorem log1Op_preserves_eEnv_cA
    {s s' : EVM.State} (h : EVM.log1Op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.log1Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h
    refine ⟨?_, ?_⟩ <;> rfl
  · exact absurd h (by simp)

theorem log2Op_preserves_eEnv_cA
    {s s' : EVM.State} (h : EVM.log2Op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.log2Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h
    refine ⟨?_, ?_⟩ <;> rfl
  · exact absurd h (by simp)

theorem log3Op_preserves_eEnv_cA
    {s s' : EVM.State} (h : EVM.log3Op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.log3Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h
    refine ⟨?_, ?_⟩ <;> rfl
  · exact absurd h (by simp)

theorem log4Op_preserves_eEnv_cA
    {s s' : EVM.State} (h : EVM.log4Op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.log4Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h
    refine ⟨?_, ?_⟩ <;> rfl
  · exact absurd h (by simp)

theorem unaryStateOp_preserves_eEnv_cA
    {op : EvmYul.State .EVM → UInt256 → EvmYul.State .EVM × UInt256}
    {s s' : EVM.State}
    (hOp : ∀ st u, (op st u).1.executionEnv = st.executionEnv)
    (hOpCA : ∀ st u, (op st u).1.createdAccounts = st.createdAccounts)
    (h : EVM.unaryStateOp op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.unaryStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h
    refine ⟨?_, ?_⟩
    · show (op s.toState _).1.executionEnv = s.executionEnv
      exact hOp _ _
    · show (op s.toState _).1.createdAccounts = s.createdAccounts
      exact hOpCA _ _
  · exact absurd h (by simp)

theorem binaryStateOp_preserves_eEnv_cA
    {op : EvmYul.State .EVM → UInt256 → UInt256 → EvmYul.State .EVM}
    {s s' : EVM.State}
    (hOpEnv : ∀ st u v, (op st u v).executionEnv = st.executionEnv)
    (hOpCA : ∀ st u v, (op st u v).createdAccounts = st.createdAccounts)
    (h : EVM.binaryStateOp op s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  unfold EVM.binaryStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h
    refine ⟨?_, ?_⟩
    · show (op s.toState _ _).executionEnv = s.executionEnv
      exact hOpEnv _ _ _
    · show (op s.toState _ _).createdAccounts = s.createdAccounts
      exact hOpCA _ _ _
  · exact absurd h (by simp)

-- Individual state-op executionEnv-preservations.

theorem balance_preserves_executionEnv
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.balance self v).1.executionEnv = self.executionEnv := by
  unfold EvmYul.State.balance EvmYul.State.addAccessedAccount
  rfl

theorem sload_preserves_executionEnv
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.sload self v).1.executionEnv = self.executionEnv := by
  unfold EvmYul.State.sload EvmYul.State.addAccessedStorageKey
  rfl

theorem tload_preserves_executionEnv
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.tload self v).1.executionEnv = self.executionEnv := by
  unfold EvmYul.State.tload; rfl

theorem extCodeSize_preserves_executionEnv
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.extCodeSize self v).1.executionEnv = self.executionEnv := by
  unfold EvmYul.State.extCodeSize EvmYul.State.addAccessedAccount; rfl

theorem extCodeHash_preserves_executionEnv
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.extCodeHash self v).1.executionEnv = self.executionEnv := by
  unfold EvmYul.State.extCodeHash
  by_cases hDead :
      EvmYul.State.dead self.accountMap (AccountAddress.ofUInt256 v) = true
  · rw [if_pos hDead]; rfl
  · rw [if_neg hDead]; rfl

theorem extCodeHash_preserves_createdAccounts
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.extCodeHash self v).1.createdAccounts = self.createdAccounts := by
  unfold EvmYul.State.extCodeHash
  by_cases hDead :
      EvmYul.State.dead self.accountMap (AccountAddress.ofUInt256 v) = true
  · rw [if_pos hDead]; rfl
  · rw [if_neg hDead]; rfl

theorem balance_preserves_createdAccounts
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.balance self v).1.createdAccounts = self.createdAccounts := by
  unfold EvmYul.State.balance EvmYul.State.addAccessedAccount; rfl

theorem sload_preserves_createdAccounts
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.sload self v).1.createdAccounts = self.createdAccounts := by
  unfold EvmYul.State.sload EvmYul.State.addAccessedStorageKey; rfl

theorem tload_preserves_createdAccounts
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.tload self v).1.createdAccounts = self.createdAccounts := by
  unfold EvmYul.State.tload; rfl

theorem extCodeSize_preserves_createdAccounts
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.extCodeSize self v).1.createdAccounts = self.createdAccounts := by
  unfold EvmYul.State.extCodeSize EvmYul.State.addAccessedAccount; rfl

theorem sstore_preserves_createdAccounts
    (self : EvmYul.State .EVM) (u v : UInt256) :
    (EvmYul.State.sstore self u v).createdAccounts = self.createdAccounts := by
  unfold EvmYul.State.sstore
  simp only [EvmYul.State.lookupAccount]
  match hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => simp [Option.option]
  | some acc =>
    simp only [Option.option]
    show (_ : EvmYul.State .EVM).createdAccounts = self.createdAccounts
    rfl

theorem tstore_preserves_createdAccounts
    (self : EvmYul.State .EVM) (u v : UInt256) :
    (EvmYul.State.tstore self u v).createdAccounts = self.createdAccounts := by
  unfold EvmYul.State.tstore
  simp only [EvmYul.State.lookupAccount]
  match hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => simp [Option.option]
  | some acc =>
    simp only [Option.option]
    unfold EvmYul.State.updateAccount; rfl

theorem sstore_preserves_executionEnv
    (self : EvmYul.State .EVM) (u v : UInt256) :
    (EvmYul.State.sstore self u v).executionEnv = self.executionEnv := by
  unfold EvmYul.State.sstore
  simp only [EvmYul.State.lookupAccount]
  match hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => simp [Option.option]
  | some acc =>
    simp only [Option.option]
    show (_ : EvmYul.State .EVM).executionEnv = self.executionEnv
    rfl

theorem tstore_preserves_executionEnv
    (self : EvmYul.State .EVM) (u v : UInt256) :
    (EvmYul.State.tstore self u v).executionEnv = self.executionEnv := by
  unfold EvmYul.State.tstore
  simp only [EvmYul.State.lookupAccount]
  match hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => simp [Option.option]
  | some acc =>
    simp only [Option.option]
    unfold EvmYul.State.updateAccount; rfl

/-! ## opRow-analog for executionEnv/createdAccounts preservation -/

/-- Row predicate for executionEnv/createdAccounts preservation. -/
def eECARow (s s' : EVM.State) : Prop :=
  s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts

private theorem eECARow_of_pair {s s' : EVM.State}
    (h : s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts) :
    eECARow s s' := h

/-- `eECARow` holds for StopArith opcodes. -/
theorem EvmYul.step_eECARow_StopArith
    (o : Operation.SAOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.StopArith o : Operation .EVM) arg s = .ok s') :
    eECARow s s' := by
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  · injection h with h; subst h; exact ⟨rfl, rfl⟩
  all_goals first
    | exact execBinOp_preserves_eEnv_cA h
    | exact execTriOp_preserves_eEnv_cA h

theorem EvmYul.step_eECARow_CompBit
    (o : Operation.CBLOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.CompBit o : Operation .EVM) arg s = .ok s') :
    eECARow s s' := by
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  all_goals first
    | exact execBinOp_preserves_eEnv_cA h
    | exact execUnOp_preserves_eEnv_cA h

theorem EvmYul.step_eECARow_Keccak
    (o : Operation.KOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Keccak o : Operation .EVM) arg s = .ok s') :
    eECARow s s' := by
  cases o
  unfold EvmYul.step at h
  simp only [Id.run] at h
  exact binaryMachineStateOp'_preserves_eEnv_cA h

theorem EvmYul.step_eECARow_Env
    (o : Operation.EOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Env o : Operation .EVM) arg s = .ok s') :
    eECARow s s' := by
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  · exact executionEnvOp_preserves_eEnv_cA h       -- ADDRESS
  · exact unaryStateOp_preserves_eEnv_cA
      (fun st v => balance_preserves_executionEnv st v)
      (fun st v => balance_preserves_createdAccounts st v) h
  · exact executionEnvOp_preserves_eEnv_cA h       -- ORIGIN
  · exact executionEnvOp_preserves_eEnv_cA h       -- CALLER
  · exact executionEnvOp_preserves_eEnv_cA h       -- CALLVALUE
  · exact unaryStateOp_preserves_eEnv_cA (fun _ _ => rfl) (fun _ _ => rfl) h  -- CALLDATALOAD
  · exact executionEnvOp_preserves_eEnv_cA h       -- CALLDATASIZE
  · exact ternaryCopyOp_preserves_eEnv_cA
      (fun ss a b c => calldatacopy_preserves_eEnv ss a b c)
      (fun ss a b c => calldatacopy_preserves_cA ss a b c) h -- CALLDATACOPY
  · exact executionEnvOp_preserves_eEnv_cA h       -- GASPRICE
  · exact executionEnvOp_preserves_eEnv_cA h       -- CODESIZE
  · exact ternaryCopyOp_preserves_eEnv_cA
      (fun ss a b c => codeCopy_preserves_eEnv ss a b c)
      (fun ss a b c => codeCopy_preserves_cA ss a b c) h -- CODECOPY
  · exact unaryStateOp_preserves_eEnv_cA
      (fun st v => extCodeSize_preserves_executionEnv st v)
      (fun st v => extCodeSize_preserves_createdAccounts st v) h
  · exact quaternaryCopyOp_preserves_eEnv_cA
      (fun ss a b c d => extCodeCopy'_preserves_eEnv ss a b c d)
      (fun ss a b c d => extCodeCopy'_preserves_cA ss a b c d) h -- EXTCODECOPY
  · exact machineStateOp_preserves_eEnv_cA h       -- RETURNDATASIZE
  · -- RETURNDATACOPY
    split at h
    · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · exact unaryStateOp_preserves_eEnv_cA
      (fun st v => extCodeHash_preserves_executionEnv st v)
      (fun st v => extCodeHash_preserves_createdAccounts st v) h

theorem EvmYul.step_eECARow_Block
    (o : Operation.BOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Block o : Operation .EVM) arg s = .ok s') :
    eECARow s s' := by
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  · exact unaryStateOp_preserves_eEnv_cA (fun _ _ => rfl) (fun _ _ => rfl) h  -- BLOCKHASH
  · exact stateOp_preserves_eEnv_cA h               -- COINBASE
  · exact stateOp_preserves_eEnv_cA h               -- TIMESTAMP
  · exact stateOp_preserves_eEnv_cA h               -- NUMBER
  · exact executionEnvOp_preserves_eEnv_cA h        -- PREVRANDAO
  · exact stateOp_preserves_eEnv_cA h               -- GASLIMIT
  · exact stateOp_preserves_eEnv_cA h               -- CHAINID
  · exact stateOp_preserves_eEnv_cA h               -- SELFBALANCE
  · exact executionEnvOp_preserves_eEnv_cA h        -- BASEFEE
  · exact unaryExecutionEnvOp_preserves_eEnv_cA h   -- BLOBHASH
  · exact executionEnvOp_preserves_eEnv_cA h        -- BLOBBASEFEE

theorem EvmYul.step_eECARow_StackMemFlow
    (o : Operation.SMSFOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.StackMemFlow o : Operation .EVM) arg s = .ok s') :
    eECARow s s' := by
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  · -- POP inline
    split at h
    · injection h with h; subst h; exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · -- MLOAD inline
    split at h
    · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · exact binaryMachineStateOp_preserves_eEnv_cA h    -- MSTORE
  · exact unaryStateOp_preserves_eEnv_cA
      (fun st v => sload_preserves_executionEnv st v)
      (fun st v => sload_preserves_createdAccounts st v) h  -- SLOAD
  · exact binaryStateOp_preserves_eEnv_cA
      (fun st u v => sstore_preserves_executionEnv st u v)
      (fun st u v => sstore_preserves_createdAccounts st u v) h  -- SSTORE
  · exact binaryMachineStateOp_preserves_eEnv_cA h    -- MSTORE8
  · -- JUMP inline
    split at h
    · injection h with h; subst h; exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · -- JUMPI inline
    split at h
    · injection h with h; subst h; exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · -- PC inline
    injection h with h; subst h; exact ⟨rfl, rfl⟩
  · exact machineStateOp_preserves_eEnv_cA h    -- MSIZE
  · exact machineStateOp_preserves_eEnv_cA h    -- GAS
  · -- JUMPDEST inline
    injection h with h; subst h; exact ⟨rfl, rfl⟩
  · exact unaryStateOp_preserves_eEnv_cA
      (fun st v => tload_preserves_executionEnv st v)
      (fun st v => tload_preserves_createdAccounts st v) h  -- TLOAD
  · exact binaryStateOp_preserves_eEnv_cA
      (fun st u v => tstore_preserves_executionEnv st u v)
      (fun st u v => tstore_preserves_createdAccounts st u v) h  -- TSTORE
  · exact ternaryMachineStateOp_preserves_eEnv_cA h   -- MCOPY

theorem EvmYul.step_eECARow_Push
    (o : Operation.POp) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Push o : Operation .EVM) arg s = .ok s') :
    eECARow s s' := by
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  · -- PUSH0
    injection h with h; subst h; exact ⟨rfl, rfl⟩
  all_goals (
    cases harg : arg with
    | none => simp [harg] at h
    | some p =>
      obtain ⟨a', w'⟩ := p
      simp [harg] at h
      subst h; exact ⟨rfl, rfl⟩)

theorem EvmYul.step_eECARow_Dup
    (o : Operation.DOp) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Dup o : Operation .EVM) arg s = .ok s') :
    eECARow s s' := by
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  all_goals exact dup_preserves_eEnv_cA h

theorem EvmYul.step_eECARow_Exchange
    (o : Operation.ExOp) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Exchange o : Operation .EVM) arg s = .ok s') :
    eECARow s s' := by
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  all_goals exact swap_preserves_eEnv_cA h

theorem EvmYul.step_eECARow_Log
    (o : Operation.LOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h : EvmYul.step (.Log o : Operation .EVM) arg s = .ok s') :
    eECARow s s' := by
  cases o
  all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
  · exact log0Op_preserves_eEnv_cA h
  · exact log1Op_preserves_eEnv_cA h
  · exact log2Op_preserves_eEnv_cA h
  · exact log3Op_preserves_eEnv_cA h
  · exact log4Op_preserves_eEnv_cA h

theorem EvmYul.step_eECARow_System
    (o : Operation.SOp .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h_handled : handledByEvmYulStep (.System o : Operation .EVM))
    (h : EvmYul.step (.System o : Operation .EVM) arg s = .ok s') :
    eECARow s s' := by
  obtain ⟨hne1, hne2, hne3, hne4, hne5, hne6⟩ := h_handled
  cases o
  all_goals (try unfold EvmYul.step at h; try simp only [Id.run] at h)
  · exact absurd rfl hne1  -- CREATE
  · exact absurd rfl hne3  -- CALL
  · exact absurd rfl hne4  -- CALLCODE
  · -- RETURN
    exact binaryMachineStateOp_preserves_eEnv_cA h
  · exact absurd rfl hne5  -- DELEGATECALL
  · exact absurd rfl hne2  -- CREATE2
  · exact absurd rfl hne6  -- STATICCALL
  · -- REVERT
    exact binaryMachineStateOp_preserves_eEnv_cA h
  · -- INVALID → dispatchInvalid → .error
    exact absurd h (by simp [dispatchInvalid])
  · -- SELFDESTRUCT
    split at h
    · -- stack pop succeeded
      rename_i stk μ₁ hPop
      split at h
      case isTrue _ =>
        -- Branch A (created in same tx). evmState' := {evmState with accountMap := _, substate := _}.
        -- Then .replaceStackAndIncrPC stk. So executionEnv & createdAccounts preserved.
        split at h
        all_goals (simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
      case isFalse _ =>
        split at h
        all_goals (simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    · simp at h

/-- Main theorem. `EvmYul.step` on the EVM side preserves `executionEnv`
and `createdAccounts` for every handled op, INCLUDING SELFDESTRUCT. -/
theorem EvmYul.step_preserves_eEnv_cA
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h_handled : handledByEvmYulStep op)
    (h : EvmYul.step op arg s = .ok s') :
    s'.executionEnv = s.executionEnv ∧ s'.createdAccounts = s.createdAccounts := by
  cases op with
  | StopArith o    => exact EvmYul.step_eECARow_StopArith o arg s s' h
  | CompBit o      => exact EvmYul.step_eECARow_CompBit o arg s s' h
  | Keccak o       => exact EvmYul.step_eECARow_Keccak o arg s s' h
  | Env o          => exact EvmYul.step_eECARow_Env o arg s s' h
  | Block o        => exact EvmYul.step_eECARow_Block o arg s s' h
  | StackMemFlow o => exact EvmYul.step_eECARow_StackMemFlow o arg s s' h
  | Push o         => exact EvmYul.step_eECARow_Push o arg s s' h
  | Dup o          => exact EvmYul.step_eECARow_Dup o arg s s' h
  | Exchange o     => exact EvmYul.step_eECARow_Exchange o arg s s' h
  | Log o          => exact EvmYul.step_eECARow_Log o arg s s' h
  | System o       => exact EvmYul.step_eECARow_System o arg s s' h_handled h

/-! ## accountMap literal-preservation for handled non-SELFDESTRUCT opcodes

Every handled opcode except SSTORE, TSTORE, and SELFDESTRUCT preserves
`accountMap` literally. For the "mostlyPreservesAccountMap" predicate we
exclude SSTORE / TSTORE / SELFDESTRUCT. SSTORE/TSTORE preserve balance
at every address (via `sstore_preserves_balanceOf` / `tstore_...`), so
StateWF carries through regardless. -/

/-- `EvmYul.step` "strictly preserves accountMap" iff `op` is neither
CREATE/CREATE2/CALL/CALLCODE/DELEGATECALL/STATICCALL nor SSTORE nor TSTORE
nor SELFDESTRUCT. -/
def strictlyPreservesAccountMap (op : Operation .EVM) : Prop :=
  handledByEvmYulStep op ∧ op ≠ .SELFDESTRUCT ∧
    op ≠ .StackMemFlow .SSTORE ∧ op ≠ .StackMemFlow .TSTORE

/-- opRow with the stronger conclusion: accountMap equals. -/
theorem EvmYul.step_accountMap_eq_of_strict
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (hStrict : strictlyPreservesAccountMap op)
    (h : EvmYul.step op arg s = .ok s') :
    s'.accountMap = s.accountMap := by
  obtain ⟨h_handled, _h_ne_sd, h_ne_sstore, h_ne_tstore⟩ := hStrict
  cases op with
  | StopArith o =>
    cases o
    all_goals (
      unfold EvmYul.step at h
      simp only [Id.run] at h)
    · injection h with h; subst h; rfl
    all_goals first
      | exact execBinOp_preserves_accountMap h
      | exact execTriOp_preserves_accountMap h
  | CompBit o =>
    cases o
    all_goals (
      unfold EvmYul.step at h
      simp only [Id.run] at h)
    all_goals first
      | exact execBinOp_preserves_accountMap h
      | exact execUnOp_preserves_accountMap h
  | Keccak o =>
    cases o
    unfold EvmYul.step at h
    simp only [Id.run] at h
    exact binaryMachineStateOp'_preserves_accountMap h
  | Env o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    · exact executionEnvOp_preserves_accountMap h
    · exact unaryStateOp_preserves_accountMap
        (fun st v => balance_preserves_accountMap st v) h
    · exact executionEnvOp_preserves_accountMap h
    · exact executionEnvOp_preserves_accountMap h
    · exact executionEnvOp_preserves_accountMap h
    · exact unaryStateOp_preserves_accountMap (fun _ _ => rfl) h
    · exact executionEnvOp_preserves_accountMap h
    · exact ternaryCopyOp_preserves_accountMap
        (fun ss a b c => calldatacopy_preserves_accountMap ss a b c) h
    · exact executionEnvOp_preserves_accountMap h
    · exact executionEnvOp_preserves_accountMap h
    · exact ternaryCopyOp_preserves_accountMap
        (fun ss a b c => codeCopy_preserves_accountMap ss a b c) h
    · exact unaryStateOp_preserves_accountMap
        (fun st v => extCodeSize_preserves_accountMap st v) h
    · exact quaternaryCopyOp_preserves_accountMap
        (fun ss a b c d => extCodeCopy'_preserves_accountMap ss a b c d) h
    · exact machineStateOp_preserves_accountMap h
    · split at h
      · simp only [Except.ok.injEq] at h; subst h; rfl
      · exact absurd h (by simp)
    · exact unaryStateOp_preserves_accountMap
        (fun st v => extCodeHash_preserves_accountMap st v) h
  | Block o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    · exact unaryStateOp_preserves_accountMap (fun _ _ => rfl) h
    · exact stateOp_preserves_accountMap h
    · exact stateOp_preserves_accountMap h
    · exact stateOp_preserves_accountMap h
    · exact executionEnvOp_preserves_accountMap h
    · exact stateOp_preserves_accountMap h
    · exact stateOp_preserves_accountMap h
    · exact stateOp_preserves_accountMap h
    · exact executionEnvOp_preserves_accountMap h
    · exact unaryExecutionEnvOp_preserves_accountMap h
    · exact executionEnvOp_preserves_accountMap h
  | StackMemFlow o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    · split at h
      · injection h with h; subst h; rfl
      · exact absurd h (by simp)
    · split at h
      · simp only [Except.ok.injEq] at h; subst h; rfl
      · exact absurd h (by simp)
    · exact binaryMachineStateOp_preserves_accountMap h
    · exact unaryStateOp_preserves_accountMap
        (fun st v => sload_preserves_accountMap st v) h
    · exact absurd rfl h_ne_sstore
    · exact binaryMachineStateOp_preserves_accountMap h
    · split at h
      · injection h with h; subst h; rfl
      · exact absurd h (by simp)
    · split at h
      · injection h with h; subst h; rfl
      · exact absurd h (by simp)
    · injection h with h; subst h; rfl
    · exact machineStateOp_preserves_accountMap h
    · exact machineStateOp_preserves_accountMap h
    · injection h with h; subst h; rfl
    · exact unaryStateOp_preserves_accountMap
        (fun st v => tload_preserves_accountMap st v) h
    · exact absurd rfl h_ne_tstore
    · exact ternaryMachineStateOp_preserves_accountMap h
  | Push o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    · injection h with h; subst h; rfl
    all_goals (
      cases harg : arg with
      | none => simp [harg] at h
      | some p =>
        obtain ⟨a', w'⟩ := p
        simp [harg] at h
        subst h; rfl)
  | Dup o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    all_goals exact dup_preserves_accountMap h
  | Exchange o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    all_goals exact swap_preserves_accountMap h
  | Log o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    · exact log0Op_preserves_accountMap h
    · exact log1Op_preserves_accountMap h
    · exact log2Op_preserves_accountMap h
    · exact log3Op_preserves_accountMap h
    · exact log4Op_preserves_accountMap h
  | System o =>
    obtain ⟨hne1, hne2, hne3, hne4, hne5, hne6⟩ := h_handled
    cases o
    all_goals (try unfold EvmYul.step at h; try simp only [Id.run] at h)
    · exact absurd rfl hne1
    · exact absurd rfl hne3
    · exact absurd rfl hne4
    · exact binaryMachineStateOp_preserves_accountMap h
    · exact absurd rfl hne5
    · exact absurd rfl hne2
    · exact absurd rfl hne6
    · exact binaryMachineStateOp_preserves_accountMap h
    · exact absurd h (by simp [dispatchInvalid])
    · exact absurd rfl _h_ne_sd

/-! ## `substate.selfDestructSet` preservation for handled non-SELFDESTRUCT
    opcodes

The only EVM opcode that modifies `substate.selfDestructSet` is
SELFDESTRUCT itself (in branch A — see `EvmYul.step` body in
`EvmYul/Semantics.lean`). Every other handled opcode either uses
`replaceStackAndIncrPC` (which doesn't touch `substate` at all), or
modifies disjoint substate fields:
  * SSTORE bumps `refundBalance` and `accessedStorageKeys`.
  * TSTORE doesn't touch `substate`.
  * SLOAD/TLOAD/BALANCE/EXTCODESIZE/EXTCODEHASH bump
    `accessedStorageKeys` or `accessedAccounts`.
  * LOG ops append to `logSeries`.
  * No other opcode touches `selfDestructSet`.

We package this as a single theorem `EvmYul.step_preserves_selfDestructSet`
covering all handled non-SELFDESTRUCT ops, mirroring the structure of
`EvmYul.step_accountMap_eq_of_strict` but covering SSTORE/TSTORE too. -/

/-! ### Per-helper substate.selfDestructSet preservation -/

theorem balance_preserves_selfDestructSet
    (self : EvmYul.State .EVM) (k : UInt256) :
    (EvmYul.State.balance self k).1.substate.selfDestructSet
      = self.substate.selfDestructSet := by
  unfold EvmYul.State.balance EvmYul.State.addAccessedAccount
  rfl

theorem sload_preserves_selfDestructSet
    (self : EvmYul.State .EVM) (spos : UInt256) :
    (EvmYul.State.sload self spos).1.substate.selfDestructSet
      = self.substate.selfDestructSet := by
  unfold EvmYul.State.sload EvmYul.State.addAccessedStorageKey; rfl

theorem tload_preserves_selfDestructSet
    (self : EvmYul.State .EVM) (spos : UInt256) :
    (EvmYul.State.tload self spos).1.substate.selfDestructSet
      = self.substate.selfDestructSet := by
  unfold EvmYul.State.tload; rfl

theorem extCodeSize_preserves_selfDestructSet
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.extCodeSize self v).1.substate.selfDestructSet
      = self.substate.selfDestructSet := by
  unfold EvmYul.State.extCodeSize EvmYul.State.addAccessedAccount; rfl

theorem extCodeHash_preserves_selfDestructSet
    (self : EvmYul.State .EVM) (v : UInt256) :
    (EvmYul.State.extCodeHash self v).1.substate.selfDestructSet
      = self.substate.selfDestructSet := by
  unfold EvmYul.State.extCodeHash
  by_cases hDead :
      EvmYul.State.dead self.accountMap (AccountAddress.ofUInt256 v) = true
  · rw [if_pos hDead]; rfl
  · rw [if_neg hDead]; rfl

theorem sstore_preserves_selfDestructSet
    (self : EvmYul.State .EVM) (u v : UInt256) :
    (EvmYul.State.sstore self u v).substate.selfDestructSet
      = self.substate.selfDestructSet := by
  unfold EvmYul.State.sstore
  simp only [EvmYul.State.lookupAccount]
  match hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => simp [Option.option]
  | some acc =>
    simp only [Option.option]
    show (_ : EvmYul.State .EVM).substate.selfDestructSet
          = self.substate.selfDestructSet
    rfl

theorem tstore_preserves_selfDestructSet
    (self : EvmYul.State .EVM) (u v : UInt256) :
    (EvmYul.State.tstore self u v).substate.selfDestructSet
      = self.substate.selfDestructSet := by
  unfold EvmYul.State.tstore
  simp only [EvmYul.State.lookupAccount]
  match hFind : self.accountMap.find? self.executionEnv.codeOwner with
  | none => simp [Option.option]
  | some acc =>
    simp only [Option.option]
    unfold EvmYul.State.updateAccount; rfl

/-! ### Per-dispatch-helper substate.selfDestructSet preservation -/

theorem execUnOp_preserves_selfDestructSet
    {f : Primop.Unary} {s s' : EVM.State}
    (h : EVM.execUnOp f s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.execUnOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem execBinOp_preserves_selfDestructSet
    {f : Primop.Binary} {s s' : EVM.State}
    (h : EVM.execBinOp f s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.execBinOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem execTriOp_preserves_selfDestructSet
    {f : Primop.Ternary} {s s' : EVM.State}
    (h : EVM.execTriOp f s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.execTriOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem execQuadOp_preserves_selfDestructSet
    {f : Primop.Quaternary} {s s' : EVM.State}
    (h : EVM.execQuadOp f s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.execQuadOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem executionEnvOp_preserves_selfDestructSet
    {op : ExecutionEnv .EVM → UInt256} {s s' : EVM.State}
    (h : EVM.executionEnvOp op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.executionEnvOp at h
  simp only [Id_run_ok, Except.ok.injEq] at h
  subst h; rfl

theorem unaryExecutionEnvOp_preserves_selfDestructSet
    {op : ExecutionEnv .EVM → UInt256 → UInt256} {s s' : EVM.State}
    (h : EVM.unaryExecutionEnvOp op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.unaryExecutionEnvOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem machineStateOp_preserves_selfDestructSet
    {op : MachineState → UInt256} {s s' : EVM.State}
    (h : EVM.machineStateOp op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.machineStateOp at h
  simp only [Id_run_ok, Except.ok.injEq] at h
  subst h; rfl

theorem stateOp_preserves_selfDestructSet
    {op : EvmYul.State .EVM → UInt256} {s s' : EVM.State}
    (h : EVM.stateOp op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.stateOp at h
  simp only [Id_run_ok, Except.ok.injEq] at h
  subst h; rfl

theorem binaryMachineStateOp_preserves_selfDestructSet
    {op : MachineState → UInt256 → UInt256 → MachineState} {s s' : EVM.State}
    (h : EVM.binaryMachineStateOp op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.binaryMachineStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem binaryMachineStateOp'_preserves_selfDestructSet
    {op : MachineState → UInt256 → UInt256 → UInt256 × MachineState} {s s' : EVM.State}
    (h : EVM.binaryMachineStateOp' op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.binaryMachineStateOp' at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem ternaryMachineStateOp_preserves_selfDestructSet
    {op : MachineState → UInt256 → UInt256 → UInt256 → MachineState} {s s' : EVM.State}
    (h : EVM.ternaryMachineStateOp op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.ternaryMachineStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem dup_preserves_selfDestructSet
    {n : ℕ} {s s' : EVM.State}
    (h : EvmYul.dup n s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EvmYul.dup at h
  simp only [] at h
  by_cases hlen : (s.stack.take n).length = n
  · rw [if_pos hlen] at h; injection h with h; subst h; rfl
  · rw [if_neg hlen] at h; exact absurd h (by simp)

theorem swap_preserves_selfDestructSet
    {n : ℕ} {s s' : EVM.State}
    (h : EvmYul.swap n s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EvmYul.swap at h
  simp only [] at h
  by_cases hlen : (s.stack.take (n + 1)).length = n + 1
  · rw [if_pos hlen] at h; injection h with h; subst h; rfl
  · rw [if_neg hlen] at h; exact absurd h (by simp)

theorem ternaryCopyOp_preserves_selfDestructSet
    {op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM}
    {s s' : EVM.State}
    (hOp : ∀ ss a b c, (op ss a b c).toState.substate.selfDestructSet
                        = ss.toState.substate.selfDestructSet)
    (h : EVM.ternaryCopyOp op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.ternaryCopyOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h
    exact hOp _ _ _ _
  · exact absurd h (by simp)

theorem quaternaryCopyOp_preserves_selfDestructSet
    {op : SharedState .EVM → UInt256 → UInt256 → UInt256 → UInt256 → SharedState .EVM}
    {s s' : EVM.State}
    (hOp : ∀ ss a b c d, (op ss a b c d).toState.substate.selfDestructSet
                          = ss.toState.substate.selfDestructSet)
    (h : EVM.quaternaryCopyOp op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.quaternaryCopyOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h
    exact hOp _ _ _ _ _
  · exact absurd h (by simp)

theorem calldatacopy_preserves_selfDestructSet
    {τ} (self : SharedState τ) (mstart datastart size : UInt256) :
    (SharedState.calldatacopy self mstart datastart size).toState.substate.selfDestructSet
      = self.toState.substate.selfDestructSet := rfl

theorem codeCopy_preserves_selfDestructSet
    (self : SharedState .EVM) (mstart cstart size : UInt256) :
    (SharedState.codeCopy self mstart cstart size).toState.substate.selfDestructSet
      = self.toState.substate.selfDestructSet := rfl

theorem extCodeCopy'_preserves_selfDestructSet
    (self : SharedState .EVM) (acc mstart cstart size : UInt256) :
    (SharedState.extCodeCopy' self acc mstart cstart size).toState.substate.selfDestructSet
      = self.toState.substate.selfDestructSet := by
  unfold SharedState.extCodeCopy'; rfl

theorem log0Op_preserves_selfDestructSet
    {s s' : EVM.State} (h : EVM.log0Op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.log0Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem log1Op_preserves_selfDestructSet
    {s s' : EVM.State} (h : EVM.log1Op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.log1Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem log2Op_preserves_selfDestructSet
    {s s' : EVM.State} (h : EVM.log2Op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.log2Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem log3Op_preserves_selfDestructSet
    {s s' : EVM.State} (h : EVM.log3Op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.log3Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem log4Op_preserves_selfDestructSet
    {s s' : EVM.State} (h : EVM.log4Op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.log4Op at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

theorem unaryStateOp_preserves_selfDestructSet
    {op : EvmYul.State .EVM → UInt256 → EvmYul.State .EVM × UInt256}
    {s s' : EVM.State}
    (hOp : ∀ st u, (op st u).1.substate.selfDestructSet
                    = st.substate.selfDestructSet)
    (h : EVM.unaryStateOp op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.unaryStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h
    show (op s.toState _).1.substate.selfDestructSet = s.substate.selfDestructSet
    exact hOp _ _
  · exact absurd h (by simp)

theorem binaryStateOp_preserves_selfDestructSet
    {op : EvmYul.State .EVM → UInt256 → UInt256 → EvmYul.State .EVM}
    {s s' : EVM.State}
    (hOp : ∀ st u v, (op st u v).substate.selfDestructSet
                      = st.substate.selfDestructSet)
    (h : EVM.binaryStateOp op s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EVM.binaryStateOp at h
  split at h
  · simp only [Id_run_ok, Except.ok.injEq] at h
    subst h
    show (op s.toState _ _).substate.selfDestructSet = s.substate.selfDestructSet
    exact hOp _ _ _
  · exact absurd h (by simp)

/-- `EvmYul.step` preserves `substate.selfDestructSet` for every handled
opcode except SELFDESTRUCT.

Mirrors the structure of `EvmYul.step_accountMap_eq_of_strict` but
covers SSTORE and TSTORE explicitly (whose substate-touching is
disjoint from `selfDestructSet`). -/
theorem EvmYul.step_preserves_selfDestructSet
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State)
    (h_handled : handledByEvmYulStep op)
    (h_ne : op ≠ .SELFDESTRUCT)
    (h : EvmYul.step op arg s = .ok s') :
    s'.substate.selfDestructSet = s.substate.selfDestructSet := by
  obtain ⟨hne1, hne2, hne3, hne4, hne5, hne6⟩ := h_handled
  cases op with
  | StopArith o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    · injection h with h; subst h; rfl
    all_goals first
      | exact execBinOp_preserves_selfDestructSet h
      | exact execTriOp_preserves_selfDestructSet h
  | CompBit o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    all_goals first
      | exact execBinOp_preserves_selfDestructSet h
      | exact execUnOp_preserves_selfDestructSet h
  | Keccak o =>
    cases o
    unfold EvmYul.step at h; simp only [Id.run] at h
    exact binaryMachineStateOp'_preserves_selfDestructSet h
  | Env o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    · exact executionEnvOp_preserves_selfDestructSet h
    · exact unaryStateOp_preserves_selfDestructSet
        (fun st v => balance_preserves_selfDestructSet st v) h
    · exact executionEnvOp_preserves_selfDestructSet h
    · exact executionEnvOp_preserves_selfDestructSet h
    · exact executionEnvOp_preserves_selfDestructSet h
    · exact unaryStateOp_preserves_selfDestructSet (fun _ _ => rfl) h
    · exact executionEnvOp_preserves_selfDestructSet h
    · exact ternaryCopyOp_preserves_selfDestructSet
        (fun ss a b c => calldatacopy_preserves_selfDestructSet ss a b c) h
    · exact executionEnvOp_preserves_selfDestructSet h
    · exact executionEnvOp_preserves_selfDestructSet h
    · exact ternaryCopyOp_preserves_selfDestructSet
        (fun ss a b c => codeCopy_preserves_selfDestructSet ss a b c) h
    · exact unaryStateOp_preserves_selfDestructSet
        (fun st v => extCodeSize_preserves_selfDestructSet st v) h
    · exact quaternaryCopyOp_preserves_selfDestructSet
        (fun ss a b c d => extCodeCopy'_preserves_selfDestructSet ss a b c d) h
    · exact machineStateOp_preserves_selfDestructSet h
    · split at h
      · simp only [Except.ok.injEq] at h; subst h; rfl
      · exact absurd h (by simp)
    · exact unaryStateOp_preserves_selfDestructSet
        (fun st v => extCodeHash_preserves_selfDestructSet st v) h
  | Block o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    · exact unaryStateOp_preserves_selfDestructSet (fun _ _ => rfl) h
    · exact stateOp_preserves_selfDestructSet h
    · exact stateOp_preserves_selfDestructSet h
    · exact stateOp_preserves_selfDestructSet h
    · exact executionEnvOp_preserves_selfDestructSet h
    · exact stateOp_preserves_selfDestructSet h
    · exact stateOp_preserves_selfDestructSet h
    · exact stateOp_preserves_selfDestructSet h
    · exact executionEnvOp_preserves_selfDestructSet h
    · exact unaryExecutionEnvOp_preserves_selfDestructSet h
    · exact executionEnvOp_preserves_selfDestructSet h
  | StackMemFlow o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    · split at h
      · injection h with h; subst h; rfl
      · exact absurd h (by simp)
    · split at h
      · simp only [Except.ok.injEq] at h; subst h; rfl
      · exact absurd h (by simp)
    · exact binaryMachineStateOp_preserves_selfDestructSet h
    · exact unaryStateOp_preserves_selfDestructSet
        (fun st v => sload_preserves_selfDestructSet st v) h
    · -- SSTORE
      exact binaryStateOp_preserves_selfDestructSet
        (fun st u v => sstore_preserves_selfDestructSet st u v) h
    · exact binaryMachineStateOp_preserves_selfDestructSet h
    · split at h
      · injection h with h; subst h; rfl
      · exact absurd h (by simp)
    · split at h
      · injection h with h; subst h; rfl
      · exact absurd h (by simp)
    · injection h with h; subst h; rfl
    · exact machineStateOp_preserves_selfDestructSet h
    · exact machineStateOp_preserves_selfDestructSet h
    · injection h with h; subst h; rfl
    · exact unaryStateOp_preserves_selfDestructSet
        (fun st v => tload_preserves_selfDestructSet st v) h
    · -- TSTORE
      exact binaryStateOp_preserves_selfDestructSet
        (fun st u v => tstore_preserves_selfDestructSet st u v) h
    · exact ternaryMachineStateOp_preserves_selfDestructSet h
  | Push o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    · injection h with h; subst h; rfl
    all_goals (
      cases harg : arg with
      | none => simp [harg] at h
      | some p =>
        obtain ⟨a', w'⟩ := p
        simp [harg] at h
        subst h; rfl)
  | Dup o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    all_goals exact dup_preserves_selfDestructSet h
  | Exchange o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    all_goals exact swap_preserves_selfDestructSet h
  | Log o =>
    cases o
    all_goals (unfold EvmYul.step at h; simp only [Id.run] at h)
    · exact log0Op_preserves_selfDestructSet h
    · exact log1Op_preserves_selfDestructSet h
    · exact log2Op_preserves_selfDestructSet h
    · exact log3Op_preserves_selfDestructSet h
    · exact log4Op_preserves_selfDestructSet h
  | System o =>
    cases o
    all_goals (try unfold EvmYul.step at h; try simp only [Id.run] at h)
    · exact absurd rfl hne1
    · exact absurd rfl hne3
    · exact absurd rfl hne4
    · exact binaryMachineStateOp_preserves_selfDestructSet h
    · exact absurd rfl hne5
    · exact absurd rfl hne2
    · exact absurd rfl hne6
    · exact binaryMachineStateOp_preserves_selfDestructSet h
    · exact absurd h (by simp [dispatchInvalid])
    · exact absurd rfl h_ne

/-- Corollary of `EvmYul.step_preserves_selfDestructSet`: a handled
non-SELFDESTRUCT step preserves `SubstateSDExclude … C`. -/
theorem EvmYul.step_preserves_SD_exclude
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s' : EVM.State) (C : AccountAddress)
    (h_handled : handledByEvmYulStep op)
    (h_ne : op ≠ .SELFDESTRUCT)
    (h : EvmYul.step op arg s = .ok s')
    (hSD : ∀ k ∈ s.substate.selfDestructSet.1.toList, k ≠ C) :
    ∀ k ∈ s'.substate.selfDestructSet.1.toList, k ≠ C := by
  have hEq := EvmYul.step_preserves_selfDestructSet op arg s s' h_handled h_ne h
  intro k hk
  rw [hEq] at hk
  exact hSD k hk

end Frame
end EvmYul
