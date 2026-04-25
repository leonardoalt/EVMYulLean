import EvmYul.Frame.Projection
import EvmYul.Frame.StepFrame
import EvmYul.Semantics
import EvmYul.EVM.State

/-!
# A2 — SELFDESTRUCT balance frame

Assuming `StateWF s.accountMap` (i.e. `totalETH < 2^256`):

  If `EvmYul.step .SELFDESTRUCT .none s = .ok s'` and `a ≠ Iₐ` then
  `balanceOf s'.accountMap a ≥ balanceOf s.accountMap a`.

Body structure: 5 shapes (Iₐ absent / r absent × σ_Iₐ zero / r absent ×
σ_Iₐ nonzero / r present × r≠Iₐ / r = Iₐ) times 2 outer branches
(created-same-tx or not). In every shape, for `a ≠ Iₐ`, either:

* accountMap is literally unchanged (shapes 1, 2, and the same-tx-self
  shape of branch B), or
* accountMap has two inserts at `r` and `Iₐ`. Since `a ≠ Iₐ`, frame
  preservation at `a ≠ r` follows from `find?_insert_ne` twice. At
  `a = r`, new balance = σ_r.balance + σ_Iₐ.balance (case 4) or
  σ_Iₐ.balance (case 3, where r was absent). The case-4 step needs
  `StateWF` to prevent UInt256 wrap.
-/

namespace EvmYul
namespace Frame

open Batteries EvmYul.EVM

/-! ## Helper lemmas -/

/-- Two inserts at `r` and `Iₐ` with `a ≠ r` and `a ≠ Iₐ` preserve
`balanceOf a`. -/
private theorem balanceOf_double_insert_ne
    (σ : AccountMap .EVM) (r Iₐ a : AccountAddress)
    (acc_r acc_Iₐ : Account .EVM)
    (hrA : r ≠ a) (hIₐA : Iₐ ≠ a) :
    balanceOf ((σ.insert r acc_r).insert Iₐ acc_Iₐ) a = balanceOf σ a := by
  apply balanceOf_of_find?_eq
  rw [find?_insert_ne _ _ _ _ hIₐA]
  exact find?_insert_ne _ _ _ _ hrA

/-- At `a = r`, with `r ≠ Iₐ`, and balances summing without wrap,
`balanceOf` of the "case 4" double-insert at `r` equals
`σ_r.balance.toNat + σ_Iₐ.balance.toNat`. -/
private theorem balanceOf_double_insert_case4_at_r
    (σ : AccountMap .EVM) (r Iₐ : AccountAddress)
    (σ_r σ_Iₐ : Account .EVM)
    (hrIₐ : r ≠ Iₐ)
    (hNoWrap : σ_r.balance.toNat + σ_Iₐ.balance.toNat < UInt256.size) :
    balanceOf
      ((σ.insert r {σ_r with balance := σ_r.balance + σ_Iₐ.balance}).insert
        Iₐ {σ_Iₐ with balance := ⟨0⟩}) r
      = σ_r.balance.toNat + σ_Iₐ.balance.toNat := by
  unfold balanceOf
  rw [find?_insert_ne _ _ _ _ hrIₐ.symm]
  rw [find?_insert_self]
  simp only [Option.elim]
  exact UInt256_add_toNat_of_no_wrap _ _ hNoWrap

/-! ## Main theorem -/

theorem selfdestruct_balanceOf_ne_Iₐ_ge
    (s s' : EVM.State) (a : AccountAddress)
    (hWF : StateWF s.accountMap)
    (h : EvmYul.step (.SELFDESTRUCT : Operation .EVM) .none s = .ok s')
    (hne : a ≠ s.executionEnv.codeOwner) :
    balanceOf s'.accountMap a ≥ balanceOf s.accountMap a := by
  unfold EvmYul.step at h
  simp only [Id.run] at h
  set Iₐ := s.executionEnv.codeOwner with hIₐ_def
  have hIₐA : Iₐ ≠ a := fun heq => hne heq.symm
  split at h
  case _ stk μ₁ hPop =>
    set r : AccountAddress := AccountAddress.ofUInt256 μ₁ with hr_def
    split at h
    case _ hCreated =>
      -- Branch A
      split at h
      case _ hLookIₐ =>
        -- Case 1: accountMap unchanged
        simp only [Except.ok.injEq] at h
        subst h
        change balanceOf s.accountMap a ≥ balanceOf s.accountMap a
        exact Nat.le_refl _
      case _ σ_Iₐ hLookIₐ =>
        split at h
        case _ hLookR =>
          split at h
          case isTrue hBal =>
            -- Case 2
            simp only [Except.ok.injEq] at h
            subst h
            change balanceOf s.accountMap a ≥ balanceOf s.accountMap a
            exact Nat.le_refl _
          case isFalse hBal =>
            -- Case 3
            simp only [Except.ok.injEq] at h
            subst h
            change balanceOf (_root_.Batteries.RBMap.insert _ _ _) a ≥ _
            by_cases hra : a = r
            · -- a = r: old balance at a was 0
              have hOldZero : balanceOf s.accountMap a = 0 := by
                unfold balanceOf
                rw [hra]
                unfold EvmYul.State.lookupAccount at hLookR
                rw [hLookR]
                rfl
              rw [hOldZero]
              exact Nat.zero_le _
            · -- a ≠ r: frame
              have hrA : r ≠ a := fun heq => hra heq.symm
              apply Nat.le_of_eq
              exact (balanceOf_double_insert_ne _ _ _ _ _ _ hrA hIₐA).symm
        case _ σ_r hLookR =>
          split at h
          case isTrue hrIₐ =>
            -- Case 4
            simp only [Except.ok.injEq] at h
            subst h
            change balanceOf (_root_.Batteries.RBMap.insert _ _ _) a ≥ _
            by_cases hra : a = r
            · have hRFind : s.accountMap.find? r = some σ_r := by
                unfold EvmYul.State.lookupAccount at hLookR
                exact hLookR
              have hIₐFind : s.accountMap.find? Iₐ = some σ_Iₐ := by
                unfold EvmYul.State.lookupAccount at hLookIₐ
                exact hLookIₐ
              have hNoWrap :
                  σ_r.balance.toNat + σ_Iₐ.balance.toNat < UInt256.size :=
                no_wrap_pair s.accountMap hWF r Iₐ σ_r σ_Iₐ hRFind hIₐFind hrIₐ
              rw [hra]
              rw [balanceOf_double_insert_case4_at_r _ _ _ _ _ hrIₐ hNoWrap]
              have hOld : balanceOf s.accountMap r = σ_r.balance.toNat := by
                unfold balanceOf; rw [hRFind]; rfl
              rw [hOld]
              exact Nat.le_add_right _ _
            · have hrA : r ≠ a := fun heq => hra heq.symm
              apply Nat.le_of_eq
              exact (balanceOf_double_insert_ne _ _ _ _ _ _ hrA hIₐA).symm
          case isFalse hrIₐ =>
            -- Case 5A: burn
            simp only [Except.ok.injEq] at h
            subst h
            change balanceOf (_root_.Batteries.RBMap.insert _ _ _) a ≥ _
            have hrIₐ' : r = Iₐ := Classical.not_not.mp hrIₐ
            have hrA : r ≠ a := hrIₐ' ▸ hIₐA
            apply Nat.le_of_eq
            exact (balanceOf_double_insert_ne _ _ _ _ _ _ hrA hIₐA).symm
    case _ hNotCreated =>
      -- Branch B
      split at h
      case _ hLookIₐ =>
        simp only [Except.ok.injEq] at h
        subst h
        change balanceOf s.accountMap a ≥ balanceOf s.accountMap a
        exact Nat.le_refl _
      case _ σ_Iₐ hLookIₐ =>
        split at h
        case _ hLookR =>
          split at h
          case isTrue hBal =>
            simp only [Except.ok.injEq] at h
            subst h
            change balanceOf s.accountMap a ≥ balanceOf s.accountMap a
            exact Nat.le_refl _
          case isFalse hBal =>
            simp only [Except.ok.injEq] at h
            subst h
            change balanceOf (_root_.Batteries.RBMap.insert _ _ _) a ≥ _
            by_cases hra : a = r
            · have hOldZero : balanceOf s.accountMap a = 0 := by
                unfold balanceOf
                rw [hra]
                unfold EvmYul.State.lookupAccount at hLookR
                rw [hLookR]
                rfl
              rw [hOldZero]
              exact Nat.zero_le _
            · have hrA : r ≠ a := fun heq => hra heq.symm
              apply Nat.le_of_eq
              exact (balanceOf_double_insert_ne _ _ _ _ _ _ hrA hIₐA).symm
        case _ σ_r hLookR =>
          split at h
          case isTrue hrIₐ =>
            simp only [Except.ok.injEq] at h
            subst h
            change balanceOf (_root_.Batteries.RBMap.insert _ _ _) a ≥ _
            by_cases hra : a = r
            · have hRFind : s.accountMap.find? r = some σ_r := by
                unfold EvmYul.State.lookupAccount at hLookR
                exact hLookR
              have hIₐFind : s.accountMap.find? Iₐ = some σ_Iₐ := by
                unfold EvmYul.State.lookupAccount at hLookIₐ
                exact hLookIₐ
              have hNoWrap :
                  σ_r.balance.toNat + σ_Iₐ.balance.toNat < UInt256.size :=
                no_wrap_pair s.accountMap hWF r Iₐ σ_r σ_Iₐ hRFind hIₐFind hrIₐ
              rw [hra]
              rw [balanceOf_double_insert_case4_at_r _ _ _ _ _ hrIₐ hNoWrap]
              have hOld : balanceOf s.accountMap r = σ_r.balance.toNat := by
                unfold balanceOf; rw [hRFind]; rfl
              rw [hOld]
              exact Nat.le_add_right _ _
            · have hrA : r ≠ a := fun heq => hra heq.symm
              apply Nat.le_of_eq
              exact (balanceOf_double_insert_ne _ _ _ _ _ _ hrA hIₐA).symm
          case isFalse hrIₐ =>
            -- Case 5B: no-op (accountMap unchanged)
            simp only [Except.ok.injEq] at h
            subst h
            change balanceOf s.accountMap a ≥ balanceOf s.accountMap a
            exact Nat.le_refl _
  case _ hPop =>
    simp at h

-- `selfdestruct_preserves_StateWF` is proved in MutualFrame.lean (it
-- needs `totalETH_insert_of_mem` / `_not_mem` which live there).

/-- SELFDESTRUCT preserves executionEnv. -/
theorem selfdestruct_preserves_executionEnv
    (s s' : EVM.State)
    (h : EvmYul.step (.SELFDESTRUCT : Operation .EVM) .none s = .ok s') :
    s'.executionEnv = s.executionEnv := by
  unfold EvmYul.step at h
  simp only [Id.run] at h
  split at h
  case _ _ _ _ =>
    split at h
    case _ _ =>
      split at h
      case _ _ => simp only [Except.ok.injEq] at h; subst h; rfl
      case _ σ_Iₐ _ =>
        split at h
        case _ _ =>
          split at h
          all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
        case _ σ_r _ =>
          split at h
          all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
    case _ _ =>
      split at h
      case _ _ => simp only [Except.ok.injEq] at h; subst h; rfl
      case _ σ_Iₐ _ =>
        split at h
        case _ _ =>
          split at h
          all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
        case _ σ_r _ =>
          split at h
          all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
  case _ _ => simp at h

/-- SELFDESTRUCT preserves createdAccounts (it only modifies
`substate.selfDestructSet`, not `createdAccounts`). -/
theorem selfdestruct_preserves_createdAccounts
    (s s' : EVM.State)
    (h : EvmYul.step (.SELFDESTRUCT : Operation .EVM) .none s = .ok s') :
    s'.createdAccounts = s.createdAccounts := by
  unfold EvmYul.step at h
  simp only [Id.run] at h
  split at h
  case _ _ _ _ =>
    split at h
    case _ _ =>
      split at h
      case _ _ => simp only [Except.ok.injEq] at h; subst h; rfl
      case _ σ_Iₐ _ =>
        split at h
        case _ _ =>
          split at h
          all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
        case _ σ_r _ =>
          split at h
          all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
    case _ _ =>
      split at h
      case _ _ => simp only [Except.ok.injEq] at h; subst h; rfl
      case _ σ_Iₐ _ =>
        split at h
        case _ _ =>
          split at h
          all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
        case _ σ_r _ =>
          split at h
          all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
  case _ _ => simp at h

/-! ### SELFDESTRUCT and `selfDestructSet` evolution

SELFDESTRUCT only adds `Iₐ` to `selfDestructSet` in branch A —
when `createdAccounts.contains Iₐ`. In branch B (the contract was
not created in the same transaction), `selfDestructSet` is
unchanged. Thus the post-step SD-set is a subset of the input SD-set
union `{Iₐ}` (with `Iₐ` only contributing in branch A). -/

/-- SELFDESTRUCT step's effect on `selfDestructSet`: every element of
the post-step SD-set is either in the pre-step SD-set or equals
`s.executionEnv.codeOwner` (i.e. `Iₐ`).

This is the structural invariant we use to derive C-exclusion of the
output SD-set: if the input SD-set excludes `C` and `Iₐ ≠ C`, then
the output SD-set excludes `C`.

In our use site (`X_inv` / `step_bundled_invariant_at_C`), `Iₐ ≠ C`
follows from `(∀ a ∈ s.createdAccounts, a ≠ C)` — since SELFDESTRUCT
adding `Iₐ` to the SD-set requires `Iₐ ∈ createdAccounts` (branch A's
guard). For non-at-C steps, `Iₐ = s.executionEnv.codeOwner ≠ C` is
the hypothesis directly. -/
theorem selfdestruct_SDset_subset_or_Iₐ
    (s s' : EVM.State)
    (h : EvmYul.step (.SELFDESTRUCT : Operation .EVM) .none s = .ok s') :
    ∀ k ∈ s'.substate.selfDestructSet.1.toList,
      k ∈ s.substate.selfDestructSet.1.toList ∨ k = s.executionEnv.codeOwner := by
  unfold EvmYul.step at h
  simp only [Id.run] at h
  set Iₐ := s.executionEnv.codeOwner with hIₐ_def
  split at h
  case _ stk μ₁ hPop =>
    split at h
    case _ hCreated =>
      -- Branch A: substate' has selfDestructSet := old.insert Iₐ.
      -- All sub-cases set substate := A' (with the .insert).
      have hSub :
        ∀ k ∈ s'.substate.selfDestructSet.1.toList,
          k ∈ s.substate.selfDestructSet.1.toList ∨ k = Iₐ := by
        intro k hk
        -- We need to show that s'.substate.selfDestructSet =
        -- s.substate.selfDestructSet.insert Iₐ. Walk the case-tree.
        have hSDeq :
            s'.substate.selfDestructSet = s.substate.selfDestructSet.insert Iₐ := by
          split at h
          case _ _ =>
            -- Look up Iₐ failed: substate = original.
            simp only [Except.ok.injEq] at h; subst h; rfl
          case _ σ_Iₐ _ =>
            split at h
            case _ _ =>
              split at h
              all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
            case _ σ_r _ =>
              split at h
              all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
        rw [hSDeq] at hk
        -- Now `k ∈ (s.substate.selfDestructSet.insert Iₐ).1.toList`.
        -- Use `RBSet.mem_insert`-style reasoning to split.
        have hMem : k ∈ s.substate.selfDestructSet.insert Iₐ :=
          Batteries.RBSet.mem_of_mem_toList hk
        rcases Batteries.RBSet.mem_insert.mp hMem with hOrig | hCmp
        · left
          -- hOrig : k ∈ s.substate.selfDestructSet
          -- We need `k ∈ s.substate.selfDestructSet.1.toList`.
          -- Convert via the underlying RBNode membership.
          -- `k ∈ s.substate.selfDestructSet` is `MemP (compare k) ...`.
          -- We need to reverse: convert to `k ∈ .1.toList`.
          -- Use the fact that for `compare` on `AccountAddress` (Fin _),
          -- `MemP (compare k) s ↔ k ∈ s.1.toList`.
          --
          -- Simpler: reuse the `Batteries.RBSet.mem_def`-style lemma
          -- that translates RBSet membership to toList membership.
          --
          -- Path: `mem_iff_mem_toList` if available; else we use
          -- a pragmatic ordering.
          --
          -- Concrete approach: AccountAddress = Fin _, with decidable eq.
          -- `MemP (compare k) s` is `Any (compare k · = .eq) s.1`.
          -- `compare a b = .eq ↔ a = b` for `LawfulEqCmp compare`.
          -- So `MemP` collapses to `Any (· = k) ↔ k ∈ s.1.toList`.
          --
          -- Empirically we already have access to
          -- `Batteries.RBSet.mem_of_mem_toList` (the forward direction).
          -- The reverse is `Batteries.RBSet.mem_toList_of_mem` if it exists.
          -- Otherwise we go through `RBNode.Any` and `LawfulEqCmp`.
          --
          -- For now, we appeal to `Std.LawfulEqCmp` (compare = .eq ↔ =).
          -- AccountAddress is `Fin _` with `compare = compareOfLessAndEq`.
          have hRBmem : Batteries.RBSet.MemP (compare k) s.substate.selfDestructSet := hOrig
          -- hRBmem unfolds via memP_def to ∃ x ∈ s.substate.selfDestructSet.1, compare k x = .eq.
          rw [show Batteries.RBSet.MemP (compare k) s.substate.selfDestructSet
                ↔ ∃ x ∈ s.substate.selfDestructSet.1, compare k x = .eq
                from Batteries.RBNode.memP_def] at hRBmem
          obtain ⟨x, hxMem, hCmp⟩ := hRBmem
          have hxk : x = k := (Std.LawfulEqCmp.compare_eq_iff_eq.mp hCmp).symm
          rw [hxk] at hxMem
          exact Batteries.RBNode.mem_toList.mpr hxMem
        · -- compare Iₐ k = .eq → Iₐ = k → k = Iₐ
          right
          exact (Std.LawfulEqCmp.compare_eq_iff_eq.mp hCmp).symm
      exact hSub
    case _ hNotCreated =>
      -- Branch B: substate' has same selfDestructSet as s.substate.
      have hSDeq : s'.substate.selfDestructSet = s.substate.selfDestructSet := by
        split at h
        case _ _ =>
          simp only [Except.ok.injEq] at h; subst h; rfl
        case _ σ_Iₐ _ =>
          split at h
          case _ _ =>
            split at h
            all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
          case _ σ_r _ =>
            split at h
            all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
      intro k hk
      rw [hSDeq] at hk
      exact Or.inl hk
  case _ _ => simp at h

/-- SELFDESTRUCT step preserves `SubstateSDExclude C` of the substate
when the executing-frame address `Iₐ ≠ C`.

This is the leaf invariant for SD-set tracking: combined with
`(∀ a ∈ createdAccounts, a ≠ C)` (which by branch A's guard implies
`Iₐ ≠ C` whenever the SD-set actually grows), it propagates SD-set
exclusion of `C` through every SELFDESTRUCT step. -/
theorem selfdestruct_preserves_SD_exclude_C
    (s s' : EVM.State) (C : AccountAddress)
    (hSD_in : ∀ k ∈ s.substate.selfDestructSet.1.toList, k ≠ C)
    (hIₐne : s.executionEnv.codeOwner ≠ C)
    (h : EvmYul.step (.SELFDESTRUCT : Operation .EVM) .none s = .ok s') :
    ∀ k ∈ s'.substate.selfDestructSet.1.toList, k ≠ C := by
  intro k hk
  rcases selfdestruct_SDset_subset_or_Iₐ s s' h k hk with hOld | hIₐ
  · exact hSD_in k hOld
  · rw [hIₐ]; exact hIₐne

end Frame
end EvmYul
