import Batteries.Data.RBMap
import Batteries.Data.RBMap.Lemmas

import EvmYul.Frame.Projection
import EvmYul.State.AccountOps
import EvmYul.Maps.AccountMap
import EvmYul.Maps.StorageMap

/-!
# Storage-sum primitives — `storageSum` (Solvency §1.4)

`storageSum σ C` is the `ℕ`-valued sum of all `UInt256` values stored
at address `C`'s persistent-storage map. It powers the Weth solvency
invariant `WethInv σ C := storageSum σ C ≤ balanceOf σ C`.

This file establishes the definition together with the simple
"unchanged-at-other-account" companion that follows directly from
`find?`-equality. The full `_sstore_eq` / `_old_le` lemmas, which
require RBMap insert/erase reasoning, live in a downstream extension
once §H's invariant-tracking closure consumes them; for the purposes
of `WethInv`'s definition (§2.1) and the SSTORE step lemma (§1.5)
the def + the unchanged-at-other-account corollary suffice.
-/

namespace EvmYul
namespace Frame

open Batteries

/-- `storageSum σ C` is `Σ_slot σ[C].storage[slot]` cast to `ℕ`.

When `C` has no account, the sum is `0` (consistent with
`balanceOf`'s "absent → 0" convention). -/
def storageSum (σ : AccountMap .EVM) (C : AccountAddress) : ℕ :=
  match σ.find? C with
  | none => 0
  | some acc => acc.storage.foldl (fun acc _ v => acc + v.toNat) 0

/-- If `σ` and `σ'` agree on `find? C`, they agree on `storageSum`. -/
theorem storageSum_of_find?_eq
    {σ σ' : AccountMap .EVM} {C : AccountAddress}
    (h : σ'.find? C = σ.find? C) :
    storageSum σ' C = storageSum σ C := by
  unfold storageSum; rw [h]

/-- Inserting at `a ≠ C` leaves `storageSum σ C` unchanged.

Direct corollary of `find?_insert_ne`: at the projection level the
two maps agree on `find? C`, so their storageSum's coincide. -/
theorem storageSum_unchanged_at_other_account
    (σ : AccountMap .EVM) (C a : AccountAddress) (acc' : Account .EVM)
    (h : a ≠ C) :
    storageSum (σ.insert a acc') C = storageSum σ C := by
  apply storageSum_of_find?_eq
  exact find?_insert_ne σ a C acc' h

/-- The empty storage's sum is `0` (when `C` has no account). -/
theorem storageSum_none (σ : AccountMap .EVM) (C : AccountAddress)
    (h : σ.find? C = none) :
    storageSum σ C = 0 := by
  unfold storageSum; rw [h]

/-- If `σ.find? C = some acc`, then `storageSum σ C` is the foldl-sum
of `acc.storage`'s values. Useful for unfolding `storageSum` once the
account is in hand. -/
theorem storageSum_of_find?_some
    (σ : AccountMap .EVM) (C : AccountAddress) (acc : Account .EVM)
    (h : σ.find? C = some acc) :
    storageSum σ C
      = acc.storage.foldl (fun acc _ v => acc + v.toNat) 0 := by
  unfold storageSum; rw [h]

/-- If two states agree on the *storage projection* `find? C ↦ storage`
— i.e. on the `Option (StorageMap)` derived from `find? C` — then they
agree on `storageSum σ C`.

This is the lemma used to lift step-level storage-projection-equality
(provided by `EvmYul.step_modifies_storage_only_at_codeOwner` at
non-codeOwner addresses) to `storageSum` equality. -/
theorem storageSum_of_storage_proj_eq
    {σ σ' : AccountMap .EVM} {C : AccountAddress}
    (h : ((σ'.find? C).map (·.storage)) = ((σ.find? C).map (·.storage))) :
    storageSum σ' C = storageSum σ C := by
  unfold storageSum
  -- Case-split on σ.find? C and σ'.find? C; the hypothesis forces the
  -- two lookups to have the same option-shape, and storage values agree
  -- when both are `some`.
  cases hσ : σ.find? C with
  | none =>
    -- σ-side: 0. σ'-side must also be `none` (else `(some ?).map …` ≠ `none`).
    rw [hσ] at h
    cases hσ' : σ'.find? C with
    | none => rfl
    | some acc' =>
      rw [hσ'] at h
      -- h : (some acc').map (·.storage) = (none).map (·.storage)
      -- i.e. some acc'.storage = none — contradiction.
      simp only [Option.map_some, Option.map_none] at h
      cases h
  | some acc =>
    rw [hσ] at h
    cases hσ' : σ'.find? C with
    | none =>
      rw [hσ'] at h
      simp only [Option.map_some, Option.map_none] at h
      cases h
    | some acc' =>
      rw [hσ'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [h]

/-! ## §1.4 — `storageSum_old_le`

The "old slot value is bounded by the storage-sum" bound. Used by
the at-`C` SSTORE step lemma: if the slot's old value is `oldVal`,
then `oldVal.toNat ≤ storageSum σ C`. The proof reduces `storageSum`
to `List.sum`-over-`toList` and uses `List.le_sum_of_mem` after
extracting the `(slot, oldVal)` pair from the `find?` hypothesis. -/

/-- Fold ↔ `List.sum` bridge for storage values. Mirror of
`Projection.totalETH_eq_sum`. -/
private theorem storageSum_acc_eq_sum
    (acc : Account .EVM) :
    acc.storage.foldl (fun a _ v => a + v.toNat) 0
      = (acc.storage.toList.map (fun p => p.2.toNat)).sum := by
  rw [Batteries.RBMap.foldl_eq_foldl_toList]
  generalize acc.storage.toList = L
  clear acc
  suffices h : ∀ (init : ℕ),
      L.foldl (fun init p => init + p.2.toNat) init
        = init + (L.map (fun p => p.2.toNat)).sum by
    simpa using h 0
  intro init
  induction L generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    ring

/-- If `σ.find? C = some acc` and `acc.storage.find? slot = some oldVal`,
then `oldVal.toNat ≤ storageSum σ C`. Mirror of `balance_toNat_le_totalETH`
for the storage map. -/
theorem storageSum_old_le
    (σ : AccountMap .EVM) (C : AccountAddress) (slot oldVal : UInt256)
    (h : ((σ.find? C).map (·.storage)).bind (·.find? slot) = some oldVal) :
    oldVal.toNat ≤ storageSum σ C := by
  -- Decompose h into σ.find? C = some acc and acc.storage.find? slot = some oldVal.
  cases hσ : σ.find? C with
  | none =>
    rw [hσ] at h
    simp only [Option.map_none, Option.bind_none] at h
    cases h
  | some acc =>
    rw [hσ] at h
    simp only [Option.map_some] at h
    -- h : (acc.storage).find? slot |>.bind … = some oldVal but already at the
    -- `bind` level via Option.some_bind: bind some f = f acc.storage.
    -- Actually: (some acc.storage).bind (·.find? slot) = some oldVal
    -- ⇒ acc.storage.find? slot = some oldVal.
    have h_find : acc.storage.find? slot = some oldVal := by
      simpa using h
    -- Reduce storageSum σ C to the foldl over acc.storage.
    rw [storageSum_of_find?_some σ C acc hσ, storageSum_acc_eq_sum acc]
    -- Use find?_some_mem_toList: ∃ slot' ∈ toList with compare-eq.
    obtain ⟨slot', hMem, _⟩ := Batteries.RBMap.find?_some_mem_toList h_find
    -- oldVal.toNat ∈ mapped list of values.
    have hIn : oldVal.toNat ∈ acc.storage.toList.map (fun p => p.2.toNat) :=
      List.mem_map.mpr ⟨(slot', oldVal), hMem, rfl⟩
    exact List.le_sum_of_mem hIn

end Frame
end EvmYul
