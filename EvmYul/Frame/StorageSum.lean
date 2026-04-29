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

end Frame
end EvmYul
