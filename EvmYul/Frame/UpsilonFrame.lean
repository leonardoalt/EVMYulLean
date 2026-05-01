import EvmYul.Frame.Projection
import EvmYul.Frame.MutualFrame
import EvmYul.EVM.Semantics
import Mathlib.Data.List.Perm.Basic

/-!
# A6 — Υ's transaction-level balance frame

Statements use the real-world assumption set (T1/T2/T4/T5). The
`ΞPreservesAtC C` witness is defined in `MutualFrame.lean` and threaded
through to `Θ_balanceOf_ge` / `Λ_balanceOf_ge` / `Ξ_balanceOf_ge` via
their own hypotheses.

## Proof strategy

Υ's body is a ~150-line `do` block with a single monadic bind (the
Θ/Λ dispatch) wrapped around ~7 pure map-manipulation steps. The
balance-frame at `C` chains:

  (i)   sender debit `σ₀ := σ.insert S_T {…}`  —  frames at `C ≠ S_T`
  (ii)  Θ/Λ dispatch                           —  MutualFrame `A3 / A4`
  (iii) refund `σ_P.increaseBalance S_T _`     —  frames at `C ≠ S_T`
  (iv)  beneficiary `_.increaseBalance H.ben _` — frames at `C ≠ H.ben`
  (v)   SELFDESTRUCT sweep (`foldl erase`)      — pure RBMap lemma
  (vi)  dead-account sweep (`foldl erase`)      — pure RBMap lemma
  (vii) tstorage wipe (`RBMap.map`)             — pure RBMap lemma

The per-step frame facts are fully captured by the MutualFrame
theorems (`Θ_balanceOf_ge`, `Λ_balanceOf_ge`) and the narrow
RBMap-manipulation lemmas declared below. The plumbing that threads
these through Υ's nested `match` / `if` structure to rebuild the
`.ok (σ', …)` output requires per-arm `split`/`subst` handling for
several dozen sub-cases (the error paths of Lambda/Θ all collapse via
`Except.noConfusion`; the success paths walk the tail by case on the
`if beneficiaryFee ≠ 0`).

To keep the trusted base tight and the surface file short, we pin
this do-block plumbing into a single narrow axiom
`Υ_output_balance_ge` whose signature is **structurally bound** to
the specific `EVM.Υ fuel σ H_f H H_gen blocks tx S_T` call. This
pattern is identical to `X_preserves_balance_ge` in
`MutualFrame.lean`, which plays the analogous role for the
per-opcode step dispatch. Like that axiom, it is not a free balance
inequality over unrelated states — σ' is syntactically the output
of the pinned Υ call, and every hypothesis is either a standard
structural invariant or a bytecode-level witness that the consumer
(B2) discharges.
-/

namespace EvmYul
namespace Frame

open Batteries EvmYul.EVM

/-! ## Narrow RBMap helpers (all inline-proved) -/

/-- Inserting at `k ≠ C` preserves `balanceOf C`. -/
private theorem balanceOf_insert_ne
    (σ : AccountMap .EVM) (k C : AccountAddress) (acc : Account .EVM)
    (hk : k ≠ C) :
    balanceOf (σ.insert k acc) C = balanceOf σ C :=
  balanceOf_of_find?_eq (find?_insert_ne _ _ _ _ hk)

/-- `AccountMap.increaseBalance` at `k ≠ C` preserves `balanceOf C`.

The two-case match on `σ.find? k` both resolve to an insert at `k`,
so `find?_insert_ne` applies at `C`. -/
private theorem balanceOf_increaseBalance_ne
    (σ : AccountMap .EVM) (k C : AccountAddress) (v : UInt256) (hk : k ≠ C) :
    balanceOf (σ.increaseBalance .EVM k v) C = balanceOf σ C := by
  unfold AccountMap.increaseBalance
  split
  · exact balanceOf_insert_ne _ _ _ _ hk
  · exact balanceOf_insert_ne _ _ _ _ hk

/-- Storage-sum companion: `AccountMap.increaseBalance` at `k ≠ C`
preserves `storageSum C`. The proof is identical in structure to
`balanceOf_increaseBalance_ne` — both internal branches reduce to an
insert at `k ≠ C`, which preserves `find? C` and hence `storageSum C`. -/
private theorem storageSum_increaseBalance_ne
    (σ : AccountMap .EVM) (k C : AccountAddress) (v : UInt256) (hk : k ≠ C) :
    storageSum (σ.increaseBalance .EVM k v) C = storageSum σ C := by
  unfold AccountMap.increaseBalance
  split
  · exact storageSum_unchanged_at_other_account _ _ _ _ hk
  · exact storageSum_unchanged_at_other_account _ _ _ _ hk

/-! ## Narrow T4-extension lemmas (pure RBMap folds / maps)

Each lemma is structurally pinned to a concrete map-manipulation that
appears in Υ's tail and requires an explicit structural "does not
touch C" hypothesis. None concludes a balance inequality between
unrelated states — every conclusion is a `find?`-level equality or a
`balanceOf` preservation under the specified structural conditions on
the map operation.

We port the minimal erase-toList-filter machinery locally
(`EvmSmith.Lemmas.RBMapSum`'s `erase_toList_filter` is not reachable
from EvmYul since `EvmYul → EvmSmith` would be a cycle). All helpers
are `private` and have real proofs.
-/

namespace Internal

open Batteries RBNode

/-- Structural helper: if `∀ x ∈ L, Q x`, then `L.filter Q = L`. -/
private theorem filter_eq_self_of_all {α} {L : List α} {Q : α → Bool}
    (h : ∀ x ∈ L, Q x = true) : L.filter Q = L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ha : Q a = true := h a (by simp)
    have ih' := ih fun x hx => h x (by simp [hx])
    simp [ha, ih']

/-- `append` on RBNodes preserves the concatenation of `toList`. -/
private theorem append_toList {α : Type*} :
    ∀ (l r : RBNode α), (l.append r).toList = l.toList ++ r.toList
  | .nil, r => by simp [RBNode.append]
  | .node _ _ _ _, .nil => by simp [RBNode.append]
  | .node .red a x b, .node .red c y d => by
    have ih := append_toList b c
    unfold RBNode.append
    match hbc : b.append c with
    | .node .red b' z c' =>
      have ih' : b'.toList ++ z :: c'.toList = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [RBNode.toList_node]
      have : b'.toList ++ z :: (c'.toList ++ y :: d.toList)
           = b.toList ++ c.toList ++ y :: d.toList := by
        rw [show b'.toList ++ z :: (c'.toList ++ y :: d.toList)
              = (b'.toList ++ z :: c'.toList) ++ y :: d.toList from by
            simp [List.append_assoc], ih']
      simp [this, List.append_assoc]
    | .nil =>
      have ih' : b.toList ++ c.toList = [] := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [RBNode.toList_node]
      have hb : b.toList = [] := List.append_eq_nil_iff.mp ih' |>.1
      have hc : c.toList = [] := List.append_eq_nil_iff.mp ih' |>.2
      simp [hb, hc]
    | .node .black a' x' b' =>
      have ih' : (RBNode.node .black a' x' b').toList = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; exact this
      simp only [RBNode.toList_node]
      have : (RBNode.node .black a' x' b').toList ++ y :: d.toList
           = b.toList ++ c.toList ++ y :: d.toList := by
        rw [ih']
      simp only [RBNode.toList_node] at this
      simp [this, List.append_assoc]
  | .node .black a x b, .node .black c y d => by
    have ih := append_toList b c
    unfold RBNode.append
    match hbc : b.append c with
    | .node .red b' z c' =>
      have ih' : b'.toList ++ z :: c'.toList = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [RBNode.toList_node]
      have : b'.toList ++ z :: (c'.toList ++ y :: d.toList)
           = b.toList ++ c.toList ++ y :: d.toList := by
        rw [show b'.toList ++ z :: (c'.toList ++ y :: d.toList)
              = (b'.toList ++ z :: c'.toList) ++ y :: d.toList from by
            simp [List.append_assoc], ih']
      simp [this, List.append_assoc]
    | .nil =>
      have ih' : b.toList ++ c.toList = [] := by
        have := ih; rw [hbc] at this; simpa using this
      simp only [RBNode.toList_node, RBNode.balLeft_toList]
      have hb : b.toList = [] := List.append_eq_nil_iff.mp ih' |>.1
      have hc : c.toList = [] := List.append_eq_nil_iff.mp ih' |>.2
      simp [hb, hc]
    | .node .black a' x' b' =>
      have ih' : (RBNode.node .black a' x' b').toList = b.toList ++ c.toList := by
        have := ih; rw [hbc] at this; exact this
      simp only [RBNode.toList_node, RBNode.balLeft_toList]
      have : (RBNode.node .black a' x' b').toList ++ y :: d.toList
           = b.toList ++ c.toList ++ y :: d.toList := by
        rw [ih']
      simp only [RBNode.toList_node] at this
      simp [this, List.append_assoc]
  | .node .black a x b, .node .red c y d => by
    unfold RBNode.append
    have ih := append_toList (.node .black a x b) c
    simp [RBNode.toList_node, ih]
  | .node .red a x b, .node .black c y d => by
    unfold RBNode.append
    have ih := append_toList b (.node .black c y d)
    simp [RBNode.toList_node, ih]
termination_by l r => l.size + r.size
decreasing_by
  all_goals (simp only [RBNode.size]; omega)

section DelToListFilter

set_option linter.unusedSimpArgs false

/-- RBNode-level lemma: `del cut` removes exactly the entries with `cut = .eq`.

The `set_option linter.unusedSimpArgs false` above suppresses two
false positives at lines 218 and 232: `simp only [hcy]` performs
contextual reduction in a match-binder where `rw` fails to find the
pattern. -/
private theorem del_toList_filter
    {α : Type*} {cmp : α → α → Ordering} {cut : α → Ordering}
    [Std.TransCmp cmp] [RBNode.IsStrictCut cmp cut]
    (t : RBNode α) (ht : t.Ordered cmp) :
    (t.del cut).toList
      = t.toList.filter (fun p => decide (cut p ≠ .eq)) := by
  induction t with
  | nil => simp [RBNode.del]
  | node c a y b iha ihb =>
    obtain ⟨ay, yb, hoa, hob⟩ := ht
    have iha' := iha hoa
    have ihb' := ihb hob
    have hAll_a_lt_y : ∀ z ∈ a.toList, cmp z y = .lt := by
      intro z hz
      have hmem := RBNode.mem_toList.mp hz
      have := RBNode.All_def.1 ay z hmem
      obtain ⟨h⟩ := this
      exact h
    have hAll_y_lt_b : ∀ z ∈ b.toList, cmp y z = .lt := by
      intro z hz
      have hmem := RBNode.mem_toList.mp hz
      have := RBNode.All_def.1 yb z hmem
      obtain ⟨h⟩ := this
      exact h
    unfold RBNode.del
    simp only [RBNode.toList_node, List.filter_append, List.filter_cons]
    match hcy : cut y with
    | .lt =>
      have hbFilter : b.toList.filter (fun p => decide (cut p ≠ .eq)) = b.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .lt :=
          RBNode.IsCut.lt_trans (hAll_y_lt_b z hz) hcy
        simp [hcz]
      have hy : decide (cut y ≠ .eq) = true := by simp [hcy]
      simp only [hcy]
      split
      all_goals
        simp only [RBNode.balLeft_toList, RBNode.toList_node,
                   hbFilter, iha']
        simp
    | .gt =>
      have haFilter : a.toList.filter (fun p => decide (cut p ≠ .eq)) = a.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .gt :=
          RBNode.IsCut.gt_trans (hAll_a_lt_y z hz) hcy
        simp [hcz]
      have hy : decide (cut y ≠ .eq) = true := by simp [hcy]
      simp only [hcy]
      split
      all_goals
        simp only [RBNode.balRight_toList, RBNode.toList_node,
                   haFilter, ihb']
        simp
    | .eq =>
      have haFilter : a.toList.filter (fun p => decide (cut p ≠ .eq)) = a.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .gt := by
          have hE := RBNode.IsStrictCut.exact (cmp := cmp) (y := z) hcy
          have hzy : cmp z y = .lt := hAll_a_lt_y z hz
          have hyz : cmp y z = .gt := Std.OrientedCmp.gt_iff_lt.mpr hzy
          rw [hyz] at hE; exact hE.symm
        simp [hcz]
      have hbFilter : b.toList.filter (fun p => decide (cut p ≠ .eq)) = b.toList := by
        apply filter_eq_self_of_all
        intro z hz
        have hcz : cut z = .lt := by
          have hE := RBNode.IsStrictCut.exact (cmp := cmp) (y := z) hcy
          have hyz : cmp y z = .lt := hAll_y_lt_b z hz
          rw [hyz] at hE; exact hE.symm
        simp [hcz]
      have hy : decide (cut y ≠ .eq) = false := by simp [hcy]
      simp only [append_toList, haFilter, hbFilter]
      simp

end DelToListFilter

/-- RBNode erase ↔ toList-filter. -/
private theorem erase_toList_filter
    {α : Type*} {cmp : α → α → Ordering} {cut : α → Ordering}
    [Std.TransCmp cmp] [RBNode.IsStrictCut cmp cut]
    (t : RBNode α) (ht : t.Ordered cmp) :
    (t.erase cut).toList
      = t.toList.filter (fun p => decide (cut p ≠ .eq)) := by
  show (t.del cut).setBlack.toList
      = t.toList.filter (fun p => decide (cut p ≠ .eq))
  rw [RBNode.setBlack_toList]
  exact del_toList_filter t ht

/-- AccountMap-level erase filter. -/
private theorem am_erase_toList_filter
    (σ : AccountMap .EVM) (k : AccountAddress) :
    (σ.erase k).toList
      = σ.toList.filter (fun p => decide (compare k p.1 ≠ .eq)) := by
  have ho : σ.1.Ordered (Ordering.byKey Prod.fst compare) := σ.2.out.1
  exact erase_toList_filter
    (cmp := Ordering.byKey Prod.fst compare)
    (cut := fun p => compare k p.1) σ.1 ho

/-- Erasing at `k ≠ C` leaves `σ.find? C` unchanged. -/
private theorem find?_erase_ne_am
    (σ : AccountMap .EVM) (k C : AccountAddress) (hne : k ≠ C) :
    (σ.erase k).find? C = σ.find? C := by
  unfold RBMap.find?
  congr 1
  ext y
  rw [RBMap.findEntry?_some, RBMap.findEntry?_some]
  have hfilter : y ∈ (σ.erase k).toList ↔
      y ∈ σ.toList ∧ compare k y.1 ≠ .eq := by
    rw [am_erase_toList_filter]
    simp [List.mem_filter]
  constructor
  · rintro ⟨hMem, hEq⟩
    rw [hfilter] at hMem
    exact ⟨hMem.1, hEq⟩
  · rintro ⟨hMem, hEq⟩
    refine ⟨?_, hEq⟩
    rw [hfilter]
    refine ⟨hMem, ?_⟩
    have hCy : C = y.1 := Std.LawfulEqCmp.compare_eq_iff_eq.mp hEq
    intro hky
    apply hne
    have hky' : k = y.1 := Std.LawfulEqCmp.compare_eq_iff_eq.mp hky
    rw [hky', hCy]

/-- Fold-erase over a list of addresses, none equal to `C`: preserves `find? C`. -/
private theorem find?_erase_fold_ne
    (σ : AccountMap .EVM) (addrs : List AccountAddress)
    (C : AccountAddress) (hCNotIn : ∀ a ∈ addrs, a ≠ C) :
    (addrs.foldl RBMap.erase σ).find? C = σ.find? C := by
  induction addrs generalizing σ with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl_cons]
    rw [ih (σ.erase a) (by intro x hx; exact hCNotIn x (List.mem_cons_of_mem _ hx))]
    exact find?_erase_ne_am σ a C (hCNotIn a (by simp))

/-! ### tstorage-wipe helpers -/

/-- `TransCmp` instance for the pair-level key comparator (needed by
`cmpLT_iff` when destructuring `toList_sorted` output). -/
private instance transCmp_pair :
    Std.TransCmp (fun (x y : AccountAddress × Account .EVM) => compare x.1 y.1) :=
  inferInstanceAs (Std.TransCmp (Ordering.byKey Prod.fst compare))

/-- Generic foldl-insert preserves `find? C` when no visited pair's key
compare-equals C. The insert function is allowed to transform each
pair into a new key-value pair with an arbitrary value, as long as the
key in the recorded `ins` function applies `p.1` (the original key).
We parameterize over a general `ins : AccountMap → (AccountAddress × Account .EVM) → AccountMap`
of the shape `fun m p => m.insert p.1 (F p)` for some `F`. -/
private theorem find?_foldl_genericInsert_ne
    (L : List (AccountAddress × Account .EVM))
    (F : AccountAddress × Account .EVM → Account .EVM)
    (σ₀ : AccountMap .EVM) (C : AccountAddress)
    (hL : ∀ p ∈ L, compare C p.1 ≠ .eq) :
    (L.foldl (fun acc p => acc.insert p.1 (F p)) σ₀).find? C = σ₀.find? C := by
  induction L generalizing σ₀ with
  | nil => rfl
  | cons p L ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q hq => hL q (List.mem_cons_of_mem _ hq))]
    have hp_ne : compare C p.1 ≠ .eq := hL p (by simp)
    exact Batteries.RBMap.find?_insert_of_ne σ₀ hp_ne

/-- The main tstorage-wipe balance lemma. -/
private theorem balanceOf_tstorage_wipe_eq_aux
    (σ : AccountMap .EVM) (C : AccountAddress) :
    balanceOf
      (σ.map fun (addr, acc) => (addr, { acc with tstorage := RBMap.empty })) C
      = balanceOf σ C := by
  -- Step 1: unfold `.map` to a foldl-insert over σ.toList.
  have hMapEq :
      (σ.map fun (addr, acc) => (addr, { acc with tstorage := (RBMap.empty : Storage) }))
        = σ.toList.foldl
            (fun m p => m.insert p.1 { p.2 with tstorage := (RBMap.empty : Storage) })
            (∅ : AccountMap .EVM) := by
    show Batteries.RBSet.map σ _ = _
    unfold Batteries.RBSet.map
    rw [Batteries.RBSet.foldl_eq_foldl_toList]
    rfl
  rw [hMapEq]
  -- Step 2: reduce both sides via the find? characterization.
  -- We show: (mapped).find? C = (σ.find? C).map (fun a => {a with tstorage := ∅})
  -- Then balanceOf is preserved because `.balance` is preserved.
  suffices h : (σ.toList.foldl
      (fun m p => m.insert p.1 { p.2 with tstorage := (RBMap.empty : Storage) })
      (∅ : AccountMap .EVM)).find? C
    = (σ.find? C).map (fun a => { a with tstorage := (RBMap.empty : Storage) }) by
    unfold balanceOf
    rw [h]
    rcases σ.find? C with _ | a
    · rfl
    · rfl
  -- Now prove the `find?` equality. Case on `σ.find? C`.
  rcases hf : σ.find? C with _ | acc
  · -- none: the foldl result has find? C = none.
    have h_ne : ∀ p ∈ σ.toList, compare C p.1 ≠ .eq := by
      intro p hp heq
      have : σ.findEntry? C = some p := Batteries.RBMap.findEntry?_some.mpr ⟨hp, heq⟩
      have h2 : σ.find? C = some p.2 := by
        show (σ.findEntry? C).map Prod.snd = some p.2
        rw [this]; rfl
      rw [hf] at h2; cases h2
    rw [find?_foldl_genericInsert_ne σ.toList
      (F := fun p => { p.2 with tstorage := (RBMap.empty : Storage) })
      ∅ C h_ne]
    -- (∅ : AccountMap .EVM).find? C = none
    rfl
  · -- some acc: the foldl result has find? C = some {acc with tstorage := ∅}.
    -- Find the matching pair in σ.toList.
    obtain ⟨a', haMem, haEq⟩ := Batteries.RBMap.find?_some_mem_toList hf
    -- haMem : (a', acc) ∈ σ.toList
    -- haEq : compare C a' = .eq
    -- Decompose σ.toList = L ++ (a', acc) :: R.
    obtain ⟨L, R, hSplit⟩ := List.append_of_mem haMem
    -- Now: the foldl over L++[(a',acc)]++R equals foldl over R on the
    -- (foldl over L then insert (a', acc)) map. The final find? C is
    -- determined by whichever matching pair comes *last*. Since Nodup
    -- and all other matching keys = (a', acc) (uniquely), there's only
    -- one matching pair, namely (a', acc).
    -- All elements of L ∪ R have key ≠ C (else they'd be (a', acc) via
    -- mem_toList_unique, but then they'd be duplicated in σ.toList,
    -- contradicting Nodup).
    have hNodup : σ.toList.Nodup := by
      have hp := Batteries.RBMap.toList_sorted (t := σ)
      refine hp.imp ?_
      intro x y hxy hxy_eq
      obtain ⟨hxy'⟩ := hxy
      -- hxy' : compare x.1 y.1 = .lt but x = y
      have : compare x.1 x.1 = .lt := hxy_eq ▸ hxy'
      have hrefl : compare x.1 x.1 = .eq := Std.ReflCmp.compare_self
      rw [hrefl] at this; cases this
    have hLR_ne : ∀ p ∈ L ++ R, compare C p.1 ≠ .eq := by
      intro p hp hEq
      have hpInσ : p ∈ σ.toList := by
        rw [hSplit]
        rcases List.mem_append.mp hp with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right L (List.mem_cons_of_mem _ h)
      -- compare C p.1 = .eq and compare C a' = .eq ⟹ compare p.1 a' = .eq
      have h2 : compare p.1 a' = .eq := by
        have hpEq : compare p.1 C = .eq := Std.OrientedCmp.eq_comm.mp hEq
        exact Std.TransCmp.eq_trans hpEq haEq
      have hpq : p = (a', acc) :=
        Batteries.RBMap.mem_toList_unique hpInσ haMem h2
      -- (a', acc) ∉ L ++ R by Nodup.
      rw [hSplit] at hNodup
      rw [List.nodup_append] at hNodup
      obtain ⟨hndL, hndR, hdisj⟩ := hNodup
      rw [List.nodup_cons] at hndR
      rcases List.mem_append.mp hp with hpL | hpR
      · -- p ∈ L; but p = (a', acc), and (a', acc) ∈ (a', acc) :: R.
        have hMemL : (a', acc) ∈ L := hpq ▸ hpL
        exact hdisj (a', acc) hMemL (a', acc) (by simp) rfl
      · -- p ∈ R; but (a', acc) ∉ R by Nodup of (a', acc) :: R.
        have hMemR : (a', acc) ∈ R := hpq ▸ hpR
        exact hndR.1 hMemR
    -- Now reduce the foldl.
    rw [hSplit]
    -- foldl over L ++ (a', acc) :: R = foldl over L, then insert, then foldl over R.
    rw [List.foldl_append, List.foldl_cons]
    -- Let σ₁ = foldl over L; σ₂ = σ₁.insert a' {acc with tstorage := ∅}.
    -- The rest of the foldl is over R. Since all keys in R differ from C:
    have hR_ne : ∀ p ∈ R, compare C p.1 ≠ .eq := fun p hp =>
      hLR_ne p (List.mem_append_right _ hp)
    rw [find?_foldl_genericInsert_ne R _ _ C hR_ne]
    -- Now: (σ₁.insert a' {acc with tstorage := ∅}).find? C = some {acc with tstorage := ∅}
    exact Batteries.RBMap.find?_insert_of_eq _ haEq

/-- Storage-sum companion of `balanceOf_tstorage_wipe_eq_aux`:
the tstorage-wipe map preserves `storageSum C`. The wipe replaces
`tstorage` with `∅` and leaves `.storage` untouched, so the foldl-sum
over `.storage` is unchanged at every account. -/
private theorem storageSum_tstorage_wipe_eq_aux
    (σ : AccountMap .EVM) (C : AccountAddress) :
    storageSum
      (σ.map fun (addr, acc) => (addr, { acc with tstorage := RBMap.empty })) C
      = storageSum σ C := by
  -- Same machinery as `balanceOf_tstorage_wipe_eq_aux`, but reduce to
  -- `storageSum`'s find?+foldl-over-storage shape.
  have hMapEq :
      (σ.map fun (addr, acc) => (addr, { acc with tstorage := (RBMap.empty : Storage) }))
        = σ.toList.foldl
            (fun m p => m.insert p.1 { p.2 with tstorage := (RBMap.empty : Storage) })
            (∅ : AccountMap .EVM) := by
    show Batteries.RBSet.map σ _ = _
    unfold Batteries.RBSet.map
    rw [Batteries.RBSet.foldl_eq_foldl_toList]
    rfl
  rw [hMapEq]
  -- It suffices to show find?-equality up to the (·.storage) projection.
  suffices h : (σ.toList.foldl
      (fun m p => m.insert p.1 { p.2 with tstorage := (RBMap.empty : Storage) })
      (∅ : AccountMap .EVM)).find? C
    = (σ.find? C).map
        (fun (a : Account .EVM) =>
          ({ a with tstorage := (RBMap.empty : Storage) } : Account .EVM)) by
    unfold storageSum
    rw [h]
    rcases σ.find? C with _ | a
    · rfl
    · rfl
  rcases hf : σ.find? C with _ | acc
  · -- none: foldl result has find? C = none.
    have h_ne : ∀ p ∈ σ.toList, compare C p.1 ≠ .eq := by
      intro p hp heq
      have : σ.findEntry? C = some p := Batteries.RBMap.findEntry?_some.mpr ⟨hp, heq⟩
      have h2 : σ.find? C = some p.2 := by
        show (σ.findEntry? C).map Prod.snd = some p.2
        rw [this]; rfl
      rw [hf] at h2; cases h2
    rw [find?_foldl_genericInsert_ne σ.toList
      (F := fun p => { p.2 with tstorage := (RBMap.empty : Storage) })
      ∅ C h_ne]
    rfl
  · -- some acc: foldl result has find? C = some {acc with tstorage := ∅}.
    obtain ⟨a', haMem, haEq⟩ := Batteries.RBMap.find?_some_mem_toList hf
    obtain ⟨L, R, hSplit⟩ := List.append_of_mem haMem
    have hNodup : σ.toList.Nodup := by
      have hp := Batteries.RBMap.toList_sorted (t := σ)
      refine hp.imp ?_
      intro x y hxy hxy_eq
      obtain ⟨hxy'⟩ := hxy
      have : compare x.1 x.1 = .lt := hxy_eq ▸ hxy'
      have hrefl : compare x.1 x.1 = .eq := Std.ReflCmp.compare_self
      rw [hrefl] at this; cases this
    have hLR_ne : ∀ p ∈ L ++ R, compare C p.1 ≠ .eq := by
      intro p hp hEq
      have hpInσ : p ∈ σ.toList := by
        rw [hSplit]
        rcases List.mem_append.mp hp with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right L (List.mem_cons_of_mem _ h)
      have h2 : compare p.1 a' = .eq := by
        have hpEq : compare p.1 C = .eq := Std.OrientedCmp.eq_comm.mp hEq
        exact Std.TransCmp.eq_trans hpEq haEq
      have hpq : p = (a', acc) :=
        Batteries.RBMap.mem_toList_unique hpInσ haMem h2
      rw [hSplit] at hNodup
      rw [List.nodup_append] at hNodup
      obtain ⟨hndL, hndR, hdisj⟩ := hNodup
      rw [List.nodup_cons] at hndR
      rcases List.mem_append.mp hp with hpL | hpR
      · have hMemL : (a', acc) ∈ L := hpq ▸ hpL
        exact hdisj (a', acc) hMemL (a', acc) (by simp) rfl
      · have hMemR : (a', acc) ∈ R := hpq ▸ hpR
        exact hndR.1 hMemR
    rw [hSplit]
    rw [List.foldl_append, List.foldl_cons]
    have hR_ne : ∀ p ∈ R, compare C p.1 ≠ .eq := fun p hp =>
      hLR_ne p (List.mem_append_right _ hp)
    rw [find?_foldl_genericInsert_ne R _ _ C hR_ne]
    -- The insert at `a'` with key compare-eq `C` lands at `find? C`.
    rw [Batteries.RBMap.find?_insert_of_eq _ haEq]
    -- Goal: some {acc with tstorage := ∅}.storage.map _ = some acc.storage.map _
    -- Both are `acc.storage` because tstorage update doesn't touch storage.
    rfl

end Internal

/-- Foldl of `erase` over an `RBNode AccountAddress` whose elements
exclude `C` preserves `find? C`.

Pinned structurally to the `RBNode.foldl RBMap.erase` shape that
arises from `A.selfDestructSet.1.foldl RBMap.erase` in Υ's step (87). -/
theorem find?_erase_rbnode_foldl_ne
    (σ : AccountMap .EVM) (n : Batteries.RBNode AccountAddress)
    (C : AccountAddress)
    (_hC : ∀ k ∈ n.toList, k ≠ C) :
    (n.foldl Batteries.RBMap.erase σ).find? C = σ.find? C := by
  rw [Batteries.RBNode.foldl_eq_foldl_toList]
  exact Internal.find?_erase_fold_ne σ n.toList C _hC

/-- Foldl of `erase` over an `RBSet` whose elements exclude `C`
preserves `find? C`.

Pinned structurally to the `RBSet.foldl RBMap.erase` shape that
arises from `deadAccounts.foldl RBMap.erase` in Υ's step (88). -/
theorem find?_erase_rbset_foldl_ne
    (σ : AccountMap .EVM) (s : Batteries.RBSet AccountAddress compare)
    (C : AccountAddress) (_hC : ∀ k ∈ s, k ≠ C) :
    (s.foldl Batteries.RBMap.erase σ).find? C = σ.find? C := by
  -- `RBSet.foldl f init s = s.1.foldl f init` by definition
  show (s.1.foldl Batteries.RBMap.erase σ).find? C = σ.find? C
  apply find?_erase_rbnode_foldl_ne
  intro k hk
  apply _hC
  -- `k ∈ s` ↔ `MemP (compare k) s`; we have `k ∈ s.1.toList = s.toList`.
  -- `s ∋ k` by definition uses `MemP`. The membership notation for an
  -- RBSet is `Mem`, and `k ∈ s.1.toList` gives `k` is literally in the
  -- underlying node's list. We need `k ∈ s`.
  have hmem : k ∈ s.1 := Batteries.RBNode.mem_toList.mp hk
  -- `k ∈ s` is `k ∈ s.1` by the RBSet Membership instance, but the
  -- hypothesis shape is `k ∈ s` which unfolds through MemP via compare.
  -- The standard reduction: `k ∈ s.1` gives EMem k s.1, and membership
  -- in the RBSet uses the MemP (cmp k) form. Convert via `mem_def`.
  -- Actually the RBSet membership instance uses `Any (cmp x · = .eq)`
  -- so we need to translate from EMem to MemP.
  exact Batteries.RBSet.mem_of_mem_toList hk

/-- `RBMap.map` rewriting only the `tstorage` field of each value
preserves `balanceOf` at every address.

Pinned structurally to the `σ.map λ (addr, acc) => (addr, { acc with
tstorage := .empty })` shape in Υ's tail. -/
theorem balanceOf_tstorage_wipe_eq
    (σ : AccountMap .EVM) (C : AccountAddress) :
    balanceOf
      (σ.map fun (addr, acc) => (addr, { acc with tstorage := RBMap.empty })) C
      = balanceOf σ C := by
  exact Internal.balanceOf_tstorage_wipe_eq_aux σ C

/-- Companion of `balanceOf_tstorage_wipe_eq` for `storageSum`.

The tstorage-wipe `σ.map (·.tstorage := ∅)` preserves persistent
`storage` at every account, hence `storageSum` is unchanged. This is
the §1.3 storage-side lemma used by `Υ_tail_storageSum_eq`. -/
theorem storageSum_tstorage_wipe_eq
    (σ : AccountMap .EVM) (C : AccountAddress) :
    storageSum
      (σ.map fun (addr, acc) => (addr, { acc with tstorage := RBMap.empty })) C
      = storageSum σ C := by
  exact Internal.storageSum_tstorage_wipe_eq_aux σ C

/-! ## Υ output balance frame (theorem, proved by tail + factorisation)

`Υ_output_balance_ge` is a theorem whose proof chains:

  (i)   tail transformation (SD sweep + dead sweep + tstorage wipe +
        `increaseBalance S_T` + conditional `increaseBalance H.ben`)
        — closed by `Υ_tail_balanceOf_ge`, using:
          * `balanceOf_increaseBalance_ne` at `S_T ≠ C` and `H.ben ≠ C`,
          * `find?_erase_rbnode_foldl_ne` / `find?_erase_rbset_foldl_ne`
            with hypothesis `ΥTailInvariant C`,
          * `balanceOf_tstorage_wipe_eq`.

  (ii)  body factorisation: `Υ`'s output has the form
        `Υ_tail_state σ_P g' A …` where `(σ_P, g', A, _)` is the
        Θ/Λ-dispatch result on the debited `σ₀`. The σ₀ → σ_P
        monotonicity plus the output shape are packaged in
        `ΥBodyFactors σ …`, discharged by the caller using
        `Θ_balanceOf_ge` / `Λ_balanceOf_ge`.

Both `ΥTailInvariant C` and `ΥBodyFactors σ …` are stated as
hypothesis predicates on the theorem. Clients of `Υ_balanceOf_ge`
(e.g. `register_balance_mono`) discharge them per-contract. -/

/-! ## T4 — Transaction validity at Υ entry (real-world axiom)

Consensus-layer transaction acceptance enforces:
  (a) Sender account `S_T` exists in σ.
  (b) Sender balance covers the upfront cost
      (`gasLimit * gasPrice + blobFee + tx.value`).

Both are discharged by node-level validation
(INSUFFICIENT_ACCOUNT_FUNDS and signature/nonce checks) **before** Υ
is invoked. Neither is a property derivable from the EVM semantics
alone — they're preconditions on Υ's input.

We package (a) and (b) as a single `TxValid` predicate and axiomatize
that every Υ call satisfies it. This matches the Yellow Paper's
`T ∈ 𝕋` pre-condition (Section 6.2). -/

/-- The price `p` used in Υ's body (UInt256). -/
def Υ_p (H_f : ℕ) (tx : Transaction) : UInt256 :=
  match tx with
  | .legacy t | .access t => t.gasPrice
  | .dynamic _ | .blob _ =>
    (match tx with
     | .legacy t | .access t => t.gasPrice - .ofNat H_f
     | .dynamic t | .blob t =>
       min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f))
    + .ofNat H_f

/-- The new sender account in σ₀ (post-debit). -/
def Υ_newSender (σ : AccountMap .EVM) (H_f : ℕ) (S_T : AccountAddress)
    (H : BlockHeader) (tx : Transaction) : Account .EVM :=
  { (σ.find? S_T).get! with
      balance := (σ.find? S_T).get!.balance
                 - tx.base.gasLimit * Υ_p H_f tx
                 - .ofNat (calcBlobFee H tx)
      nonce := (σ.find? S_T).get!.nonce + ⟨1⟩ }

/-- The post-debit checkpoint state σ₀. -/
def Υ_σ₀ (σ : AccountMap .EVM) (H_f : ℕ) (S_T : AccountAddress)
    (H : BlockHeader) (tx : Transaction) : AccountMap .EVM :=
  σ.insert S_T (Υ_newSender σ H_f S_T H tx)

/-- Predicate: `σ, tx, H, H_f` is a valid Υ input.

In addition to the standard upfront-cost bound, we package three
structural consequences that node-level validation also discharges:

  * `newSenderBal ≤ senderBal`: the post-debit sender balance does
    not exceed the original (no underflow).
  * `value ≤ newSenderBal`: value is fundable from the post-debit
    sender balance.
  * For every recipient `r`, `recipBal + value < UInt256.size`.

These would all follow from the upfront-cost bound + `StateWF σ`
+ the absence of UInt256 wrap, but proving them individually requires
several hundred lines of UInt256 arithmetic. Since `tx_validity` is
already a real-world axiom, we package the structural consequences
together: real-world validation does enforce all three (e.g.,
INSUFFICIENT_ACCOUNT_FUNDS implicitly verifies no-wrap). -/
def TxValid (σ : AccountMap .EVM) (S_T : AccountAddress)
    (tx : Transaction) (H : BlockHeader) (H_f : ℕ) : Prop :=
  ∃ acc, σ.find? S_T = some acc ∧
    -- upfront cost: gasLimit·gasPrice + blobFee + tx.value ≤ sender.balance
    (tx.base.gasLimit.toNat *
       (match tx with
        | .legacy t => t.gasPrice.toNat
        | .access t => t.gasPrice.toNat
        | .dynamic t => (min t.maxPriorityFeePerGas
                             (t.maxFeePerGas - .ofNat H_f)).toNat + H_f
        | .blob t    => (min t.maxPriorityFeePerGas
                             (t.maxFeePerGas - .ofNat H_f)).toNat + H_f)
     + calcBlobFee H tx
     + tx.base.value.toNat) ≤ acc.balance.toNat
    -- newSender.balance ≤ acc.balance (no underflow in σ₀'s sender balance)
    ∧ (Υ_newSender σ H_f S_T H tx).balance.toNat ≤ acc.balance.toNat
    -- value ≤ newSender.balance (funds_strict at σ₀)
    ∧ tx.base.value.toNat ≤ (Υ_newSender σ H_f S_T H tx).balance.toNat
    -- For every recipient r, recipient-balance + value < UInt256.size
    ∧ (∀ r accR, (Υ_σ₀ σ H_f S_T H tx).find? r = some accR →
         accR.balance.toNat + tx.base.value.toNat < UInt256.size)

/-! **T4** note: `TxValid` was previously discharged by a global axiom
`tx_validity`. We removed the axiom and now require consumers (e.g.
`register_balance_mono`) to take `TxValid` as an explicit hypothesis.
Real-world Υ invocations satisfy this via node-level validation. -/

/-! ### `RBSet.filter` membership helper

`s.filter p` is implemented as a `foldl` that conditionally inserts
each element. So `k ∈ s.filter p` implies `p k = true`. We need this
to discharge the gated dead-filter clause in `ΥTailInvariant` for
Register. -/

namespace InternalFilter

open Batteries

/-- A `foldl` that conditionally inserts an element of the input list
into an `acc : RBSet`: any element of the foldl result is either in
the initial accumulator or its predicate is `true`. -/
private theorem mem_foldl_cond_insert
    {α} {cmp : α → α → Ordering} [Std.OrientedCmp cmp] [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp]
    (L : List α) (p : α → Bool) (acc₀ : RBSet α cmp) (k : α)
    (hk : k ∈ L.foldl
      (fun acc a => bif p a then acc.insert a else acc) acc₀) :
    k ∈ acc₀ ∨ p k = true := by
  induction L generalizing acc₀ with
  | nil =>
    simp at hk
    exact Or.inl hk
  | cons a L ih =>
    simp only [List.foldl_cons] at hk
    have hRec := ih _ hk
    rcases hRec with hMem | hPk
    · by_cases hpa : p a = true
      · simp [hpa] at hMem
        rcases Batteries.RBSet.mem_insert.mp hMem with hkAcc | hkEq
        · exact Or.inl hkAcc
        · -- hkEq : cmp a k = .eq, so a = k by LawfulEqCmp.
          have hka : k = a := by
            have hkaSym : cmp k a = .eq := Std.OrientedCmp.eq_comm.mpr hkEq
            exact Std.LawfulEqCmp.compare_eq_iff_eq.mp hkaSym
          rw [hka]; exact Or.inr hpa
      · simp [hpa] at hMem
        exact Or.inl hMem
    · exact Or.inr hPk

end InternalFilter

/-- If `k ∈ s.filter p`, then `p k = true`. -/
theorem mem_filter_pred {α} {cmp : α → α → Ordering}
    [Std.OrientedCmp cmp] [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (s : Batteries.RBSet α cmp) (p : α → Bool) (k : α)
    (hk : k ∈ s.filter p) : p k = true := by
  unfold Batteries.RBSet.filter at hk
  rw [Batteries.RBSet.foldl_eq_foldl_toList] at hk
  rcases InternalFilter.mem_foldl_cond_insert s.toList p ∅ k hk with h | h
  · exfalso
    -- Membership in ∅ is impossible.
    have hEmpty : ¬ k ∈ (∅ : Batteries.RBSet α cmp) := by
      intro hMem
      have : (∅ : Batteries.RBSet α cmp).1.MemP (cmp k) := hMem
      cases this
    exact hEmpty h
  · exact h

/-- Post-dispatch structural predicate: structurally bound to the
substate `A` that `EVM.Υ`'s `.ok` output produces. States that:

  * `C` is *not* in `A.selfDestructSet` (so the SD-erase sweep at Υ's
    step 87 skips `C`); and
  * for any post-fee state `σ_F` at which `C` is *not* dead
    (`State.dead σ_F C = false`), none of the accounts in the
    dead-filtered `A.touchedAccounts` equal `C` (so the dead-erase
    sweep at step 88 skips `C`).

The dead-filter clause's hypothesis `State.dead σ_F C = false` is
satisfied at the concrete `σStar'` used in Υ's tail because `C`'s
account in `σ_P` has Register's bytecode (non-empty code), and the
two `increaseBalance` updates that produce `σStar'` from `σ_P` only
touch `S_T` and `H.beneficiary`, both `≠ C`.

The predicate is structurally pinned to the **specific** `A` produced
by Υ — no longer vacuously universally quantified over arbitrary
`A`. Clients (e.g. `register_balance_mono`) discharge it via
per-contract reasoning over Υ's call tree. -/
def ΥTailInvariant (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) : Prop :=
  match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | .ok (_, A, _, _) =>
      (∀ k ∈ A.selfDestructSet.1.toList, k ≠ C) ∧
      (∀ σ_F : AccountMap .EVM, State.dead σ_F C = false →
        ∀ k ∈ A.touchedAccounts.filter (State.dead σ_F ·), k ≠ C)
  | .error _ => True

/-- The pure tail transformation of Υ, from the Θ/Λ-dispatch result
`(σ_P, g', A, _)` to the final output state. -/
def Υ_tail_state
    (σ_P : AccountMap .EVM) (g' : UInt256) (A : Substate)
    (H : BlockHeader) (H_f : ℕ) (tx : Transaction)
    (S_T : AccountAddress) : AccountMap .EVM :=
  let f :=
    match tx with
      | .legacy t | .access t => t.gasPrice - .ofNat H_f
      | .dynamic t | .blob t =>
            min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)
  let p :=
    match tx with
      | .legacy t | .access t => t.gasPrice
      | .dynamic _ | .blob _ => f + .ofNat H_f
  let gStar := g' + min ((tx.base.gasLimit - g') / ⟨5⟩) A.refundBalance
  let σStar := σ_P.increaseBalance .EVM S_T (gStar * p)
  let beneficiaryFee := (tx.base.gasLimit - gStar) * f
  let σStar' :=
    if beneficiaryFee != ⟨0⟩ then
      σStar.increaseBalance .EVM H.beneficiary beneficiaryFee
    else σStar
  let σ'0 := A.selfDestructSet.1.foldl Batteries.RBMap.erase σStar'
  let deadAccounts := A.touchedAccounts.filter (State.dead σStar' ·)
  let σ'1 := deadAccounts.foldl Batteries.RBMap.erase σ'0
  σ'1.map (fun (addr, acc) => (addr, { acc with tstorage := RBMap.empty }))

/-- A generic helper: for any `σ_F` (fee-state) and any `σ_X` with
`balanceOf σ_X C = balanceOf σ_F C`, as long as the SD-set and dead
filter at `σ_F` exclude C, the tail-transformed state has the same
balance at C. -/
private theorem balanceOf_tail_generic
    (σ_F : AccountMap .EVM) (A : Substate) (C : AccountAddress)
    (hSD_ne : ∀ k ∈ A.selfDestructSet.1.toList, k ≠ C)
    (hDead_ne : ∀ k ∈ A.touchedAccounts.filter (State.dead σ_F ·), k ≠ C) :
    balanceOf
      ((A.touchedAccounts.filter (State.dead σ_F ·)).foldl Batteries.RBMap.erase
        (A.selfDestructSet.1.foldl Batteries.RBMap.erase σ_F)
        |>.map (fun (addr, acc) => (addr, { acc with tstorage := RBMap.empty }))) C
      = balanceOf σ_F C := by
  rw [balanceOf_tstorage_wipe_eq]
  rw [balanceOf_of_find?_eq (find?_erase_rbset_foldl_ne _ _ C hDead_ne)]
  rw [balanceOf_of_find?_eq (find?_erase_rbnode_foldl_ne _ _ C hSD_ne)]

/-- Fully-generic tail formula: any σ_F satisfying the SD/dead
invariants at C preserves balanceOf through the sweep+wipe chain. -/
private theorem Υ_tail_over_σF
    (σ_F : AccountMap .EVM) (A : Substate) (C : AccountAddress)
    (hSD_ne : ∀ k ∈ A.selfDestructSet.1.toList, k ≠ C)
    (hDead_ne : ∀ k ∈ A.touchedAccounts.filter (State.dead σ_F ·), k ≠ C) :
    balanceOf
      ((A.touchedAccounts.filter (State.dead σ_F ·)).foldl Batteries.RBMap.erase
        (A.selfDestructSet.1.foldl Batteries.RBMap.erase σ_F)
        |>.map (fun (addr, acc) => (addr, { acc with tstorage := RBMap.empty }))) C
      = balanceOf σ_F C := balanceOf_tail_generic σ_F A C hSD_ne hDead_ne

/-- `State.dead` is preserved by `increaseBalance` at a different key. -/
private theorem dead_increaseBalance_ne
    (σ : AccountMap .EVM) (k C : AccountAddress) (v : UInt256) (hk : k ≠ C) :
    State.dead (σ.increaseBalance .EVM k v) C = State.dead σ C := by
  unfold State.dead AccountMap.increaseBalance
  split
  all_goals rw [find?_insert_ne _ _ _ _ hk]

/-- The pure tail of Υ preserves `balanceOf C` under: `C ≠ S_T`, `C ≠
H.beneficiary`, the SD-set excludes `C`, the dead-filter at any σ_F
with `dead σ_F C = false` excludes `C`, and `dead σ_P C = false`
(suffices for the dead-filter clause to apply at the concrete σStar'). -/
private theorem Υ_tail_balanceOf_ge
    (σ_P : AccountMap .EVM) (g' : UInt256) (A : Substate)
    (H : BlockHeader) (H_f : ℕ) (tx : Transaction)
    (S_T C : AccountAddress)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (hSD : ∀ k ∈ A.selfDestructSet.1.toList, k ≠ C)
    (hDeadGated :
       ∀ σ_F : AccountMap .EVM, State.dead σ_F C = false →
         ∀ k ∈ A.touchedAccounts.filter (State.dead σ_F ·), k ≠ C)
    (hDead_σP : State.dead σ_P C = false) :
    balanceOf (Υ_tail_state σ_P g' A H H_f tx S_T) C = balanceOf σ_P C := by
  unfold Υ_tail_state
  simp only
  generalize
    ((g' + min ((tx.base.gasLimit - g') / ⟨5⟩) A.refundBalance) *
      (match tx with
       | .legacy t | .access t => t.gasPrice
       | .dynamic _ | .blob _ =>
            (match tx with
             | .legacy t | .access t => t.gasPrice - .ofNat H_f
             | .dynamic t | .blob t =>
                   min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)) +
            .ofNat H_f)) = payFee
  generalize
    ((tx.base.gasLimit -
        (g' + min ((tx.base.gasLimit - g') / ⟨5⟩) A.refundBalance)) *
       (match tx with
        | .legacy t | .access t => t.gasPrice - .ofNat H_f
        | .dynamic t | .blob t =>
              min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f))) = benFee
  -- The σ_F at which the dead-filter is taken is σStar'.
  set σStar' : AccountMap .EVM :=
    if benFee != ⟨0⟩
      then (σ_P.increaseBalance .EVM S_T payFee).increaseBalance .EVM
            H.beneficiary benFee
      else σ_P.increaseBalance .EVM S_T payFee with hσStar'_def
  -- Both increaseBalance updates are at addresses ≠ C, so dead at C is
  -- preserved from σ_P.
  have hDead_σStar' : State.dead σStar' C = false := by
    rw [hσStar'_def]
    split
    · rw [dead_increaseBalance_ne _ _ _ _ hBen.symm,
          dead_increaseBalance_ne _ _ _ _ hS_T.symm]
      exact hDead_σP
    · rw [dead_increaseBalance_ne _ _ _ _ hS_T.symm]
      exact hDead_σP
  have hDead_at := hDeadGated σStar' hDead_σStar'
  rw [balanceOf_tail_generic _ A C hSD hDead_at]
  -- Now reduce the `if` at the balance level.
  show balanceOf σStar' C = balanceOf σ_P C
  rw [hσStar'_def]
  split
  · rw [balanceOf_increaseBalance_ne _ _ _ _ hBen.symm,
        balanceOf_increaseBalance_ne _ _ _ _ hS_T.symm]
  · rw [balanceOf_increaseBalance_ne _ _ _ _ hS_T.symm]

/-! ## §1.3 — Storage-sum side of Υ's tail

Mirrors the balance-side helpers above, but for `storageSum`. The
arithmetic is simpler because storageSum at `C` is **strictly
preserved** (not just monotone) by every step of the tail: the two
`increaseBalance` calls at `S_T ≠ C` and `H.beneficiary ≠ C` don't
touch persistent storage at any other account; the SD/dead foldl
erases skip `C`; and the final tstorage wipe only modifies the
`.tstorage` field, leaving `.storage` intact. -/

/-- Storage-sum analogue of `balanceOf_tail_generic`: for any σ_F
satisfying the SD/dead invariants at C, the tail-transformed state
has the same storageSum at C. -/
private theorem storageSum_tail_generic
    (σ_F : AccountMap .EVM) (A : Substate) (C : AccountAddress)
    (hSD_ne : ∀ k ∈ A.selfDestructSet.1.toList, k ≠ C)
    (hDead_ne : ∀ k ∈ A.touchedAccounts.filter (State.dead σ_F ·), k ≠ C) :
    storageSum
      ((A.touchedAccounts.filter (State.dead σ_F ·)).foldl Batteries.RBMap.erase
        (A.selfDestructSet.1.foldl Batteries.RBMap.erase σ_F)
        |>.map (fun (addr, acc) => (addr, { acc with tstorage := RBMap.empty }))) C
      = storageSum σ_F C := by
  rw [storageSum_tstorage_wipe_eq]
  rw [storageSum_of_find?_eq (find?_erase_rbset_foldl_ne _ _ C hDead_ne)]
  rw [storageSum_of_find?_eq (find?_erase_rbnode_foldl_ne _ _ C hSD_ne)]

/-- The pure tail of Υ preserves `storageSum C` under: `C ≠ S_T`, `C
≠ H.beneficiary`, the SD-set excludes `C`, and the dead-filter (at
σStar', the post-fee state) excludes `C`.

Storage-side mirror of `Υ_tail_balanceOf_ge`. The structure is
identical — same case split on `benFee != 0` for σStar' — but each
balance lemma is replaced by its storageSum companion:

* `balanceOf_increaseBalance_ne` ↦ `storageSum_increaseBalance_ne`,
* `balanceOf_tail_generic` ↦ `storageSum_tail_generic`.

Note: unlike the balance side, no `State.dead σ_P C = false`
hypothesis is needed for the conclusion itself. We do still require
the `hDeadGated` clause to apply at the concrete σStar', and that
clause is gated by `dead σStar' C = false`. To avoid burdening callers
with an additional structural fact, we accept `hDead_σP : State.dead
σ_P C = false` (same as the balance side) and use it to derive
`dead σStar' C = false` via `dead_increaseBalance_ne`. -/
private theorem Υ_tail_storageSum_eq
    (σ_P : AccountMap .EVM) (g' : UInt256) (A : Substate)
    (H : BlockHeader) (H_f : ℕ) (tx : Transaction)
    (S_T C : AccountAddress)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (hSD : ∀ k ∈ A.selfDestructSet.1.toList, k ≠ C)
    (hDeadGated :
       ∀ σ_F : AccountMap .EVM, State.dead σ_F C = false →
         ∀ k ∈ A.touchedAccounts.filter (State.dead σ_F ·), k ≠ C)
    (hDead_σP : State.dead σ_P C = false) :
    storageSum (Υ_tail_state σ_P g' A H H_f tx S_T) C = storageSum σ_P C := by
  unfold Υ_tail_state
  simp only
  generalize
    ((g' + min ((tx.base.gasLimit - g') / ⟨5⟩) A.refundBalance) *
      (match tx with
       | .legacy t | .access t => t.gasPrice
       | .dynamic _ | .blob _ =>
            (match tx with
             | .legacy t | .access t => t.gasPrice - .ofNat H_f
             | .dynamic t | .blob t =>
                   min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)) +
            .ofNat H_f)) = payFee
  generalize
    ((tx.base.gasLimit -
        (g' + min ((tx.base.gasLimit - g') / ⟨5⟩) A.refundBalance)) *
       (match tx with
        | .legacy t | .access t => t.gasPrice - .ofNat H_f
        | .dynamic t | .blob t =>
              min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f))) = benFee
  -- The σ_F at which the dead-filter is taken is σStar'.
  set σStar' : AccountMap .EVM :=
    if benFee != ⟨0⟩
      then (σ_P.increaseBalance .EVM S_T payFee).increaseBalance .EVM
            H.beneficiary benFee
      else σ_P.increaseBalance .EVM S_T payFee with hσStar'_def
  -- Both increaseBalance updates are at addresses ≠ C, so dead at C is
  -- preserved from σ_P.
  have hDead_σStar' : State.dead σStar' C = false := by
    rw [hσStar'_def]
    split
    · rw [dead_increaseBalance_ne _ _ _ _ hBen.symm,
          dead_increaseBalance_ne _ _ _ _ hS_T.symm]
      exact hDead_σP
    · rw [dead_increaseBalance_ne _ _ _ _ hS_T.symm]
      exact hDead_σP
  have hDead_at := hDeadGated σStar' hDead_σStar'
  rw [storageSum_tail_generic _ A C hSD hDead_at]
  -- Now reduce the `if` at the storageSum level.
  show storageSum σStar' C = storageSum σ_P C
  rw [hσStar'_def]
  split
  · rw [storageSum_increaseBalance_ne _ _ _ _ hBen.symm,
        storageSum_increaseBalance_ne _ _ _ _ hS_T.symm]
  · rw [storageSum_increaseBalance_ne _ _ _ _ hS_T.symm]

/-- Hypothesis form of Υ's body factorisation.

Whenever Υ returns `.ok (σ', A, z, _)`, σ' decomposes as
`Υ_tail_state σ_P g' A …` for some `(σ_P, g')` produced by the Θ/Λ
dispatch, with `balanceOf σ_P C ≥ balanceOf σ C` and `C` not dead in
σ_P (its account exists with non-empty bytecode — Register's). The
caller discharges this by direct inspection of Υ and invocation of
`Θ_balanceOf_ge` / `Λ_balanceOf_ge`, plus a code-preservation
hypothesis. -/
def ΥBodyFactors (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) : Prop :=
  match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | .ok (σ', A', _, _) =>
      ∃ σ_P g',
        σ' = Υ_tail_state σ_P g' A' H H_f tx S_T ∧
        balanceOf σ_P C ≥ balanceOf σ C ∧
        State.dead σ_P C = false
  | .error _ => True

/-- Υ's transaction-level balance frame, proved from the body
factorisation and tail-invariant hypotheses.

The tail-invariant `hTail` captures the two structural conditions
that C is not affected by the SD or dead-account sweeps; the body
factorisation `hFactor` captures the Θ/Λ dispatch monotonicity +
the pure-tail identity. Both are discharged per-contract by the
caller (e.g. `register_balance_mono`). -/
theorem Υ_output_balance_ge
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress)
    (_hWF : StateWF σ)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (_hWitness : ΞPreservesAtC C)
    (hTail : ΥTailInvariant σ fuel H_f H H_gen blocks tx S_T C)
    (hFactor : ΥBodyFactors σ fuel H_f H H_gen blocks tx S_T C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => balanceOf σ' C ≥ balanceOf σ C
    | .error _ => True := by
  unfold ΥBodyFactors at hFactor
  unfold ΥTailInvariant at hTail
  cases hΥ : EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | error e => trivial
  | ok r =>
    obtain ⟨σ', A, z, gUsed⟩ := r
    rw [hΥ] at hFactor
    rw [hΥ] at hTail
    obtain ⟨σ_P, g', hEq, hP_ge, hDead_σP⟩ := hFactor
    obtain ⟨hSD, hDeadGated⟩ := hTail
    show balanceOf σ' C ≥ balanceOf σ C
    rw [hEq]
    rw [Υ_tail_balanceOf_ge σ_P g' A H H_f tx S_T C hS_T hBen
          hSD hDeadGated hDead_σP]
    exact hP_ge

/-! ## The closing theorem -/

/-- Υ's balance frame — monotone at `C` under the real-world
structural hypothesis set.

Projection of `Υ_output_balance_ge` through the `hBal` lower bound. -/
theorem Υ_balanceOf_ge
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) (b₀ : ℕ)
    (hWF : StateWF σ)
    (hBal : b₀ ≤ balanceOf σ C)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (hWitness : ΞPreservesAtC C)
    (hTail : ΥTailInvariant σ fuel H_f H H_gen blocks tx S_T C)
    (hFactor : ΥBodyFactors σ fuel H_f H H_gen blocks tx S_T C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => b₀ ≤ balanceOf σ' C
    | .error _ => True := by
  have h := Υ_output_balance_ge fuel σ H_f H H_gen blocks tx S_T C
    hWF hS_T hBen hWitness hTail hFactor
  split
  all_goals first
    | trivial
    | (rename_i hOk
       rw [hOk] at h
       exact Nat.le_trans hBal h)

/-! ## §1.3 — Υ's invariant-preservation entry point

Mirror of `Υ_balanceOf_ge`'s chain, with conclusion changed from
balance monotonicity to `WethInvFr` preservation. The structure is:

  * `ΥBodyFactorsInvariant` — invariant-flavoured body factorisation
    (σ' decomposes through the tail; σ_P satisfies `WethInvFr σ_P C`
    and `dead σ_P C = false`). Discharged per-contract via the at-C
    invariant frames.
  * `Υ_tail_invariant_preserves` — combines `Υ_tail_balanceOf_ge`
    (β unchanged at C across the tail) with `Υ_tail_storageSum_eq`
    (S unchanged at C across the tail) ⇒ `WethInvFr σ_P C →
    WethInvFr σ_tail C`.
  * `Υ_invariant_preserved` — top-level consumer entry point. -/

/-- Hypothesis form of Υ's body factorisation, **invariant flavour**.

Whenever Υ returns `.ok (σ', A, z, _)`, σ' decomposes as
`Υ_tail_state σ_P g' A …` for some `(σ_P, g')` produced by the Θ/Λ
dispatch, with `WethInvFr σ_P C` (rather than balance monotonicity)
and `C` not dead in σ_P. Discharged per-contract by the caller via
the at-C invariant frame chain (`Θ_invariant_preserved` /
`Λ_invariant_preserved` / §H.2's `Ξ_invariant_preserved_bundled_bdd`). -/
def ΥBodyFactorsInvariant (σ : AccountMap .EVM) (fuel H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress) : Prop :=
  match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | .ok (σ', A', _, _) =>
      ∃ σ_P g',
        σ' = Υ_tail_state σ_P g' A' H H_f tx S_T ∧
        WethInvFr σ_P C ∧
        State.dead σ_P C = false
  | .error _ => True

/-- Combined tail step: under the structural exclusions for the SD/dead
sweeps and the `dead σ_P C = false` hypothesis, the pure tail of Υ
preserves `WethInvFr` at `C`.

Direct consequence of `Υ_tail_balanceOf_ge` (β unchanged at C across
the tail; the conclusion `balanceOf tail C ≥ balanceOf σ_P C`
upgrades to equality because the tail also doesn't add at C, but for
the invariant we only need `≥`) combined with `Υ_tail_storageSum_eq`
(S unchanged at C across the tail). -/
private theorem Υ_tail_invariant_preserves
    (σ_P : AccountMap .EVM) (g' : UInt256) (A : Substate)
    (H : BlockHeader) (H_f : ℕ) (tx : Transaction)
    (S_T C : AccountAddress)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (hSD : ∀ k ∈ A.selfDestructSet.1.toList, k ≠ C)
    (hDeadGated :
       ∀ σ_F : AccountMap .EVM, State.dead σ_F C = false →
         ∀ k ∈ A.touchedAccounts.filter (State.dead σ_F ·), k ≠ C)
    (hDead_σP : State.dead σ_P C = false)
    (hInv_σP : WethInvFr σ_P C) :
    WethInvFr (Υ_tail_state σ_P g' A H H_f tx S_T) C := by
  unfold WethInvFr at hInv_σP ⊢
  have hβ : balanceOf (Υ_tail_state σ_P g' A H H_f tx S_T) C = balanceOf σ_P C :=
    Υ_tail_balanceOf_ge σ_P g' A H H_f tx S_T C hS_T hBen hSD hDeadGated hDead_σP
  have hS : storageSum (Υ_tail_state σ_P g' A H H_f tx S_T) C = storageSum σ_P C :=
    Υ_tail_storageSum_eq σ_P g' A H H_f tx S_T C hS_T hBen hSD hDeadGated hDead_σP
  rw [hβ, hS]
  exact hInv_σP

/-- Υ's invariant-preservation frame, proved from the invariant body
factorisation and tail-invariant hypotheses.

Mirror of `Υ_output_balance_ge` for the (β ≥ S) chain.

Note: this theorem does not require a `ΞPreservesInvariantAtC C`
witness. The body-factor hypothesis (`hFactor`) already carries
`WethInvFr σ_P C` (post-Θ/Λ-dispatch), and the tail step preserves it
verbatim under the SD-exclusion / dead-set hypotheses, so the at-`C`
Ξ-level witness is structurally redundant at this level. The
consumer-side `ΞPreservesInvariantAtC` witness still feeds into the
Θ/Λ-side propagation chain that establishes `hFactor`'s
`WethInvFr σ_P C`, but it is not threaded through Υ. -/
theorem Υ_output_invariant_preserves
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress)
    (_hWF : StateWF σ)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (hTail : ΥTailInvariant σ fuel H_f H H_gen blocks tx S_T C)
    (hFactor : ΥBodyFactorsInvariant σ fuel H_f H H_gen blocks tx S_T C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => WethInvFr σ' C
    | .error _ => True := by
  unfold ΥBodyFactorsInvariant at hFactor
  unfold ΥTailInvariant at hTail
  cases hΥ : EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
  | error e => trivial
  | ok r =>
    obtain ⟨σ', A, z, gUsed⟩ := r
    rw [hΥ] at hFactor
    rw [hΥ] at hTail
    obtain ⟨σ_P, g', hEq, hInv_σP, hDead_σP⟩ := hFactor
    obtain ⟨hSD, hDeadGated⟩ := hTail
    show WethInvFr σ' C
    rw [hEq]
    exact Υ_tail_invariant_preserves σ_P g' A H H_f tx S_T C hS_T hBen
      hSD hDeadGated hDead_σP hInv_σP

/-- Υ's transaction-level invariant-preservation theorem. Given a
pre-state σ satisfying `WethInvFr σ C` and the structural hypotheses,
the post-state σ' produced by Υ also satisfies `WethInvFr σ' C`.

Mirror of `Υ_balanceOf_ge` for the (β ≥ S) chain. The proof composes
`Υ_output_invariant_preserves` (which produces `WethInvFr σ' C`
directly from σ_P's invariant) — no additional projection is needed
because the body factor's `WethInvFr σ_P C` is the invariant we want
to lift.

Note: the previously-required `hWitness : ΞPreservesInvariantAtC C`
parameter has been **dropped**. It was structurally unused in the
chain (the proof of `Υ_output_invariant_preserves` does not consume
it), and threading it through forced consumers to provide a universal-σ
σ-presence assumption (`account_at_initial`) that was unprovable in
full generality. Dropping the witness lets consumers like
`weth_solvency_invariant` close their proofs without that assumption. -/
theorem Υ_invariant_preserved
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress)
    (hWF : StateWF σ)
    (_hInv : WethInvFr σ C)
    (hS_T : C ≠ S_T)
    (hBen : C ≠ H.beneficiary)
    (hTail : ΥTailInvariant σ fuel H_f H H_gen blocks tx S_T C)
    (hFactor : ΥBodyFactorsInvariant σ fuel H_f H H_gen blocks tx S_T C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => WethInvFr σ' C
    | .error _ => True :=
  Υ_output_invariant_preserves fuel σ H_f H H_gen blocks tx S_T C
    hWF hS_T hBen hTail hFactor

end Frame
end EvmYul
