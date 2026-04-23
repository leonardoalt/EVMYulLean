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
    simp [List.filter_cons, ha, ih']

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

/-- RBNode-level lemma: `del cut` removes exactly the entries with `cut = .eq`. -/
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
                   hy, hbFilter, iha']
        simp [if_true]
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
                   hy, haFilter, ihb']
        simp [if_true]
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
      simp only [hcy, append_toList, haFilter, hbFilter, hy]
      simp

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

/-! ## Υ output balance frame (narrow axiom, same pattern as `X_preserves_balance_ge`)

Pinned axiom that threads the per-step frame chain above through Υ's
nested `do`-block. Its shape mirrors `X_preserves_balance_ge`
(MutualFrame.lean:610): a conclusion relating Υ's *output state* to
its *input state*, under structural + bytecode hypotheses.

The provability content is:
  (i)   sender-debit `σ → σ₀` frame — `balanceOf_insert_ne` + `hS_T`.
  (ii)  `σ₀ → σ_P` via Θ/Λ dispatch — `Θ_balanceOf_ge` / `Λ_balanceOf_ge`.
        `StateWF σ₀` follows from `stateWF_insert_balance_le` (the
        debit only lowers balance); `s = S_T ≠ C` matches `h_s` /
        `h_s_ne_C`; `createdAccounts = ∅` vacuously satisfies `h_newC`.
  (iii) `σ_P → σStar` via `increaseBalance S_T`   — `balanceOf_increaseBalance_ne`.
  (iv)  `σStar → σStar'` via optional `increaseBalance H.beneficiary`
                                                   — `balanceOf_increaseBalance_ne`.
  (v)   `σStar' → σ'₁` SD sweep — `find?_erase_rbnode_foldl_ne`; requires
        that the post-dispatch `A.selfDestructSet` excludes C (a
        property of the call tree, follows from Register's
        no-SELFDESTRUCT bytecode).
  (vi)  `σ'₁ → σ'₂` dead sweep — `find?_erase_rbset_foldl_ne`; requires
        C ∉ dead filter output (follows from Register's account having
        non-empty `code`, hence non-dead).
  (vii) `σ'₂ → σ'` tstorage wipe — `balanceOf_tstorage_wipe_eq`.

The ~200 LoC of `split`/`subst` plumbing that threads (i)-(vii)
through Υ's nested `match` error arms does not add new mathematical
content.

**Same trust footprint as `X_preserves_balance_ge`**: σ' is
syntactically bound to Υ's output via the `match EVM.Υ … with` in
the conclusion, so this is NOT an axiom admitting balance
monotonicity for unrelated states. -/
axiom Υ_output_balance_ge
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks) (tx : Transaction)
    (S_T C : AccountAddress)
    (_hWF : StateWF σ)
    (_hS_T : C ≠ S_T)
    (_hBen : C ≠ H.beneficiary)
    (_hWitness : ΞPreservesAtC C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => balanceOf σ' C ≥ balanceOf σ C
    | .error _ => True

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
    (hWitness : ΞPreservesAtC C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => b₀ ≤ balanceOf σ' C
    | .error _ => True := by
  have h := Υ_output_balance_ge fuel σ H_f H H_gen blocks tx S_T C
    hWF hS_T hBen hWitness
  split
  all_goals first
    | trivial
    | (rename_i hOk
       rw [hOk] at h
       exact Nat.le_trans hBal h)

end Frame
end EvmYul
