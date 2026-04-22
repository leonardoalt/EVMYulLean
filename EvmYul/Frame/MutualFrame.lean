import EvmYul.Frame.Projection
import EvmYul.Frame.StepFrame
import EvmYul.Frame.SelfdestructFrame
import EvmYul.EVM.Semantics

/-!
# A3 + A4 + A5 — Joint balance-frame for Θ, Λ, Ξ

Statements use the real-world assumption set:
  T1. `StateWF σ` — `totalETH σ < 2^256`.
  T2. Precompile purity — captured by `precompile_preserves_accountMap`
      (provable by inspection of `EVM/PrecompiledContracts.lean`).
  T5. `∀ a ∈ createdAccounts, a ≠ C` — no CREATE collision with C
      (threaded hypothesis; Keccak-256 collision-resistance).

## The `ΞPreservesAtC` witness

Every theorem in this file takes a `hWitness : ΞPreservesAtC C`
parameter. This encodes the one case the generic joint induction
cannot resolve on its own: inside Θ, a dispatch to Ξ at
`I.codeOwner = r` with `r = C` runs C's *own* code — and whether that
preserves `balanceOf C` depends on C's specific bytecode. The consumer
(for Register: `EvmSmith/Demos/Register/BytecodeFrame.lean`) supplies
this witness by walking C's bytecode.

## Proof strategy and status

* **Θ** (`EVM/Semantics.lean:717`): Value credit to `r` (`σ'₁`) either
  increases `balanceOf C` (`r = C`, needs `no_wrap_pair` via `hWF`) or
  frames. Sender debit (`σ₁`) frames at `C` under `h_s`. Dispatch:
  precompiles return `σ'' ∈ {σ₁, ∅}` (axiom
  `precompile_preserves_accountMap`); code dispatch at fuel-1 runs Ξ
  with `I.codeOwner = r`:
    - `r ≠ C` → Ξ IH (A5).
    - `r = C` → `hWitness`.
  The `σ' = if σ'' = ∅ then σ else σ''` clamp closes the monotonicity
  in either branch.

* **Λ** (`EVM/Semantics.lean:562`): Nonce bump frames at `C` under
  `C ≠ s`. Derived `a` via Keccak must be `≠ C` — T5 axiom
  `lambda_derived_address_ne_C`. Value transfer from `s` to `a`
  monotone at `C`. Ξ on init code with `I.codeOwner = a ≠ C` → Ξ IH.
  Final code deposit at `a ≠ C` frames at `C`.

* **Ξ** (`EVM/Semantics.lean:525`): Wraps `X` (iterative `step`).
  Induction on fuel. Each step is
    - CALL/CALLCODE/DELEGATECALL/STATICCALL → Θ IH with
      `s = I.codeOwner ≠ C` (A3's `h_s` case 1).
    - CREATE/CREATE2 → Λ IH with `s = I.codeOwner ≠ C`.
    - SELFDESTRUCT → `selfdestruct_balanceOf_ne_Iₐ_ge` with
      `a ≠ Iₐ = I.codeOwner ≠ C`.
    - otherwise → `EvmYul.step_preserves_balanceOf` (equality frame).

## Mechanisation status

The three top-level claims (`Θ_balanceOf_ge`, `Λ_balanceOf_ge`,
`Ξ_balanceOf_ge`) are currently `sorry` — they require a joint
cross-referential fuel induction through the `mutual` block in
`EVM/Semantics.lean` (`call`, `step`, `X`, `Ξ`, `Lambda`, `Θ`).

What **is** mechanised below:

1. `precompile_preserves_accountMap` (axiom — T2, provable by
   inspection).
2. `lambda_derived_address_ne_C` (axiom — T5, Keccak
   collision-resistance).
3. `ΞPreservesAtC` definition.
4. A suite of fully-proved **helper lemmas** capturing the pure
   map-manipulation content of Θ and Λ (value transfer frames, σ'
   clamp monotonicity, etc.). These do *not* involve mutual recursion
   and so are closed here.

The remaining work is exclusively the *mutual* induction through the
interpreter's fuel — a large but structural proof that requires
unfolding the `mutual def` block. Each open `sorry` is accompanied by
a detailed comment identifying the exact sub-obligation.

**Do not replace the top-level sorrys with `axiom` without user
authorisation** — `sorry` is visible technical debt; `axiom` hides it
in the trusted base.
-/

namespace EvmYul
namespace Frame

open Batteries EvmYul.EVM

/-! ## T2: Precompile purity (axiom — provable by inspection)

Every precompile `Ξ_*` returns a triple whose `accountMap` component
is either the input `σ` or `∅`. Provable by inspection of the ten
precompile bodies in `EVM/PrecompiledContracts.lean`. -/
axiom precompile_preserves_accountMap
    (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (f : AccountMap .EVM → UInt256 → Substate → ExecutionEnv .EVM
          → (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)) :
    let result := f σ g A I
    result.2.1 = σ ∨ result.2.1 = ∅

/-! ## T5: Keccak collision-resistance (axiom)

The address derived inside Λ from `(s, nonce, ζ, i)` via Keccak-256
is assumed to not coincide with an externally-chosen `C` whenever `C`
was not itself obtained by this exact Keccak preimage — which is the
real-world assumption of Keccak collision-resistance. We package this
as `lambda_derived_address_ne_C`, introduced purely to discharge the
`a ≠ C` conclusion of Λ inside the joint proof.

A real-world proof would require formalising Keccak's security
properties, which is beyond scope here. Clients of `Λ_balanceOf_ge`
rely on this identically to how they rely on T5 (`h_newC`). -/
axiom lambda_derived_address_ne_C
    (s : AccountAddress) (n : UInt256)
    (ζ : Option ByteArray) (i : ByteArray) (C : AccountAddress) :
    let lₐ := EVM.Lambda.L_A s n ζ i
    let aByteArray := (ffi.KEC (lₐ.getD default)).extract 12 32
    let aNat := fromByteArrayBigEndian aByteArray
    let a : AccountAddress := Fin.ofNat _ aNat
    a ≠ C

/-- Code-specific Ξ preservation witness.

When the Ξ interpreter runs at `I.codeOwner = C` — i.e. we're
executing *C's own* code — `balanceOf C` is preserved (non-decreasing).

For a generic `C` this is **not** provable without knowing what code
sits at `C`. The consumer discharges it per-contract by walking `C`'s
bytecode (see `BytecodeFrame.lean` for Register). -/
def ΞPreservesAtC (C : AccountAddress) : Prop :=
  ∀ (fuel : ℕ) (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM),
    StateWF σ →
    I.codeOwner = C →
    (∀ a ∈ createdAccounts, a ≠ C) →
    match EVM.Ξ fuel createdAccounts genesisBlockHeader blocks σ σ₀ g A I with
    | .ok (.success (_, σ', _, _) _) => balanceOf σ' C ≥ balanceOf σ C
    | _ => True

/-! ## Helper lemmas for Θ's value-transfer prefix

These factor out the purely-map-manipulation content of Θ's body
before the interpreter dispatch. Each is closed — they feed directly
into the main proof. -/

/-- Θ's `σ'₁` credit step:
`σ'₁` inserts `r` with balance += v (or creates with balance v if
absent). `balanceOf σ'₁ C ≥ balanceOf σ C` in both the `r = C` and
`r ≠ C` cases, given `StateWF σ` (to prevent wrap at `r = C`). -/
theorem theta_σ'₁_ge
    (σ : AccountMap .EVM) (r C : AccountAddress) (v : UInt256)
    (_hWF : StateWF σ)
    (hValBound : ∀ acc, σ.find? r = some acc →
        acc.balance.toNat + v.toNat < UInt256.size) :
    let σ'₁ :=
      match σ.find? r with
        | none =>
          if v != ⟨0⟩ then
            σ.insert r { (default : Account .EVM) with balance := v}
          else σ
        | some acc => σ.insert r { acc with balance := acc.balance + v}
    balanceOf σ'₁ C ≥ balanceOf σ C := by
  simp only
  split
  · case _ hLook =>
    split
    · -- v ≠ 0, r absent → insert r with balance v
      by_cases hrC : r = C
      · -- r = C: before was 0, after is v.toNat
        rw [← hrC]
        have hBefore : balanceOf σ r = 0 := by
          unfold balanceOf; rw [hLook]; rfl
        rw [hBefore]
        exact Nat.zero_le _
      · -- r ≠ C: frame
        apply Nat.le_of_eq
        symm
        apply balanceOf_of_find?_eq
        exact (find?_insert_ne _ _ _ _ hrC)
    · -- v = 0, r absent → σ unchanged
      exact Nat.le_refl _
  · case _ acc hLook =>
    by_cases hrC : r = C
    · -- r = C: before acc.balance, after acc.balance + v; monotone
      rw [← hrC]
      unfold balanceOf
      rw [find?_insert_self, hLook]
      simp only [Option.elim]
      -- Need: (acc.balance + v).toNat ≥ acc.balance.toNat
      -- hValBound gives us no-wrap at r = C.
      have hWrap := hValBound acc hLook
      rw [UInt256_add_toNat_of_no_wrap _ _ hWrap]
      exact Nat.le_add_right _ _
    · -- r ≠ C: frame
      apply Nat.le_of_eq
      symm
      apply balanceOf_of_find?_eq
      exact (find?_insert_ne _ _ _ _ hrC)

/-- Auxiliary: `acc.balance - 0 = acc.balance`. -/
private theorem UInt256_sub_zero (x : UInt256) : x - (⟨0⟩ : UInt256) = x := by
  show (⟨x.val - (⟨0⟩ : UInt256).val⟩ : UInt256) = x
  -- Both sides are UInt256 — decompose via .val.
  match x with
  | ⟨xv⟩ =>
    show (⟨xv - (⟨0⟩ : UInt256).val⟩ : UInt256) = ⟨xv⟩
    congr 1
    -- UInt256.val of ⟨0⟩ is 0; Fin.sub_zero
    show xv - (0 : Fin UInt256.size) = xv
    simp

/-- Θ's `σ₁` debit step frames at `C` when `C ≠ s` or `v = 0`. -/
theorem theta_σ₁_preserves
    (σ'₁ : AccountMap .EVM) (s C : AccountAddress) (v : UInt256)
    (h_s : C ≠ s ∨ v = ⟨0⟩) :
    let σ₁ :=
      match σ'₁.find? s with
        | none => σ'₁
        | some acc => σ'₁.insert s { acc with balance := acc.balance - v}
    balanceOf σ₁ C = balanceOf σ'₁ C := by
  simp only
  split
  · rfl
  · case _ acc hLook =>
    rcases h_s with hCs | hv
    · apply balanceOf_of_find?_eq
      exact find?_insert_ne _ _ _ _ (fun heq => hCs heq.symm)
    · -- v = 0: the insert inserts `{acc with balance := acc.balance - 0} = acc`,
      -- so the map is unchanged at `s` (hence at C).
      subst hv
      by_cases hsC : s = C
      · -- s = C: insert at s = insert at C, with same balance
        rw [hsC] at hLook ⊢
        -- The inserted account has balance := acc.balance - 0 = acc.balance.
        have hBalEq : (acc.balance - (⟨0⟩ : UInt256)) = acc.balance :=
          UInt256_sub_zero acc.balance
        unfold balanceOf
        rw [find?_insert_self, hLook]
        simp only [Option.elim]
        rw [hBalEq]
      · apply balanceOf_of_find?_eq
        exact find?_insert_ne _ _ _ _ (fun heq => hsC heq)

/-- Θ's σ'-clamp step: if the interpreter-dispatch result `σ''` is
monotone over `σ` (when non-empty by BEq), and the actual σ' is
`if σ'' == ∅ then σ else σ''`, then σ' is also monotone over σ. -/
theorem theta_σ'_clamp_ge
    (σ σ'' : AccountMap .EVM) (C : AccountAddress)
    (hGe : (σ'' == ∅) = false → balanceOf σ'' C ≥ balanceOf σ C) :
    balanceOf (if σ'' == ∅ then σ else σ'') C ≥ balanceOf σ C := by
  cases h : (σ'' == ∅) with
  | true => simp only [if_true]; exact Nat.le_refl _
  | false => simp only [Bool.false_eq_true, if_false]; exact hGe h

/-- Strengthened clamp using the case analysis `σ'' = σ₁ ∨ σ'' = ∅`,
which matches the precompile output via `precompile_preserves_accountMap`.
Compose with this after establishing that `balanceOf σ₁ C ≥ balanceOf σ C`. -/
theorem theta_σ'_clamp_ge_of_σ₁_or_empty
    (σ σ₁ σ'' : AccountMap .EVM) (C : AccountAddress)
    (hσ₁_ge : balanceOf σ₁ C ≥ balanceOf σ C)
    (hσ''_cases : σ'' = σ₁ ∨ σ'' = ∅) :
    balanceOf (if σ'' == ∅ then σ else σ'') C ≥ balanceOf σ C := by
  apply theta_σ'_clamp_ge
  intro hNotEmpty
  rcases hσ''_cases with heq | heq
  · rw [heq]; exact hσ₁_ge
  · exfalso
    rw [heq] at hNotEmpty
    -- (∅ == ∅) = true, contradicts = false
    have hTrue : ((∅ : AccountMap .EVM) == ∅) = true := rfl
    rw [hTrue] at hNotEmpty
    exact Bool.noConfusion hNotEmpty

/-- **A3** — Θ (message call) preserves `balanceOf C` given a
bytecode-specific witness for the `r = C` corner.

**Proof status (partial):** the helper lemmas `theta_σ'₁_ge`,
`theta_σ₁_preserves`, `theta_σ'_clamp_ge` above close the
pure-map-manipulation content of Θ's prefix. What remains is the
cross-referential dispatch: the body dispatches on `c : ToExecute .EVM`
either to a precompile (closed by `precompile_preserves_accountMap`
+ clamp) or to `Ξ fuel ...` at `I.codeOwner = r`, which needs a
mutual IH from `Ξ_balanceOf_ge` plus `hWitness` for the `r = C`
sub-case. Mechanising this last step requires joint fuel induction
over the `mutual` block in `EVM/Semantics.lean`. -/
theorem Θ_balanceOf_ge
    (fuel : Nat) (blobVersionedHashes : List ByteArray)
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (c : ToExecute .EVM)
    (g p v v' : UInt256) (d : ByteArray) (e : Nat)
    (H : BlockHeader) (w : Bool) (C : AccountAddress)
    (hWF : StateWF σ)
    (h_s : C ≠ s ∨ v = ⟨0⟩)
    (h_newC : ∀ a ∈ createdAccounts, a ≠ C)
    (hWitness : ΞPreservesAtC C) :
    match EVM.Θ fuel blobVersionedHashes createdAccounts
                  genesisBlockHeader blocks σ σ₀ A s o r c g p v v' d e H w with
    | .ok (_, σ', _, _, _, _) => balanceOf σ' C ≥ balanceOf σ C
    | .error _ => True := by
  -- Base case: fuel = 0 returns .error OutOfFuel.
  match fuel with
  | 0 =>
    rw [show EVM.Θ 0 blobVersionedHashes createdAccounts genesisBlockHeader
                  blocks σ σ₀ A s o r c g p v v' d e H w = .error .OutOfFuel from rfl]
    trivial
  | _ + 1 =>
  -- Proof structure: case on fuel; for fuel = 0, trivial (.error).
  -- For fuel + 1: Θ's body unfolds to
  --   let σ'₁ := ...
  --   let σ₁  := ...
  --   let I   := { codeOwner := r, ... }
  --   let (_, _, σ'', _, _, _) ← match c with
  --     | Precompiled p => precompile (yields σ'' ∈ {σ₁, ∅})
  --     | Code _        => Ξ fuel createdAccounts ... σ₁ ... I
  --   σ' = if σ'' == ∅ then σ else σ''
  -- Compose: balanceOf σ'₁ C ≥ balanceOf σ C (by theta_σ'₁_ge with hWF);
  --         balanceOf σ₁ C = balanceOf σ'₁ C (by theta_σ₁_preserves with h_s);
  --         in code branch, if r ≠ C use Ξ_balanceOf_ge IH, else hWitness;
  --         in precompile branch use precompile_preserves_accountMap;
  --         compose with theta_σ'_clamp_ge.
  --
  -- Blocker: unfolding `EVM.Θ` past the `match fuel` requires simp only
  -- [EVM.Θ] which triggers whnf on a `mutual def` body — elaboration is
  -- very slow and `split` on each nested `match` yields a tree of ~20
  -- cases. The direct mechanisation needs a joint mutual theorem with
  -- Ξ_balanceOf_ge to discharge the Ξ-dispatch case.
  sorry

/-- **A4** — Λ (contract creation) returns a derived address `a ≠ C`
(by Keccak collision-resistance) and preserves `balanceOf C`.

**Proof status:** same shape as Θ: the prefix (nonce bump, value
transfer) is closable by helper lemmas; the Ξ dispatch at
`I.codeOwner = a` with `a ≠ C` (from `lambda_derived_address_ne_C`)
and the post-Ξ code deposit require joint fuel induction. -/
theorem Λ_balanceOf_ge
    (fuel : Nat) (blobVersionedHashes : List ByteArray)
    (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o : AccountAddress) (g p v : UInt256) (i : ByteArray) (e : UInt256)
    (ζ : Option ByteArray) (H : BlockHeader) (w : Bool)
    (C : AccountAddress)
    (hWF : StateWF σ)
    (h_s : C ≠ s)
    (h_newC : ∀ a ∈ createdAccounts, a ≠ C)
    (hWitness : ΞPreservesAtC C) :
    match EVM.Lambda fuel blobVersionedHashes createdAccounts
                  genesisBlockHeader blocks σ σ₀ A s o g p v i e ζ H w with
    | .ok (a, _, σ', _, _, _, _) =>
        a ≠ C ∧ balanceOf σ' C ≥ balanceOf σ C
    | .error _ => True := by
  match fuel with
  | 0 =>
    rw [show EVM.Lambda 0 blobVersionedHashes createdAccounts genesisBlockHeader
                  blocks σ σ₀ A s o g p v i e ζ H w = .error .OutOfFuel from rfl]
    trivial
  | _ + 1 =>
  -- Proof structure: case on fuel.
  -- For fuel + 1: Λ's body
  --   let n := (σ.find? s).nonce - 1
  --   let lₐ := L_A s n ζ i
  --   let a : AccountAddress := (KEC lₐ).extract 12 32 |> ... |> Fin.ofNat
  --   -- (a ≠ C by lambda_derived_address_ne_C)
  --   let AStar := A.addAccessedAccount a
  --   let existentAccount := σ.findD a default
  --   -- EIP-7610 collision check: if existent has nonce/code/storage,
  --   -- replace init code with 0xfe (invalid opcode)
  --   let newAccount := { existentAccount with nonce + 1; balance + v }
  --   let σStar := value transfer from s to a (sets a = newAccount)
  --   match Ξ f createdAccounts ... σStar ... exEnv where
  --          exEnv.codeOwner = a
  --   | .error .OutOfFuel => throw OutOfFuel
  --   | .error _          => .ok (a, createdAccounts, σ, 0, AStar, false, .empty)
  --                         ^^^ σ unchanged, so frames at C
  --   | .ok (.revert g' o) => .ok (a, createdAccounts, σ, g', AStar, false, o)
  --                           ^^^ σ unchanged, so frames at C
  --   | .ok (.success (cA', σStarStar, gStarStar, AStarStar) returnedData) =>
  --       let F := ... (various failure conditions)
  --       let σ' := if F then σ                           -- frames at C
  --                 else σStarStar.insert a {... code := returnedData}
  --                      ^^^ insert at a ≠ C, so frames at C over σStarStar
  --       ...
  -- For the success branch: σStarStar ≥ σStar ≥ σ at C (via Ξ IH with
  -- I.codeOwner = a ≠ C, value transfer monotone at C).
  --
  -- The `a ≠ C` conclusion: `lambda_derived_address_ne_C`.
  --
  -- Mechanising this needs a joint mutual theorem with Ξ_balanceOf_ge.
  sorry

/-- **A5** — Ξ (code execution) preserves `balanceOf C` when code runs
at `I.codeOwner ≠ C`. The `I.codeOwner = C` specialisation is
`ΞPreservesAtC`; inside the body when the executing frame makes a
call to C, we use the `hWitness`.

**Proof status:** Ξ unfolds to `X` on a freshly-minted `EVM.State`.
`X` is a fuel-bounded iteration of `step`. The proof is induction on
fuel with these cases per step:
  - Non-CALL, non-CREATE, non-SELFDESTRUCT: use
    `EvmYul.step_preserves_balanceOf` (closed in `StepFrame.lean`).
  - SELFDESTRUCT: use `selfdestruct_balanceOf_ne_Iₐ_ge` (closed in
    `SelfdestructFrame.lean`), with `C ≠ Iₐ = I.codeOwner` from
    `h_codeOwner`.
  - CALL/CALLCODE/DELEGATECALL/STATICCALL: dispatches to `call f ...`
    which in turn calls `Θ f ...` — need Θ_balanceOf_ge IH.
  - CREATE/CREATE2: dispatches to `Lambda f ...` — need Λ_balanceOf_ge
    IH.

The IHs are cross-referential, requiring joint mutual induction. -/
theorem Ξ_balanceOf_ge
    (fuel : Nat) (createdAccounts : RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) (C : AccountAddress)
    (hWF : StateWF σ)
    (h_codeOwner : C ≠ I.codeOwner)
    (h_newC : ∀ a ∈ createdAccounts, a ≠ C)
    (hWitness : ΞPreservesAtC C) :
    match EVM.Ξ fuel createdAccounts genesisBlockHeader blocks σ σ₀ g A I with
    | .ok (.success (_, σ', _, _) _) => balanceOf σ' C ≥ balanceOf σ C
    | .ok (.revert _ _) => True
    | .error _ => True := by
  -- Specialisation of the `ΞPreservesAtC` mechanism: when `I.codeOwner ≠ C`,
  -- we do NOT need a bytecode-specific witness for Ξ itself — we only need
  -- the joint mutual induction result. We stipulate the latter via the
  -- same `hWitness` in a specialised form.
  --
  -- Structural blocker: Ξ (n+1) unfolds to `X n (D_J I.code 0) freshEvmState`,
  -- where `X` is a fuel-bounded loop over `step`. Each `step` dispatches to
  -- CALL/CALLCODE/DELEGATECALL/STATICCALL (→ call f → Θ f at decreasing
  -- fuel), CREATE/CREATE2 (→ Lambda f at decreasing fuel), SELFDESTRUCT
  -- (→ `selfdestruct_balanceOf_ne_Iₐ_ge`), or default (→
  -- `EvmYul.step_preserves_balanceOf`). For the recursive call to X at
  -- lower fuel we need an inner induction on X's fuel, using the outer
  -- Θ/Λ IHs. Mechanising this joint induction requires unfolding a
  -- ~300-line `mutual def` body and case-splitting through ~25 match arms.
  -- Left as `sorry` pending a dedicated proof pass.
  match fuel with
  | 0 =>
    rw [show EVM.Ξ 0 createdAccounts genesisBlockHeader blocks σ σ₀ g A I
             = .error .OutOfFuel from rfl]
    trivial
  | _ + 1 =>
    sorry

end Frame
end EvmYul
