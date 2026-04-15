/-
Extracted from Algebra/Homology/HomotopyCategory/HomComplexInduction.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Construction of cochains by induction

Let `K` and `L` be cochain complexes in a preadditive category `C`.
We provide an API to construct a cochain in `Cochain K L d` in the following
situation. Assume that `X n : Set (Cochain K L d)` is a sequence of subsets
of `Cochain K L d`, and `φ n : X n → X (n + 1)` is a sequence of maps such
that for a certain `p₀ : ℕ` and any `x : X n`, `φ n x` and `x` coincide
up to the degree `p₀ + n`, then we construct a cochain
`InductionUp.limitSequence` in `Cochain K L d` which coincides with the
`n`th-iteration of `φ` evaluated on `x₀` up to the degree `p₀ + n` for any `n : ℕ`.

-/

universe v u

open CategoryTheory

namespace CochainComplex.HomComplex.Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ}

def EqUpTo {n : ℤ} (α β : Cochain K L n) (p₀ : ℤ) : Prop :=
  ∀ (p q : ℤ) (hpq : p + n = q), p ≤ p₀ → α.v p q hpq = β.v p q hpq

namespace InductionUp

variable {d : ℤ} {X : ℕ → Set (Cochain K L d)} (φ : ∀ (n : ℕ), X n → X (n + 1))
   {p₀ : ℤ} (hφ : ∀ (n : ℕ) (x : X n), (φ n x).val.EqUpTo x.val (p₀ + n)) (x₀ : X 0)

def sequence : ∀ n, X n
  | 0 => x₀
  | n + 1 => φ n (sequence n)

include hφ in

lemma sequence_eqUpTo (n₁ n₂ : ℕ) (h : n₁ ≤ n₂) :
    (sequence φ x₀ n₁).val.EqUpTo (sequence φ x₀ n₂).val (p₀ + n₁) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k generalizing n₁ with
  | zero => intro _ _ _ _; simp
  | succ k hk =>
    intro p q hpq hp
    rw [hk n₁ p q hpq hp, ← hφ (n₁ + k) (sequence φ x₀ (n₁ + k)) p q hpq (by lia)]
    dsimp [sequence]
