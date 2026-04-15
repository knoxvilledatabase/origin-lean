/-
Extracted from Data/Sigma/Lex.lean
Genuine: 4 of 19 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core

/-!
# Lexicographic order on a sigma type

This defines the lexicographical order of two arbitrary relations on a sigma type and proves some
lemmas about `PSigma.Lex`, which is defined in core Lean.

Given a relation in the index type and a relation on each summand, the lexicographical order on the
sigma type relates `a` and `b` if their summands are related or they are in the same summand and
related by the summand's relation.

## See also

Related files are:
* `Combinatorics.CoLex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i` per say.
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`. Can be thought of as the special case of
  `Sigma.Lex` where all summands are the same
-/

namespace Sigma

variable {ι : Type*} {α : ι → Type*} {r r₁ r₂ : ι → ι → Prop} {s s₁ s₂ : ∀ i, α i → α i → Prop}
  {a b : Σ i, α i}

inductive Lex (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) : ∀ _ _ : Σ i, α i, Prop
  | left {i j : ι} (a : α i) (b : α j) : r i j → Lex r s ⟨i, a⟩ ⟨j, b⟩
  | right {i : ι} (a b : α i) : s i a b → Lex r s ⟨i, a⟩ ⟨i, b⟩

theorem lex_iff : Lex r s a b ↔ r a.1 b.1 ∨ ∃ h : a.1 = b.1, s b.1 (h.rec a.2) b.2 := by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact Lex.left _ _ h
    · exact Lex.right _ _ h

-- INSTANCE (free from Core): Lex.decidable

theorem lex_swap : Lex (Function.swap r) s a b ↔ Lex r (fun i => Function.swap (s i)) b a := by
  constructor <;>
    · rintro (⟨a, b, h⟩ | ⟨a, b, h⟩)
      · exact Lex.left _ _ h
      · exact Lex.right _ _ h

-- INSTANCE (free from Core): [∀

-- INSTANCE (free from Core): [Std.Irrefl

-- INSTANCE (free from Core): [IsTrans

-- INSTANCE (free from Core): [Std.Symm

-- INSTANCE (free from Core): [Std.Asymm

-- INSTANCE (free from Core): [Std.Trichotomous

-- INSTANCE (free from Core): [Std.Trichotomous

end Sigma

/-! ### `PSigma` -/

namespace PSigma

variable {ι : Sort*} {α : ι → Sort*} {r : ι → ι → Prop} {s : ∀ i, α i → α i → Prop}

theorem lex_iff {a b : Σ' i, α i} :
    Lex r s a b ↔ r a.1 b.1 ∨ ∃ h : a.1 = b.1, s b.1 (h.rec a.2) b.2 := by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨i, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact Lex.left _ _ h
    · exact Lex.right _ h

-- INSTANCE (free from Core): Lex.decidable

end PSigma
