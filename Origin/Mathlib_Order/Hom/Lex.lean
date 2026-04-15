/-
Extracted from Order/Hom/Lex.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lexicographic order and order isomorphisms

## Main declarations

* `OrderIso.sumLexIioIci` and `OrderIso.sumLexIicIoi`: if `α` is a linear order and `x : α`,
  then `α` is order isomorphic to both `Iio x ⊕ₗ Ici x` and `Iic x ⊕ₗ Ioi x`.
* `Prod.Lex.prodUnique` and `Prod.Lex.uniqueProd`: `α ×ₗ β` is order isomorphic to one side if the
  other side is `Unique`.
-/

open Set

variable {α : Type*}

/-! ### Relation isomorphism -/

namespace RelIso

variable {r : α → α → Prop} {x y : α} [IsTrans α r] [Std.Trichotomous r] [DecidableRel r]

variable (r x) in

def sumLexComplLeft : Sum.Lex (Subrel r (r · x)) (Subrel r (¬ r · x)) ≃r r where
  toEquiv := .sumCompl (r · x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_right ha hb
    · simpa using fun h ↦ ha <| trans h hb
    · simp
