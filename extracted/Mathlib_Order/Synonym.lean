/-
Extracted from Order/Synonym.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 29
-/
import Origin.Core
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Order.Basic

noncomputable section

/-!
# Type synonyms

This file provides two type synonyms for order theory:
* `OrderDual α`: Type synonym of `α` to equip it with the dual order (`a ≤ b` becomes `b ≤ a`).
* `Lex α`: Type synonym of `α` to equip it with its lexicographic order. The precise meaning depends
  on the type we take the lex of. Examples include `Prod`, `Sigma`, `List`, `Finset`.

## Notation

`αᵒᵈ` is notation for `OrderDual α`.

The general rule for notation of `Lex` types is to append `ₗ` to the usual notation.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`/`Lex α`. Instead, explicit
coercions should be inserted:
* `OrderDual`: `OrderDual.toDual : α → αᵒᵈ` and `OrderDual.ofDual : αᵒᵈ → α`
* `Lex`: `toLex : α → Lex α` and `ofLex : Lex α → α`.

## See also

This file is similar to `Algebra.Group.TypeTags`.
-/

variable {α : Type*}

/-! ### Order dual -/

namespace OrderDual

instance [h : Nontrivial α] : Nontrivial αᵒᵈ :=
  h

def toDual : α ≃ αᵒᵈ :=
  Equiv.refl _

def ofDual : αᵒᵈ ≃ α :=
  Equiv.refl _

@[simp]
theorem toDual_symm_eq : (@toDual α).symm = ofDual := rfl

@[simp]
theorem ofDual_symm_eq : (@ofDual α).symm = toDual := rfl

@[simp]
theorem toDual_ofDual (a : αᵒᵈ) : toDual (ofDual a) = a :=
  rfl

@[simp]
theorem ofDual_toDual (a : α) : ofDual (toDual a) = a :=
  rfl

@[simp]
theorem toDual_le_toDual [LE α] {a b : α} : toDual a ≤ toDual b ↔ b ≤ a :=
  Iff.rfl

@[simp]
theorem toDual_lt_toDual [LT α] {a b : α} : toDual a < toDual b ↔ b < a :=
  Iff.rfl

@[simp]
theorem ofDual_le_ofDual [LE α] {a b : αᵒᵈ} : ofDual a ≤ ofDual b ↔ b ≤ a :=
  Iff.rfl

@[simp]
theorem ofDual_lt_ofDual [LT α] {a b : αᵒᵈ} : ofDual a < ofDual b ↔ b < a :=
  Iff.rfl

@[elab_as_elim]
protected def rec {C : αᵒᵈ → Sort*} (h₂ : ∀ a : α, C (toDual a)) : ∀ a : αᵒᵈ, C a :=
  h₂

@[simp]
protected theorem «forall» {p : αᵒᵈ → Prop} : (∀ a, p a) ↔ ∀ a, p (toDual a) :=
  Iff.rfl

@[simp]
protected theorem «exists» {p : αᵒᵈ → Prop} : (∃ a, p a) ↔ ∃ a, p (toDual a) :=
  Iff.rfl

alias ⟨_, _root_.LE.le.dual⟩ := toDual_le_toDual

alias ⟨_, _root_.LT.lt.dual⟩ := toDual_lt_toDual

alias ⟨_, _root_.LE.le.ofDual⟩ := ofDual_le_ofDual

alias ⟨_, _root_.LT.lt.ofDual⟩ := ofDual_lt_ofDual

end OrderDual

/-! ### Lexicographic order -/

def Lex (α : Type*) :=
  α

@[match_pattern]
def toLex : α ≃ Lex α :=
  Equiv.refl _

@[match_pattern]
def ofLex : Lex α ≃ α :=
  Equiv.refl _

@[simp]
theorem toLex_symm_eq : (@toLex α).symm = ofLex :=
  rfl

@[simp]
theorem ofLex_symm_eq : (@ofLex α).symm = toLex :=
  rfl

@[simp]
theorem toLex_ofLex (a : Lex α) : toLex (ofLex a) = a :=
  rfl

@[simp]
theorem ofLex_toLex (a : α) : ofLex (toLex a) = a :=
  rfl

instance (α : Type*) [BEq α] : BEq (Lex α) where
  beq a b := ofLex a == ofLex b

instance (α : Type*) [BEq α] [LawfulBEq α] : LawfulBEq (Lex α) :=
  inferInstanceAs (LawfulBEq α)

instance (α : Type*) [DecidableEq α] : DecidableEq (Lex α) :=
  inferInstanceAs (DecidableEq α)

instance (α : Type*) [Inhabited α] : Inhabited (Lex α) :=
  inferInstanceAs (Inhabited α)

@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def Lex.rec {β : Lex α → Sort*} (h : ∀ a, β (toLex a)) : ∀ a, β a := fun a => h (ofLex a)

@[simp] lemma Lex.forall {p : Lex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toLex a) := Iff.rfl

@[simp] lemma Lex.exists {p : Lex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toLex a) := Iff.rfl
