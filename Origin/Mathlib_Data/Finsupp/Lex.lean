/-
Extracted from Data/Finsupp/Lex.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.DFinsupp.Lex
import Mathlib.Data.Finsupp.ToDFinsupp

noncomputable section

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `Finsupp`.
-/

variable {α N : Type*}

namespace Finsupp

section NHasZero

variable [Zero N]

protected def Lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
  Pi.Lex r s x y

instance [LT α] [LT N] : LT (Lex (α →₀ N)) :=
  ⟨fun f g ↦ Finsupp.Lex (· < ·) (· < ·) (ofLex f) (ofLex g)⟩

theorem lex_lt_of_lt_of_preorder [Preorder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  DFinsupp.lex_lt_of_lt_of_preorder r (id hlt : x.toDFinsupp < y.toDFinsupp)

theorem lex_lt_of_lt [PartialOrder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    Pi.Lex r (· < ·) x y :=
  DFinsupp.lex_lt_of_lt r (id hlt : x.toDFinsupp < y.toDFinsupp)

instance Lex.isStrictOrder [LinearOrder α] [PartialOrder N] :
    IsStrictOrder (Lex (α →₀ N)) (· < ·) where
  irrefl _ := lt_irrefl (α := Lex (α → N)) _
  trans _ _ _ := lt_trans (α := Lex (α → N))

variable [LinearOrder α]

instance Lex.partialOrder [PartialOrder N] : PartialOrder (Lex (α →₀ N)) where
  lt := (· < ·)
  le x y := ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Lex (α →₀ N) ↦ toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := Finsupp α N))

instance Lex.linearOrder [LinearOrder N] : LinearOrder (Lex (α →₀ N)) where
  lt := (· < ·)
  le := (· ≤ ·)
  __ := LinearOrder.lift' (toLex ∘ toDFinsupp ∘ ofLex) finsuppEquivDFinsupp.injective

variable [PartialOrder N]

theorem toLex_monotone : Monotone (@toLex (α →₀ N)) :=
  fun a b h ↦ DFinsupp.toLex_monotone (id h : ∀ i, ofLex (toDFinsupp a) i ≤ ofLex (toDFinsupp b) i)

theorem lt_of_forall_lt_of_lt (a b : Lex (α →₀ N)) (i : α) :
    (∀ j < i, ofLex a j = ofLex b j) → ofLex a i < ofLex b i → a < b :=
  fun h1 h2 ↦ ⟨i, h1, h2⟩

end NHasZero

section Covariants

variable [LinearOrder α] [AddMonoid N] [LinearOrder N]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `AddLeftStrictMono` (covariant with *strict* inequality `<`) also when proving the one
with the *weak* inequality `≤`.  This is actually necessary: addition on `Lex (α →₀ N)` may fail to
be monotone, when it is "just" monotone on `N`.

See `Counterexamples/ZeroDivisorsInAddMonoidAlgebras.lean` for a counterexample. -/

section Left

variable [AddLeftStrictMono N]

instance Lex.addLeftStrictMono : AddLeftStrictMono (Lex (α →₀ N)) :=
  ⟨fun _ _ _ ⟨a, lta, ha⟩ ↦ ⟨a, fun j ja ↦ congr_arg _ (lta j ja), add_lt_add_left ha _⟩⟩

instance Lex.addLeftMono : AddLeftMono (Lex (α →₀ N)) :=
  addLeftMono_of_addLeftStrictMono _

end Left

section Right

variable [AddRightStrictMono N]

instance Lex.addRightStrictMono : AddRightStrictMono (Lex (α →₀ N)) :=
  ⟨fun f _ _ ⟨a, lta, ha⟩ ↦
    ⟨a, fun j ja ↦ congr_arg (· + ofLex f j) (lta j ja), add_lt_add_right ha _⟩⟩

instance Lex.addRightMono : AddRightMono (Lex (α →₀ N)) :=
  addRightMono_of_addRightStrictMono _

end Right

end Covariants

section OrderedAddMonoid

variable [LinearOrder α]

instance Lex.orderBot [CanonicallyOrderedAddCommMonoid N] : OrderBot (Lex (α →₀ N)) where
  bot := 0
  bot_le _ := Finsupp.toLex_monotone bot_le

noncomputable instance Lex.orderedAddCancelCommMonoid [OrderedCancelAddCommMonoid N] :
    OrderedCancelAddCommMonoid (Lex (α →₀ N)) where
  add_le_add_left _ _ h _ := add_le_add_left (α := Lex (α → N)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (α → N))

noncomputable instance Lex.orderedAddCommGroup [OrderedAddCommGroup N] :
    OrderedAddCommGroup (Lex (α →₀ N)) where
  add_le_add_left _ _ := add_le_add_left

noncomputable instance Lex.linearOrderedCancelAddCommMonoid [LinearOrderedCancelAddCommMonoid N] :
    LinearOrderedCancelAddCommMonoid (Lex (α →₀ N)) where
  __ : LinearOrder (Lex (α →₀ N)) := inferInstance
  __ : OrderedCancelAddCommMonoid (Lex (α →₀ N)) := inferInstance

noncomputable instance Lex.linearOrderedAddCommGroup [LinearOrderedAddCommGroup N] :
    LinearOrderedAddCommGroup (Lex (α →₀ N)) where
  __ : LinearOrder (Lex (α →₀ N)) := inferInstance
  add_le_add_left _ _ := add_le_add_left

end OrderedAddMonoid

end Finsupp
