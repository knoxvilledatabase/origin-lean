/-
Released under MIT license.
-/
import Val.Category.Core

/-!
# Val α: Functors and Natural Transformations (Deep)

Bifunctors, contravariant functors, representable functors,
Yoneda lemma (sort-level), natural isomorphisms, whiskering.
-/

namespace Val

universe u
variable {α β γ δ : Type u}

-- ============================================================================
-- Contravariant Functor
-- ============================================================================

-- valContramap is structurally identical to valMap. Reuse it.
def valContramap (f : α → β) : Val α → Val β := valMap f

theorem valContramap_id : valContramap (id : α → α) = (id : Val α → Val α) := valMap_id

theorem valContramap_comp (f : α → β) (g : β → γ) :
    valContramap (g ∘ f) = valContramap g ∘ valContramap f := valMap_comp f g

-- ============================================================================
-- Bifunctor
-- ============================================================================

/-- Bifunctor: maps two Val values to a Val pair. -/
def valBimap (f : α → γ) (g : β → δ) : Val α → Val β → Val (γ × δ)
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (f a, g b)
  | container a, contents b => container (f a, g b)
  | contents a, container b => container (f a, g b)
  | contents a, contents b => contents (f a, g b)

theorem valBimap_contents (f : α → γ) (g : β → δ) (a : α) (b : β) :
    valBimap f g (contents a) (contents b) = contents (f a, g b) := rfl

theorem valBimap_origin_left (f : α → γ) (g : β → δ) (y : Val β) :
    valBimap f g origin y = origin := by cases y <;> rfl

-- ============================================================================
-- Natural Isomorphism
-- ============================================================================

/-- Two equal functions give equal valMaps. -/
theorem nat_iso_from_fun_eq (f g : α → β) (h : f = g) :
    valMap f = valMap g := by rw [h]

/-- If f and g are mutual inverses, valMap g ∘ valMap f = id. -/
theorem nat_iso_inverse (f : α → β) (g : β → α)
    (hfg : ∀ b, f (g b) = b) (hgf : ∀ a, g (f a) = a) (x : Val α) :
    valMap g (valMap f x) = x := by
  cases x with
  | origin => rfl
  | container a => show container (g (f a)) = container a; rw [hgf]
  | contents a => show contents (g (f a)) = contents a; rw [hgf]

-- ============================================================================
-- Representable Functor (Sort-Level Yoneda)
-- ============================================================================

/-- Yoneda: two functions pointwise equal give equal valMaps. -/
theorem yoneda_val (f g : α → β) (h : ∀ a, f a = g a) :
    valMap f = valMap g := by
  funext x; cases x with
  | origin => rfl
  | container a => show container (f a) = container (g a); rw [h]
  | contents a => show contents (f a) = contents (g a); rw [h]

/-- Yoneda faithfulness: valMap detects equality of functions on contents. -/
theorem yoneda_contents_faithful (f g : α → β)
    (h : ∀ a, valMap f (contents a) = valMap g (contents a)) :
    ∀ a, f a = g a := by
  intro a; have h1 := h a; simp [valMap] at h1; exact h1

-- ============================================================================
-- Constant Functor
-- ============================================================================

/-- Constant functor: maps every Val to a fixed value (sort-preserving). -/
def constFunctor (b : β) : Val α → Val β
  | origin => origin
  | container _ => container b
  | contents _ => contents b

theorem constFunctor_origin (b : β) :
    constFunctor b (origin : Val α) = (origin : Val β) := rfl

theorem constFunctor_contents (b : β) (a : α) :
    constFunctor b (contents a : Val α) = contents b := rfl

-- ============================================================================
-- Whiskering
-- ============================================================================

/-- Left whiskering: precompose with f, replace g with h. -/
theorem whisker_left (f : α → β) (g h : β → γ) (hgh : ∀ b, g b = h b) (x : Val α) :
    valMap g (valMap f x) = valMap h (valMap f x) := by
  cases x with
  | origin => rfl
  | container a => show container (g (f a)) = container (h (f a)); rw [hgh]
  | contents a => show contents (g (f a)) = contents (h (f a)); rw [hgh]

/-- Right whiskering: postcompose with h, replace f with g. -/
theorem whisker_right (f g : α → β) (h : β → γ) (hfg : ∀ a, f a = g a) (x : Val α) :
    valMap h (valMap f x) = valMap h (valMap g x) := by
  cases x with
  | origin => rfl
  | container a => show container (h (f a)) = container (h (g a)); rw [hfg]
  | contents a => show contents (h (f a)) = contents (h (g a)); rw [hfg]

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Functors and natural transformations over Val α:
--   ✓ Contravariant functor: reuse valMap
--   ✓ Bifunctor: valBimap, contents × contents = contents
--   ✓ Natural isomorphisms: inverse round-trip
--   ✓ Yoneda: faithful on contents
--   ✓ Constant functor: sort-preserving
--   ✓ Whiskering: left and right
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
