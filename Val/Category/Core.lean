/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Category-Theoretic Formulation of Val α

valMap as functor, contents as natural transformation, universal property, monad structure.
The universal property: Val α is the free "type with boundary" over α.
-/

namespace Val

universe u
variable {α β γ : Type u}

-- ============================================================================
-- valMap: Sort-Preserving Maps
-- ============================================================================

/-- Sort-preserving map: origin → origin, container → container, contents → contents. -/
def valMap (f : α → β) : Val α → Val β
  | origin => origin
  | container a => container (f a)
  | contents a => contents (f a)

-- ============================================================================
-- Functor Laws
-- ============================================================================

@[simp] theorem valMap_origin (f : α → β) : valMap f (origin : Val α) = origin := rfl
@[simp] theorem valMap_container (f : α → β) (a : α) : valMap f (container a) = container (f a) := rfl
@[simp] theorem valMap_contents (f : α → β) (a : α) : valMap f (contents a) = contents (f a) := rfl

/-- valMap id = id -/
theorem valMap_id : valMap (id : α → α) = id := by
  funext x; cases x <;> rfl

/-- valMap (g ∘ f) = valMap g ∘ valMap f -/
theorem valMap_comp (f : α → β) (g : β → γ) :
    valMap (g ∘ f) = valMap g ∘ valMap f := by
  funext x; cases x <;> rfl

-- ============================================================================
-- valMap Preserves Operations
-- ============================================================================

/-- valMap commutes with mul when f preserves multiplication. -/
theorem valMap_preserves_mul (f : α → β) (mulA : α → α → α) (mulB : β → β → β)
    (hf : ∀ a b : α, f (mulA a b) = mulB (f a) (f b))
    (x y : Val α) :
    valMap f (mul mulA x y) = mul mulB (valMap f x) (valMap f y) := by
  cases x <;> cases y <;> simp [mul, hf]

/-- valMap commutes with add when f preserves addition. -/
theorem valMap_preserves_add (f : α → β) (addA : α → α → α) (addB : β → β → β)
    (hf : ∀ a b : α, f (addA a b) = addB (f a) (f b))
    (x y : Val α) :
    valMap f (add addA x y) = add addB (valMap f x) (valMap f y) := by
  cases x <;> cases y <;> simp [add, hf]

/-- valMap commutes with inv when f preserves inversion. -/
theorem valMap_preserves_inv (f : α → β) (invA : α → α) (invB : β → β)
    (hf : ∀ a : α, f (invA a) = invB (f a))
    (x : Val α) :
    valMap f (inv invA x) = inv invB (valMap f x) := by
  cases x <;> simp [inv, hf]

-- ============================================================================
-- Natural Transformation: contents is the unit
-- ============================================================================

/-- contents is natural: contents ∘ f = valMap f ∘ contents -/
theorem contents_naturality (f : α → β) :
    contents ∘ f = valMap f ∘ contents := rfl

-- ============================================================================
-- Universal Property
-- ============================================================================

/-- valMap f is the unique sort-preserving extension of f through contents. -/
theorem valMap_unique (f : α → β) (g : Val α → Val β)
    (h_origin : g origin = origin)
    (h_container : ∀ a : α, g (container a) = container (f a))
    (h_contents : ∀ a : α, g (contents a) = contents (f a)) :
    g = valMap f := by
  funext x; cases x with
  | origin => exact h_origin
  | container a => exact h_container a
  | contents a => exact h_contents a

-- ============================================================================
-- Monad Structure
-- ============================================================================

/-- Collapse Val (Val α) → Val α: boundary structure doesn't nest. -/
def valJoin : Val (Val α) → Val α
  | origin => origin
  | container x => x
  | contents x => x

@[simp] theorem valJoin_origin : valJoin (origin : Val (Val α)) = origin := rfl
@[simp] theorem valJoin_container (x : Val α) : valJoin (container x) = x := rfl
@[simp] theorem valJoin_contents (x : Val α) : valJoin (contents x) = x := rfl

/-- Left unit: valJoin ∘ contents = id -/
theorem monad_left_unit : valJoin ∘ contents = (id : Val α → Val α) := by
  funext x; rfl

/-- Join is associative. -/
theorem monad_join_assoc :
    valJoin ∘ valJoin = valJoin ∘ valMap (valJoin : Val (Val α) → Val α) := by
  funext x; cases x with
  | origin => rfl
  | container y => cases y <;> rfl
  | contents y => cases y <;> rfl

/-- Right unit holds on origin and contents, not container (honest boundary). -/
theorem monad_right_unit_origin :
    valJoin (valMap (contents : α → Val α) (origin : Val α)) = origin := rfl

theorem monad_right_unit_contents (a : α) :
    valJoin (valMap (contents : α → Val α) (contents a)) = contents a := rfl

theorem monad_right_unit_container_flattens (a : α) :
    valJoin (valMap (contents : α → Val α) (container a)) = contents a := rfl

end Val
