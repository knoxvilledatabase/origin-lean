/-
Extracted from Order/Hom/Basic.lean
Genuine: 5 of 7 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Order homomorphisms

This file defines order homomorphisms, which are bundled monotone functions. A preorder
homomorphism `f : α →o β` is a function `α → β` along with a proof that `∀ x y, x ≤ y → f x ≤ f y`.

## Main definitions

In this file we define the following bundled monotone maps:
* `OrderHom α β` a.k.a. `α →o β`: Preorder homomorphism.
  An `OrderHom α β` is a function `f : α → β` such that `a₁ ≤ a₂ → f a₁ ≤ f a₂`
* `OrderEmbedding α β` a.k.a. `α ↪o β`: Relation embedding.
  An `OrderEmbedding α β` is an embedding `f : α ↪ β` such that `a ≤ b ↔ f a ≤ f b`.
  Defined as an abbreviation of `@RelEmbedding α β (≤) (≤)`.
* `OrderIso`: Relation isomorphism.
  An `OrderIso α β` is an equivalence `f : α ≃ β` such that `a ≤ b ↔ f a ≤ f b`.
  Defined as an abbreviation of `@RelIso α β (≤) (≤)`.

We also define many `OrderHom`s. In some cases we define two versions, one with `ₘ` suffix and
one without it (e.g., `OrderHom.compₘ` and `OrderHom.comp`). This means that the former
function is a "more bundled" version of the latter. We can't just drop the "less bundled" version
because the more bundled version usually does not work with dot notation.

* `OrderHom.id`: identity map as `α →o α`;
* `OrderHom.curry`: an order isomorphism between `α × β →o γ` and `α →o β →o γ`;
* `OrderHom.comp`: composition of two bundled monotone maps;
* `OrderHom.compₘ`: composition of bundled monotone maps as a bundled monotone map;
* `OrderHom.const`: constant function as a bundled monotone map;
* `OrderHom.prod`: combine `α →o β` and `α →o γ` into `α →o β × γ`;
* `OrderHom.prodₘ`: a more bundled version of `OrderHom.prod`;
* `OrderHom.prodIso`: order isomorphism between `α →o β × γ` and `(α →o β) × (α →o γ)`;
* `OrderHom.diag`: diagonal embedding of `α` into `α × α` as a bundled monotone map;
* `OrderHom.onDiag`: restrict a monotone map `α →o α →o β` to the diagonal;
* `OrderHom.fst`: projection `Prod.fst : α × β → α` as a bundled monotone map;
* `OrderHom.snd`: projection `Prod.snd : α × β → β` as a bundled monotone map;
* `OrderHom.prodMap`: `Prod.map f g` as a bundled monotone map;
* `Pi.evalOrderHom`: evaluation of a function at a point `Function.eval i` as a bundled
  monotone map;
* `OrderHom.coeFnHom`: coercion to function as a bundled monotone map;
* `OrderHom.apply`: application of an `OrderHom` at a point as a bundled monotone map;
* `OrderHom.pi`: combine a family of monotone maps `f i : α →o π i` into a monotone map
  `α →o Π i, π i`;
* `OrderHom.piIso`: order isomorphism between `α →o Π i, π i` and `Π i, α →o π i`;
* `OrderHom.subtype.val`: embedding `Subtype.val : Subtype p → α` as a bundled monotone map;
* `OrderHom.dual`: reinterpret a monotone map `α →o β` as a monotone map `αᵒᵈ →o βᵒᵈ`;
* `OrderHom.dualIso`: order isomorphism between `α →o β` and `(αᵒᵈ →o βᵒᵈ)ᵒᵈ`;
* `OrderHom.compl`: order isomorphism `α ≃o αᵒᵈ` given by taking complements in a
  Boolean algebra;

We also define two functions to convert other bundled maps to `α →o β`:

* `OrderEmbedding.toOrderHom`: convert `α ↪o β` to `α →o β`;
* `RelHom.toOrderHom`: convert a `RelHom` between strict orders to an `OrderHom`.

## Tags

monotone map, bundled morphism
-/

assert_not_imported Mathlib.Data.Set.Basic

open OrderDual

variable {F α β γ δ : Type*}

structure OrderHom (α β : Type*) [Preorder α] [Preorder β] where
  /-- The underlying function of an `OrderHom`. -/
  toFun : α → β
  /-- The underlying function of an `OrderHom` is monotone. -/
  monotone' : Monotone toFun

infixr:25 " →o " => OrderHom

abbrev OrderEmbedding (α β : Type*) [LE α] [LE β] :=
  @RelEmbedding α β (· ≤ ·) (· ≤ ·)

to_dual_insert_cast_fun OrderEmbedding :=

  fun ⟨iso, h⟩ ↦ ⟨iso, by rwa [forall_comm]⟩,

  fun ⟨iso, h⟩ ↦ ⟨iso, by rwa [forall_comm]⟩

infixl:25 " ↪o " => OrderEmbedding

abbrev OrderIso (α β : Type*) [LE α] [LE β] :=
  @RelIso α β (· ≤ ·) (· ≤ ·)

to_dual_insert_cast_fun OrderIso :=

  fun ⟨iso, h⟩ ↦ ⟨iso, by rwa [forall_comm]⟩,

  fun ⟨iso, h⟩ ↦ ⟨iso, by rwa [forall_comm]⟩

infixl:25 " ≃o " => OrderIso

-- INSTANCE (free from Core): (α

-- INSTANCE (free from Core): (α

abbrev OrderHomClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [FunLike F α β] :=
  RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop)

to_dual_insert_cast OrderHomClass := by grind only [RelHomClass]

class OrderIsoClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [EquivLike F α β] :
    Prop where
  /-- An order isomorphism respects `≤`. -/
  map_le_map_iff (f : F) {a b : α} : f a ≤ f b ↔ a ≤ b

attribute [to_dual self] OrderIsoClass.map_le_map_iff

end

export OrderIsoClass (map_le_map_iff)

attribute [simp] map_le_map_iff
