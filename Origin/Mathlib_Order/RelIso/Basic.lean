/-
Extracted from Order/RelIso/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relation homomorphisms, embeddings, isomorphisms

This file defines relation homomorphisms, embeddings, isomorphisms and order embeddings and
isomorphisms.

## Main declarations

* `RelHom`: Relation homomorphism. A `RelHom r s` is a function `f : α → β` such that
  `r a b → s (f a) (f b)`.
* `RelEmbedding`: Relation embedding. A `RelEmbedding r s` is an embedding `f : α ↪ β` such that
  `r a b ↔ s (f a) (f b)`.
* `RelIso`: Relation isomorphism. A `RelIso r s` is an equivalence `f : α ≃ β` such that
  `r a b ↔ s (f a) (f b)`.
* `sumLexCongr`, `prodLexCongr`: Creates a relation homomorphism between two `Sum.Lex` or two
  `Prod.Lex` from relation homomorphisms between their arguments.

## Notation

* `→r`: `RelHom`
* `↪r`: `RelEmbedding`
* `≃r`: `RelIso`
-/

open Function

universe u v w

variable {α β γ δ : Type*} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop} {u : δ → δ → Prop}

structure RelHom {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) where
  /-- The underlying function of a `RelHom` -/
  toFun : α → β
  /-- A `RelHom` sends related elements to related elements -/
  map_rel' : ∀ {a b}, r a b → s (toFun a) (toFun b)

infixl:25 " →r " => RelHom

class RelHomClass (F : Type*) {α β : outParam Type*} (r : outParam <| α → α → Prop)
  (s : outParam <| β → β → Prop) [FunLike F α β] : Prop where
  /-- A `RelHomClass` sends related elements to related elements -/
  map_rel : ∀ (f : F) {a b}, r a b → s (f a) (f b)

export RelHomClass (map_rel)

end

namespace RelHomClass

variable {F : Type*} [FunLike F α β]

protected theorem irrefl [RelHomClass F r s] (f : F) : ∀ [Std.Irrefl s], Std.Irrefl r
  | ⟨H⟩ => ⟨fun _ h => H _ (map_rel f h)⟩
