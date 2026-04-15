/-
Extracted from Logic/Embedding/Basic.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Injective functions
-/

universe u v w x

namespace Function

structure Embedding (α : Sort*) (β : Sort*) where
  /-- An embedding as a function. Use coercion instead. -/
  toFun : α → β
  /-- An embedding is an injective function. Use `Function.Embedding.injective` instead. -/
  inj' : Injective toFun

infixr:25 " ↪ " => Embedding

-- INSTANCE (free from Core): {α

-- INSTANCE (free from Core): {α

initialize_simps_projections Embedding (toFun → apply)

-- INSTANCE (free from Core): {α

theorem exists_surjective_iff {α β : Sort*} :
    (∃ f : α → β, Surjective f) ↔ Nonempty (α → β) ∧ Nonempty (β ↪ α) :=
  ⟨fun ⟨f, h⟩ ↦ ⟨⟨f⟩, ⟨⟨_, injective_surjInv h⟩⟩⟩, fun ⟨h, ⟨e⟩⟩ ↦ (nonempty_fun.mp h).elim
    (fun _ ↦ ⟨isEmptyElim, (isEmptyElim <| e ·)⟩) fun _ ↦ ⟨_, invFun_surjective e.inj'⟩⟩

end Function

namespace Equiv

variable {α : Sort u} {β : Sort v} (f : α ≃ β)
