/-
Extracted from CategoryTheory/Sigma/Basic.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Disjoint union of categories

We define the category structure on a sigma-type (disjoint union) of categories.
-/

namespace CategoryTheory

namespace Sigma

universe w₁ w₂ w₃ v₁ v₂ u₁ u₂

variable {I : Type w₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]

inductive SigmaHom : (Σ i, C i) → (Σ i, C i) → Type max w₁ v₁ u₁
  | mk : ∀ {i : I} {X Y : C i}, (X ⟶ Y) → SigmaHom ⟨i, X⟩ ⟨i, Y⟩

namespace SigmaHom

def id : ∀ X : Σ i, C i, SigmaHom X X
  | ⟨_, _⟩ => mk (𝟙 _)

-- INSTANCE (free from Core): (X

def comp : ∀ {X Y Z : Σ i, C i}, SigmaHom X Y → SigmaHom Y Z → SigmaHom X Z
  | _, _, _, mk f, mk g => mk (f ≫ g)

-- INSTANCE (free from Core): :
