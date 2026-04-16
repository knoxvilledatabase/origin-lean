/-
Extracted from CategoryTheory/Category/KleisliCat.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.CategoryTheory.Category.Basic

noncomputable section

/-!
# The Kleisli construction on the Type category

Define the Kleisli category for (control) monads.
`CategoryTheory/Monad/Kleisli` defines the general version for a monad on `C`, and demonstrates
the equivalence between the two.

## TODO

Generalise this to work with CategoryTheory.Monad
-/

universe u v

namespace CategoryTheory

@[nolint unusedArguments]
def KleisliCat (_ : Type u → Type v) :=
  Type u

def KleisliCat.mk (m) (α : Type u) : KleisliCat m :=
  α

instance KleisliCat.categoryStruct {m} [Monad.{u, v} m] :
    CategoryStruct (KleisliCat m) where
  Hom α β := α → m β
  id _ x := pure x
  comp f g := f >=> g

instance KleisliCat.category {m} [Monad.{u, v} m] [LawfulMonad m] : Category (KleisliCat m) := by
  -- Porting note: was
  -- refine' { id_comp' := _, comp_id' := _, assoc' := _ } <;> intros <;> ext <;> unfold_projs <;>
  --  simp only [(· >=> ·), functor_norm]
  refine { id_comp := ?_, comp_id := ?_, assoc := ?_ } <;> intros <;>
  refine funext (fun x => ?_) <;>
  simp (config := { unfoldPartialApp := true }) [CategoryStruct.id, CategoryStruct.comp, (· >=> ·)]

instance : Inhabited (KleisliCat id) :=
  ⟨PUnit⟩

instance {α : Type u} [Inhabited α] : Inhabited (KleisliCat.mk id α) :=
  ⟨show α from default⟩

end CategoryTheory
