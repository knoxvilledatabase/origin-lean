/-
Extracted from Combinatorics/Quiver/SingleObj.lean
Genuine: 13 | Conflates: 0 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core
import Mathlib.Combinatorics.Quiver.Cast
import Mathlib.Combinatorics.Quiver.Symmetric

noncomputable section

/-!
# Single-object quiver

Single object quiver with a given arrows type.

## Main definitions

Given a type `α`, `SingleObj α` is the `Unit` type, whose single object is called `star α`, with
`Quiver` structure such that `star α ⟶ star α` is the type `α`.
An element `x : α` can be reinterpreted as an element of `star α ⟶ star α` using
`toHom`.
More generally, a list of elements of `a` can be reinterpreted as a path from `star α` to
itself using `pathEquivList`.
-/

namespace Quiver

@[nolint unusedArguments]
def SingleObj (_ : Type*) : Type :=
  Unit

instance {α : Type*} : Unique (SingleObj α) where
  default := ⟨⟩
  uniq := fun _ => rfl

namespace SingleObj

variable (α β γ : Type*)

instance : Quiver (SingleObj α) :=
  ⟨fun _ _ => α⟩

def star : SingleObj α :=
  Unit.unit

instance : Inhabited (SingleObj α) :=
  ⟨star α⟩

variable {α β γ}

lemma ext {x y : SingleObj α} : x = y := Unit.ext x y

abbrev hasReverse (rev : α → α) : HasReverse (SingleObj α) := ⟨rev⟩

abbrev hasInvolutiveReverse (rev : α → α) (h : Function.Involutive rev) :
    HasInvolutiveReverse (SingleObj α) where
  toHasReverse := hasReverse rev
  inv' := h

@[simps!]
def toHom : α ≃ (star α ⟶ star α) :=
  Equiv.refl _

@[simps]
def toPrefunctor : (α → β) ≃ SingleObj α ⥤q SingleObj β where
  toFun f := ⟨id, f⟩
  invFun f a := f.map (toHom a)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem toPrefunctor_symm_id : toPrefunctor.symm (𝟭q (SingleObj α)) = id :=
  rfl

theorem toPrefunctor_comp (f : α → β) (g : β → γ) :
    toPrefunctor (g ∘ f) = toPrefunctor f ⋙q toPrefunctor g :=
  rfl

@[simp]
theorem toPrefunctor_symm_comp (f : SingleObj α ⥤q SingleObj β) (g : SingleObj β ⥤q SingleObj γ) :
    toPrefunctor.symm (f ⋙q g) = toPrefunctor.symm g ∘ toPrefunctor.symm f := by
  simp only [Equiv.symm_apply_eq, toPrefunctor_comp, Equiv.apply_symm_apply]

def pathToList : ∀ {x : SingleObj α}, Path (star α) x → List α
  | _, Path.nil => []
  | _, Path.cons p a => a :: pathToList p

@[simp]
def listToPath : List α → Path (star α) (star α)
  | [] => Path.nil
  | a :: l => (listToPath l).cons a

theorem listToPath_pathToList {x : SingleObj α} (p : Path (star α) x) :
    listToPath (pathToList p) = p.cast rfl ext := by
  induction p with
  | nil => rfl
  | cons _ _ ih => dsimp at *; rw [ih]

theorem pathToList_listToPath (l : List α) : pathToList (listToPath l) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => change a :: pathToList (listToPath l) = a :: l; rw [ih]

def pathEquivList : Path (star α) (star α) ≃ List α :=
  ⟨pathToList, listToPath, fun p => listToPath_pathToList p, pathToList_listToPath⟩

@[simp]
theorem pathEquivList_nil : pathEquivList Path.nil = ([] : List α) :=
  rfl

@[simp]
theorem pathEquivList_cons (p : Path (star α) (star α)) (a : star α ⟶ star α) :
    pathEquivList (Path.cons p a) = a :: pathToList p :=
  rfl

@[simp]
theorem pathEquivList_symm_nil : pathEquivList.symm ([] : List α) = Path.nil :=
  rfl

@[simp]
theorem pathEquivList_symm_cons (l : List α) (a : α) :
    pathEquivList.symm (a :: l) = Path.cons (pathEquivList.symm l) a :=
  rfl

end SingleObj

end Quiver
