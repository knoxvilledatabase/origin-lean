/-
Extracted from CategoryTheory/Subobject/Basic.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Subobjects

We define `Subobject X` as the quotient (by isomorphisms) of
`MonoOver X := {f : Over X // Mono f.hom}`.

Here `MonoOver X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not a partial order.

There is a coercion from `Subobject X` back to the ambient category `C`
(using choice to pick a representative), and for `P : Subobject X`,
`P.arrow : (P : C) ⟶ X` is the inclusion morphism.

We provide
* `def pullback [HasPullbacks C] (f : X ⟶ Y) : Subobject Y ⥤ Subobject X`
* `def map (f : X ⟶ Y) [Mono f] : Subobject X ⥤ Subobject Y`
* `def «exists_» [HasImages C] (f : X ⟶ Y) : Subobject X ⥤ Subobject Y`

and prove their basic properties and relationships.
These are all easy consequences of the earlier development
of the corresponding functors for `MonoOver`.

The subobjects of `X` form a preorder making them into a category. We have `X ≤ Y` if and only if
`X.arrow` factors through `Y.arrow`: see `ofLE`/`ofLEMk`/`ofMkLE`/`ofMkLEMk` and
`le_of_comm`. Similarly, to show that two subobjects are equal, we can supply an isomorphism between
the underlying objects that commutes with the arrows (`eq_of_comm`).

See also

* `CategoryTheory.Subobject.factorThru` :
  an API describing factorization of morphisms through subobjects.
* `CategoryTheory.Subobject.lattice` :
  the lattice structures on subobjects.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Kim Morrison.

### Implementation note

Currently we describe `pullback`, `map`, etc., as functors.
It may be better to just say that they are monotone functions,
and even avoid using categorical language entirely when describing `Subobject X`.
(It's worth keeping this in mind in future use; it should be a relatively easy change here
if it looks preferable.)

### Relation to pseudoelements

There is a separate development of pseudoelements in `CategoryTheory.Abelian.Pseudoelements`,
as a quotient (but not by isomorphism) of `Over X`.

When a morphism `f` has an image, the image represents the same pseudoelement.
In a category with images `Pseudoelements X` could be constructed as a quotient of `MonoOver X`.
In fact, in an abelian category (I'm not sure in what generality beyond that),
`Pseudoelements X` agrees with `Subobject X`, but we haven't developed this in mathlib yet.

-/

universe w' w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

/-!
We now construct the subobject lattice for `X : C`,
as the quotient by isomorphisms of `MonoOver X`.

Since `MonoOver X` is a thin category, we use `ThinSkeleton` to take the quotient.

Essentially all the structure defined above on `MonoOver X` descends to `Subobject X`,
with morphisms becoming inequalities, and isomorphisms becoming equations.
-/

def Subobject (X : C) :=
  ThinSkeleton (MonoOver X)

-- INSTANCE (free from Core): (X

namespace Subobject

lemma skeletal (X : C) : Skeletal (Subobject X) := ThinSkeleton.skeletal

def mk {X A : C} (f : A ⟶ X) [Mono f] : Subobject X :=
  (toThinSkeleton _).obj (MonoOver.mk f)

attribute [local ext] CategoryTheory.Comma

protected theorem ind {X : C} (p : Subobject X → Prop)
    (h : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], p (Subobject.mk f)) (P : Subobject X) : p P := by
  induction P using Quotient.inductionOn' with | _ a
  exact h a.arrow

protected theorem ind₂ {X : C} (p : Subobject X → Subobject X → Prop)
    (h : ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g],
      p (Subobject.mk f) (Subobject.mk g))
    (P Q : Subobject X) : p P Q := by
  induction P, Q using Quotient.inductionOn₂' with | _ a b
  exact h a.arrow b.arrow

end

protected def lift {α : Sort*} {X : C} (F : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], α)
    (h :
      ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g] (i : A ≅ B),
        i.hom ≫ g = f → F f = F g) :
    Subobject X → α := fun P =>
  Quotient.liftOn' P (fun m => F m.arrow) fun m n ⟨i⟩ =>
    h m.arrow n.arrow ((MonoOver.forget X ⋙ Over.forget X).mapIso i) (Over.w i.hom.hom)
