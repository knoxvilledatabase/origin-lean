/-
Extracted from CategoryTheory/SmallObject/Construction.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Construction for the small object argument

Given a family of morphisms `f i : A i ⟶ B i` in a category `C`,
we define a functor
`SmallObject.functor f : Arrow S ⥤ Arrow S` which sends
an object given by arrow `πX : X ⟶ S` to the pushout `functorObj f πX`:
```
∐ functorObjSrcFamily f πX ⟶       X

            |                      |
            |                      |
            v                      v

∐ functorObjTgtFamily f πX ⟶ functorObj f πX
```
where the morphism on the left is a coproduct (of copies of maps `f i`)
indexed by a type `FunctorObjIndex f πX` which parametrizes the
diagrams of the form
```
A i ⟶ X
 |    |
 |    |
 v    v
B i ⟶ S
```

The morphism `ιFunctorObj f πX : X ⟶ functorObj f πX` is part of
a natural transformation `SmallObject.ε f : 𝟭 (Arrow C) ⟶ functor f S`.
The main idea in this construction is that for any commutative square
as above, there may not exist a lifting `B i ⟶ X`, but the construction
provides a tautological morphism `B i ⟶ functorObj f πX`
(see `SmallObject.ιFunctorObj_extension`).

## References
- https://ncatlab.org/nlab/show/small+object+argument

-/

universe t w v u

namespace CategoryTheory

open Category Limits HomotopicalAlgebra

namespace SmallObject

variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I → C} (f : ∀ i, A i ⟶ B i)

variable {S X : C} (πX : X ⟶ S)

structure FunctorObjIndex where
  /-- an element in the index type -/
  i : I
  /-- the top morphism in the square -/
  t : A i ⟶ X
  /-- the bottom morphism in the square -/
  b : B i ⟶ S
  w : t ≫ πX = f i ≫ b

attribute [reassoc (attr := simp)] FunctorObjIndex.w

variable [HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]

abbrev functorObjSrcFamily (x : FunctorObjIndex f πX) : C := A x.i

abbrev functorObjTgtFamily (x : FunctorObjIndex f πX) : C := B x.i

abbrev functorObjLeftFamily (x : FunctorObjIndex f πX) :
    functorObjSrcFamily f πX x ⟶ functorObjTgtFamily f πX x := f x.i

noncomputable abbrev functorObjTop : ∐ functorObjSrcFamily f πX ⟶ X :=
  Limits.Sigma.desc (fun x => x.t)

noncomputable abbrev functorObjLeft :
    ∐ functorObjSrcFamily f πX ⟶ ∐ functorObjTgtFamily f πX :=
  Limits.Sigma.map (functorObjLeftFamily f πX)

variable [HasPushout (functorObjTop f πX) (functorObjLeft f πX)]

noncomputable abbrev functorObj : C :=
  pushout (functorObjTop f πX) (functorObjLeft f πX)

noncomputable abbrev ιFunctorObj : X ⟶ functorObj f πX := pushout.inl _ _

noncomputable abbrev ρFunctorObj : ∐ functorObjTgtFamily f πX ⟶ functorObj f πX := pushout.inr _ _
