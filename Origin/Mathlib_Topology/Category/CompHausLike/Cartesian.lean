/-
Extracted from Topology/Category/CompHausLike/Cartesian.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cartesian monoidal structure on `CompHausLike`

If the predicate `P` is preserved under taking type-theoretic products and `PUnit` satisfies it,
then `CompHausLike P` is a cartesian monoidal category.

If the predicate `P` is preserved under taking type-theoretic sums, we provide an explicit coproduct
cocone in `CompHausLike P`. When we have the dual of `CartesianMonoidalCategory`, this can be used
to provide an instance of that on `CompHausLike P`.
-/

universe u

open CategoryTheory Limits

namespace CompHausLike

variable {P : TopCat.{u} → Prop} (X Y : CompHausLike.{u} P)

section Product

variable [HasProp P (X × Y)]

def productCone : BinaryFan X Y :=
  BinaryFan.mk (P := CompHausLike.of P (X × Y))
    (ofHom _ { toFun := Prod.fst }) (ofHom _ { toFun := Prod.snd })

def productIsLimit : IsLimit (productCone X Y) := by
  refine BinaryFan.isLimitMk (fun s ↦ ofHom _ { toFun x := (s.fst x, s.snd x) })
    (by rfl_cat) (by rfl_cat) fun _ _ h₁ h₂ ↦ ?_
  ext x
  exacts [ConcreteCategory.congr_hom h₁ _, ConcreteCategory.congr_hom h₂ _]
