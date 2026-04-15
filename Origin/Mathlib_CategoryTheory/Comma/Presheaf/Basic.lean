/-
Extracted from CategoryTheory/Comma/Presheaf/Basic.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Computation of `Over A` for a presheaf `A`

Let `A : Cᵒᵖ ⥤ Type v` be a presheaf. In this file, we construct an equivalence
`e : Over A ≌ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` and show that there is a quasi-commutative
diagram

```
CostructuredArrow yoneda A      ⥤      Over A

                             ⇘           ⥥

                               PSh(CostructuredArrow yoneda A)
```

where the top arrow is the forgetful functor forgetting the yoneda-costructure, the right arrow is
the aforementioned equivalence and the diagonal arrow is the Yoneda embedding.

In the notation of Kashiwara-Schapira, the type of the equivalence is written `C^ₐ ≌ Cₐ^`, where
`·ₐ` is `CostructuredArrow` (with the functor `S` being either the identity or the Yoneda
embedding) and `^` is taking presheaves. The equivalence is a key ingredient in various results in
Kashiwara-Schapira.

The proof is somewhat long and technical, in part due to the construction inherently involving a
sigma type which comes with the usual DTT issues. However, a user of this result should not need
to interact with the actual construction, the mere existence of the equivalence and the commutative
triangle should generally be sufficient.

## Main results
* `overEquivPresheafCostructuredArrow`:
  the equivalence `Over A ≌ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v`
* `CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow`: the natural isomorphism
  `CostructuredArrow.toOver yoneda A ⋙ (overEquivPresheafCostructuredArrow A).functor ≅ yoneda`

## Implementation details

The proof needs to introduce "correction terms" in various places in order to overcome DTT issues,
and these need to be canceled against each other when appropriate. It is important to deal with
these in a structured manner, otherwise you get large goals containing many correction terms which
are very tedious to manipulate. We avoid this blowup by carefully controlling which definitions
`(d)simp` is allowed to unfold and stating many lemmas explicitly before they are required. This
leads to manageable goals containing only a small number of correction terms. Generally, we use
the form `F.map (eqToHom _)` for these correction terms and try to push them as far outside as
possible.

## Future work
* If needed, it should be possible to show that the equivalence is natural in `A`.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Lemma 1.4.12

## Tags
presheaf, over category, coyoneda

-/

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}

namespace OverPresheafAux

/-! ### Construction of the forward functor `Over A ⥤ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` -/

structure MakesOverArrow {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A)
    (u : F.obj (op X)) : Prop where
  app : η.app (op X) u = yonedaEquiv s

namespace MakesOverArrow

lemma map₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {ε : F ⟶ G}
    (hε : ε ≫ μ = η) {X : C} {s : yoneda.obj X ⟶ A} {u : F.obj (op X)}
    (h : MakesOverArrow η s u) : MakesOverArrow μ s (ε.app _ u) :=
  ⟨by rw [← comp_apply, ← NatTrans.comp_app, hε, h.app]⟩

lemma map₂ {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
    {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (hst : yoneda.map f ≫ t = s)
    {u : F.obj (op Y)} (h : MakesOverArrow η t u) : MakesOverArrow η s (F.map f.op u) :=
  ⟨by simp [h.app, yonedaEquiv_naturality, hst]⟩

lemma of_arrow {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    {f : yoneda.obj X ⟶ F} (hf : f ≫ η = s) : MakesOverArrow η s (yonedaEquiv f) :=
  ⟨hf ▸ rfl⟩

lemma of_yoneda_arrow {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
    (hf : yoneda.map f ≫ η = s) : MakesOverArrow η s f := by
  simpa only [yonedaEquiv_yoneda_map f] using of_arrow hf

end MakesOverArrow

def OverArrows {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) : Type v :=
  Subtype (MakesOverArrow η s)

namespace OverArrows

def val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} :
    OverArrows η s → F.obj (op X) :=
  Subtype.val
