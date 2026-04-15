/-
Extracted from CategoryTheory/Sites/Point/Map.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The image of a point by a cocontinuous functor

Let `F : C ⥤ D` be a cocontinuous functor between sites `(C, J)` and `(D, K)`.
Let `Φ` be a point of `(C, J)`. In this file, we define a point `Φ.map F K`
of `(D, K)` and show that there are natural isomorphisms
`(Φ.map F K).presheafFiber ≅ (Functor.whiskeringLeft _ _ A).obj F.op ⋙ Φ.presheafFiber`
and `(Φ.map F K).sheafFiber ≅ F.sheafPushforwardContinuous A J K ⋙ Φ.sheafFiber`
(the latter is defined only if `F` is also continuous).

-/

universe w v'' v' v u'' u' u

namespace CategoryTheory

open Limits Opposite

namespace GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} (Φ : Point.{w} J) (F : C ⥤ D)
  (K : GrothendieckTopology D) [F.IsCocontinuous J K]

lemma map_aux ⦃X : D⦄ (R : Sieve X) (hR : R ∈ K X)
    ⦃u : Φ.fiber.Elements⦄ (f : (CategoryOfElements.π Φ.fiber ⋙ F).obj u ⟶ X) :
    ∃ (Y : D) (g : Y ⟶ X) (_ : R.arrows g) (v : Φ.fiber.Elements)
      (q : v ⟶ u) (a : F.obj v.fst ⟶ Y), a ≫ g = F.map q.1 ≫ f := by
  obtain ⟨U, u⟩ := u
  dsimp at f ⊢
  obtain ⟨V, g, hg, v, rfl⟩ :=
    Φ.jointly_surjective _ (F.cover_lift J K (K.pullback_stable f hR)) u
  exact ⟨_, F.map g ≫ f, hg, Φ.fiber.elementsMk _ v, ⟨g, rfl⟩, 𝟙 _, by simp⟩

variable [LocallySmall.{w} D]

noncomputable def map : Point.{w} K :=
  Point.ofIsCofiltered.{w} (CategoryOfElements.π Φ.fiber ⋙ F) (Φ.map_aux F K)

variable {A : Type u''} [Category.{v''} A] [HasColimitsOfSize.{w, w} A]

noncomputable def toPresheafFiberMap (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) :
    P.obj (op (F.obj X)) ⟶ (Φ.map F K).presheafFiber.obj P :=
  toPresheafFiberOfIsCofiltered _ (Φ.map_aux F K) (Φ.fiber.elementsMk X x) P
