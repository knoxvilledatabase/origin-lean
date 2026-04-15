/-
Extracted from AlgebraicTopology/RelativeCellComplex/AttachCells.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Attaching cells

Given a family of morphisms `g a : A a ⟶ B a` and a morphism `f : X₁ ⟶ X₂`,
we introduce a structure `AttachCells g f` which expresses that `X₂`
is obtained from `X₁` by attaching cells of the form `g a`. It means that
there is a pushout diagram of the form
```
⨿ i, A (π i) -----> X₁
  |                 |f
  v                 v
⨿ i, B (π i) -----> X₂
```
In other words, the morphism `f` is a pushout of coproducts of morphisms
of the form `g a : A a ⟶ B a`, see `nonempty_attachCells_iff`.

See the file `Mathlib/AlgebraicTopology/RelativeCellComplex/Basic.lean` for transfinite compositions
of morphisms `f` with `AttachCells g f` structures.

-/

universe w' w t t' v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]
  {α : Type t} {A B : α → C} (g : ∀ a, A a ⟶ B a)
  {X₁ X₂ : C} (f : X₁ ⟶ X₂)

structure AttachCells where
  /-- the index type of the cells -/
  ι : Type w
  /-- for each `i : ι`, we shall attach a cell given by the morphism `g (π i)`. -/
  π : ι → α
  /-- a colimit cofan which gives the coproduct of the object `A (π i)` -/
  cofan₁ : Cofan (fun i ↦ A (π i))
  /-- a colimit cofan which gives the coproduct of the object `B (π i)` -/
  cofan₂ : Cofan (fun i ↦ B (π i))
  /-- `cofan₁` is colimit -/
  isColimit₁ : IsColimit cofan₁
  /-- `cofan₂` is colimit -/
  isColimit₂ : IsColimit cofan₂
  /-- the coproduct of the maps `g (π i) : A (π i) ⟶ B (π i)` for all `i : ι`. -/
  m : cofan₁.pt ⟶ cofan₂.pt
  hm (i : ι) : cofan₁.inj i ≫ m = g (π i) ≫ cofan₂.inj i := by cat_disch
  /-- the top morphism of the pushout square -/
  g₁ : cofan₁.pt ⟶ X₁
  /-- the bottom morphism of the pushout square -/
  g₂ : cofan₂.pt ⟶ X₂
  isPushout : IsPushout g₁ m f g₂

namespace AttachCells

open MorphismProperty

attribute [reassoc (attr := simp)] hm

variable {g f} (c : AttachCells.{w} g f)

include c

lemma pushouts_coproducts : (coproducts.{w} (ofHoms g)).pushouts f := by
  refine ⟨_, _, _, _, _, ?_, c.isPushout⟩
  have : c.m = c.isColimit₁.desc
      (Cocone.mk _ (Discrete.natTrans (fun ⟨i⟩ ↦ by exact g (c.π i)) ≫ c.cofan₂.ι)) :=
    c.isColimit₁.hom_ext (fun ⟨i⟩ ↦ by rw [IsColimit.fac]; exact c.hm i)
  rw [this, coproducts_iff]
  exact ⟨c.ι, ⟨_, _, _, _, c.isColimit₁, c.isColimit₂, _, fun i ↦ ⟨_⟩⟩⟩

def cell (i : c.ι) : B (c.π i) ⟶ X₂ := c.cofan₂.inj i ≫ c.g₂
