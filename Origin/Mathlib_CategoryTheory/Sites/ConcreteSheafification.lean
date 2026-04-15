/-
Extracted from CategoryTheory/Sites/ConcreteSheafification.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Sheafification

We construct the sheafification of a presheaf over a site `C` with values in `D` whenever
`D` is a concrete category for which the forgetful functor preserves the appropriate (co)limits
and reflects isomorphisms.

We generally follow the approach of https://stacks.math.columbia.edu/tag/00W1

-/

namespace CategoryTheory

open CategoryTheory.Limits Opposite

universe t w' w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable {D : Type w} [Category.{w'} D]

variable {FD : D → D → Type*} {CD : D → Type t} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]

variable [ConcreteCategory.{t} D FD]

def Meq {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) :=
  { x : ∀ I : S.Arrow, ToType (P.obj (op I.Y)) //
    ∀ I : S.Relation, P.map I.r.g₁.op (x I.fst) = P.map I.r.g₂.op (x I.snd) }

end

namespace Meq

variable {FD : D → D → Type*} {CD : D → Type t} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]

variable [ConcreteCategory.{t} D FD]

-- INSTANCE (free from Core): {X}

lemma congr_apply {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) {Y}
    {f g : Y ⟶ X} (h : f = g) (hf : S f) :
    x ⟨_, _, hf⟩ = x ⟨_, g, by simpa only [← h] using hf⟩ := by
  subst h
  rfl
