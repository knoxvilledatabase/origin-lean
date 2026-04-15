/-
Extracted from AlgebraicTopology/Quasicategory/TwoTruncated.lean
Genuine: 20 of 22 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# 2-truncated quasicategories and homotopy relations

We define 2-truncated quasicategories `Quasicategory₂` by three horn-filling properties,
and the left and right homotopy relations `HomotopicL` and `HomotopicR` on the edges in a
2-truncated simplicial set.

We prove that for 2-truncated quasicategories, both homotopy relations are equivalence
relations, and that the left and right homotopy relations coincide.

For a 2-truncated quasicategory `A`, we define a category `HomotopyCategory₂ A` whose
morphisms are given by (left) homotopy classes of edges. The construction of this category
is different from `HomotopyCategory A` in `AlgebraicTopology.SimplicialSet.HomotopyCat`:
* `HomotopyCategory₂ A` has morphisms given by homotopy classes of edges
* `HomotopyCategory A` has morphisms given by equivalence classes of paths in the underlying
  reflexive quiver of `A`.

The two constructions agree for 2-truncated quasicategories (TODO: handled by future PR).

## Implementation notes

Throughout this file, we make use of `Edge` and `CompStruct` to conveniently deal with
edges and triangles in a 2-truncated simplicial set.
-/

open CategoryTheory SimplicialObject.Truncated

namespace SSet.Truncated

open Edge CompStruct

class Quasicategory₂ (X : Truncated 2) where
  fill21 {x₀ x₁ x₂ : X _⦋0⦌₂}
      (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) :
      Nonempty (Σ e₀₂ : Edge x₀ x₂, CompStruct e₀₁ e₁₂ e₀₂)
  fill31 {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}
      {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
      {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
      (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
      (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
      (f₂ : CompStruct e₀₁ e₁₃ e₀₃) :
      Nonempty (CompStruct e₀₂ e₂₃ e₀₃)
  fill32 {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}
      {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
      {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
      (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
      (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
      (f₁ : CompStruct e₀₂ e₂₃ e₀₃) :
      Nonempty (CompStruct e₀₁ e₁₃ e₀₃)

abbrev HomotopicL {X : Truncated 2} {x y : X _⦋0⦌₂} (f g : Edge x y) :=
  Nonempty (CompStruct f (id y) g)

abbrev HomotopicR {X : Truncated 2} {x y : X _⦋0⦌₂} (f g : Edge x y) :=
  Nonempty (CompStruct (id x) f g)

section homotopy_eqrel

variable {X : Truncated 2}

lemma HomotopicL.refl {x y : X _⦋0⦌₂} {f : Edge x y} : HomotopicL f f := ⟨compId f⟩

lemma HomotopicL.symm [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicL f g) :
    HomotopicL g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill31 hfg (idComp (id y)) (compId f)

lemma HomotopicL.trans [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicL f g)
    (hgh : HomotopicL g h) : HomotopicL f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill32 hfg (idComp (id y)) hgh

lemma HomotopicR.refl {x y : X _⦋0⦌₂} {f : Edge x y} : HomotopicR f f := ⟨idComp f⟩

lemma HomotopicR.symm [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicR f g) :
    HomotopicR g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill32 (idComp (id x)) hfg (idComp f)

lemma HomotopicR.trans [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicR f g)
    (hgh : HomotopicR g h) : HomotopicR f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill31 (idComp (id x)) hfg hgh

lemma HomotopicL.homotopicR [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y}
    (h : HomotopicL f g) : HomotopicR f g := by
  rcases h with ⟨h⟩
  exact Quasicategory₂.fill32 (idComp f) (compId f) h

lemma HomotopicR.homotopicL [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y}
    (h : HomotopicR f g) : HomotopicL f g := by
  rcases h with ⟨h⟩
  exact Quasicategory₂.fill31 (idComp f) (compId f) h

theorem homotopicL_iff_homotopicR [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} :
    HomotopicL f g ↔ HomotopicR f g :=
  ⟨HomotopicL.homotopicR, HomotopicR.homotopicL⟩

end homotopy_eqrel

section homotopy_category

variable {A : Truncated 2} [Quasicategory₂ A] {x y z : A _⦋0⦌₂}

lemma Edge.CompStruct.comp_unique {f f' : Edge x y} {g g' : Edge y z} {h h' : Edge x z}
    (s : CompStruct f g h) (s' : CompStruct f' g' h')
    (hf : HomotopicL f f') (hg : HomotopicL g g') : HomotopicL h h' := by
  rcases hg.homotopicR with ⟨hg⟩
  rcases hf with ⟨hf⟩
  let ⟨s₁⟩ := Quasicategory₂.fill32 hf (idComp g') s'
  let ⟨s₂⟩ := Quasicategory₂.fill31 (compId f) hg s₁
  exact Quasicategory₂.fill31 s (compId g) s₂

noncomputable def Edge.comp (f : Edge x y) (g : Edge y z) : Edge x z :=
  (Quasicategory₂.fill21 f g).some.1

noncomputable def Edge.compStruct (f : Edge x y) (g : Edge y z) : CompStruct f g (f.comp g) :=
  (Quasicategory₂.fill21 f g).some.2

structure HomotopyCategory₂ (A : Truncated 2) where
  /-- An object of the homotopy category is a vertex of `A`. -/
  pt : A _⦋0⦌₂

-- INSTANCE (free from Core): instSetoidEdge

namespace HomotopyCategory₂

def Hom (x y : HomotopyCategory₂ A) := Quotient (instSetoidEdge x.pt y.pt)

noncomputable

-- INSTANCE (free from Core): :

omit [A.Quasicategory₂] in

lemma mk_surjective : Function.Surjective (mk : A _⦋0⦌₂ → _) :=
  fun ⟨x⟩ ↦ ⟨x, rfl⟩

def homMk (f : Edge x y) : mk x ⟶ mk y := ⟦f⟧

lemma homMk_surjective : Function.Surjective (homMk : Edge x y → _) := Quotient.mk_surjective
