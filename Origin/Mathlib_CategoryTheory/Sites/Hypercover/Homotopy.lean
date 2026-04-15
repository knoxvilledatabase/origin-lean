/-
Extracted from CategoryTheory/Sites/Hypercover/Homotopy.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The category of `1`-hypercovers up to homotopy

In this file we define the category of `1`-hypercovers up to homotopy. This is the category of
`1`-hypercovers, but where morphisms are considered up to existence of a homotopy.

## Main definitions

- `CategoryTheory.PreOneHypercover.Homotopy`: A homotopy of refinements `E ⟶ F` is a family of
  morphisms `Xᵢ ⟶ Yₐ` where `Yₐ` is a component of the cover of `X_{f(i)} ×[S] X_{g(i)}`.
- `CategoryTheory.GrothendieckTopology.HOneHypercover`: The category of `1`-hypercovers
  with respect to a Grothendieck topology and morphisms up to homotopy.

## Main results

- `CategoryTheory.GrothendieckTopology.HOneHypercover.isCofiltered_of_hasPullbacks`: The
  category of `1`-hypercovers up to homotopy is cofiltered if `C` has pullbacks.
-/

universe w'' w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace PreOneHypercover

variable {S : C} {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S}

structure Homotopy (f g : E.Hom F) where
  /-- The index map sending `i : E.I₀` to `a` above `(f(i), g(i))`. -/
  H (i : E.I₀) : F.I₁ (f.s₀ i) (g.s₀ i)
  /-- The morphism `Xᵢ ⟶ Yₐ`. -/
  a (i : E.I₀) : E.X i ⟶ F.Y (H i)
  wl (i : E.I₀) : a i ≫ F.p₁ (H i) = f.h₀ i
  wr (i : E.I₀) : a i ≫ F.p₂ (H i) = g.h₀ i

attribute [reassoc (attr := simp)] Homotopy.wl Homotopy.wr

variable {A : Type*} [Category* A]

set_option backward.isDefEq.respectTransparency false in

lemma Homotopy.mapMultiforkOfIsLimit_eq
    {E F : PreOneHypercover.{w} S} {f g : E.Hom F} (H : Homotopy f g)
    (P : Cᵒᵖ ⥤ A) {c : Multifork (E.multicospanIndex P)} (hc : IsLimit c)
    (d : Multifork (F.multicospanIndex P)) :
    f.mapMultiforkOfIsLimit P hc d = g.mapMultiforkOfIsLimit P hc d := by
  refine Multifork.IsLimit.hom_ext hc fun a ↦ ?_
  have heq := d.condition ⟨⟨(f.s₀ a), (g.s₀ a)⟩, H.H a⟩
  simp only [multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
    multicospanIndex_fst, multicospanShape_snd, multicospanIndex_snd] at heq
  simp [-Homotopy.wl, -Homotopy.wr, ← H.wl, ← H.wr, reassoc_of% heq]

set_option backward.isDefEq.respectTransparency false in

def Homotopy.isLimitMultifork (f : E.Hom F) (g : F.Hom E) (hgf : Homotopy (g.comp f) (.id F))
    {G : Cᵒᵖ ⥤ A} (hE : IsLimit (E.multifork G)) :
    IsLimit (F.multifork G) := by
  refine Multifork.IsLimit.mk _ ?_ ?_ ?_
  · intro t
    refine Multifork.IsLimit.lift hE (fun a ↦ t.ι (f.s₀ a) ≫ G.map (f.h₀ a).op) ?_
    intro b
    dsimp
    simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
    rw [← f.w₁₁, ← f.w₁₂]
    simp only [op_comp, Functor.map_comp]
    exact t.condition_assoc ⟨(f.s₀ b.1.1, f.s₀ b.1.2), f.s₁ b.2⟩ _
  · intro t i
    simp only [multicospanIndex_left, multicospanShape_L, multifork_ι]
    have h1 := hgf.wl i
    have h2 := t.condition ⟨⟨_, _⟩, hgf.H i⟩
    dsimp at h1 h2
    rw [← g.w₀, op_comp, Functor.map_comp, ← E.multifork_ι, Multifork.IsLimit.fac_assoc,
      Category.assoc, ← Functor.map_comp, ← op_comp, ← h1, op_comp, Functor.map_comp,
      reassoc_of% h2, ← Functor.map_comp, ← op_comp, hgf.wr i]
    simp
  · intro t m hm
    refine Multifork.IsLimit.hom_ext hE fun i ↦ ?_
    rw [Multifork.IsLimit.fac, multifork_ι, ← f.w₀, op_comp, Functor.map_comp, ← F.multifork_ι,
      reassoc_of% hm]

def Homotopy.isLimitMultiforkEquiv (f : E.Hom F) (g : F.Hom E)
    (hfg : Homotopy (f.comp g) (.id E)) (hgf : Homotopy (g.comp f) (.id F)) {G : Cᵒᵖ ⥤ A} :
    IsLimit (E.multifork G) ≃ IsLimit (F.multifork G) where
  toFun h := hgf.isLimitMultifork _ _ h
  invFun h := hfg.isLimitMultifork _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end

variable [Limits.HasPullbacks C] (f g : E.Hom F)

noncomputable

abbrev cylinderX {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : C :=
  pullback (pullback.lift (f.h₀ i) (g.h₀ i) (by simp)) (F.toPullback k)

noncomputable

abbrev cylinderf {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : cylinderX f g k ⟶ S :=
  pullback.fst _ _ ≫ E.f _
