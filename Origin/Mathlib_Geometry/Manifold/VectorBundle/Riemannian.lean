/-
Extracted from Geometry/Manifold/VectorBundle/Riemannian.lean
Genuine: 12 of 20 | Dissolved: 1 | Infrastructure: 7
-/
import Origin.Core

/-! # Riemannian vector bundles

Given a vector bundle over a manifold whose fibers are all endowed with a scalar product, we
say that this bundle is Riemannian if the scalar product depends smoothly on the base point.

We introduce a typeclass `[IsContMDiffRiemannianBundle IB n F E]` registering this property.
Under this assumption, we show that the scalar product of two smooth maps into the same fibers of
the bundle is a smooth function.

If the fibers of a bundle `E` have a preexisting topology (like the tangent bundle), one cannot
assume additionally `[∀ b, InnerProductSpace ℝ (E b)]` as this would create diamonds. Instead,
use `[RiemannianBundle E]`, which endows the fibers with a scalar product while ensuring that
there is no diamond (for this, the `Bundle` scope should be open). We provide a
constructor for `[RiemannianBundle E]` from a smooth family of metrics, which registers
automatically `[IsContMDiffRiemannianBundle IB n F E]`.

The following code block is the standard way to say "Let `E` be a smooth vector bundle equipped with
a `C^n` Riemannian structure over a `C^n` manifold `B`":
```
variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffRiemannianBundle IB n F E]
```
-/

open Manifold Bundle ContinuousLinearMap ENat Bornology

open scoped ContDiff Topology

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable (IB n F E) in

class IsContMDiffRiemannianBundle : Prop where
  exists_contMDiff : ∃ g : Π (x : B), E x →L[ℝ] E x →L[ℝ] ℝ,
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g b))
    ∧ ∀ (x : B) (v w : E x), ⟪v, w⟫ = g x v w

lemma IsContMDiffRiemannianBundle.of_le [h : IsContMDiffRiemannianBundle IB n F E] (h' : n' ≤ n) :
    IsContMDiffRiemannianBundle IB n' F E := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  exact ⟨g, g_smooth.of_le h', hg⟩

-- INSTANCE (free from Core): {a

-- INSTANCE (free from Core): {a

-- INSTANCE (free from Core): [IsContMDiffRiemannianBundle

-- INSTANCE (free from Core): [IsContMDiffRiemannianBundle

-- INSTANCE (free from Core): [IsContMDiffRiemannianBundle

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

end Trivial

section ContMDiff

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffRiemannianBundle IB n F E]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

lemma ContMDiffWithinAt.inner_bundle
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ ⟪v m, w m⟫) s x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : ContMDiffWithinAt IM IB n b s x := by
    simp only [contMDiffWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact ContMDiffAt.comp_contMDiffWithinAt x g_smooth.contMDiffAt hb
    · exact hv
    · exact hw
  simp only [contMDiffWithinAt_totalSpace] at this
  exact this.2

lemma ContMDiffAt.inner_bundle
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun b ↦ ⟪v b, w b⟫) x :=
  ContMDiffWithinAt.inner_bundle hv hw

lemma ContMDiffOn.inner_bundle
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun b ↦ ⟪v b, w b⟫) s :=
  fun x hx ↦ (hv x hx).inner_bundle (hw x hx)

lemma ContMDiff.inner_bundle
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E))) :
    CMDiff n (fun b ↦ ⟪v b, w b⟫) :=
  fun x ↦ (hv x).inner_bundle (hw x)

end ContMDiff

section MDifferentiable

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [h : IsContMDiffRiemannianBundle IB 1 F E]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

lemma MDifferentiableWithinAt.inner_bundle
    (hv : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E)) s x) :
    MDiffAt[s] (fun m ↦ ⟪v m, w m⟫) x := by
  rcases h.exists_contMDiff with ⟨g, g_smooth, hg⟩
  have hb : MDifferentiableWithinAt IM IB b s x := by
    simp only [mdifferentiableWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : MDifferentiableWithinAt IM (IB.prod 𝓘(ℝ))
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x := by
    apply MDifferentiableWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
    · exact MDifferentiableAt.comp_mdifferentiableWithinAt x
        (g_smooth.mdifferentiableAt one_ne_zero) hb
    · exact hv
    · exact hw
  simp only [mdifferentiableWithinAt_totalSpace] at this
  exact this.2

lemma MDifferentiableAt.inner_bundle
    (hv : MDifferentiableAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : MDifferentiableAt IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E)) x) :
    MDiffAt (fun b ↦ ⟪v b, w b⟫) x :=
  MDifferentiableWithinAt.inner_bundle hv hw

lemma MDifferentiableOn.inner_bundle
    (hv : MDifferentiableOn IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : MDifferentiableOn IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E)) s) :
    MDiff[s] (fun b ↦ ⟪v b, w b⟫) :=
  fun x hx ↦ (hv x hx).inner_bundle (hw x hx)

lemma MDifferentiable.inner_bundle
    (hv : MDifferentiable IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (v m : TotalSpace F E)))
    (hw : MDifferentiable IM (IB.prod 𝓘(ℝ, F)) (fun m ↦ (w m : TotalSpace F E))) :
    MDiff (fun b ↦ ⟪v b, w b⟫) :=
  fun x ↦ (hv x).inner_bundle (hw x)

end MDifferentiable

end

namespace Bundle

section Construction

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in

-- DISSOLVED: ContMDiffRiemannianMetric

def ContMDiffRiemannianMetric.toContinuousRiemannianMetric
    (g : ContMDiffRiemannianMetric IB n F E) : ContinuousRiemannianMetric F E :=
  { g with continuous := g.contMDiff.continuous }

def ContMDiffRiemannianMetric.toRiemannianMetric
    (g : ContMDiffRiemannianMetric IB n F E) : RiemannianMetric E :=
  g.toContinuousRiemannianMetric.toRiemannianMetric

-- INSTANCE (free from Core): (g

end Construction

end Bundle
