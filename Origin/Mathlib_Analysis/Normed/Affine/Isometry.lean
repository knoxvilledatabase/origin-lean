/-
Extracted from Analysis/Normed/Affine/Isometry.lean
Genuine: 94 | Conflates: 0 | Dissolved: 0 | Infrastructure: 53
-/
import Origin.Core
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.AffineSpace.Restrict
import Mathlib.Tactic.FailIfNoProgress

noncomputable section

/-!
# Affine isometries

In this file we define `AffineIsometry 𝕜 P P₂` to be an affine isometric embedding of normed
add-torsors `P` into `P₂` over normed `𝕜`-spaces and `AffineIsometryEquiv` to be an affine
isometric equivalence between `P` and `P₂`.

We also prove basic lemmas and provide convenience constructors.  The choice of these lemmas and
constructors is closely modelled on those for the `LinearIsometry` and `AffineMap` theories.

Since many elementary properties don't require `‖x‖ = 0 → x = 0` we initially set up the theory for
`SeminormedAddCommGroup` and specialize to `NormedAddCommGroup` only when needed.

## Notation

We introduce the notation `P →ᵃⁱ[𝕜] P₂` for `AffineIsometry 𝕜 P P₂`, and `P ≃ᵃⁱ[𝕜] P₂` for
`AffineIsometryEquiv 𝕜 P P₂`.  In contrast with the notation `→ₗᵢ` for linear isometries, `≃ᵢ`
for isometric equivalences, etc., the "i" here is a superscript.  This is for aesthetic reasons to
match the superscript "a" (note that in mathlib `→ᵃ` is an affine map, since `→ₐ` has been taken by
algebra-homomorphisms.)

-/

open Function Set

variable (𝕜 : Type*) {V V₁ V₁' V₂ V₃ V₄ : Type*} {P₁ P₁' : Type*} (P P₂ : Type*) {P₃ P₄ : Type*}
  [NormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [SeminormedAddCommGroup V₁] [NormedSpace 𝕜 V₁] [PseudoMetricSpace P₁] [NormedAddTorsor V₁ P₁]
  [SeminormedAddCommGroup V₁'] [NormedSpace 𝕜 V₁'] [MetricSpace P₁'] [NormedAddTorsor V₁' P₁']
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂]
  [SeminormedAddCommGroup V₃] [NormedSpace 𝕜 V₃] [PseudoMetricSpace P₃] [NormedAddTorsor V₃ P₃]
  [SeminormedAddCommGroup V₄] [NormedSpace 𝕜 V₄] [PseudoMetricSpace P₄] [NormedAddTorsor V₄ P₄]

structure AffineIsometry extends P →ᵃ[𝕜] P₂ where
  norm_map : ∀ x : V, ‖linear x‖ = ‖x‖

variable {𝕜 P P₂}

notation:25 -- `→ᵃᵢ` would be more consistent with the linear isometry notation, but it is uglier

P " →ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometry 𝕜 P P₂

namespace AffineIsometry

variable (f : P →ᵃⁱ[𝕜] P₂)

protected def linearIsometry : V →ₗᵢ[𝕜] V₂ :=
  { f.linear with norm_map' := f.norm_map }

@[simp]
theorem linear_eq_linearIsometry : f.linear = f.linearIsometry.toLinearMap := by
  ext
  rfl

instance : FunLike (P →ᵃⁱ[𝕜] P₂) P P₂ where
  coe f := f.toFun
  coe_injective' f g := by cases f; cases g; simp

theorem toAffineMap_injective : Injective (toAffineMap : (P →ᵃⁱ[𝕜] P₂) → P →ᵃ[𝕜] P₂) := by
  rintro ⟨f, _⟩ ⟨g, _⟩ rfl
  rfl

theorem coeFn_injective : @Injective (P →ᵃⁱ[𝕜] P₂) (P → P₂) (↑) :=
  AffineMap.coeFn_injective.comp toAffineMap_injective

@[ext]
theorem ext {f g : P →ᵃⁱ[𝕜] P₂} (h : ∀ x, f x = g x) : f = g :=
  coeFn_injective <| funext h

end AffineIsometry

namespace LinearIsometry

variable (f : V →ₗᵢ[𝕜] V₂)

def toAffineIsometry : V →ᵃⁱ[𝕜] V₂ :=
  { f.toLinearMap.toAffineMap with norm_map := f.norm_map }

@[simp]
theorem toAffineIsometry_linearIsometry : f.toAffineIsometry.linearIsometry = f := by
  ext
  rfl

end LinearIsometry

namespace AffineIsometry

variable (f : P →ᵃⁱ[𝕜] P₂) (f₁ : P₁' →ᵃⁱ[𝕜] P₂)

@[simp]
theorem map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.linearIsometry v +ᵥ f p :=
  f.toAffineMap.map_vadd p v

@[simp]
theorem map_vsub (p1 p2 : P) : f.linearIsometry (p1 -ᵥ p2) = f p1 -ᵥ f p2 :=
  f.toAffineMap.linearMap_vsub p1 p2

@[simp]
theorem dist_map (x y : P) : dist (f x) (f y) = dist x y := by
  rw [dist_eq_norm_vsub V₂, dist_eq_norm_vsub V, ← map_vsub, f.linearIsometry.norm_map]

@[simp]
theorem nndist_map (x y : P) : nndist (f x) (f y) = nndist x y := by simp [nndist_dist]

@[simp]
theorem edist_map (x y : P) : edist (f x) (f y) = edist x y := by simp [edist_dist]

protected theorem isometry : Isometry f :=
  f.edist_map

protected theorem injective : Injective f₁ :=
  f₁.isometry.injective

@[simp]
theorem map_eq_iff {x y : P₁'} : f₁ x = f₁ y ↔ x = y :=
  f₁.injective.eq_iff

theorem map_ne {x y : P₁'} (h : x ≠ y) : f₁ x ≠ f₁ y :=
  f₁.injective.ne h

protected theorem lipschitz : LipschitzWith 1 f :=
  f.isometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 f :=
  f.isometry.antilipschitz

@[continuity]
protected theorem continuous : Continuous f :=
  f.isometry.continuous

theorem ediam_image (s : Set P) : EMetric.diam (f '' s) = EMetric.diam s :=
  f.isometry.ediam_image s

theorem ediam_range : EMetric.diam (range f) = EMetric.diam (univ : Set P) :=
  f.isometry.ediam_range

theorem diam_image (s : Set P) : Metric.diam (f '' s) = Metric.diam s :=
  f.isometry.diam_image s

theorem diam_range : Metric.diam (range f) = Metric.diam (univ : Set P) :=
  f.isometry.diam_range

@[simp]
theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] {g : α → P} :
    Continuous (f ∘ g) ↔ Continuous g :=
  f.isometry.comp_continuous_iff

def id : P →ᵃⁱ[𝕜] P :=
  ⟨AffineMap.id 𝕜 P, fun _ => rfl⟩

instance : Inhabited (P →ᵃⁱ[𝕜] P) :=
  ⟨id⟩

def comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : P →ᵃⁱ[𝕜] P₃ :=
  ⟨g.toAffineMap.comp f.toAffineMap, fun _ => (g.norm_map _).trans (f.norm_map _)⟩

@[simp]
theorem id_comp : (id : P₂ →ᵃⁱ[𝕜] P₂).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id : f.comp id = f :=
  ext fun _ => rfl

theorem comp_assoc (f : P₃ →ᵃⁱ[𝕜] P₄) (g : P₂ →ᵃⁱ[𝕜] P₃) (h : P →ᵃⁱ[𝕜] P₂) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

instance : Monoid (P →ᵃⁱ[𝕜] P) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

end AffineIsometry

namespace AffineSubspace

def subtypeₐᵢ (s : AffineSubspace 𝕜 P) [Nonempty s] : s →ᵃⁱ[𝕜] P :=
  { s.subtype with norm_map := s.direction.subtypeₗᵢ.norm_map }

end AffineSubspace

variable (𝕜 P P₂)

structure AffineIsometryEquiv extends P ≃ᵃ[𝕜] P₂ where
  norm_map : ∀ x, ‖linear x‖ = ‖x‖

variable {𝕜 P P₂}

notation:25 P " ≃ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometryEquiv 𝕜 P P₂

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

protected def linearIsometryEquiv : V ≃ₗᵢ[𝕜] V₂ :=
  { e.linear with norm_map' := e.norm_map }

@[simp]
theorem linear_eq_linear_isometry : e.linear = e.linearIsometryEquiv.toLinearEquiv := by
  ext
  rfl

instance : EquivLike (P ≃ᵃⁱ[𝕜] P₂) P P₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h _ := by
    cases f
    cases g
    congr
    simpa [DFunLike.coe_injective.eq_iff] using h

theorem toAffineEquiv_injective : Injective (toAffineEquiv : (P ≃ᵃⁱ[𝕜] P₂) → P ≃ᵃ[𝕜] P₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[ext]
theorem ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : ∀ x, e x = e' x) : e = e' :=
  toAffineEquiv_injective <| AffineEquiv.ext h

def toAffineIsometry : P →ᵃⁱ[𝕜] P₂ :=
  ⟨e.1.toAffineMap, e.2⟩

def mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p : P₁) (h : ∀ p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) :
    P₁ ≃ᵃⁱ[𝕜] P₂ :=
  { AffineEquiv.mk' e e'.toLinearEquiv p h with norm_map := e'.norm_map }

@[simp]
theorem linearIsometryEquiv_mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) :
    (mk' e e' p h).linearIsometryEquiv = e' := by
  ext
  rfl

end AffineIsometryEquiv

namespace LinearIsometryEquiv

variable (e : V ≃ₗᵢ[𝕜] V₂)

def toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂ :=
  { e.toLinearEquiv.toAffineEquiv with norm_map := e.norm_map }

@[simp]
theorem toAffineIsometryEquiv_linearIsometryEquiv :
    e.toAffineIsometryEquiv.linearIsometryEquiv = e := by
  ext
  rfl

end LinearIsometryEquiv

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

protected theorem isometry : Isometry e :=
  e.toAffineIsometry.isometry

def toIsometryEquiv : P ≃ᵢ P₂ :=
  ⟨e.toAffineEquiv.toEquiv, e.isometry⟩

@[simp]
theorem coe_toIsometryEquiv : ⇑e.toIsometryEquiv = e :=
  rfl

theorem range_eq_univ (e : P ≃ᵃⁱ[𝕜] P₂) : Set.range e = Set.univ := by
  rw [← coe_toIsometryEquiv]
  exact IsometryEquiv.range_eq_univ _

def toHomeomorph : P ≃ₜ P₂ :=
  e.toIsometryEquiv.toHomeomorph

protected theorem continuous : Continuous e :=
  e.isometry.continuous

protected theorem continuousAt {x} : ContinuousAt e x :=
  e.continuous.continuousAt

protected theorem continuousOn {s} : ContinuousOn e s :=
  e.continuous.continuousOn

protected theorem continuousWithinAt {s x} : ContinuousWithinAt e s x :=
  e.continuous.continuousWithinAt

variable (𝕜 P)

def refl : P ≃ᵃⁱ[𝕜] P :=
  ⟨AffineEquiv.refl 𝕜 P, fun _ => rfl⟩

variable {𝕜 P}

instance : Inhabited (P ≃ᵃⁱ[𝕜] P) :=
  ⟨refl 𝕜 P⟩

def symm : P₂ ≃ᵃⁱ[𝕜] P :=
  { e.toAffineEquiv.symm with norm_map := e.linearIsometryEquiv.symm.norm_map }

@[simp]
theorem apply_symm_apply (x : P₂) : e (e.symm x) = x :=
  e.toAffineEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (x : P) : e.symm (e x) = x :=
  e.toAffineEquiv.symm_apply_apply x

def trans (e' : P₂ ≃ᵃⁱ[𝕜] P₃) : P ≃ᵃⁱ[𝕜] P₃ :=
  ⟨e.toAffineEquiv.trans e'.toAffineEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩

@[simp]
theorem trans_refl : e.trans (refl 𝕜 P₂) = e :=
  ext fun _ => rfl

@[simp]
theorem refl_trans : (refl 𝕜 P).trans e = e :=
  ext fun _ => rfl

@[simp]
theorem self_trans_symm : e.trans e.symm = refl 𝕜 P :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self : e.symm.trans e = refl 𝕜 P₂ :=
  ext e.apply_symm_apply

theorem trans_assoc (ePP₂ : P ≃ᵃⁱ[𝕜] P₂) (eP₂G : P₂ ≃ᵃⁱ[𝕜] P₃) (eGG' : P₃ ≃ᵃⁱ[𝕜] P₄) :
    ePP₂.trans (eP₂G.trans eGG') = (ePP₂.trans eP₂G).trans eGG' :=
  rfl

instance instGroup : Group (P ≃ᵃⁱ[𝕜] P) where
  mul e₁ e₂ := e₂.trans e₁
  one := refl _ _
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc _ _ _ := trans_assoc _ _ _
  inv_mul_cancel := self_trans_symm

@[simp]
theorem map_vadd (p : P) (v : V) : e (v +ᵥ p) = e.linearIsometryEquiv v +ᵥ e p :=
  e.toAffineIsometry.map_vadd p v

@[simp]
theorem map_vsub (p1 p2 : P) : e.linearIsometryEquiv (p1 -ᵥ p2) = e p1 -ᵥ e p2 :=
  e.toAffineIsometry.map_vsub p1 p2

@[simp]
theorem dist_map (x y : P) : dist (e x) (e y) = dist x y :=
  e.toAffineIsometry.dist_map x y

@[simp]
theorem edist_map (x y : P) : edist (e x) (e y) = edist x y :=
  e.toAffineIsometry.edist_map x y

protected theorem bijective : Bijective e :=
  e.1.bijective

protected theorem injective : Injective e :=
  e.1.injective

protected theorem surjective : Surjective e :=
  e.1.surjective

theorem map_eq_iff {x y : P} : e x = e y ↔ x = y :=
  e.injective.eq_iff

theorem map_ne {x y : P} (h : x ≠ y) : e x ≠ e y :=
  e.injective.ne h

protected theorem lipschitz : LipschitzWith 1 e :=
  e.isometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 e :=
  e.isometry.antilipschitz

@[simp]
theorem ediam_image (s : Set P) : EMetric.diam (e '' s) = EMetric.diam s :=
  e.isometry.ediam_image s

@[simp]
theorem diam_image (s : Set P) : Metric.diam (e '' s) = Metric.diam s :=
  e.isometry.diam_image s

variable {α : Type*} [TopologicalSpace α]

@[simp]
theorem comp_continuousOn_iff {f : α → P} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.isometry.comp_continuousOn_iff

@[simp]
theorem comp_continuous_iff {f : α → P} : Continuous (e ∘ f) ↔ Continuous f :=
  e.isometry.comp_continuous_iff

section Constructions

variable (𝕜)

def vaddConst (p : P) : V ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.vaddConst 𝕜 p with norm_map := fun _ => rfl }

variable {𝕜}

variable (𝕜)

def constVSub (p : P) : P ≃ᵃⁱ[𝕜] V :=
  { AffineEquiv.constVSub 𝕜 p with norm_map := norm_neg }

variable {𝕜}

@[simp]
theorem symm_constVSub (p : P) :
    (constVSub 𝕜 p).symm =
      (LinearIsometryEquiv.neg 𝕜).toAffineIsometryEquiv.trans (vaddConst 𝕜 p) := by
  ext
  rfl

variable (𝕜 P)

def constVAdd (v : V) : P ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.constVAdd 𝕜 P v with norm_map := fun _ => rfl }

variable {𝕜 P}

@[simp]
theorem constVAdd_zero : constVAdd 𝕜 P (0 : V) = refl 𝕜 P :=
  ext <| zero_vadd V

include 𝕜 in
/-- The map `g` from `V` to `V₂` corresponding to a map `f` from `P` to `P₂`, at a base point `p`,

is an isometry if `f` is one. -/

theorem vadd_vsub {f : P → P₂} (hf : Isometry f) {p : P} {g : V → V₂}
    (hg : ∀ v, g v = f (v +ᵥ p) -ᵥ f p) : Isometry g := by
  convert (vaddConst 𝕜 (f p)).symm.isometry.comp (hf.comp (vaddConst 𝕜 p).isometry)
  exact funext hg

variable (𝕜)

def pointReflection (x : P) : P ≃ᵃⁱ[𝕜] P :=
  (constVSub 𝕜 x).trans (vaddConst 𝕜 x)

variable {𝕜}

theorem pointReflection_apply (x y : P) : (pointReflection 𝕜 x) y = (x -ᵥ y) +ᵥ x :=
  rfl

@[simp]
theorem pointReflection_self (x : P) : pointReflection 𝕜 x x = x :=
  AffineEquiv.pointReflection_self 𝕜 x

theorem pointReflection_involutive (x : P) : Function.Involutive (pointReflection 𝕜 x) :=
  Equiv.pointReflection_involutive x

@[simp]
theorem pointReflection_symm (x : P) : (pointReflection 𝕜 x).symm = pointReflection 𝕜 x :=
  toAffineEquiv_injective <| AffineEquiv.pointReflection_symm 𝕜 x

@[simp]
theorem dist_pointReflection_fixed (x y : P) : dist (pointReflection 𝕜 x y) x = dist y x := by
  rw [← (pointReflection 𝕜 x).dist_map y x, pointReflection_self]

theorem dist_pointReflection_self' (x y : P) :
    dist (pointReflection 𝕜 x y) y = ‖2 • (x -ᵥ y)‖ := by
  rw [pointReflection_apply, dist_eq_norm_vsub V, vadd_vsub_assoc, two_nsmul]

theorem dist_pointReflection_self (x y : P) :
    dist (pointReflection 𝕜 x y) y = ‖(2 : 𝕜)‖ * dist x y := by
  rw [dist_pointReflection_self', two_nsmul, ← two_smul 𝕜, norm_smul, ← dist_eq_norm_vsub V]

theorem pointReflection_fixed_iff [Invertible (2 : 𝕜)] {x y : P} :
    pointReflection 𝕜 x y = y ↔ y = x :=
  AffineEquiv.pointReflection_fixed_iff_of_module 𝕜

variable [NormedSpace ℝ V]

theorem dist_pointReflection_self_real (x y : P) :
    dist (pointReflection ℝ x y) y = 2 * dist x y := by
  rw [dist_pointReflection_self, Real.norm_two]

@[simp]
theorem pointReflection_midpoint_left (x y : P) : pointReflection ℝ (midpoint ℝ x y) x = y :=
  AffineEquiv.pointReflection_midpoint_left x y

@[simp]
theorem pointReflection_midpoint_right (x y : P) : pointReflection ℝ (midpoint ℝ x y) y = x :=
  AffineEquiv.pointReflection_midpoint_right x y

end Constructions

end AffineIsometryEquiv

theorem AffineMap.continuous_linear_iff {f : P →ᵃ[𝕜] P₂} : Continuous f.linear ↔ Continuous f := by
  inhabit P
  have :
    (f.linear : V → V₂) =
      (AffineIsometryEquiv.vaddConst 𝕜 <| f default).toHomeomorph.symm ∘
        f ∘ (AffineIsometryEquiv.vaddConst 𝕜 default).toHomeomorph := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_continuous_iff, Homeomorph.comp_continuous_iff']

theorem AffineMap.isOpenMap_linear_iff {f : P →ᵃ[𝕜] P₂} : IsOpenMap f.linear ↔ IsOpenMap f := by
  inhabit P
  have :
    (f.linear : V → V₂) =
      (AffineIsometryEquiv.vaddConst 𝕜 <| f default).toHomeomorph.symm ∘
        f ∘ (AffineIsometryEquiv.vaddConst 𝕜 default).toHomeomorph := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_isOpenMap_iff, Homeomorph.comp_isOpenMap_iff']

attribute [local instance] AffineSubspace.nonempty_map -- Porting note: removed `fails_quickly`

namespace AffineSubspace

@[simps linear, simps! toFun]
noncomputable def equivMapOfInjective (E : AffineSubspace 𝕜 P₁) [Nonempty E] (φ : P₁ →ᵃ[𝕜] P₂)
    (hφ : Function.Injective φ) : E ≃ᵃ[𝕜] E.map φ :=
  { Equiv.Set.image _ (E : Set P₁) hφ with
    linear :=
      (E.direction.equivMapOfInjective φ.linear (φ.linear_injective_iff.mpr hφ)).trans
        (LinearEquiv.ofEq _ _ (AffineSubspace.map_direction _ _).symm)
    map_vadd' := fun p v => Subtype.ext <| φ.map_vadd p v }

noncomputable def isometryEquivMap (φ : P₁' →ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁') [Nonempty E] :
    E ≃ᵃⁱ[𝕜] E.map φ.toAffineMap :=
  ⟨E.equivMapOfInjective φ.toAffineMap φ.injective, fun _ => φ.norm_map _⟩

@[simp]
theorem isometryEquivMap.apply_symm_apply {E : AffineSubspace 𝕜 P₁'} [Nonempty E]
    {φ : P₁' →ᵃⁱ[𝕜] P₂} (x : E.map φ.toAffineMap) : φ ((E.isometryEquivMap φ).symm x) = x :=
  congr_arg Subtype.val <| (E.isometryEquivMap φ).apply_symm_apply _

end AffineSubspace
