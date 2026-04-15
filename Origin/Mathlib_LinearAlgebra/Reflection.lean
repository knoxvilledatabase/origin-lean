/-
Extracted from LinearAlgebra/Reflection.lean
Genuine: 15 | Conflates: 0 | Dissolved: 2 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.FiniteSpan

/-!
# Reflections in linear algebra

Given an element `x` in a module `M` together with a linear form `f` on `M` such that `f x = 2`, the
map `y ↦ y - (f y) • x` is an involutive endomorphism of `M`, such that:
 1. the kernel of `f` is fixed,
 2. the point `x ↦ -x`.

Such endomorphisms are often called reflections of the module `M`. When `M` carries an inner product
for which `x` is perpendicular to the kernel of `f`, then (with mild assumptions) the endomorphism
is characterised by properties 1 and 2 above, and is a linear isometry.

## Main definitions / results:

 * `Module.preReflection`: the definition of the map `y ↦ y - (f y) • x`. Its main utility lies in
   the fact that it does not require the assumption `f x = 2`, giving the user freedom to defer
   discharging this proof obligation.
 * `Module.reflection`: the definition of the map `y ↦ y - (f y) • x`. This requires the assumption
   that `f x = 2` but by way of compensation it produces a linear equivalence rather than a mere
   linear map.
 * `Module.Dual.eq_of_preReflection_mapsTo`: a uniqueness result about reflections preserving
   finite spanning sets that is useful in the theory of root data / systems.

## TODO

Related definitions of reflection exists elsewhere in the library. These more specialised
definitions, which require an ambient `InnerProductSpace` structure, are `reflection` (of type
`LinearIsometryEquiv`) and `EuclideanGeometry.reflection` (of type `AffineIsometryEquiv`). We
should connect (or unify) these definitions with `Module.reflecton` defined here.

-/

open Function Set

open Module hiding Finite

open Submodule (span)

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x : M) (f : Dual R M) (y : M)

namespace Module

def preReflection : End R M :=
  LinearMap.id - f.smulRight x

lemma preReflection_apply :
    preReflection x f y = y - (f y) • x := by
  simp [preReflection]

variable {x f}

lemma preReflection_apply_self (h : f x = 2) :
    preReflection x f x = - x := by
  rw [preReflection_apply, h, two_smul]; abel

lemma involutive_preReflection (h : f x = 2) :
    Involutive (preReflection x f) :=
  fun y ↦ by simp [map_sub, h, smul_sub, two_smul, preReflection_apply]

lemma preReflection_preReflection (g : Dual R M) (h : f x = 2) :
    preReflection (preReflection x f y) (preReflection f (Dual.eval R M x) g) =
    (preReflection x f) ∘ₗ (preReflection y g) ∘ₗ (preReflection x f) := by
  ext m
  simp only [h, preReflection_apply, mul_comm (g x) (f m), mul_two, mul_assoc, Dual.eval_apply,
    LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.smul_apply, smul_eq_mul, smul_sub, sub_smul,
    smul_smul, sub_mul, comp_apply, map_sub, map_smul, add_smul]
  abel

def reflection (h : f x = 2) : M ≃ₗ[R] M :=
  { preReflection x f, (involutive_preReflection h).toPerm with }

lemma reflection_apply (h : f x = 2) :
    reflection h y = y - (f y) • x :=
  preReflection_apply x f y

@[simp]
lemma reflection_apply_self (h : f x = 2) :
    reflection h x = - x :=
  preReflection_apply_self h

lemma involutive_reflection (h : f x = 2) :
    Involutive (reflection h) :=
  involutive_preReflection h

@[simp]
lemma reflection_symm (h : f x = 2) :
    (reflection h).symm = reflection h :=
  rfl

lemma invOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) :
    InvOn (reflection h) (reflection h) Φ Φ :=
  ⟨fun x _ ↦ involutive_reflection h x, fun x _ ↦ involutive_reflection h x⟩

lemma bijOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) (h' : MapsTo (reflection h) Φ Φ) :
    BijOn (reflection h) Φ Φ :=
  (invOn_reflection_of_mapsTo h).bijOn h' h'

-- DISSOLVED: Dual.eq_of_preReflection_mapsTo

-- DISSOLVED: Dual.eq_of_preReflection_mapsTo'

variable {y}

variable {g : Dual R M}

lemma reflection_reflection_iterate
    (hfx : f x = 2) (hgy : g y = 2) (hgxfy : f y * g x = 4) (n : ℕ) :
    ((reflection hgy).trans (reflection hfx))^[n] y = y + n • (f y • x - (2 : R) • y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : ∀ z : M, f y • g x • z = 2 • 2 • z := by
      intro z
      rw [smul_smul, hgxfy, smul_smul, ← Nat.cast_smul_eq_nsmul R (2 * 2), Nat.cast_eq_ofNat]
    simp only [iterate_succ', comp_apply, ih, two_smul, smul_sub, smul_add, map_add,
      LinearEquiv.trans_apply, reflection_apply_self, map_neg, reflection_apply, neg_sub, map_sub,
      map_nsmul, map_smul, smul_neg, hz, add_smul]
    abel

lemma infinite_range_reflection_reflection_iterate_iff [NoZeroSMulDivisors ℤ M]
    (hfx : f x = 2) (hgy : g y = 2) (hgxfy : f y * g x = 4) :
    (range <| fun n ↦ ((reflection hgy).trans (reflection hfx))^[n] y).Infinite ↔
    f y • x ≠ (2 : R) • y := by
  simp only [reflection_reflection_iterate hfx hgy hgxfy, infinite_range_add_nsmul_iff, sub_ne_zero]

lemma eq_of_mapsTo_reflection_of_mem [NoZeroSMulDivisors ℤ M] {Φ : Set M} (hΦ : Φ.Finite)
    (hfx : f x = 2) (hgy : g y = 2) (hgx : g x = 2) (hfy : f y = 2)
    (hxfΦ : MapsTo (preReflection x f) Φ Φ)
    (hygΦ : MapsTo (preReflection y g) Φ Φ)
    (hyΦ : y ∈ Φ) :
    x = y := by
  suffices h : f y • x = (2 : R) • y by
    rw [hfy, two_smul R x, two_smul R y, ← two_zsmul, ← two_zsmul] at h
    exact smul_right_injective _ two_ne_zero h
  rw [← not_infinite] at hΦ
  contrapose! hΦ
  apply ((infinite_range_reflection_reflection_iterate_iff hfx hgy
    (by rw [hfy, hgx]; norm_cast)).mpr hΦ).mono
  rw [range_subset_iff]
  intro n
  rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo hfx hxfΦ).comp
    (bijOn_reflection_of_mapsTo hgy hygΦ)).image_eq n]
  exact mem_image_of_mem _ hyΦ

lemma injOn_dualMap_subtype_span_range_range {ι : Type*} [NoZeroSMulDivisors ℤ M]
    {r : ι ↪ M} {c : ι → Dual R M} (hfin : (range r).Finite)
    (h_two : ∀ i, c i (r i) = 2)
    (h_mapsTo : ∀ i, MapsTo (preReflection (r i) (c i)) (range r) (range r)) :
    InjOn (span R (range r)).subtype.dualMap (range c) := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  congr
  suffices ∀ k, c i (r k) = c j (r k) by
    rw [← EmbeddingLike.apply_eq_iff_eq r]
    exact eq_of_mapsTo_reflection_of_mem (f := c i) (g := c j) hfin (h_two i) (h_two j)
      (by rw [← this, h_two]) (by rw [this, h_two]) (h_mapsTo i) (h_mapsTo j) (mem_range_self j)
  intro k
  simpa using LinearMap.congr_fun hij ⟨r k, Submodule.subset_span (mem_range_self k)⟩

end Module
