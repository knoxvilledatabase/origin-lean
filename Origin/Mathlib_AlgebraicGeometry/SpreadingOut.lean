/-
Extracted from AlgebraicGeometry/SpreadingOut.lean
Genuine: 8 of 11 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Spreading out morphisms

Under certain conditions, a morphism on stalks `Spec 𝒪_{X, x} ⟶ Spec 𝒪_{Y, y}` can be spread
out into a neighborhood of `x`.

## Main result
Given `S`-schemes `X Y` and points `x : X` `y : Y` over `s : S`.
Suppose we have the following diagram of `S`-schemes
```
Spec 𝒪_{X, x} ⟶ X
    |
  Spec(φ)
    ↓
Spec 𝒪_{Y, y} ⟶ Y
```
We would like to spread `Spec(φ)` out to an `S`-morphism on an open subscheme `U ⊆ X`
```
Spec 𝒪_{X, x} ⟶ U ⊆ X
    |             |
  Spec(φ)         |
    ↓             ↓
Spec 𝒪_{Y, y} ⟶ Y
```
- `AlgebraicGeometry.spread_out_unique_of_isGermInjective`:
  The lift is "unique" if the germ map is injective at `x`.
- `AlgebraicGeometry.spread_out_of_isGermInjective`:
  The lift exists if `Y` is locally of finite type and the germ map is injective at `x`.

## TODO

Show that certain morphism properties can also be spread out.

-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (sX : X ⟶ S) (sY : Y ⟶ S) {R A : CommRingCat.{u}}

class Scheme.IsGermInjectiveAt (X : Scheme.{u}) (x : X) : Prop where
  cond : ∃ (U : X.Opens) (hx : x ∈ U), IsAffineOpen U ∧ Function.Injective (X.presheaf.germ U x hx)

lemma injective_germ_basicOpen (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (f : Γ(X, U))
    (hf : x ∈ X.basicOpen f)
    (H : Function.Injective (X.presheaf.germ U x hx)) :
    Function.Injective (X.presheaf.germ (X.basicOpen f) x hf) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero] at H ⊢
  intro t ht
  have := hU.isLocalization_basicOpen f
  obtain ⟨t, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) t
  rw [← RingHom.mem_ker, IsLocalization.mk'_eq_mul_mk'_one, Ideal.mul_unit_mem_iff_mem,
    RingHom.mem_ker, RingHom.algebraMap_toAlgebra, TopCat.Presheaf.germ_res_apply] at ht
  swap; · exact @isUnit_of_invertible _ _ _ (@IsLocalization.invertible_mk'_one ..)
  rw [H _ ht, IsLocalization.mk'_zero]

lemma Scheme.exists_germ_injective (X : Scheme.{u}) (x : X) [X.IsGermInjectiveAt x] :
    ∃ (U : X.Opens) (hx : x ∈ U),
      IsAffineOpen U ∧ Function.Injective (X.presheaf.germ U x hx) :=
  Scheme.IsGermInjectiveAt.cond

lemma Scheme.exists_le_and_germ_injective (X : Scheme.{u}) (x : X) [X.IsGermInjectiveAt x]
    (V : X.Opens) (hxV : x ∈ V) :
    ∃ (U : X.Opens) (hx : x ∈ U),
      IsAffineOpen U ∧ U ≤ V ∧ Function.Injective (X.presheaf.germ U x hx) := by
  obtain ⟨U, hx, hU, H⟩ := Scheme.IsGermInjectiveAt.cond (x := x)
  obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
  exact ⟨X.basicOpen f, hxf, hU.basicOpen f, hf, injective_germ_basicOpen U hU x hx f hxf H⟩

-- INSTANCE (free from Core): (x

variable {f} in

lemma isGermInjectiveAt_iff_of_isOpenImmersion {x : X} [IsOpenImmersion f] :
    Y.IsGermInjectiveAt (f x) ↔ X.IsGermInjectiveAt x := by
  refine ⟨fun H ↦ ?_, fun _ ↦ inferInstance⟩
  obtain ⟨U, hxU, hU, hU', H⟩ :=
    Y.exists_le_and_germ_injective (f x) (V := f.opensRange) ⟨x, rfl⟩
  obtain ⟨V, hV⟩ := (IsOpenImmersion.affineOpensEquiv f).surjective ⟨⟨U, hU⟩, hU'⟩
  obtain rfl : f ''ᵁ V = U := Subtype.ext_iff.mp (Subtype.ext_iff.mp hV)
  obtain ⟨y, hy, e : f y = f x⟩ := hxU
  obtain rfl := f.isOpenEmbedding.injective e
  refine ⟨V, hy, V.2, ?_⟩
  replace H := ((MorphismProperty.injective CommRingCat).cancel_right_of_respectsIso _
    (f.stalkMap y)).mpr H
  replace H := ((MorphismProperty.injective CommRingCat).cancel_left_of_respectsIso
    (f.appIso V).inv _).mpr H
  simpa using H

abbrev Scheme.IsGermInjective (X : Scheme.{u}) := ∀ x : X, X.IsGermInjectiveAt x

lemma Scheme.IsGermInjective.of_openCover
    {X : Scheme.{u}} (𝒰 : X.OpenCover) [∀ i, (𝒰.X i).IsGermInjective] : X.IsGermInjective := by
  intro x
  rw [← (𝒰.covers x).choose_spec]
  infer_instance

set_option backward.isDefEq.respectTransparency false in

protected

lemma Scheme.IsGermInjective.Spec
    (H : ∀ I : Ideal R, I.IsPrime →
      ∃ f : R, f ∉ I ∧ ∀ (x y : R), y * x = 0 → y ∉ I → ∃ n, f ^ n * x = 0) :
    (Spec R).IsGermInjective := by
  refine fun p ↦ ⟨?_⟩
  obtain ⟨f, hf, H⟩ := H p.asIdeal p.2
  refine ⟨PrimeSpectrum.basicOpen f, hf, ?_, ?_⟩
  · rw [← basicOpen_eq_of_affine]
    exact (isAffineOpen_top (Spec R)).basicOpen _
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (S := ((Spec.structureSheaf R).obj.obj (.op <| PrimeSpectrum.basicOpen f))) (.powers f) x
  rw [← RingHom.mem_ker, IsLocalization.mk'_eq_mul_mk'_one, Ideal.mul_unit_mem_iff_mem,
    RingHom.mem_ker] at hx
  swap; · exact @isUnit_of_invertible _ _ _ (@IsLocalization.invertible_mk'_one ..)
  -- There is an `Opposite.unop (Opposite.op _)` in `hx` which doesn't seem removable using
  -- `simp`/`rw`.
  erw [elementwise_of% StructureSheaf.algebraMap_germ] at hx
  obtain ⟨⟨y, hy⟩, hy'⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl
    ((Spec.structureSheaf R).presheaf.stalk p) _).mp hx
  obtain ⟨n, hn⟩ := H x y hy' hy
  refine (@IsLocalization.mk'_eq_zero_iff ..).mpr ?_
  exact ⟨⟨_, n, rfl⟩, hn⟩

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority
