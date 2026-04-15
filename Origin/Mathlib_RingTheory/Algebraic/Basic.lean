/-
Extracted from RingTheory/Algebraic/Basic.lean
Genuine: 54 | Conflates: 9 | Dissolved: 9 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Polynomial.Tower

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/

universe u v w

open Polynomial

section

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

-- CONFLATES (assumes ground = zero): is_transcendental_of_subsingleton
@[nontriviality]
theorem is_transcendental_of_subsingleton [Subsingleton R] (x : A) : Transcendental R x :=
  fun ⟨p, h, _⟩ => h <| Subsingleton.elim p 0

variable {R}

variable (R) in

theorem Polynomial.transcendental_X : Transcendental R (X (R := R)) := by
  simp [transcendental_iff]

-- DISSOLVED: IsAlgebraic.of_aeval

-- DISSOLVED: Transcendental.aeval

theorem Transcendental.aeval_of_transcendental {r : A} (H : Transcendental R r)
    {f : R[X]} (hf : Transcendental R f) : Transcendental R (Polynomial.aeval r f) := by
  rw [transcendental_iff] at H hf ⊢
  intro p hp
  exact hf _ (H _ (by rwa [← aeval_comp, comp_eq_aeval] at hp))

theorem Transcendental.of_aeval {r : A} {f : R[X]}
    (H : Transcendental R (Polynomial.aeval r f)) : Transcendental R f := by
  rw [transcendental_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp, comp_eq_aeval, hp, map_zero])

theorem IsAlgebraic.of_aeval_of_transcendental {r : A} {f : R[X]}
    (H : IsAlgebraic R (aeval r f)) (hf : Transcendental R f) : IsAlgebraic R r := by
  contrapose H
  exact Transcendental.aeval_of_transcendental H hf

-- DISSOLVED: Polynomial.transcendental

theorem isAlgebraic_iff_not_injective {x : A} :
    IsAlgebraic R x ↔ ¬Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  simp only [IsAlgebraic, injective_iff_map_eq_zero, not_forall, and_comm, exists_prop]

theorem transcendental_iff_injective {x : A} :
    Transcendental R x ↔ Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) :=
  isAlgebraic_iff_not_injective.not_left

theorem transcendental_iff_ker_eq_bot {x : A} :
    Transcendental R x ↔ RingHom.ker (aeval (R := R) x) = ⊥ := by
  rw [transcendental_iff_injective, RingHom.injective_iff_ker_eq_bot]

end

section zero_ne_one

variable {R : Type u} {S : Type*} {A : Type v} [CommRing R]

variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]

variable [IsScalarTower R S A]

-- CONFLATES (assumes ground = zero): isAlgebraic_zero
theorem isAlgebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A) :=
  ⟨_, X_ne_zero, aeval_X 0⟩

-- CONFLATES (assumes ground = zero): isAlgebraic_algebraMap
theorem isAlgebraic_algebraMap [Nontrivial R] (x : R) : IsAlgebraic R (algebraMap R A x) :=
  ⟨_, X_sub_C_ne_zero x, by rw [map_sub, aeval_X, aeval_C, sub_self]⟩

-- CONFLATES (assumes ground = zero): isAlgebraic_one
theorem isAlgebraic_one [Nontrivial R] : IsAlgebraic R (1 : A) := by
  rw [← map_one (algebraMap R A)]
  exact isAlgebraic_algebraMap 1

-- CONFLATES (assumes ground = zero): isAlgebraic_nat
theorem isAlgebraic_nat [Nontrivial R] (n : ℕ) : IsAlgebraic R (n : A) := by
  rw [← map_natCast (_ : R →+* A) n]
  exact isAlgebraic_algebraMap (Nat.cast n)

-- CONFLATES (assumes ground = zero): isAlgebraic_int
theorem isAlgebraic_int [Nontrivial R] (n : ℤ) : IsAlgebraic R (n : A) := by
  rw [← map_intCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Int.cast n)

theorem isAlgebraic_rat (R : Type u) {A : Type v} [DivisionRing A] [Field R] [Algebra R A] (n : ℚ) :
    IsAlgebraic R (n : A) := by
  rw [← map_ratCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Rat.cast n)

theorem isAlgebraic_of_mem_rootSet {R : Type u} {A : Type v} [Field R] [Field A] [Algebra R A]
    {p : R[X]} {x : A} (hx : x ∈ p.rootSet A) : IsAlgebraic R x :=
  ⟨p, ne_zero_of_mem_rootSet hx, aeval_eq_zero_of_mem_rootSet hx⟩

open IsScalarTower

protected theorem IsAlgebraic.algebraMap {a : S} :
    IsAlgebraic R a → IsAlgebraic R (algebraMap S A a) := fun ⟨f, hf₁, hf₂⟩ =>
  ⟨f, hf₁, by rw [aeval_algebraMap_apply, hf₂, map_zero]⟩

section

variable {B : Type*} [Ring B] [Algebra R B]

protected theorem IsAlgebraic.algHom (f : A →ₐ[R] B) {a : A}
    (h : IsAlgebraic R a) : IsAlgebraic R (f a) :=
  let ⟨p, hp, ha⟩ := h
  ⟨p, hp, by rw [aeval_algHom, f.comp_apply, ha, map_zero]⟩

theorem isAlgebraic_algHom_iff (f : A →ₐ[R] B) (hf : Function.Injective f)
    {a : A} : IsAlgebraic R (f a) ↔ IsAlgebraic R a :=
  ⟨fun ⟨p, hp0, hp⟩ ↦ ⟨p, hp0, hf <| by rwa [map_zero, ← f.comp_apply, ← aeval_algHom]⟩,
    IsAlgebraic.algHom f⟩

section RingHom

omit [Algebra R S] [Algebra S A] [IsScalarTower R S A] [Algebra R B]

variable [Algebra S B] {FRS FAB : Type*}

section

variable [FunLike FRS R S] [RingHomClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB) {a : A}

theorem IsAlgebraic.ringHom_of_comp_eq (halg : IsAlgebraic R a)
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    IsAlgebraic S (g a) := by
  obtain ⟨p, h1, h2⟩ := halg
  refine ⟨p.map f, (Polynomial.map_ne_zero_iff hf).2 h1, ?_⟩
  change aeval ((g : A →+* B) a) _ = 0
  rw [← map_aeval_eq_aeval_map h, h2, map_zero]

theorem Transcendental.of_ringHom_of_comp_eq (H : Transcendental S (g a))
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Transcendental R a := fun halg ↦ H (halg.ringHom_of_comp_eq f g hf h)

theorem Algebra.IsAlgebraic.ringHom_of_comp_eq [Algebra.IsAlgebraic R A]
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic S B := by
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hg b
  exact (Algebra.IsAlgebraic.isAlgebraic a).ringHom_of_comp_eq f g hf h

theorem Algebra.Transcendental.of_ringHom_of_comp_eq [H : Algebra.Transcendental S B]
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental R A := by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg ↦ H (halg.ringHom_of_comp_eq f g hf hg h)

theorem IsAlgebraic.of_ringHom_of_comp_eq (halg : IsAlgebraic S (g a))
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    IsAlgebraic R a := by
  obtain ⟨p, h1, h2⟩ := halg
  obtain ⟨q, rfl⟩ := map_surjective f hf p
  refine ⟨q, fun h' ↦ by simp [h'] at h1, hg ?_⟩
  change aeval ((g : A →+* B) a) _ = 0 at h2
  change (g : A →+* B) _ = _
  rw [map_zero, map_aeval_eq_aeval_map h, h2]

theorem Transcendental.ringHom_of_comp_eq (H : Transcendental R a)
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Transcendental S (g a) := fun halg ↦ H (halg.of_ringHom_of_comp_eq f g hf hg h)

theorem Algebra.IsAlgebraic.of_ringHom_of_comp_eq [Algebra.IsAlgebraic S B]
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic R A :=
  ⟨fun a ↦ (Algebra.IsAlgebraic.isAlgebraic (g a)).of_ringHom_of_comp_eq f g hf hg h⟩

theorem Algebra.Transcendental.ringHom_of_comp_eq [H : Algebra.Transcendental R A]
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental S B := by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg ↦ H (halg.of_ringHom_of_comp_eq f g hf hg h)

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB)

theorem isAlgebraic_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} :
    IsAlgebraic S (g a) ↔ IsAlgebraic R a :=
  ⟨fun H ↦ H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) hg h,
    fun H ↦ H.ringHom_of_comp_eq f g (EquivLike.injective f) h⟩

theorem transcendental_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} :
    Transcendental S (g a) ↔ Transcendental R a :=
  not_congr (isAlgebraic_ringHom_iff_of_comp_eq f g hg h)

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [EquivLike FAB A B] [RingEquivClass FAB A B]
  (f : FRS) (g : FAB)

theorem Algebra.isAlgebraic_ringHom_iff_of_comp_eq
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic S B ↔ Algebra.IsAlgebraic R A :=
  ⟨fun H ↦ H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) (EquivLike.injective g) h,
    fun H ↦ H.ringHom_of_comp_eq f g (EquivLike.injective f) (EquivLike.surjective g) h⟩

theorem Algebra.transcendental_ringHom_iff_of_comp_eq
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental S B ↔ Algebra.Transcendental R A := by
  simp_rw [Algebra.transcendental_iff_not_isAlgebraic,
    Algebra.isAlgebraic_ringHom_iff_of_comp_eq f g h]

end

end RingHom

theorem Algebra.IsAlgebraic.of_injective (f : A →ₐ[R] B) (hf : Function.Injective f)
    [Algebra.IsAlgebraic R B] : Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (isAlgebraic_algHom_iff f hf).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩

theorem AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B)
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic R B :=
  Algebra.IsAlgebraic.of_injective e.symm.toAlgHom e.symm.injective

theorem AlgEquiv.isAlgebraic_iff (e : A ≃ₐ[R] B) :
    Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R B :=
  ⟨fun _ ↦ e.isAlgebraic, fun _ ↦ e.symm.isAlgebraic⟩

end

theorem isAlgebraic_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    IsAlgebraic R (algebraMap S A a) ↔ IsAlgebraic R a :=
  isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R S A) h

theorem transcendental_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    Transcendental R (algebraMap S A a) ↔ Transcendental R a := by
  simp_rw [Transcendental, isAlgebraic_algebraMap_iff h]

namespace Subalgebra

theorem isAlgebraic_iff_isAlgebraic_val {S : Subalgebra R A} {x : S} :
    _root_.IsAlgebraic R x ↔ _root_.IsAlgebraic R x.1 :=
  (isAlgebraic_algHom_iff S.val Subtype.val_injective).symm

theorem isAlgebraic_of_isAlgebraic_bot {x : S} (halg : _root_.IsAlgebraic (⊥ : Subalgebra R S) x) :
    _root_.IsAlgebraic R x :=
  halg.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id rfl

theorem isAlgebraic_bot_iff (h : Function.Injective (algebraMap R S)) {x : S} :
    _root_.IsAlgebraic (⊥ : Subalgebra R S) x ↔ _root_.IsAlgebraic R x :=
  isAlgebraic_ringHom_iff_of_comp_eq (Algebra.botEquivOfInjective h).symm (RingHom.id S)
    Function.injective_id (by rfl)

variable (R S) in

theorem algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left
    [Algebra.IsAlgebraic (⊥ : Subalgebra R S) S] : Algebra.IsAlgebraic R S :=
  Algebra.IsAlgebraic.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id (by ext; rfl)

theorem algebra_isAlgebraic_bot_left_iff (h : Function.Injective (algebraMap R S)) :
    Algebra.IsAlgebraic (⊥ : Subalgebra R S) S ↔ Algebra.IsAlgebraic R S := by
  simp_rw [Algebra.isAlgebraic_def, isAlgebraic_bot_iff h]

instance algebra_isAlgebraic_bot_right [Nontrivial R] :
    Algebra.IsAlgebraic R (⊥ : Subalgebra R S) :=
  ⟨by rintro ⟨_, x, rfl⟩; exact isAlgebraic_algebraMap _⟩

end Subalgebra

theorem IsAlgebraic.of_pow {r : A} {n : ℕ} (hn : 0 < n) (ht : IsAlgebraic R (r ^ n)) :
    IsAlgebraic R r := by
  obtain ⟨p, p_nonzero, hp⟩ := ht
  refine ⟨Polynomial.expand _ n p, ?_, ?_⟩
  · rwa [Polynomial.expand_ne_zero hn]
  · rwa [Polynomial.expand_aeval n p r]

theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : ℕ} (hn : 0 < n) :
    Transcendental R (r ^ n) := fun ht' ↦ ht <| ht'.of_pow hn

lemma IsAlgebraic.invOf {x : S} [Invertible x] (h : IsAlgebraic R x) : IsAlgebraic R (⅟ x) := by
  obtain ⟨p, hp, hp'⟩ := h
  refine ⟨p.reverse, by simpa using hp, ?_⟩
  rwa [Polynomial.aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, ← Polynomial.aeval_def]

lemma IsAlgebraic.invOf_iff {x : S} [Invertible x] :
    IsAlgebraic R (⅟ x) ↔ IsAlgebraic R x :=
  ⟨IsAlgebraic.invOf, IsAlgebraic.invOf⟩

lemma IsAlgebraic.inv_iff {K} [Field K] [Algebra R K] {x : K} :
    IsAlgebraic R (x⁻¹) ↔ IsAlgebraic R x := by
  by_cases hx : x = 0
  · simp [hx]
  letI := invertibleOfNonzero hx
  exact IsAlgebraic.invOf_iff (R := R) (x := x)

alias ⟨_, IsAlgebraic.inv⟩ := IsAlgebraic.inv_iff

end zero_ne_one

section

variable {K L R S A : Type*}

section Ring

section CommRing

variable [CommRing R] [CommRing S] [Ring A]

variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

theorem IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R S)) {x : A}
    (A_alg : IsAlgebraic R x) : IsAlgebraic S x :=
  let ⟨p, hp₁, hp₂⟩ := A_alg
  ⟨p.map (algebraMap _ _), by
    rwa [Ne, ← degree_eq_bot, degree_map_eq_of_injective hinj, degree_eq_bot], by simpa⟩

alias IsAlgebraic.tower_top_of_injective := IsAlgebraic.extendScalars

theorem IsAlgebraic.tower_top_of_subalgebra_le
    {A B : Subalgebra R S} (hle : A ≤ B) {x : S}
    (h : IsAlgebraic A x) : IsAlgebraic B x := by
  letI : Algebra A B := (Subalgebra.inclusion hle).toAlgebra
  haveI : IsScalarTower A B S := .of_algebraMap_eq fun _ ↦ rfl
  exact h.extendScalars (Subalgebra.inclusion_injective hle)

theorem Transcendental.restrictScalars (hinj : Function.Injective (algebraMap R S)) {x : A}
    (h : Transcendental S x) : Transcendental R x := fun H ↦ h (H.extendScalars hinj)

alias Transcendental.of_tower_top_of_injective := Transcendental.restrictScalars

theorem Transcendental.of_tower_top_of_subalgebra_le
    {A B : Subalgebra R S} (hle : A ≤ B) {x : S}
    (h : Transcendental B x) : Transcendental A x :=
  fun H ↦ h (H.tower_top_of_subalgebra_le hle)

theorem Algebra.IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R S))
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic S A :=
  ⟨fun _ ↦ _root_.IsAlgebraic.extendScalars hinj (Algebra.IsAlgebraic.isAlgebraic _)⟩

alias Algebra.IsAlgebraic.tower_top_of_injective := Algebra.IsAlgebraic.extendScalars

theorem Algebra.IsAlgebraic.tower_bot_of_injective [Algebra.IsAlgebraic R A]
    (hinj : Function.Injective (algebraMap S A)) :
    Algebra.IsAlgebraic R S where
  isAlgebraic x := by
    simpa [isAlgebraic_algebraMap_iff hinj] using isAlgebraic (R := R) (A := A) (algebraMap _ _ x)

end CommRing

section Field

variable [Field K] [Field L] [Ring A]

variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

variable (L)

@[stacks 09GF "part one"]
theorem IsAlgebraic.tower_top {x : A} (A_alg : IsAlgebraic K x) :
    IsAlgebraic L x :=
  A_alg.extendScalars (algebraMap K L).injective

variable {L} (K) in

theorem Transcendental.of_tower_top {x : A} (h : Transcendental L x) :
    Transcendental K x := fun H ↦ h (H.tower_top L)

@[stacks 09GF "part two"]
theorem Algebra.IsAlgebraic.tower_top [Algebra.IsAlgebraic K A] : Algebra.IsAlgebraic L A :=
  Algebra.IsAlgebraic.extendScalars (algebraMap K L).injective

variable (K) (A)

-- CONFLATES (assumes ground = zero): Algebra.IsAlgebraic.tower_bot
theorem Algebra.IsAlgebraic.tower_bot (K L A : Type*) [CommRing K] [Field L] [Ring A]
    [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
    [Nontrivial A] [Algebra.IsAlgebraic K A] :
    Algebra.IsAlgebraic K L :=
  tower_bot_of_injective (algebraMap L A).injective

end Field

end Ring

section NoZeroSMulDivisors

namespace Algebra.IsAlgebraic

variable [CommRing K] [Field L]

variable [Algebra K L]

theorem algHom_bijective [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L] (f : L →ₐ[K] L) :
    Function.Bijective f := by
  refine ⟨f.injective, fun b ↦ ?_⟩
  obtain ⟨p, hp, he⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) b
  let f' : p.rootSet L → p.rootSet L := (rootSet_maps_to' (fun x ↦ x) f).restrict f _ _
  have : f'.Surjective := Finite.injective_iff_surjective.1
    fun _ _ h ↦ Subtype.eq <| f.injective <| Subtype.ext_iff.1 h
  obtain ⟨a, ha⟩ := this ⟨b, mem_rootSet.2 ⟨hp, he⟩⟩
  exact ⟨a, Subtype.ext_iff.1 ha⟩

theorem algHom_bijective₂ [NoZeroSMulDivisors K L] [Field R] [Algebra K R]
    [Algebra.IsAlgebraic K L] (f : L →ₐ[K] R) (g : R →ₐ[K] L) :
    Function.Bijective f ∧ Function.Bijective g :=
  (g.injective.bijective₂_of_surjective f.injective (algHom_bijective <| g.comp f).2).symm

theorem bijective_of_isScalarTower [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L]
    [Field R] [Algebra K R] [Algebra L R] [IsScalarTower K L R] (f : R →ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ (IsScalarTower.toAlgHom K L R) f).2

theorem bijective_of_isScalarTower' [Field R] [Algebra K R]
    [NoZeroSMulDivisors K R]
    [Algebra.IsAlgebraic K R] [Algebra L R] [IsScalarTower K L R] (f : R →ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ f (IsScalarTower.toAlgHom K L R)).1

variable (K L)

@[simps]
noncomputable def algEquivEquivAlgHom [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) where
  toFun ϕ := ϕ.toAlgHom
  invFun ϕ := AlgEquiv.ofBijective ϕ (algHom_bijective ϕ)
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := rfl

end Algebra.IsAlgebraic

end NoZeroSMulDivisors

end

section

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]

-- DISSOLVED: IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero

-- DISSOLVED: IsAlgebraic.exists_nonzero_dvd

theorem IsAlgebraic.exists_smul_eq_mul
    (a : S) {b : S} (hRb : IsAlgebraic R b) (hb : b ∈ nonZeroDivisors S) :
    ∃ᵉ (c : S) (d ≠ (0 : R)), d • a = b * c := by
  obtain ⟨r, hr, s, h⟩ := IsAlgebraic.exists_nonzero_dvd (R := R) (S := S) hRb hb
  exact ⟨s * a, r, hr, by rw [Algebra.smul_def, h, mul_assoc]⟩

variable (R)

-- DISSOLVED: Algebra.IsAlgebraic.exists_smul_eq_mul

end

variable {R S : Type*} [CommRing R] [CommRing S]

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : Subalgebra K L)

-- DISSOLVED: inv_eq_of_aeval_divX_ne_zero

-- DISSOLVED: inv_eq_of_root_of_coeff_zero_ne_zero

-- DISSOLVED: Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero

theorem Subalgebra.inv_mem_of_algebraic {x : A} (hx : _root_.IsAlgebraic K (x : L)) :
    (x⁻¹ : L) ∈ A := by
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx
  rw [Subalgebra.aeval_coe, Subalgebra.coe_eq_zero] at aeval_eq
  revert ne_zero aeval_eq
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a hp ha _ih _ne_zero aeval_eq
    refine A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq ?_
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl]
  · intro p hp ih _ne_zero aeval_eq
    rw [map_mul, aeval_X, mul_eq_zero] at aeval_eq
    cases' aeval_eq with aeval_eq x_eq
    · exact ih hp aeval_eq
    · rw [x_eq, Subalgebra.coe_zero, inv_zero]
      exact A.zero_mem

@[stacks 0BID]
theorem Subalgebra.isField_of_algebraic [Algebra.IsAlgebraic K L] : IsField A :=
  { show Nontrivial A by infer_instance, Subalgebra.toCommRing A with
    mul_inv_cancel := fun {a} ha =>
      ⟨⟨a⁻¹, A.inv_mem_of_algebraic (Algebra.IsAlgebraic.isAlgebraic (a : L))⟩,
        Subtype.ext (mul_inv_cancel₀ (mt (Subalgebra.coe_eq_zero _).mp ha))⟩ }

end Field

section Infinite

-- CONFLATES (assumes ground = zero): Transcendental.infinite
theorem Transcendental.infinite {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Nontrivial R] {x : A} (hx : Transcendental R x) : Infinite A :=
  .of_injective _ (transcendental_iff_injective.mp hx)

-- CONFLATES (assumes ground = zero): Algebra.Transcendental.infinite
theorem Algebra.Transcendental.infinite (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    [Nontrivial R] [Algebra.Transcendental R A] : Infinite A :=
  have ⟨x, hx⟩ := ‹Algebra.Transcendental R A›
  hx.infinite

end Infinite
