/-
Extracted from RingTheory/IntegralClosure/IsIntegral/Basic.lean
Genuine: 16 of 17 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Properties of integral elements.

We prove basic properties of integral elements in a ring extension.
-/

open Polynomial Submodule

section Ring

variable {R S A T : Type*}

variable [CommRing R] [Ring A] [Ring S] [Ring T] (f : R →+* S) (g : S →+* T)

variable [Algebra R A]

theorem RingHom.isIntegralElem_map {x : R} : f.IsIntegralElem (f x) :=
  ⟨X - C x, monic_X_sub_C _, by simp⟩

theorem isIntegral_algebraMap {x : R} : IsIntegral R (algebraMap R A x) :=
  (algebraMap R A).isIntegralElem_map

variable {f} in

lemma RingHom.IsIntegralElem.map {x : S} (hx : f.IsIntegralElem x) (g : S →+* T) :
    (g.comp f).IsIntegralElem (g x) := by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p, hp, by simp_rw [← hom_eval₂, eval₂_eq_eval_map] at hx ⊢; simp [hx]⟩

variable {f g} in

lemma RingHom.IsIntegralElem.of_map (hg : Function.Injective g) {x : S}
    (hx : (g.comp f).IsIntegralElem (g x)) :
    f.IsIntegralElem x := by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p, hp, hg <| by simp [Polynomial.hom_eval₂, hx]⟩

variable {f g} in

lemma RingHom.IsIntegralElem.map_iff (hg : Function.Injective g) {x : S} :
    (g.comp f).IsIntegralElem (g x) ↔ f.IsIntegralElem x :=
  ⟨of_map hg, (map · g)⟩

end Ring

variable {R A B S T : Type*}

variable [CommRing R] [CommRing A] [Ring B] [CommRing S] [Ring T]

variable [Algebra R A] (f : R →+* S)

variable {f} in

lemma RingHom.IsIntegralElem.of_comp {g : S →+* T} {x : T} (hx : (g.comp f).IsIntegralElem x) :
    g.IsIntegralElem x := by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p.map f, hp.map _, by simpa only [eval₂_eq_eval_map, map_map] using hx⟩

theorem IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebra R B] [Algebra A B] [Algebra R C]
    [IsScalarTower R A B] [Algebra A C] [IsScalarTower R A C] {b : B}
    [FunLike F B C] [AlgHomClass F A B C] (f : F)
    (hb : IsIntegral R b) : IsIntegral R (f b) := by
  rw [IsIntegral, ← ((AlgHomClass.toAlgHom f).restrictScalars R).comp_algebraMap]
  exact .map hb (RingHomClass.toRingHom f)

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

theorem isIntegral_algHom_iff (f : A →ₐ[R] B) (hf : Function.Injective f) {x : A} :
    IsIntegral R (f x) ↔ IsIntegral R x := by
  simp [IsIntegral, ← RingHom.IsIntegralElem.map_iff (g := (f : A →+* B)) hf]

end

open Classical in

theorem Submodule.span_range_natDegree_eq_adjoin {R A} [CommRing R] [Semiring A] [Algebra R A]
    {x : A} {f : R[X]} (hf : f.Monic) (hfx : aeval x f = 0) :
    span R (Finset.image (x ^ ·) (Finset.range (natDegree f))) =
      Subalgebra.toSubmodule (Algebra.adjoin R {x}) := by
  nontriviality A
  have hf1 : f ≠ 1 := by rintro rfl; simp [one_ne_zero' A] at hfx
  refine (span_le.mpr fun s hs ↦ ?_).antisymm fun r hr ↦ ?_
  · rcases Finset.mem_image.1 (SetLike.mem_coe.mp hs) with ⟨k, -, rfl⟩
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin rfl) k
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hr
  rcases (aeval x).mem_range.mp hr with ⟨p, rfl⟩
  rw [← modByMonic_add_div p f, map_add, map_mul, hfx,
      zero_mul, add_zero, ← sum_C_mul_X_pow_eq (p %ₘ f), aeval_def, eval₂_sum, sum_def]
  refine sum_mem fun k hkq ↦ ?_
  rw [C_mul_X_pow_eq_monomial, eval₂_monomial, ← Algebra.smul_def]
  exact smul_mem _ _ (subset_span <| Finset.mem_image_of_mem _ <| Finset.mem_range.mpr <|
    (le_natDegree_of_mem_supp _ hkq).trans_lt <| natDegree_modByMonic_lt p hf hf1)

theorem IsIntegral.fg_adjoin_singleton [Algebra R B] {x : B} (hx : IsIntegral R x) :
    (Algebra.adjoin R {x}).toSubmodule.FG := by
  classical
  rcases hx with ⟨f, hfm, hfx⟩
  use (Finset.range <| f.natDegree).image (x ^ ·)
  exact span_range_natDegree_eq_adjoin hfm (by rwa [aeval_def])

variable (f : R →+* B)

theorem RingHom.isIntegralElem_zero : f.IsIntegralElem 0 :=
  f.map_zero ▸ f.isIntegralElem_map

theorem isIntegral_zero [Algebra R B] : IsIntegral R (0 : B) :=
  (algebraMap R B).isIntegralElem_zero

theorem RingHom.isIntegralElem_one : f.IsIntegralElem 1 :=
  f.map_one ▸ f.isIntegralElem_map

theorem isIntegral_one [Algebra R B] : IsIntegral R (1 : B) :=
  (algebraMap R B).isIntegralElem_one

variable (f : R →+* S)

theorem IsIntegral.of_pow [Algebra R B] {x : B} {n : ℕ} (hn : 0 < n) (hx : IsIntegral R <| x ^ n) :
    IsIntegral R x :=
  have ⟨p, hmonic, heval⟩ := hx
  ⟨expand R n p, hmonic.expand hn, by rwa [← aeval_def, expand_aeval]⟩

-- DISSOLVED: IsIntegral.of_aeval_monic

end

variable {R A B S : Type*}

variable [CommRing R] [CommRing A] [Ring B] [CommRing S]

variable [Algebra R A] [Algebra R B] (f : R →+* S)

theorem IsIntegral.map_of_comp_eq {R S T U : Type*} [CommRing R] [Ring S]
    [CommRing T] [Ring U] [Algebra R S] [Algebra T U] (φ : R →+* T) (ψ : S →+* U)
    (h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)) {a : S} (ha : IsIntegral R a) :
    IsIntegral T (ψ a) :=
  let ⟨p, hp⟩ := ha
  ⟨p.map φ, hp.1.map _, by
    rw [← eval_map, map_map, h, ← map_map, eval_map, eval₂_at_apply, eval_map, hp.2, ψ.map_zero]⟩
