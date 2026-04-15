/-
Extracted from RingTheory/Etale/Field.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Étale algebras over fields

## Main results

Let `K` be a field, `A` be a `K`-algebra and `L` be a field extension of `K`.

- `Algebra.FormallyEtale.of_isSeparable`:
    If `L` is separable over `K`, then `L` is formally étale over `K`.
- `Algebra.FormallyEtale.iff_isSeparable`:
    If `L` is (essentially) of finite type over `K`, then `L/K` is étale iff `L/K` is separable.
- `Algebra.FormallyEtale.iff_formallyUnramified_of_field`:
    If `A` is (essentially) of finite type over `K`,
    then `A/K` is formally étale iff `A/K` is formally unramified.
- `Algebra.FormallyEtale.iff_exists_algEquiv_prod`:
    If `A` is (essentially) of finite type over `K`,
    then `A/K` is étale iff `A` is a finite product of separable field extensions.
- `Algebra.Etale.iff_exists_algEquiv_prod`:
    `A/K` is étale iff `A` is a finite product of finite separable field extensions.

## References

- [B. Iversen, *Generic Local Structure of the Morphisms in Commutative Algebra*][iversen]

-/

universe u

variable (K L : Type*) (A : Type u) [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A]

open Algebra Polynomial

open scoped TensorProduct

namespace Algebra.FormallyEtale

theorem of_isSeparable_aux [Algebra.IsSeparable K L] [EssFiniteType K L] :
    FormallyEtale K L := by
  -- We already know that for field extensions
  -- IsSeparable + EssFiniteType => FormallyUnramified + Finite
  have := FormallyUnramified.of_isSeparable K L
  have := FormallyUnramified.finite_of_free (R := K) (S := L)
  -- We shall show that any `f : L → B/I` can be lifted to `L → B` if `I^2 = ⊥`
  refine FormallyEtale.iff_comp_bijective.mpr fun B _ _ I h ↦ ?_
  refine ⟨FormallyUnramified.iff_comp_injective_of_small.mp
    (FormallyUnramified.of_isSeparable K L) I h, ?_⟩
  intro f
  -- By separability and finiteness, we may assume `L = K(α)` with `p` the minpoly of `α`.
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  -- Let `x : B` such that `f(α) = x` in `B / I`.
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (f pb.gen)
  have helper : ∀ x, IsScalarTower.toAlgHom K B (B ⧸ I) x = Ideal.Quotient.mk I x := fun _ ↦ rfl
  -- Then `p(x) = 0 mod I`, and the goal is to find some `ε ∈ I` such that
  -- `p(x + ε) = p(x) + ε p'(x) = 0`, and we will get our lift into `B`.
  have hx' : Ideal.Quotient.mk I (aeval x (minpoly K pb.gen)) = 0 := by
    rw [← helper, ← aeval_algHom_apply, helper, hx, aeval_algHom_apply, minpoly.aeval, map_zero]
  -- Since `p` is separable, `-p'(x)` is invertible in `B ⧸ I`,
  obtain ⟨u, hu⟩ : ∃ u, (aeval x) (derivative (minpoly K pb.gen)) * u + 1 ∈ I := by
    have := (isUnit_iff_ne_zero.mpr ((Algebra.IsSeparable.isSeparable K
      pb.gen).aeval_derivative_ne_zero (minpoly.aeval K _))).map f
    rw [← aeval_algHom_apply, ← hx, ← helper, aeval_algHom_apply, helper] at this
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (-this.unit⁻¹ : B ⧸ I)
    use u
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_mul, map_one, hu, mul_neg,
      IsUnit.mul_val_inv, neg_add_cancel]
  -- And `ε = p(x)/(-p'(x))` works.
  use pb.liftEquiv.symm ⟨x + u * aeval x (minpoly K pb.gen), ?_⟩
  · apply pb.algHom_ext
    simp [hx, hx']
  · rw [← eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero, derivative_map,
      ← one_mul (eval x _), eval_map_algebraMap, eval_map_algebraMap, ← mul_assoc, ← add_mul,
      ← Ideal.mem_bot, ← h, pow_two, add_comm]
    · exact Ideal.mul_mem_mul hu (Ideal.Quotient.eq_zero_iff_mem.mp hx')
    rw [← Ideal.mem_bot, ← h]
    apply Ideal.pow_mem_pow
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hx', mul_zero]

open scoped IntermediateField in

lemma of_isSeparable [Algebra.IsSeparable K L] : FormallyEtale K L := by
  -- We shall show that any `f : L → B/I` can be lifted to `L → B` if `I^2 = ⊥`.
  refine FormallyEtale.iff_comp_bijective.mpr fun B _ _ I h ↦ ?_
  -- But we already know that there exists a unique lift for every finite subfield of `L`
  -- by `of_isSeparable_aux`, so we can glue them all together.
  refine ⟨FormallyUnramified.iff_comp_injective_of_small.mp
    (FormallyUnramified.of_isSeparable K L) I h, ?_⟩
  intro f
  have : ∀ k : L, ∃! g : K⟮k⟯ →ₐ[K] B,
      (Ideal.Quotient.mkₐ K I).comp g = f.comp (IsScalarTower.toAlgHom K _ L) := by
    intro k
    have := IsSeparable.of_algHom _ _ (IsScalarTower.toAlgHom K (K⟮k⟯) L)
    have := IntermediateField.adjoin.finiteDimensional
      (Algebra.IsSeparable.isSeparable K k).isIntegral
    have := FormallyEtale.of_isSeparable_aux K (K⟮k⟯)
    have := FormallyEtale.comp_bijective (R := K) (A := K⟮k⟯) I h
    exact this.existsUnique _
  choose g hg₁ hg₂ using this
  have hg₃ : ∀ x y (h : x ∈ K⟮y⟯), g y ⟨x, h⟩ = g x (IntermediateField.AdjoinSimple.gen K x) := by
    intro x y h
    have e : K⟮x⟯ ≤ K⟮y⟯ := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact h
    rw [← hg₂ _ ((g _).comp (IntermediateField.inclusion e))]
    · rfl
    apply AlgHom.ext
    rw [← AlgHom.comp_assoc, hg₁, AlgHom.comp_assoc]
    simp
  have H : ∀ x y : L, ∃ α : L, x ∈ K⟮α⟯ ∧ y ∈ K⟮α⟯ := by
    intro x y
    have : FiniteDimensional K K⟮x, y⟯ := by
      apply IntermediateField.finiteDimensional_adjoin
      intro x _; exact (Algebra.IsSeparable.isSeparable K x).isIntegral
    have := IsSeparable.of_algHom _ _ (IsScalarTower.toAlgHom K (K⟮x, y⟯) L)
    obtain ⟨⟨α, hα⟩, e⟩ := Field.exists_primitive_element K K⟮x, y⟯
    apply_fun (IntermediateField.map (IntermediateField.val _)) at e
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map] at e
    simp only [IntermediateField.coe_val, Set.image_singleton,
      IntermediateField.fieldRange_val] at e
    have hx : x ∈ K⟮α⟯ := e ▸ IntermediateField.subset_adjoin K {x, y} (by simp)
    have hy : y ∈ K⟮α⟯ := e ▸ IntermediateField.subset_adjoin K {x, y} (by simp)
    exact ⟨α, hx, hy⟩
  refine ⟨⟨⟨⟨⟨fun x ↦ g x (IntermediateField.AdjoinSimple.gen K x), ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩
  · change g 1 1 = 1; rw [map_one]
  · intro x y
    obtain ⟨α, hx, hy⟩ := H x y
    simp only [← hg₃ _ _ hx, ← hg₃ _ _ hy, ← map_mul, ← hg₃ _ _ (mul_mem hx hy)]
    rfl
  · change g 0 0 = 0; rw [map_zero]
  · intro x y
    obtain ⟨α, hx, hy⟩ := H x y
    simp only [← hg₃ _ _ hx, ← hg₃ _ _ hy, ← map_add, ← hg₃ _ _ (add_mem hx hy)]
    rfl
  · intro r
    change g _ (algebraMap K _ r) = _
    rw [AlgHom.commutes]
  · ext x
    simpa using AlgHom.congr_fun (hg₁ x) (IntermediateField.AdjoinSimple.gen K x)

theorem iff_isSeparable [EssFiniteType K L] :
    FormallyEtale K L ↔ Algebra.IsSeparable K L :=
  ⟨fun _ ↦ FormallyUnramified.isSeparable K L, fun _ ↦ of_isSeparable K L⟩

attribute [local instance] Ideal.Quotient.field FormallyUnramified.finite_of_free in

lemma of_formallyUnramified_of_field [EssFiniteType K A] [FormallyUnramified K A] :
    FormallyEtale K A := by
  have := FormallyUnramified.isReduced_of_field K A
  have : IsArtinianRing A := .of_finite K A
  have (I : MaximalSpectrum A) : FormallyEtale K (A ⧸ I.asIdeal) := by
    rw [FormallyEtale.iff_isSeparable, ← FormallyUnramified.iff_isSeparable]
    infer_instance
  exact .of_equiv ((IsArtinianRing.equivPi A).restrictScalars K).symm

variable {K A} in

lemma iff_formallyUnramified_of_field [EssFiniteType K A] :
    FormallyEtale K A ↔ FormallyUnramified K A :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ .of_formallyUnramified_of_field K A⟩

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in

theorem iff_exists_algEquiv_prod [EssFiniteType K A] :
    FormallyEtale K A ↔
      ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
        (_ : ∀ i, Algebra K (Ai i)) (_ : A ≃ₐ[K] Π i, Ai i),
        ∀ i, Algebra.IsSeparable K (Ai i) := by
  classical
  constructor
  · intro H
    have := FormallyUnramified.finite_of_free K A
    have := FormallyUnramified.isReduced_of_field K A
    have : IsArtinianRing A := isArtinian_of_tower K inferInstance
    let v (i : MaximalSpectrum A) : A := (IsArtinianRing.equivPi A).symm (Pi.single i 1)
    rw [FormallyEtale.iff_of_equiv ((IsArtinianRing.equivPi A).restrictScalars K),
      FormallyEtale.pi_iff] at H
    exact ⟨_, inferInstance, _, _, _, (IsArtinianRing.equivPi A).restrictScalars K,
      fun I ↦ (iff_isSeparable _ _).mp inferInstance⟩
  · intro ⟨I, _, Ai, _, _, e, _⟩
    rw [FormallyEtale.iff_of_equiv e, FormallyEtale.pi_iff]
    exact fun I ↦ of_isSeparable K (Ai I)

end Algebra.FormallyEtale

theorem Algebra.Etale.iff_exists_algEquiv_prod :
    Etale K A ↔
      ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
        (_ : ∀ i, Algebra K (Ai i)) (_ : A ≃ₐ[K] Π i, Ai i),
        ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) := by
  constructor
  · intro H
    obtain ⟨I, _, Ai, _, _, e, _⟩ := (FormallyEtale.iff_exists_algEquiv_prod K A).mp inferInstance
    have := FormallyUnramified.finite_of_free K A
    exact ⟨_, ‹_›, _, _, _, e, fun i ↦ ⟨.of_surjective ((LinearMap.proj i).comp e.toLinearMap)
      ((Function.surjective_eval i).comp e.surjective), inferInstance⟩⟩
  · intro ⟨I, _, Ai, _, _, e, H⟩
    choose h₁ h₂ using H
    have := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
    refine ⟨?_, FinitePresentation.of_finiteType.mp inferInstance⟩
    exact (FormallyEtale.iff_exists_algEquiv_prod K A).mpr ⟨_, inferInstance, _, _, _, e, h₂⟩
