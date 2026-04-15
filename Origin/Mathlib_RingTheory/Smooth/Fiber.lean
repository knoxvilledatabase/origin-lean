/-
Extracted from RingTheory/Smooth/Fiber.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Flat and smooth fibers imply smooth

## Main results
- `Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`:
  Let `(R, m, k)` be a local ring, `S` be a local `R`-algebra that is flat,
  essentially of finite presentation, and `k ⊗[R] S` is `k`-formally smooth.
  Then `S` is `R`-formally smooth.
- `Algebra.mem_smoothLocus_of_formallySmooth_fiber`:
  Let `S` be a flat and finitely presented `R`-algebra, and `q` be a prime of `S` lying over `p`.
  If `κ(p) ⊗[R] S` is `κ(p)`-smooth, then `S` is smooth at `q`.
- `Algebra.Smooth.of_formallySmooth_fiber`:
  Flat and finitely presented and smooth fibers imply smooth.
- `Algebra.Etale.of_formallyUnramified_of_flat`:
  Flat and finitely presented and (formally) unramified implies etale.

## Note

For the converse that smooth implies flat, see `Mathlib/RingTheory/Smooth/Flat.lean`.

-/

open TensorProduct IsLocalRing

namespace Algebra

local notation "𝓀[" R "]" => ResidueField R

local notation "𝓂[" R "]" => maximalIdeal R

variable {R S P : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

variable [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]

section IsLocalRing

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra.FormallySmooth 𝓀[R] (𝓀[R] ⊗[R] S)]

set_option backward.isDefEq.respectTransparency false in

attribute [local irreducible] KaehlerDifferential in

attribute [local instance] TensorProduct.rightAlgebra in

lemma FormallySmooth.of_formallySmooth_residueField_tensor (M : Submonoid P)
    [IsLocalization M S] [Algebra.FinitePresentation R P] : Algebra.FormallySmooth R S := by
  /-
  By the fact that `S` is essentially of finite presentation, we get
  `S = (P/I)[M⁻¹] = P[M⁻¹]/I[M⁻¹]`, where `P` is a polynomial ring and `M` some submonoid of `P/I`.
  We then apply `FormallySmooth.of_formallySmooth_residueField_tensor_aux` to this presentation.
  -/
  classical
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R P)
  let M' := M.comap f₀
  let P' := Localization M'
  let fP : P' →ₐ[R] S := IsLocalization.liftAlgHom (M := M')
      (f := (IsScalarTower.toAlgHom R P S).comp f₀) fun x ↦ by
    simpa using IsLocalization.map_units (M := M) _ ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := M') _ x ⟨s, hs⟩, ?_⟩
    simp [fP, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight]
  have hfP : (RingHom.ker fP).FG := by
    have := Algebra.FinitePresentation.ker_fG_of_surjective _ hf₀
    convert this.map (algebraMap _ P')
    refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ by simp_all [fP])
    intro x hx
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M' x
    obtain ⟨a, ha, e⟩ : ∃ a ∈ M, a * f₀ x = 0 := by
      simpa [fP, IsLocalization.lift_mk', IsLocalization.map_eq_zero_iff M] using hx
    obtain ⟨a, rfl⟩ := hf₀ a
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨a, ha, by simpa⟩
  algebraize [fP.toRingHom]
  have : FormallyEtale (MvPolynomial (Fin n) R) P' := .of_isLocalization M'
  have : FormallySmooth R P' := .comp _ (MvPolynomial (Fin n) R) _
  have : Module.Free P' Ω[P'⁄R] :=
    .of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) P')
  exact FormallySmooth.of_formallySmooth_residueField_tensor_aux (R := R) (S := S) hf₁ hfP

end IsLocalRing
