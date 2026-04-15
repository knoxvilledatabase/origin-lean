/-
Extracted from Algebra/Category/ModuleCat/Ext/DimensionShifting.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Dimension Shifting

-/

universe v u

variable {R : Type u} [CommRing R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

open CategoryTheory Abelian

noncomputable abbrev ModuleCat.projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    ShortComplex (ModuleCat.{v} R) :=
  let e : Module.Basis M R (M →₀ Shrink.{v} R) :=
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
  (e.constr ℕ id).shortComplexKer

theorem ModuleCat.shortExact_projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    M.projectiveShortComplex.ShortExact := by
  apply LinearMap.shortExact_shortComplexKer
  refine fun m ↦ ⟨Finsupp.single m 1, ?_⟩
  simp [Module.Basis.constr_apply]

-- INSTANCE (free from Core): [Small.{v}

theorem precomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    (M : ModuleCat.{v} R) {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (n : ℕ)
    [Projective S.X₂] : Function.Surjective (h.extClass.precomp M (add_comm 1 n)) :=
  fun x ↦ Ext.contravariant_sequence_exact₃ h M x (Ext.eq_zero_of_projective _) (add_comm 1 n)

theorem postcomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (M : ModuleCat.{v} R) (n : ℕ)
    [Injective S.X₂] : Function.Surjective (h.extClass.postcomp M (rfl : n + 1 = n + 1)) :=
  fun x ↦ Ext.covariant_sequence_exact₁ M h x (Ext.eq_zero_of_injective _) rfl
