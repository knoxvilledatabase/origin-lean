/-
Extracted from RingTheory/EssentialFiniteness.lean
Genuine: 16 of 24 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Essentially of finite type algebras

## Main results
- `Algebra.EssFiniteType`: The class of essentially of finite type algebras. An `R`-algebra is
  essentially of finite type if it is the localization of an algebra of finite type.
- `Algebra.EssFiniteType.algHom_ext`: The algebra homomorphisms out from an algebra essentially of
  finite type is determined by its values on a finite set.

-/

open scoped TensorProduct

namespace Algebra

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]

variable [Algebra R S] [Algebra R T]

class EssFiniteType : Prop where
  cond : ∃ s : Finset S,
    IsLocalization ((IsUnit.submonoid S).comap (algebraMap (adjoin R (s : Set S)) S)) S

noncomputable

def EssFiniteType.finset [h : EssFiniteType R S] : Finset S := h.cond.choose

noncomputable

abbrev EssFiniteType.subalgebra [EssFiniteType R S] : Subalgebra R S :=
  Algebra.adjoin R (finset R S : Set S)

lemma EssFiniteType.adjoin_mem_finset [EssFiniteType R S] :
    adjoin R { x : subalgebra R S | x.1 ∈ finset R S } = ⊤ := adjoin_adjoin_coe_preimage

-- INSTANCE (free from Core): [EssFiniteType

noncomputable

def EssFiniteType.submonoid [EssFiniteType R S] : Submonoid (EssFiniteType.subalgebra R S) :=
  ((IsUnit.submonoid S).comap (algebraMap (EssFiniteType.subalgebra R S) S))

-- INSTANCE (free from Core): EssFiniteType.isLocalization

lemma essFiniteType_cond_iff (σ : Finset S) :
    IsLocalization ((IsUnit.submonoid S).comap (algebraMap (adjoin R (σ : Set S)) S)) S ↔
    (∀ s : S, ∃ t ∈ Algebra.adjoin R (σ : Set S),
      IsUnit t ∧ s * t ∈ Algebra.adjoin R (σ : Set S)) := by
  constructor <;> intro hσ
  · intro s
    obtain ⟨⟨⟨x, hx⟩, ⟨t, ht⟩, ht'⟩, h⟩ := hσ.1.2 s
    exact ⟨t, ht, ht', h ▸ hx⟩
  · constructor; constructor
    · exact fun y ↦ y.prop
    · intro s
      obtain ⟨t, ht, ht', h⟩ := hσ s
      exact ⟨⟨⟨_, h⟩, ⟨t, ht⟩, ht'⟩, rfl⟩
    · intro x y e
      exact ⟨1, by simpa using Subtype.ext e⟩

lemma essFiniteType_iff :
    EssFiniteType R S ↔ ∃ (σ : Finset S),
      (∀ s : S, ∃ t ∈ Algebra.adjoin R (σ : Set S),
        IsUnit t ∧ s * t ∈ Algebra.adjoin R (σ : Set S)) := by
  simp_rw [← essFiniteType_cond_iff]
  constructor <;> exact fun ⟨a, b⟩ ↦ ⟨a, b⟩

-- INSTANCE (free from Core): EssFiniteType.of_finiteType

variable {R} in

lemma EssFiniteType.of_isLocalization (M : Submonoid R) [IsLocalization M S] :
    EssFiniteType R S := by
  rw [essFiniteType_iff]
  use ∅
  simp only [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot,
    Set.mem_range, exists_exists_eq_and]
  intro s
  obtain ⟨⟨x, t⟩, e⟩ := IsLocalization.surj M s
  exact ⟨_, IsLocalization.map_units S t, x, e.symm⟩

lemma EssFiniteType.of_id : EssFiniteType R R := inferInstance

variable [Algebra S T] [IsScalarTower R S T]

lemma EssFiniteType.aux (σ : Subalgebra R S)
    (hσ : ∀ s : S, ∃ t ∈ σ, IsUnit t ∧ s * t ∈ σ)
    (τ : Set T) (t : T) (ht : t ∈ Algebra.adjoin S τ) :
    ∃ s ∈ σ, IsUnit s ∧ s • t ∈ σ.map (IsScalarTower.toAlgHom R S T) ⊔ Algebra.adjoin R τ := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ht
  · intro t ht
    exact ⟨1, Subalgebra.one_mem _, isUnit_one,
      (one_smul S t).symm ▸ Algebra.mem_sup_right (Algebra.subset_adjoin ht)⟩
  · intro s
    obtain ⟨s', hs₁, hs₂, hs₃⟩ := hσ s
    refine ⟨_, hs₁, hs₂, Algebra.mem_sup_left ?_⟩
    rw [Algebra.smul_def, ← map_mul, mul_comm]
    exact ⟨_, hs₃, rfl⟩
  · rintro x y - - ⟨sx, hsx, hsx', hsx''⟩ ⟨sy, hsy, hsy', hsy''⟩
    refine ⟨_, σ.mul_mem hsx hsy, hsx'.mul hsy', ?_⟩
    rw [smul_add, mul_smul, mul_smul, Algebra.smul_def sx (sy • y), smul_comm,
      Algebra.smul_def sy (sx • x)]
    apply add_mem (mul_mem _ hsx'') (mul_mem _ hsy'') <;>
      exact Algebra.mem_sup_left ⟨_, ‹_›, rfl⟩
  · rintro x y - - ⟨sx, hsx, hsx', hsx''⟩ ⟨sy, hsy, hsy', hsy''⟩
    refine ⟨_, σ.mul_mem hsx hsy, hsx'.mul hsy', ?_⟩
    rw [mul_smul, ← smul_eq_mul, smul_comm sy x, ← smul_assoc, smul_eq_mul]
    exact mul_mem hsx'' hsy''

lemma EssFiniteType.comp [h₁ : EssFiniteType R S] [h₂ : EssFiniteType S T] :
    EssFiniteType R T := by
  rw [essFiniteType_iff] at h₁ h₂ ⊢
  classical
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  use s.image (IsScalarTower.toAlgHom R S T) ∪ t
  simp only [Finset.coe_union, Finset.coe_image, Algebra.adjoin_union, Algebra.adjoin_image]
  intro x
  obtain ⟨y, hy₁, hy₂, hy₃⟩ := ht x
  obtain ⟨t₁, h₁, h₂, h₃⟩ := EssFiniteType.aux _ _ _ _ hs _ y hy₁
  obtain ⟨t₂, h₄, h₅, h₆⟩ := EssFiniteType.aux _ _ _ _ hs _ _ hy₃
  refine ⟨t₂ • t₁ • y, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact mul_mem (Algebra.mem_sup_left ⟨_, h₄, rfl⟩) h₃
  · rw [Algebra.smul_def, Algebra.smul_def]
    exact (h₅.map _).mul ((h₂.map _).mul hy₂)
  · rw [← mul_smul, mul_comm, smul_mul_assoc, mul_comm, mul_comm y, mul_smul, Algebra.smul_def]
    exact mul_mem (Algebra.mem_sup_left ⟨_, h₁, rfl⟩) h₆

open EssFiniteType in

lemma essFiniteType_iff_exists_subalgebra : EssFiniteType R S ↔
    ∃ (S₀ : Subalgebra R S) (M : Submonoid S₀), FiniteType R S₀ ∧ IsLocalization M S := by
  refine ⟨fun h ↦ ⟨subalgebra R S, submonoid R S, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨S₀, M, _, _⟩
  letI := of_isLocalization S M
  exact comp R S₀ S

-- INSTANCE (free from Core): EssFiniteType.baseChange

lemma EssFiniteType.comp_iff [EssFiniteType R S] :
    EssFiniteType R T ↔ EssFiniteType S T :=
  ⟨fun _ ↦ of_comp R S T, fun _ ↦ comp R S T⟩

-- INSTANCE (free from Core): [EssFiniteType

-- INSTANCE (free from Core): [EssFiniteType

end

variable {R S T} in

lemma EssFiniteType.of_surjective (f : S →ₐ[R] T) (hf : Function.Surjective f)
    [EssFiniteType R S] : EssFiniteType R T := by
  let := f.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S T := .of_surjective (Algebra.linearMap S T) hf
  exact .comp R S T

variable {R S T} in

lemma EssFiniteType.iff_of_algEquiv (f : S ≃ₐ[R] T) :
    EssFiniteType R S ↔ EssFiniteType R T where
  mp _ := .of_surjective f.toAlgHom f.surjective
  mpr _ := .of_surjective f.symm.toAlgHom f.symm.surjective

variable {R S} in

lemma EssFiniteType.algHom_ext [EssFiniteType R S]
    (f g : S →ₐ[R] T) (H : ∀ s ∈ finset R S, f s = g s) : f = g := by
  suffices f.toRingHom = g.toRingHom by ext; exact RingHom.congr_fun this _
  apply IsLocalization.ringHom_ext (EssFiniteType.submonoid R S)
  suffices f.comp (IsScalarTower.toAlgHom R _ S) = g.comp (IsScalarTower.toAlgHom R _ S) by
    ext; exact AlgHom.congr_fun this _
  apply AlgHom.ext_of_adjoin_eq_top (s := { x | x.1 ∈ finset R S })
  · exact adjoin_mem_finset R S
  · rintro ⟨x, hx⟩ hx'; exact H x hx'

-- INSTANCE (free from Core): EssFiniteType.quotient_map

end Algebra

namespace RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {f : R →+* S}
