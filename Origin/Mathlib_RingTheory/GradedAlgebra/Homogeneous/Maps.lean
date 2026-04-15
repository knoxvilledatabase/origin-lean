/-
Extracted from RingTheory/GradedAlgebra/Homogeneous/Maps.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Maps on homogeneous ideals

In this file we define `HomogeneousIdeal.map` and `HomogeneousIdeal.comap`.
-/

namespace HomogeneousIdeal

section arbitrary_grading

variable {A B C σ τ ω ι F G : Type*}
  [Semiring A] [Semiring B] [Semiring C]
  [SetLike σ A] [SetLike τ B] [SetLike ω C]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [AddSubmonoidClass ω C]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} {𝒞 : ι → ω}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)

def map (I : HomogeneousIdeal 𝒜) : HomogeneousIdeal ℬ where
  __ := I.toIdeal.map f
  is_homogeneous' i b hb := by
    rw [Ideal.map] at hb
    induction hb using Submodule.span_induction generalizing i with
    | zero => simp
    | add => simp [*, Ideal.add_mem]
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      rw [← f.map_directSumDecompose]
      exact Ideal.mem_map_of_mem _ (I.2 _ ha)
    | smul a₁ a₂ ha₂ ih =>
      classical rw [smul_eq_mul, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
      exact sum_mem fun ij hij ↦ Ideal.mul_mem_left _ _ <| ih _

def comap (I : HomogeneousIdeal ℬ) : HomogeneousIdeal 𝒜 where
  __ := I.toIdeal.comap f
  is_homogeneous' n a ha := by
    rw [Ideal.mem_comap, HomogeneousIdeal.mem_iff, f.map_directSumDecompose]
    exact I.2 _ ha

variable {I I₁ I₂ I₃ : HomogeneousIdeal 𝒜} {J J₁ J₂ J₃ : HomogeneousIdeal ℬ}
  {K : HomogeneousIdeal 𝒞}

lemma map_le_iff_le_comap : I.map f ≤ J ↔ I ≤ J.comap f := Ideal.map_le_iff_le_comap

alias ⟨le_comap_of_map_le, map_le_of_le_comap⟩ := map_le_iff_le_comap

theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦
  map_le_iff_le_comap f
