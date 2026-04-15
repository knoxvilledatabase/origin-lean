/-
Extracted from LinearAlgebra/CliffordAlgebra/Grading.lean
Genuine: 10 of 14 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Results about the grading structure of the clifford algebra

The main result is `CliffordAlgebra.gradedAlgebra`, which says that the clifford algebra is a
ℤ₂-graded algebra (or "superalgebra").
-/

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

open scoped DirectSum

variable (Q)

def evenOdd (i : ZMod 2) : Submodule R (CliffordAlgebra Q) :=
  ⨆ j : { n : ℕ // ↑n = i }, LinearMap.range (ι Q) ^ (j : ℕ)

theorem one_le_evenOdd_zero : 1 ≤ evenOdd Q 0 := by
  refine le_trans ?_ (le_iSup _ ⟨0, Nat.cast_zero⟩)
  exact (pow_zero _).ge

theorem range_ι_le_evenOdd_one : LinearMap.range (ι Q) ≤ evenOdd Q 1 := by
  refine le_trans ?_ (le_iSup _ ⟨1, Nat.cast_one⟩)
  exact (pow_one _).ge

theorem ι_mem_evenOdd_one (m : M) : ι Q m ∈ evenOdd Q 1 :=
  range_ι_le_evenOdd_one Q <| LinearMap.mem_range_self _ m

theorem ι_mul_ι_mem_evenOdd_zero (m₁ m₂ : M) : ι Q m₁ * ι Q m₂ ∈ evenOdd Q 0 :=
  Submodule.mem_iSup_of_mem ⟨2, rfl⟩
    (by
      rw [Subtype.coe_mk, pow_two]
      exact
        Submodule.mul_mem_mul (LinearMap.mem_range_self (ι Q) m₁)
          (LinearMap.mem_range_self (ι Q) m₂))

theorem evenOdd_mul_le (i j : ZMod 2) : evenOdd Q i * evenOdd Q j ≤ evenOdd Q (i + j) := by
  simp_rw [evenOdd, Submodule.iSup_eq_span, Submodule.span_mul_span]
  apply Submodule.span_mono
  simp_rw [Set.iUnion_mul, Set.mul_iUnion, Set.iUnion_subset_iff, Set.mul_subset_iff]
  rintro ⟨xi, rfl⟩ ⟨yi, rfl⟩ x hx y hy
  refine Set.mem_iUnion.mpr ⟨⟨xi + yi, Nat.cast_add _ _⟩, ?_⟩
  simp only [pow_add]
  exact Submodule.mul_mem_mul hx hy

-- INSTANCE (free from Core): evenOdd.gradedMonoid

protected def GradedAlgebra.ι : M →ₗ[R] ⨁ i : ZMod 2, evenOdd Q i :=
  DirectSum.lof R (ZMod 2) (fun i => ↥(evenOdd Q i)) 1 ∘ₗ (ι Q).codRestrict _ (ι_mem_evenOdd_one Q)

nonrec theorem GradedAlgebra.ι_sq_scalar (m : M) :
    GradedAlgebra.ι Q m * GradedAlgebra.ι Q m = algebraMap R _ (Q m) := by
  rw [GradedAlgebra.ι_apply Q, DirectSum.of_mul_of, DirectSum.algebraMap_apply]
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl <| ι_sq_scalar _ _)

theorem GradedAlgebra.lift_ι_eq (i' : ZMod 2) (x' : evenOdd Q i') :
    lift Q ⟨GradedAlgebra.ι Q, GradedAlgebra.ι_sq_scalar Q⟩ x' =
      DirectSum.of (fun i => evenOdd Q i) i' x' := by
  obtain ⟨x', hx'⟩ := x'
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx' using Submodule.iSup_induction' with
  | mem i x hx =>
    obtain ⟨i, rfl⟩ := i
    dsimp only [Subtype.coe_mk] at hx
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [map_mul, ih, lift_ι_apply, GradedAlgebra.ι_apply Q, DirectSum.of_mul_of]
      refine DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext ?_ ?_) <;>
        dsimp only [GradedMonoid.mk, Subtype.coe_mk]
      · rw [Nat.succ_eq_add_one, add_comm, Nat.cast_add, Nat.cast_one]
      rfl
  | zero =>
    rw [map_zero]
    apply Eq.symm
    apply DFinsupp.single_eq_zero.mpr; rfl
  | add x y hx hy ihx ihy =>
    rw [map_add, ihx, ihy, ← map_add]; rfl

-- INSTANCE (free from Core): gradedAlgebra

theorem iSup_ι_range_eq_top : ⨆ i : ℕ, LinearMap.range (ι Q) ^ i = ⊤ := by
  rw [← (DirectSum.Decomposition.isInternal (evenOdd Q)).submodule_iSup_eq_top, eq_comm]
  calc
    -- Porting note: needs extra annotations, no longer unifies against the goal in the face of
    -- ambiguity
    ⨆ (i : ZMod 2) (j : { n : ℕ // ↑n = i }), LinearMap.range (ι Q) ^ (j : ℕ) =
        ⨆ i : Σ i : ZMod 2, { n : ℕ // ↑n = i }, LinearMap.range (ι Q) ^ (i.2 : ℕ) := by
      rw [iSup_sigma]
    _ = ⨆ i : ℕ, LinearMap.range (ι Q) ^ i :=
      Function.Surjective.iSup_congr (fun i => i.2) (fun i => ⟨⟨_, i, rfl⟩, rfl⟩) fun _ => rfl
