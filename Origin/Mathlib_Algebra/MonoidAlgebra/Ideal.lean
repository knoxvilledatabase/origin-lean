/-
Extracted from Algebra/MonoidAlgebra/Ideal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about ideals of `MonoidAlgebra` and `AddMonoidAlgebra`
-/

variable {k A G : Type*}

set_option backward.isDefEq.respectTransparency false in

theorem MonoidAlgebra.mem_ideal_span_of_image [Monoid G] [Semiring k] {s : Set G}
    {x : MonoidAlgebra k G} :
    x ∈ Ideal.span (MonoidAlgebra.of k G '' s) ↔ ∀ m ∈ x.support, ∃ m' ∈ s, ∃ d, m = d * m' := by
  classical
  let RHS : Ideal (MonoidAlgebra k G) :=
    { carrier := { p | ∀ m : G, m ∈ p.support → ∃ m' ∈ s, ∃ d, m = d * m' }
      add_mem' {x y} hx hy m hm := (Finset.mem_union.1 <| Finsupp.support_add hm).elim (hx m) (hy m)
      zero_mem' := by simp
      smul_mem' x y hy m hm := by
        simp only [smul_eq_mul, mul_def] at hm
        obtain ⟨xm, -, hm⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hm)
        obtain ⟨ym, hym, hm⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hm)
        obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hm)
        refine (hy _ hym).imp fun sm p => And.imp_right ?_ p
        rintro ⟨d, rfl⟩
        exact ⟨xm * d, (mul_assoc _ _ _).symm⟩ }
  change _ ↔ x ∈ RHS
  constructor
  · suffices Ideal.span (⇑(of k G) '' s) ≤ RHS from @this x
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩ m hm
    refine ⟨_, hi, 1, ?_⟩
    simpa using Finsupp.support_single_subset hm
  · intro hx
    rw [← Finsupp.sum_single x]
    apply Ideal.sum_mem _ fun i hi ↦ ?_
    obtain ⟨d, hd, d2, rfl⟩ := hx _ hi
    simpa using Ideal.mul_mem_left _ (.single d2 <| x (d2 * d)) (b := of k G d)
      (Ideal.subset_span <| Set.mem_image_of_mem _ hd)

theorem AddMonoidAlgebra.mem_ideal_span_of'_image [AddMonoid A] [Semiring k] {s : Set A}
    {x : AddMonoidAlgebra k A} :
    x ∈ Ideal.span (AddMonoidAlgebra.of' k A '' s) ↔ ∀ m ∈ x.support, ∃ m' ∈ s, ∃ d, m = d + m' :=
  @MonoidAlgebra.mem_ideal_span_of_image k (Multiplicative A) _ _ _ _
