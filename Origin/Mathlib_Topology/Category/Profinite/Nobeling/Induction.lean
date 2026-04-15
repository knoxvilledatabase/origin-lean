/-
Extracted from Topology/Category/Profinite/Nobeling/Induction.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Nöbeling's theorem

This file proves Nöbeling's theorem. For the overall proof outline see
`Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean`.

## Main result

* `LocallyConstant.freeOfProfinite`: Nöbeling's theorem.
  For `S : Profinite`, the `ℤ`-module `LocallyConstant S ℤ` is free.

## References

- [scholze2019condensed], Theorem 5.4.
-/

open Module Topology

universe u

namespace Profinite

namespace NobelingProof

variable {I : Type u} (C : Set (I → Bool)) [LinearOrder I] [WellFoundedLT I]

section Induction

/-!
## The induction

Here we put together the results of the sections `Zero`, `Limit` and `Successor` to prove the
predicate `P I o` holds for all ordinals `o`, and conclude with the main result:

* `GoodProducts.linearIndependent` which says that `GoodProducts C` is linearly independent when `C`
  is closed.

We also define

* `GoodProducts.Basis` which uses `GoodProducts.linearIndependent` and `GoodProducts.span` to
  define a basis for `LocallyConstant C ℤ`
-/

theorem GoodProducts.P0 : P I 0 := fun _ C _ hsC ↦ by
  have : C ⊆ {(fun _ ↦ false)} := fun c hc ↦ by
    ext x; exact Bool.eq_false_iff.mpr (fun ht ↦ not_lt_zero (hsC c hc x ht))
  rw [Set.subset_singleton_iff_eq] at this
  cases this
  · subst C
    exact linearIndependentEmpty
  · subst C
    exact linearIndependentSingleton

theorem GoodProducts.Plimit (o : Ordinal) (ho : Order.IsSuccLimit o) :
    (∀ (o' : Ordinal), o' < o → P I o') → P I o := by
  intro h hho C hC hsC
  rw [linearIndependent_iff_union_smaller C ho hsC, linearIndependent_subtype_iff]
  exact linearIndepOn_iUnion_of_directed
    (Monotone.directed_le fun _ _ h ↦ GoodProducts.smaller_mono C h) fun ⟨o', ho'⟩ ↦
    (linearIndependent_iff_smaller _ _).mp (h o' ho' (ho'.le.trans hho)
    (π C (ord I · < o')) (isClosed_proj _ _ hC) (contained_proj _ _))

theorem GoodProducts.linearIndependentAux (μ : Ordinal) : P I μ := by
  refine Ordinal.limitRecOn μ P0 (fun o h ho C hC hsC ↦ ?_)
      (fun o ho h ↦ (GoodProducts.Plimit o ho (fun o' ho' ↦ (h o' ho'))))
  have ho' : o < Ordinal.type (· < · : I → I → Prop) :=
    lt_of_lt_of_le (Order.lt_succ _) ho
  rw [linearIndependent_iff_sum C hsC ho']
  refine ModuleCat.linearIndependent_leftExact (succ_exact C hC hsC ho') ?_ ?_ (succ_mono C o)
    (square_commutes C ho')
  · exact h (le_of_lt ho') (π C (ord I · < o)) (isClosed_proj C o hC) (contained_proj C o)
  · exact linearIndependent_comp_of_eval C hC hsC ho' (span (π C (ord I · < o))
      (isClosed_proj C o hC)) (h (le_of_lt ho') (C' C ho') (isClosed_C' C hC ho')
      (contained_C' C ho'))

theorem GoodProducts.linearIndependent (hC : IsClosed C) :
    LinearIndependent ℤ (GoodProducts.eval C) :=
  GoodProducts.linearIndependentAux (Ordinal.type (· < · : I → I → Prop)) (le_refl _)
    C hC (fun _ _ _ _ ↦ Ordinal.typein_lt_type _ _)

noncomputable

def GoodProducts.Basis (hC : IsClosed C) :
    Basis (GoodProducts C) ℤ (LocallyConstant C ℤ) :=
  Basis.mk (GoodProducts.linearIndependent C hC) (GoodProducts.span C hC)

end Induction

variable {S : Profinite} {ι : S → I → Bool} (hι : IsClosedEmbedding ι)

include hι

theorem Nobeling_aux : Module.Free ℤ (LocallyConstant S ℤ) := Module.Free.of_equiv'
  (Module.Free.of_basis <| GoodProducts.Basis _ hι.isClosed_range) (LocallyConstant.congrLeftₗ ℤ
    hι.isEmbedding.toHomeomorph).symm

end NobelingProof

variable (S : Profinite.{u})

open scoped Classical in

noncomputable

def Nobeling.ι : S → ({C : Set S // IsClopen C} → Bool) := fun s C => decide (s ∈ C.1)

open scoped Classical in

theorem Nobeling.isClosedEmbedding : IsClosedEmbedding (Nobeling.ι S) := by
  apply Continuous.isClosedEmbedding
  · dsimp +unfoldPartialApp [ι]
    refine continuous_pi ?_
    intro C
    rw [← IsLocallyConstant.iff_continuous]
    refine ((IsLocallyConstant.tfae _).out 0 3).mpr ?_
    rintro ⟨⟩
    · refine IsClopen.isOpen (isClopen_compl_iff.mp ?_)
      convert C.2
      ext x
      simp
    · refine IsClopen.isOpen ?_
      convert C.2
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
  · intro a b h
    by_contra hn
    obtain ⟨C, hC, hh⟩ := exists_isClopen_of_totally_separated hn
    apply hh.2 ∘ of_decide_eq_true
    dsimp +unfoldPartialApp [ι] at h
    rw [← congr_fun h ⟨C, hC⟩]
    exact decide_eq_true hh.1

end Profinite

open Profinite NobelingProof

-- INSTANCE (free from Core): LocallyConstant.freeOfProfinite
