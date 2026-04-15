/-
Extracted from RingTheory/Flat/EquationalCriterion.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # The equational criterion for flatness

Let $M$ be a module over a commutative ring $R$. Let us say that a relation
$\sum_{i \in \iota} f_i x_i = 0$ in $M$ is *trivial* (`Module.IsTrivialRelation`) if there exist a
finite index type $\kappa$ = `Fin k`, elements $(y_j)_{j \in \kappa}$ of $M$,
and elements $(a_{ij})_{i \in \iota, j \in \kappa}$ of $R$ such that for all $i$,
$$x_i = \sum_j a_{ij} y_j$$
and for all $j$,
$$\sum_i f_i a_{ij} = 0.$$

The *equational criterion for flatness* [Stacks 00HK](https://stacks.math.columbia.edu/tag/00HK)
(`Module.Flat.iff_forall_isTrivialRelation`) states that $M$ is flat if and only if every relation
in $M$ is trivial.

The equational criterion for flatness can be stated in the following form
(`Module.Flat.iff_forall_exists_factorization`). Let $M$ be an $R$-module. Then the following two
conditions are equivalent:
* $M$ is flat.
* For finite free modules $R^l$, all elements $f \in R^l$, and all linear maps
  $x \colon R^l \to M$ such that $x(f) = 0$, there exist a finite free module $R^k$ and
  linear maps $a \colon R^l \to R^k$ and $y \colon R^k \to M$ such
  that $x = y \circ a$ and $a(f) = 0$.

Of course, the module $R^l$ in this statement can be replaced by an arbitrary free module
(`Module.Flat.exists_factorization_of_apply_eq_zero_of_free`).

We also have the following strengthening of the equational criterion for flatness
(`Module.Flat.exists_factorization_of_comp_eq_zero_of_free`): Let $M$ be a
flat module. Let $K$ and $N$ be finite $R$-modules with $N$ free, and let $f \colon K \to N$ and
$x \colon N \to M$ be linear maps such that $x \circ f = 0$. Then there exist a finite free module
$R^k$ and linear maps $a \colon N \to R^k$ and $y \colon R^k \to M$ such
that $x = y \circ a$ and $a \circ f = 0$. We recover the usual equational criterion for flatness if
$K = R$ and $N = R^l$. This is used in the proof of Lazard's theorem.

We conclude that every linear map from a finitely presented module to a flat module factors
through a finite free module (`Module.Flat.exists_factorization_of_isFinitelyPresented`), and
every finitely presented flat module is projective (`Module.Flat.projective_of_finitePresentation`).

## References

* [Stacks: Flat modules and flat ring maps](https://stacks.math.columbia.edu/tag/00H9)
* [Stacks: Characterizing flatness](https://stacks.math.columbia.edu/tag/058C)

-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open LinearMap TensorProduct Finsupp

namespace Module

variable {ι : Type*} [Fintype ι] (f : ι → R) (x : ι → M)

abbrev IsTrivialRelation : Prop :=
  ∃ (k : ℕ) (a : ι → Fin k → R) (y : Fin k → M),
    (∀ i, x i = ∑ j, a i j • y j) ∧ ∀ j, ∑ i, f i * a i j = 0

variable {f x}

theorem isTrivialRelation_iff_vanishesTrivially :
    IsTrivialRelation f x ↔ VanishesTrivially R f x := by
  simp only [IsTrivialRelation, VanishesTrivially, smul_eq_mul, mul_comm]

theorem _root_.Equiv.isTrivialRelation_comp {κ} [Fintype κ] (e : κ ≃ ι) :
    IsTrivialRelation (f ∘ e) (x ∘ e) ↔ IsTrivialRelation f x := by
  simp_rw [isTrivialRelation_iff_vanishesTrivially, e.vanishesTrivially_comp]

theorem sum_smul_eq_zero_of_isTrivialRelation (h : IsTrivialRelation f x) :
    ∑ i, f i • x i = 0 := by
  simpa using
    congr_arg (TensorProduct.lid R M) <|
      sum_tmul_eq_zero_of_vanishesTrivially R (isTrivialRelation_iff_vanishesTrivially.mp h)

end Module

namespace Module.Flat

variable (R M) in
