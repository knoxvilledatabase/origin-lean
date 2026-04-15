/-
Extracted from Analysis/Calculus/IteratedDeriv/Lemmas.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# One-dimensional iterated derivatives

This file contains a number of further results on `iteratedDerivWithin` that need more imports
than are available in `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`.
-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ} {x : 𝕜} {s : Set 𝕜} (hx : x ∈ s) (h : UniqueDiffOn 𝕜 s) {f g : 𝕜 → F}
  -- For maximum generality, results about `smul` involve a second type besides `𝕜`,
  -- with varying hypotheses.
  -- * `R`: general type.
  {R : Type*} [DistribSMul R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]
  -- * `𝕝`: division semiring. (Addition in `𝕝` is not used, so the results would work with a
  -- `GroupWithZero` if we had a `DistribSMulWithZero` typeclass.)
  {𝕝 : Type*} [DivisionSemiring 𝕝] [Module 𝕝 F] [SMulCommClass 𝕜 𝕝 F] [ContinuousConstSMul 𝕝 F]
  -- * `𝔸`: normed `𝕜`-algebra.
  {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Module 𝔸 F] [IsBoundedSMul 𝔸 F]
    [IsScalarTower 𝕜 𝔸 F]
  -- * `𝕜'`: normed `𝕜`-division algebra.
  {𝕜' : Type*} [NormedDivisionRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [Module 𝕜' F] [SMulCommClass 𝕜 𝕜' F] [ContinuousSMul 𝕜' F]

section one_dimensional

open scoped Topology

theorem Filter.EventuallyEq.iteratedDerivWithin_eq (hfg : f =ᶠ[𝓝[s] x] g) (hfg' : f x = g x) :
    iteratedDerivWithin n f s x = iteratedDerivWithin n g s x :=
  congr($(hfg.iteratedFDerivWithin_eq hfg' n) _)

theorem Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ) {f g : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}
    (hfg : f =ᶠ[𝓝[insert x s] x] g) :
    iteratedDerivWithin n f s x = iteratedDerivWithin n g s x :=
  (hfg.filter_mono (by simp)).iteratedDerivWithin_eq (hfg.eq_of_nhdsWithin (by simp))

theorem iteratedDerivWithin_congr (hfg : Set.EqOn f g s) :
    Set.EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n g s) s :=
  fun _ hx ↦ hfg.eventuallyEq_nhdsWithin.iteratedDerivWithin_eq (hfg hx)

include h hx in

theorem iteratedDerivWithin_add
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (f + g) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simp_rw [iteratedDerivWithin, iteratedFDerivWithin_add_apply hf hg h hx,
    ContinuousMultilinearMap.add_apply]

include h hx in

theorem iteratedDerivWithin_fun_add
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (fun z ↦ f z + g z) s x =
      iteratedDerivWithin n f s x + iteratedDerivWithin n g s x := by
  simpa using iteratedDerivWithin_add hx h hf hg

theorem iteratedDerivWithin_const_add (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c + f z) s x = iteratedDerivWithin n f s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ', iteratedDerivWithin_succ']
  congr 1 with y
  exact derivWithin_const_add _

theorem iteratedDerivWithin_const_sub (hn : 0 < n) (c : F) :
    iteratedDerivWithin n (fun z => c - f z) s x = iteratedDerivWithin n (fun z => -f z) s x := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDerivWithin_succ', iteratedDerivWithin_succ']
  congr 1 with y
  rw [derivWithin.fun_neg]
  exact derivWithin_const_sub _

include h hx in

theorem iteratedDerivWithin_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (c • f) s x = c • iteratedDerivWithin n f s x := by
  simp_rw [iteratedDerivWithin]
  rw [iteratedFDerivWithin_const_smul_apply (a := c) hf h hx]
  simp only [ContinuousMultilinearMap.smul_apply]

include h hx in

theorem iteratedDerivWithin_fun_const_smul (c : R) (hf : ContDiffWithinAt 𝕜 n f s x) :
    iteratedDerivWithin n (fun w ↦ c • f w) s x = c • iteratedDerivWithin n f s x :=
  iteratedDerivWithin_const_smul hx h c hf
