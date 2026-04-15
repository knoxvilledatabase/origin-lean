/-
Extracted from Analysis/Calculus/IteratedDeriv/Defs.lean
Genuine: 33 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# One-dimensional iterated derivatives

We define the `n`-th derivative of a function `f : 𝕜 → F` as a function
`iteratedDeriv n f : 𝕜 → F`, as well as a version on domains `iteratedDerivWithin n f s : 𝕜 → F`,
and prove their basic properties.

## Main definitions and results

Let `𝕜` be a nontrivially normed field, and `F` a normed vector space over `𝕜`. Let `f : 𝕜 → F`.

* `iteratedDeriv n f` is the `n`-th derivative of `f`, seen as a function from `𝕜` to `F`.
  It is defined as the `n`-th Fréchet derivative (which is a multilinear map) applied to the
  vector `(1, ..., 1)`, to take advantage of all the existing framework, but we show that it
  coincides with the naive iterative definition.
* `iteratedDeriv_eq_iterate` states that the `n`-th derivative of `f` is obtained by starting
  from `f` and differentiating it `n` times.
* `iteratedDerivWithin n f s` is the `n`-th derivative of `f` within the domain `s`. It only
  behaves well when `s` has the unique derivative property.
* `iteratedDerivWithin_eq_iterate` states that the `n`-th derivative of `f` in the domain `s` is
  obtained by starting from `f` and differentiating it `n` times within `s`. This only holds when
  `s` has the unique derivative property.

## Implementation details

The results are deduced from the corresponding results for the more general (multilinear) iterated
Fréchet derivative. For this, we write `iteratedDeriv n f` as the composition of
`iteratedFDeriv 𝕜 n f` and a continuous linear equiv. As continuous linear equivs respect
differentiability and commute with differentiation, this makes it possible to prove readily that
the derivative of the `n`-th derivative is the `n+1`-th derivative in `iteratedDerivWithin_succ`,
by translating the corresponding result `iteratedFDerivWithin_succ_apply_left` for the
iterated Fréchet derivative.
-/

noncomputable section

open scoped Topology

open Filter Asymptotics Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def iteratedDeriv (n : ℕ) (f : 𝕜 → F) (x : 𝕜) : F :=
  (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) fun _ : Fin n => 1

def iteratedDerivWithin (n : ℕ) (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) : F :=
  (iteratedFDerivWithin 𝕜 n f s x : (Fin n → 𝕜) → F) fun _ : Fin n => 1

variable {n : ℕ} {f : 𝕜 → F} {s : Set 𝕜} {x : 𝕜}

theorem iteratedDerivWithin_univ : iteratedDerivWithin n f univ = iteratedDeriv n f := by
  ext x
  rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_univ]

/-! ### Properties of the iterated derivative within a set -/

theorem iteratedDerivWithin_eq_iteratedFDerivWithin : iteratedDerivWithin n f s x =
    (iteratedFDerivWithin 𝕜 n f s x : (Fin n → 𝕜) → F) fun _ : Fin n => 1 :=
  rfl

theorem iteratedDerivWithin_eq_equiv_comp : iteratedDerivWithin n f s =
    (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDerivWithin 𝕜 n f s := by
  ext x; rfl

theorem iteratedFDerivWithin_eq_equiv_comp :
    iteratedFDerivWithin 𝕜 n f s =
      ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDerivWithin n f s := by
  rw [iteratedDerivWithin_eq_equiv_comp, ← Function.comp_assoc, LinearIsometryEquiv.self_comp_symm,
    Function.id_comp]

theorem iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod {m : Fin n → 𝕜} :
    (iteratedFDerivWithin 𝕜 n f s x : (Fin n → 𝕜) → F) m =
      (∏ i, m i) • iteratedDerivWithin n f s x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, ← ContinuousMultilinearMap.map_smul_univ]
  simp

theorem norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin :
    ‖iteratedFDerivWithin 𝕜 n f s x‖ = ‖iteratedDerivWithin n f s x‖ := by
  rw [iteratedDerivWithin_eq_equiv_comp, Function.comp_apply, LinearIsometryEquiv.norm_map]

@[simp]
theorem iteratedDerivWithin_zero : iteratedDerivWithin 0 f s = f := by
  ext x
  simp [iteratedDerivWithin]

@[simp]
theorem iteratedDerivWithin_one {x : 𝕜} (h : UniqueDiffWithinAt 𝕜 s x) :
    iteratedDerivWithin 1 f s x = derivWithin f s x := by
  simp only [iteratedDerivWithin, iteratedFDerivWithin_one_apply h]; rfl

theorem contDiffOn_of_continuousOn_differentiableOn_deriv {n : ℕ∞}
    (Hcont : ∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (fun x => iteratedDerivWithin m f s x) s)
    (Hdiff : ∀ m : ℕ, (m : ℕ∞) < n → DifferentiableOn 𝕜 (fun x => iteratedDerivWithin m f s x) s) :
    ContDiffOn 𝕜 n f s := by
  apply contDiffOn_of_continuousOn_differentiableOn
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff]
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

theorem contDiffOn_of_differentiableOn_deriv {n : ℕ∞}
    (h : ∀ m : ℕ, (m : ℕ∞) ≤ n → DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s) :
    ContDiffOn 𝕜 n f s := by
  apply contDiffOn_of_differentiableOn
  simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

theorem ContDiffOn.continuousOn_iteratedDerivWithin
    {n : WithTop ℕ∞} {m : ℕ} (h : ContDiffOn 𝕜 n f s)
    (hmn : m ≤ n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedDerivWithin m f s) s := by
  simpa only [iteratedDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff] using
    h.continuousOn_iteratedFDerivWithin hmn hs

theorem ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin {n : WithTop ℕ∞} {m : ℕ}
    (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (insert x s)) :
    DifferentiableWithinAt 𝕜 (iteratedDerivWithin m f s) s x := by
  simpa only [iteratedDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_differentiableWithinAt_iff] using
    h.differentiableWithinAt_iteratedFDerivWithin hmn hs

theorem ContDiffOn.differentiableOn_iteratedDerivWithin {n : WithTop ℕ∞} {m : ℕ}
    (h : ContDiffOn 𝕜 n f s) (hmn : m < n) (hs : UniqueDiffOn 𝕜 s) :
    DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := fun x hx =>
  (h x hx).differentiableWithinAt_iteratedDerivWithin hmn <| by rwa [insert_eq_of_mem hx]

theorem contDiffOn_iff_continuousOn_differentiableOn_deriv {n : ℕ∞} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔ (∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (iteratedDerivWithin m f s) s) ∧
      ∀ m : ℕ, (m : ℕ∞) < n → DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := by
  simp only [contDiffOn_iff_continuousOn_differentiableOn hs, iteratedFDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuousOn_iff, LinearIsometryEquiv.comp_differentiableOn_iff]

theorem contDiffOn_nat_iff_continuousOn_differentiableOn_deriv {n : ℕ} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔ (∀ m : ℕ, m ≤ n → ContinuousOn (iteratedDerivWithin m f s) s) ∧
      ∀ m : ℕ, m < n → DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := by
  rw [show n = ((n : ℕ∞) : WithTop ℕ∞) from rfl,
    contDiffOn_iff_continuousOn_differentiableOn_deriv hs]
  simp

theorem iteratedDerivWithin_succ {x : 𝕜} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    iteratedDerivWithin (n + 1) f s x = derivWithin (iteratedDerivWithin n f s) s x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_succ_apply_left,
    iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_fderivWithin _ hxs, derivWithin]
  change ((ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) ((fderivWithin 𝕜
    (iteratedDerivWithin n f s) s x : 𝕜 → F) 1) : (Fin n → 𝕜) → F) fun _ : Fin n => 1) =
    (fderivWithin 𝕜 (iteratedDerivWithin n f s) s x : 𝕜 → F) 1
  simp

theorem iteratedDerivWithin_eq_iterate {x : 𝕜} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedDerivWithin n f s x = (fun g : 𝕜 → F => derivWithin g s)^[n] f x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    rw [iteratedDerivWithin_succ (hs x hx), Function.iterate_succ']
    exact derivWithin_congr (fun y hy => IH hy) (IH hx)

theorem iteratedDerivWithin_succ' {x : 𝕜} (hxs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedDerivWithin (n + 1) f s x = (iteratedDerivWithin n (derivWithin f s) s) x := by
  rw [iteratedDerivWithin_eq_iterate hxs hx, iteratedDerivWithin_eq_iterate hxs hx]; rfl

/-! ### Properties of the iterated derivative on the whole space -/

theorem iteratedDeriv_eq_iteratedFDeriv :
    iteratedDeriv n f x = (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) fun _ : Fin n => 1 :=
  rfl

theorem iteratedDeriv_eq_equiv_comp : iteratedDeriv n f =
    (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDeriv 𝕜 n f := by
  ext x; rfl

theorem iteratedFDeriv_eq_equiv_comp : iteratedFDeriv 𝕜 n f =
    ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDeriv n f := by
  rw [iteratedDeriv_eq_equiv_comp, ← Function.comp_assoc, LinearIsometryEquiv.self_comp_symm,
    Function.id_comp]

theorem iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod {m : Fin n → 𝕜} :
    (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) m = (∏ i, m i) • iteratedDeriv n f x := by
  rw [iteratedDeriv_eq_iteratedFDeriv, ← ContinuousMultilinearMap.map_smul_univ]; simp

theorem norm_iteratedFDeriv_eq_norm_iteratedDeriv :
    ‖iteratedFDeriv 𝕜 n f x‖ = ‖iteratedDeriv n f x‖ := by
  rw [iteratedDeriv_eq_equiv_comp, Function.comp_apply, LinearIsometryEquiv.norm_map]

@[simp]
theorem iteratedDeriv_zero : iteratedDeriv 0 f = f := by ext x; simp [iteratedDeriv]

@[simp]
theorem iteratedDeriv_one : iteratedDeriv 1 f = deriv f := by ext x; simp [iteratedDeriv]

theorem contDiff_iff_iteratedDeriv {n : ℕ∞} : ContDiff 𝕜 n f ↔
    (∀ m : ℕ, (m : ℕ∞) ≤ n → Continuous (iteratedDeriv m f)) ∧
      ∀ m : ℕ, (m : ℕ∞) < n → Differentiable 𝕜 (iteratedDeriv m f) := by
  simp only [contDiff_iff_continuous_differentiable, iteratedFDeriv_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuous_iff, LinearIsometryEquiv.comp_differentiable_iff]

theorem contDiff_nat_iff_iteratedDeriv {n : ℕ} : ContDiff 𝕜 n f ↔
    (∀ m : ℕ, m ≤ n → Continuous (iteratedDeriv m f)) ∧
      ∀ m : ℕ, m < n → Differentiable 𝕜 (iteratedDeriv m f) := by
  rw [show n = ((n : ℕ∞) : WithTop ℕ∞) from rfl, contDiff_iff_iteratedDeriv]
  simp

theorem contDiff_of_differentiable_iteratedDeriv {n : ℕ∞}
    (h : ∀ m : ℕ, (m : ℕ∞) ≤ n → Differentiable 𝕜 (iteratedDeriv m f)) : ContDiff 𝕜 n f :=
  contDiff_iff_iteratedDeriv.2 ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩

theorem ContDiff.continuous_iteratedDeriv {n : WithTop ℕ∞} (m : ℕ) (h : ContDiff 𝕜 n f)
    (hmn : m ≤ n) : Continuous (iteratedDeriv m f) :=
  (contDiff_iff_iteratedDeriv.1 (h.of_le hmn)).1 m le_rfl

theorem ContDiff.differentiable_iteratedDeriv {n : WithTop ℕ∞} (m : ℕ) (h : ContDiff 𝕜 n f)
    (hmn : m < n) : Differentiable 𝕜 (iteratedDeriv m f) :=
  (contDiff_iff_iteratedDeriv.1 (h.of_le (ENat.add_one_natCast_le_withTop_of_lt hmn))).2 m
    (mod_cast (lt_add_one m))

theorem iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f) := by
  ext x
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_succ uniqueDiffWithinAt_univ

theorem iteratedDeriv_eq_iterate : iteratedDeriv n f = deriv^[n] f := by
  ext x
  rw [← iteratedDerivWithin_univ]
  convert iteratedDerivWithin_eq_iterate uniqueDiffOn_univ (F := F) (mem_univ x)
  simp [derivWithin_univ]

theorem iteratedDeriv_succ' : iteratedDeriv (n + 1) f = iteratedDeriv n (deriv f) := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate]; rfl
