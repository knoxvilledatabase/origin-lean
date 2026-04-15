/-
Extracted from Analysis/Normed/Module/Multilinear/Curry.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Currying and uncurrying continuous multilinear maps

We associate to a continuous multilinear map in `n+1` variables (i.e., based on `Fin n.succ`) two
curried functions, named `f.curryLeft` (which is a continuous linear map on `E 0` taking values
in continuous multilinear maps in `n` variables) and `f.curryRight` (which is a continuous
multilinear map in `n` variables taking values in continuous linear maps on `E (last n)`).
The inverse operations are called `uncurryLeft` and `uncurryRight`.

We also register continuous linear equiv versions of these correspondences, in
`continuousMultilinearCurryLeftEquiv` and `continuousMultilinearCurryRightEquiv`.

## Main results

* `ContinuousMultilinearMap.curryLeft`, `ContinuousLinearMap.uncurryLeft` and
  `continuousMultilinearCurryLeftEquiv`
* `ContinuousMultilinearMap.curryRight`, `ContinuousMultilinearMap.uncurryRight` and
  `continuousMultilinearCurryRightEquiv`.
* `ContinuousMultilinearMap.curryMid`, `ContinuousLinearMap.uncurryMid` and
  `ContinuousMultilinearMap.curryMidEquiv`
-/

suppress_compilation

noncomputable section

open NNReal Finset Metric ContinuousMultilinearMap Fin Function

/-!
### Type variables

We use the following type variables in this file:

* `𝕜` : a `NontriviallyNormedField`;
* `ι`, `ι'` : finite index types with decidable equality;
* `E`, `E₁` : families of normed vector spaces over `𝕜` indexed by `i : ι`;
* `E'` : a family of normed vector spaces over `𝕜` indexed by `i' : ι'`;
* `Ei` : a family of normed vector spaces over `𝕜` indexed by `i : Fin (Nat.succ n)`;
* `G`, `G'` : normed vector spaces over `𝕜`.
-/

universe u v v' wE wE₁ wE' wEi wG wG'

variable {𝕜 : Type u} {ι : Type v} {ι' : Type v'} {n : ℕ} {E : ι → Type wE}
  {Ei : Fin n.succ → Type wEi} {G : Type wG} {G' : Type wG'} [Fintype ι]
  [Fintype ι'] [NontriviallyNormedField 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

theorem ContinuousLinearMap.norm_map_removeNth_le {i : Fin (n + 1)}
    (f : Ei i →L[𝕜] ContinuousMultilinearMap 𝕜 (fun j ↦ Ei (i.succAbove j)) G) (m : ∀ i, Ei i) :
    ‖f (m i) (i.removeNth m)‖ ≤ ‖f‖ * ∏ j, ‖m j‖ := by
  rw [i.prod_univ_succAbove, ← mul_assoc]
  exact (f (m i)).le_of_opNorm_le (f.le_opNorm _) _

theorem ContinuousLinearMap.norm_map_tail_le
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (m : ∀ i, Ei i) :
    ‖f (m 0) (tail m)‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
  ContinuousLinearMap.norm_map_removeNth_le (i := 0) f m

theorem ContinuousMultilinearMap.norm_map_init_le
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G))
    (m : ∀ i, Ei i) : ‖f (init m) (m (last n))‖ ≤ ‖f‖ * ∏ i, ‖m i‖ := by
  rw [prod_univ_castSucc, ← mul_assoc]
  exact (f (init m)).le_of_opNorm_le (f.le_opNorm _) _

theorem ContinuousMultilinearMap.norm_map_insertNth_le (f : ContinuousMultilinearMap 𝕜 Ei G)
    {i : Fin (n + 1)} (x : Ei i) (m : ∀ j, Ei (i.succAbove j)) :
    ‖f (i.insertNth x m)‖ ≤ ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ := by
  simpa [i.prod_univ_succAbove, mul_assoc] using f.le_opNorm (i.insertNth x m)

theorem ContinuousMultilinearMap.norm_map_cons_le (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
    (m : ∀ i : Fin n, Ei i.succ) : ‖f (cons x m)‖ ≤ ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ := by
  simpa [prod_univ_succ, mul_assoc] using f.le_opNorm (cons x m)

theorem ContinuousMultilinearMap.norm_map_snoc_le (f : ContinuousMultilinearMap 𝕜 Ei G)
    (m : ∀ i : Fin n, Ei <| castSucc i) (x : Ei (last n)) :
    ‖f (snoc m x)‖ ≤ (‖f‖ * ∏ i, ‖m i‖) * ‖x‖ := by
  simpa [prod_univ_castSucc, mul_assoc] using f.le_opNorm (snoc m x)

/-! #### Left currying -/

def ContinuousLinearMap.uncurryLeft
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  (ContinuousMultilinearMap.toMultilinearMapLinear ∘ₗ f.toLinearMap).uncurryLeft.mkContinuous
    ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_tail_le f m
