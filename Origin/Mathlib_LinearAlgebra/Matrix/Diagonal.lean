/-
Extracted from LinearAlgebra/Matrix/Diagonal.lean
Genuine: 5 | Conflates: 0 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-!
# Diagonal matrices

This file contains some results on the linear map corresponding to a
diagonal matrix (`range`, `ker` and `rank`).

## Tags

matrix, diagonal, linear_map
-/

noncomputable section

open LinearMap Matrix Set Submodule Matrix

universe u v w

namespace Matrix

section CommSemiring -- Porting note: generalized from `CommRing`

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type v} [CommSemiring R]

theorem proj_diagonal (i : n) (w : n → R) : (proj i).comp (toLin' (diagonal w)) = w i • proj i :=
  LinearMap.ext fun _ => mulVec_diagonal _ _ _

theorem diagonal_comp_single (w : n → R) (i : n) :
    (diagonal w).toLin'.comp (LinearMap.single R (fun _ : n => R) i) =
      w i • LinearMap.single R (fun _ : n => R) i :=
  LinearMap.ext fun x => (diagonal_mulVec_single w _ _).trans (Pi.single_smul' i (w i) x)

set_option linter.deprecated false in

theorem diagonal_comp_stdBasis (w : n → R) (i : n) :
    (diagonal w).toLin'.comp (LinearMap.stdBasis R (fun _ : n => R) i) =
      w i • LinearMap.stdBasis R (fun _ : n => R) i :=
  LinearMap.ext fun x => (diagonal_mulVec_single w _ _).trans (Pi.single_smul' i (w i) x)

theorem diagonal_toLin' (w : n → R) :
    toLin' (diagonal w) = LinearMap.pi fun i => w i • LinearMap.proj i :=
  LinearMap.ext fun _ => funext fun _ => mulVec_diagonal _ _ _

end CommSemiring

section Semifield

variable {m : Type*} [Fintype m] {K : Type u} [Semifield K]

theorem ker_diagonal_toLin' [DecidableEq m] (w : m → K) :
    ker (toLin' (diagonal w)) =
      ⨆ i ∈ { i | w i = 0 }, LinearMap.range (LinearMap.single K (fun _ => K) i) := by
  rw [← comap_bot, ← iInf_ker_proj, comap_iInf]
  have := fun i : m => ker_comp (toLin' (diagonal w)) (proj i)
  simp only [comap_iInf, ← this, proj_diagonal, ker_smul']
  have : univ ⊆ { i : m | w i = 0 } ∪ { i : m | w i = 0 }ᶜ := by rw [Set.union_compl_self]
  exact (iSup_range_single_eq_iInf_ker_proj K (fun _ : m => K) disjoint_compl_right this
    (Set.toFinite _)).symm

-- DISSOLVED: range_diagonal

end Semifield

end Matrix

namespace LinearMap

section Field

variable {m : Type*} [Fintype m] {K : Type u} [Field K]

-- DISSOLVED: rank_diagonal

end Field

end LinearMap
