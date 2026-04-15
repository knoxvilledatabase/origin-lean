/-
Extracted from LinearAlgebra/Multilinear/Curry.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Currying of multilinear maps
We register isomorphisms corresponding to currying or uncurrying variables, transforming a
multilinear function `f` on `n+1` variables into a linear function taking values in multilinear
functions in `n` variables, and into a multilinear function in `n` variables taking values in linear
functions. These operations are called `f.curryLeft` and `f.curryRight` respectively
(with inverses `f.uncurryLeft` and `f.uncurryRight`). These operations induce linear equivalences
between spaces of multilinear functions in `n+1` variables and spaces of linear functions into
multilinear functions in `n` variables (resp. multilinear functions in `n` variables taking values
in linear functions), called respectively `multilinearCurryLeftEquiv` and
`multilinearCurryRightEquiv`.

-/

open Fin Function Finset Set

universe uR uS uι uι' v v' v₁ v₂ v₃

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

/-!
### Currying

We associate to a multilinear map in `n+1` variables (i.e., based on `Fin n.succ`) two
curried functions, named `f.curryLeft` (which is a linear map on `E 0` taking values
in multilinear maps in `n` variables) and `f.curryRight` (which is a multilinear map in `n`
variables taking values in linear maps on `E 0`). In both constructions, the variable that is
singled out is `0`, to take advantage of the operations `cons` and `tail` on `Fin n`.
The inverse operations are called `uncurryLeft` and `uncurryRight`.

We also register linear equiv versions of these correspondences, in
`multilinearCurryLeftEquiv` and `multilinearCurryRightEquiv`.
-/

open MultilinearMap

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

/-! #### Left currying -/

def LinearMap.uncurryLeft (f : M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) :
    MultilinearMap R M M₂ :=
  MultilinearMap.mk' (fun m ↦ f (m 0) (tail m))
    (fun m i x y ↦ by cases i using Fin.cases <;> simp [Ne.symm])
    (fun m i c x ↦ by cases i using Fin.cases <;> simp [Ne.symm])
