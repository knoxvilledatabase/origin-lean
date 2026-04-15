/-
Extracted from Topology/UniformSpace/OfFun.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Topology.UniformSpace.Basic

/-!
# Construct a `UniformSpace` from a `dist`-like function

In this file we provide a constructor for `UniformSpace`
given a `dist`-like function

## TODO

RFC: use `UniformSpace.Core.mkOfBasis`? This will change defeq here and there
-/

open Filter Set

open scoped Uniformity

variable {X M : Type*}

namespace UniformSpace

def ofFun [OrderedAddCommMonoid M] (d : X → X → M) (refl : ∀ x, d x x = 0)
    (symm : ∀ x y, d x y = d y x) (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (half : ∀ ε > (0 : M), ∃ δ > (0 : M), ∀ x < δ, ∀ y < δ, x + y < ε) :
    UniformSpace X :=
  .ofCore
    { uniformity := ⨅ r > 0, 𝓟 { x | d x.1 x.2 < r }
      refl := le_iInf₂ fun r hr => principal_mono.2 <| idRel_subset.2 fun x => by simpa [refl]
      symm := tendsto_iInf_iInf fun r => tendsto_iInf_iInf fun _ => tendsto_principal_principal.2
        fun x hx => by rwa [mem_setOf, symm]
      comp := le_iInf₂ fun r hr => let ⟨δ, h0, hδr⟩ := half r hr; le_principal_iff.2 <|
        mem_of_superset
          (mem_lift' <| mem_iInf_of_mem δ <| mem_iInf_of_mem h0 <| mem_principal_self _)
          fun (x, z) ⟨y, h₁, h₂⟩ => (triangle _ _ _).trans_lt (hδr _ h₁ _ h₂) }

theorem hasBasis_ofFun [LinearOrderedAddCommMonoid M]
    (h₀ : ∃ x : M, 0 < x) (d : X → X → M) (refl : ∀ x, d x x = 0) (symm : ∀ x y, d x y = d y x)
    (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (half : ∀ ε > (0 : M), ∃ δ > (0 : M), ∀ x < δ, ∀ y < δ, x + y < ε) :
    𝓤[.ofFun d refl symm triangle half].HasBasis ((0 : M) < ·) (fun ε => { x | d x.1 x.2 < ε }) :=
  hasBasis_biInf_principal'
    (fun ε₁ h₁ ε₂ h₂ => ⟨min ε₁ ε₂, lt_min h₁ h₂, fun _x hx => lt_of_lt_of_le hx (min_le_left _ _),
      fun _x hx => lt_of_lt_of_le hx (min_le_right _ _)⟩) h₀

end UniformSpace
