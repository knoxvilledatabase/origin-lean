/-
Extracted from Topology/Algebra/UniformField.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Completion of topological fields

The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion `hat K` of a Hausdorff topological field is a field if the image under
the mapping `x ↦ x⁻¹` of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at `0` is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does not give any detail here, he refers to the general discussion of extending
functions defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

Note that the separated completion of a non-separated topological field is the zero ring, hence
the separation assumption is needed. Indeed the kernel of the completion map is the closure of
zero which is an ideal. Hence it's either zero (and the field is separated) or the full field,
which implies one is sent to zero and the completion ring is trivial.

The main definition is `CompletableTopField` which packages the assumptions as a Prop-valued
type class and the main results are the instances `UniformSpace.Completion.Field` and
`UniformSpace.Completion.IsTopologicalDivisionRing`.
-/

noncomputable section

open uniformity Topology

open Set UniformSpace UniformSpace.Completion Filter

variable (K : Type*) [Field K] [UniformSpace K]

local notation "hat" => Completion

class CompletableTopField : Prop extends T0Space K where
  nice : ∀ F : Filter K, Cauchy F → 𝓝 0 ⊓ F = ⊥ → Cauchy (map (fun x => x⁻¹) F)

namespace UniformSpace

namespace Completion

-- INSTANCE (free from Core): (priority

variable {K}

def hatInv : hat K → hat K :=
  isDenseInducing_coe.extend fun x : K => (↑x⁻¹ : hat K)
