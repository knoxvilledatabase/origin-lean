/-
Extracted from Topology/ContinuousMap/CocompactMap.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cocompact continuous maps

The type of *cocompact continuous maps* are those which tend to the cocompact filter on the
codomain along the cocompact filter on the domain. When the domain and codomain are Hausdorff, this
is equivalent to many other conditions, including that preimages of compact sets are compact. -/

universe u v w

open Filter Set

/-! ### Cocompact continuous maps -/

structure CocompactMap (α : Type u) (β : Type v) [TopologicalSpace α] [TopologicalSpace β] :
    Type max u v
    extends ContinuousMap α β where
  /-- The cocompact filter on `α` tends to the cocompact filter on `β` under the function -/
  cocompact_tendsto' : Tendsto toFun (cocompact α) (cocompact β)

class CocompactMapClass (F : Type*) (α β : outParam Type*) [TopologicalSpace α]
  [TopologicalSpace β] [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  /-- The cocompact filter on `α` tends to the cocompact filter on `β` under the function -/
  cocompact_tendsto (f : F) : Tendsto f (cocompact α) (cocompact β)

end

namespace CocompactMapClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

variable [FunLike F α β] [CocompactMapClass F α β]
