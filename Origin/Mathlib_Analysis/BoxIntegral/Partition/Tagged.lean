/-
Extracted from Analysis/BoxIntegral/Partition/Tagged.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Tagged partitions

A tagged (pre)partition is a (pre)partition `π` enriched with a tagged point for each box of
`π`. For simplicity we require that the function `BoxIntegral.TaggedPrepartition.tag` is defined
on all boxes `J : Box ι` but use its values only on boxes of the partition. Given
`π : BoxIntegral.TaggedPrepartition I`, we require that each `BoxIntegral.TaggedPrepartition π J`
belongs to `BoxIntegral.Box.Icc I`. If for every `J ∈ π`, `π.tag J` belongs to `J.Icc`, then `π` is
called a *Henstock* partition. We do not include this assumption into the definition of a tagged
(pre)partition because McShane integral is defined as a limit along tagged partitions without this
requirement.

## Tags

rectangular box, box partition
-/

noncomputable section

open Finset Function ENNReal NNReal Set

namespace BoxIntegral

variable {ι : Type*}

structure TaggedPrepartition (I : Box ι) extends Prepartition I where
  /-- Choice of tagged point of each box in this prepartition:
  we extend this to a total function, on all boxes in `ι → ℝ`. -/
  tag : Box ι → ι → ℝ
  /-- Each tagged point belongs to `I` -/
  tag_mem_Icc : ∀ J, tag J ∈ Box.Icc I

namespace TaggedPrepartition

variable {I J J₁ J₂ : Box ι} (π : TaggedPrepartition I) {x : ι → ℝ}

-- INSTANCE (free from Core): :
