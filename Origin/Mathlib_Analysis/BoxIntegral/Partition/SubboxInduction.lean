/-
Extracted from Analysis/BoxIntegral/Partition/SubboxInduction.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Induction on subboxes

In this file we prove (see
`BoxIntegral.Box.exists_taggedPartition_isHenstock_isSubordinate_homothetic`) that for every box `I`
in `ℝⁿ` and a function `r : ℝⁿ → ℝ` positive on `I` there exists a tagged partition `π` of `I` such
that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ n`.

Later we will use this lemma to prove that the Henstock filter is nontrivial, hence the Henstock
integral is well-defined.

## Tags

partition, tagged partition, Henstock integral
-/

namespace BoxIntegral

open Set Metric

open Topology

noncomputable section

variable {ι : Type*} [Fintype ι] {I J : Box ι}

namespace Prepartition

def splitCenter (I : Box ι) : Prepartition I where
  boxes := Finset.univ.map (Box.splitCenterBoxEmb I)
  le_of_mem' := by simp [I.splitCenterBox_le]
  pairwiseDisjoint := by
    rw [Finset.coe_map, Finset.coe_univ, image_univ]
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ Hne
    exact I.disjoint_splitCenterBox (mt (congr_arg _) Hne)
