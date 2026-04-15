/-
Extracted from Topology/Instances/Int.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Topology on the integers

The structure of a metric space on `ℤ` is introduced in this file, induced from `ℝ`.
-/

noncomputable section

open Filter Metric Set Topology

namespace Int

-- INSTANCE (free from Core): :

theorem dist_eq' (m n : ℤ) : dist m n = |m - n| := by rw [dist_eq]; norm_cast
