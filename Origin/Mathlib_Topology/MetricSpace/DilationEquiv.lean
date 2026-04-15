/-
Extracted from Topology/MetricSpace/DilationEquiv.lean
Genuine: 1 of 3 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# Dilation equivalence

In this file we define `DilationEquiv X Y`, a type of bundled equivalences between `X` and `Y` such
that `edist (f x) (f y) = r * edist x y` for some `r : ℝ≥0`, `r ≠ 0`.

We also develop basic API about these equivalences.

## TODO

- Add missing lemmas (compare to other `*Equiv` structures).
- [after-port] Add `DilationEquivInstance` for `IsometryEquiv`.
-/

open scoped NNReal ENNReal

open Function Set Filter Bornology

open Dilation (ratio ratio_ne_zero ratio_pos edist_eq)

section Class

variable (F : Type*) (X Y : outParam Type*) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

-- DISSOLVED: DilationEquivClass

-- INSTANCE (free from Core): (priority

end Class

structure DilationEquiv (X Y : Type*) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    extends X ≃ Y, Dilation X Y
