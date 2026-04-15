/-
Extracted from CategoryTheory/Limits/Shapes/Preorder/Fin.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Limits and colimits indexed by `Fin`

In this file, we show that `0 : Fin (n + 1)` is an initial object
and `Fin.last n` is a terminal object. This allows to compute
limits and colimits indexed by `Fin (n + 1)`, see
`limitOfDiagramInitial` and `colimitOfDiagramTerminal`
in the file `Limits.Shapes.IsTerminal`.

-/

universe v v' u u' w

open CategoryTheory Limits

namespace Fin

variable (n : ℕ)

-- DISSOLVED: isInitialZero

def isTerminalLast : IsTerminal (Fin.last n) := isTerminalTop

end Fin
