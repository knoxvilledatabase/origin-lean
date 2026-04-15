/-
Extracted from Data/List/OffDiag.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Definition and basic properties of `List.offDiag`

In this file we define `List.offDiag l` to be the product `l.product l`
with the diagonal removed.
The actual definition is more complicated to avoid assuming that equality on `α` is decidable.
-/

assert_not_exists Preorder

namespace List

variable {α : Type*} {l : List α}

def offDiag (l : List α) : List (α × α) :=
  l.zipIdx.flatMap fun (x, n) ↦ map (Prod.mk x) <| l.eraseIdx n
