/-
Extracted from ModelTheory/Algebra/Field/CharP.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# First-order theory of fields

This file defines the first-order theory of fields of characteristic `p` as a theory over the
language of rings

## Main definitions

- `FirstOrder.Language.Theory.fieldOfChar` : the first-order theory of fields of characteristic `p`
  as a theory over the language of rings
-/

variable {p : ℕ} {K : Type*}

namespace FirstOrder

namespace Field

open Language Ring

noncomputable def eqZero (n : ℕ) : Language.ring.Sentence :=
  Term.equal (termOfFreeCommRing n) 0
