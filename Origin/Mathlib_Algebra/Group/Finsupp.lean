/-
Extracted from Algebra/Group/Finsupp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Additive monoid structure on `ι →₀ M`
-/

assert_not_exists MonoidWithZero

open Finset

noncomputable section

variable {ι F M N O G H : Type*}

namespace Finsupp

section Zero

variable [Zero M] [Zero N] [Zero O]

lemma apply_single [FunLike F M N] [ZeroHomClass F M N] (e : F) (i : ι) (m : M) (b : ι) :
    e (single i m b) = single i (e m) b := apply_single' e (map_zero e) i m b
