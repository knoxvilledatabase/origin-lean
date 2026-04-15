/-
Extracted from Algebra/Star/Subsemiring.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Star subrings

A *-subring is a subring of a *-ring which is closed under *.
-/

universe v

structure StarSubsemiring (R : Type v) [NonAssocSemiring R] [Star R] : Type v
    extends Subsemiring R where
  /-- The `carrier` of a `StarSubsemiring` is closed under the `star` operation. -/
  star_mem' {a} : a ∈ carrier → star a ∈ carrier

section StarSubsemiring

namespace StarSubsemiring

add_decl_doc StarSubsemiring.toSubsemiring

-- INSTANCE (free from Core): setLike

-- INSTANCE (free from Core): {R

initialize_simps_projections StarSubsemiring (carrier → coe, as_prefix coe)

variable {R : Type v} [NonAssocSemiring R] [StarRing R]
