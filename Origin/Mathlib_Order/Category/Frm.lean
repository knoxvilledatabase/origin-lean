/-
Extracted from Order/Category/Frm.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of frames

This file defines `Frm`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/

universe u

open CategoryTheory Order

structure Frm where
  /-- Construct a bundled `Frm` from the underlying type and typeclass. -/
  of ::
  /-- The underlying frame. -/
  (carrier : Type*)
  [str : Frame carrier]

attribute [instance] Frm.str

initialize_simps_projections Frm (carrier → coe, -str)

namespace Frm

-- INSTANCE (free from Core): :

attribute [coe] Frm.carrier

set_option backward.privateInPublic true in
