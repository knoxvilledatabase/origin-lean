/-
Extracted from Analysis/Normed/Group/SemiNormedGrp.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of seminormed groups

We define `SemiNormedGrp`, the category of seminormed groups and normed group homs between
them, as well as `SemiNormedGrp₁`, the subcategory of norm non-increasing morphisms.
-/

noncomputable section

universe u

open CategoryTheory

structure SemiNormedGrp : Type (u + 1) where
  /-- Construct a bundled `SemiNormedGrp` from the underlying type and typeclass. -/
  of ::
  /-- The underlying seminormed abelian group. -/
  carrier : Type u
  [str : SeminormedAddCommGroup carrier]

attribute [instance] SemiNormedGrp.str

namespace SemiNormedGrp

-- INSTANCE (free from Core): :
