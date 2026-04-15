/-
Extracted from Topology/Category/TopCat/Limits/Products.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Products and coproducts in the category of topological spaces
-/

open CategoryTheory Limits Set TopologicalSpace Topology

universe v u w

noncomputable section

namespace TopCat

variable {J : Type v} [Category.{w} J]

abbrev piπ {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : TopCat.of (∀ i, α i) ⟶ α i :=
  ofHom ⟨fun f => f i, continuous_apply i⟩
