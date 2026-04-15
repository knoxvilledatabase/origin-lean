/-
Extracted from CategoryTheory/ConcreteCategory/Bundled.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Bundled types

`Bundled c` provides a uniform structure for bundling a type equipped with a type class.

We provide `Category` instances for these in
`Mathlib/CategoryTheory/ConcreteCategory/UnbundledHom.lean`
(for categories with unbundled homs, e.g. topological spaces)
and in `Mathlib/CategoryTheory/ConcreteCategory/BundledHom.lean`
(for categories with bundled homs, e.g. monoids).

Note: this structure will be deprecated in the future in favor of defining the category manually
and then providing the `ConcreteCategory` instance on top of this. See
`Mathlib/CategoryTheory/ConcreteCategory/Basic.lean` for more details.
-/

universe u v

namespace CategoryTheory

variable {c d : Type u → Type v}

structure Bundled (c : Type u → Type v) : Type max (u + 1) v where
  /-- The underlying type of the bundled type -/
  α : Type u
  /-- The corresponding instance of the bundled type class -/
  str : c α := by infer_instance

namespace Bundled

attribute [coe] α

set_option checkBinderAnnotations false in

def of {c : Type u → Type v} (α : Type u) [str : c α] : Bundled c :=
  ⟨α, str⟩

-- INSTANCE (free from Core): coeSort

abbrev map (f : ∀ {α}, c α → d α) (b : Bundled c) : Bundled d :=
  ⟨b, f b.str⟩

end Bundled

end CategoryTheory
