/-
Extracted from RepresentationTheory/Rep/Res.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Restriction of representations
Given a group homomorphism `f : H →* G`, we have the restriction functor
`resFunctor f : Rep k G ⥤ Rep k H` which sends a `G`-representation `ρ` to the
`H`-representation `ρ.comp f`.

-/

universe t w u v v1 v2

variable {k : Type u} [CommRing k] {G : Type v1} {H : Type v2} [Monoid G] [Monoid H]

open CategoryTheory

namespace Rep

abbrev resFunctor (f : H →* G) : Rep.{t} k G ⥤ Rep k H where
  obj A := of (X := A.V) (A.ρ.comp f)
  map f' := ofHom ⟨f'.hom, fun h ↦ by simpa using f'.hom.2 (f h)⟩

abbrev res (f : H →* G) (M : Rep k G) := (resFunctor f).obj M

variable (f : H →* G) (M : Rep k G)
