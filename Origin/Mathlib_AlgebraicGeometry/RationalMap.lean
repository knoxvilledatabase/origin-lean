/-
Extracted from AlgebraicGeometry/RationalMap.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Rational maps between schemes

## Main definitions

* `AlgebraicGeometry.Scheme.PartialMap`: A partial map from `X` to `Y` (`X.PartialMap Y`) is
  a morphism into `Y` defined on a dense open subscheme of `X`.
* `AlgebraicGeometry.Scheme.PartialMap.equiv`:
  Two partial maps are equivalent if they are equal on a dense open subscheme.
* `AlgebraicGeometry.Scheme.RationalMap`:
  A rational map from `X` to `Y` (`X ⤏ Y`) is an equivalence class of partial maps.
* `AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver`:
  Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
  `S`-morphisms `Spec K(X) ⟶ Y` correspond bijectively to `S`-rational maps from `X` to `Y`.
* `AlgebraicGeometry.Scheme.RationalMap.toPartialMap`:
  If `X` is integral and `Y` is separated, then any `f : X ⤏ Y` can be realized as a partial
  map on `f.domain`, the domain of definition of `f`.
-/

universe u

open CategoryTheory hiding Quotient

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

namespace Scheme

structure PartialMap (X Y : Scheme.{u}) where
  /-- The domain of definition of a partial map. -/
  domain : X.Opens
  dense_domain : Dense (domain : Set X)
  /-- The underlying morphism of a partial map. -/
  hom : ↑domain ⟶ Y

variable (S) in

abbrev PartialMap.IsOver [X.Over S] [Y.Over S] (f : X.PartialMap Y) :=
  f.hom.IsOver S

namespace PartialMap

lemma ext_iff (f g : X.PartialMap Y) :
    f = g ↔ ∃ e : f.domain = g.domain, f.hom = (X.isoOfEq e).hom ≫ g.hom := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U, hU, f⟩ := f
    obtain ⟨V, hV, g⟩ := g
    rintro ⟨rfl : U = V, e⟩
    congr 1
    simpa using e
