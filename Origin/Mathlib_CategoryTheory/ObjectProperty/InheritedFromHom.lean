/-
Extracted from CategoryTheory/ObjectProperty/InheritedFromHom.lean
Genuine: 6 of 12 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Object properties transported along morphisms

In this file we define the predicates `InheritedFromSource` and `InheritedFromTarget`
for an object property `P` along a morphism property `Q`.
`P` is inherited from the source (resp. target) along `Q` if for every morphism
`f : X ⟶ Y` with `Q f`, `P X` implies `P Y` (resp. `P Y` implies `P X`).
-/

namespace CategoryTheory

variable {C : Type*} [Category* C]

namespace ObjectProperty

variable (P P' : ObjectProperty C) (Q Q' : MorphismProperty C)

class InheritedFromSource (P : ObjectProperty C) (Q : MorphismProperty C) : Prop where
  of_hom_of_source {X Y : C} (f : X ⟶ Y) (hf : Q f) : P X → P Y

class InheritedFromTarget (P : ObjectProperty C) (Q : MorphismProperty C) : Prop where
  of_hom_of_target {X Y : C} (f : X ⟶ Y) (hf : Q f) : P Y → P X

export InheritedFromSource (of_hom_of_source)

export InheritedFromTarget (of_hom_of_target)

namespace InheritedFromSource

-- INSTANCE (free from Core): [P.IsClosedUnderIsomorphisms]

-- INSTANCE (free from Core): op

-- INSTANCE (free from Core): [P.InheritedFromSource

lemma of_le (hQ : Q ≤ Q') [P.InheritedFromSource Q'] : P.InheritedFromSource Q where
  of_hom_of_source f hf h := P.of_hom_of_source f (hQ _ hf) h

end InheritedFromSource

namespace InheritedFromTarget

-- INSTANCE (free from Core): [P.IsClosedUnderIsomorphisms]

-- INSTANCE (free from Core): op

-- INSTANCE (free from Core): [P.InheritedFromTarget

lemma of_le (hQ : Q ≤ Q') [P.InheritedFromTarget Q'] : P.InheritedFromTarget Q where
  of_hom_of_target f hf h := P.of_hom_of_target f (hQ _ hf) h

end InheritedFromTarget

lemma IsClosedUnderIsomorphisms.of_inheritedFromSource [P.InheritedFromSource Q] [Q.RespectsIso]
    [Q.ContainsIdentities] : P.IsClosedUnderIsomorphisms where
  of_iso e h := P.of_hom_of_source e.hom (Q.of_isIso e.hom) h

lemma IsClosedUnderIsomorphisms.of_inheritedFromTarget [P.InheritedFromTarget Q] [Q.RespectsIso]
    [Q.ContainsIdentities] : P.IsClosedUnderIsomorphisms where
  of_iso e h := P.of_hom_of_target e.inv (Q.of_isIso e.inv) h

end ObjectProperty

end CategoryTheory
