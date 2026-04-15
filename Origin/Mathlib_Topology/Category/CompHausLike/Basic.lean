/-
Extracted from Topology/Category/CompHausLike/Basic.lean
Genuine: 16 | Conflates: 0 | Dissolved: 0 | Infrastructure: 18
-/
import Origin.Core
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.Topology.Category.TopCat.Basic

/-!

# Categories of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces satisfying an additional property `P`.

## Implementation

We define a structure `CompHausLike` which takes as an argument a predicate `P` on topological
spaces. It consists of the data of a topological space, satisfying the additional properties of
being compact and Hausdorff, and satisfying `P`. We give a category structure to `CompHausLike P`
induced by the forgetful functor to topological spaces.

It used to be the case (before https://github.com/leanprover-community/mathlib4/pull/12930 was merged) that several different categories of compact
Hausdorff spaces, possibly satisfying some extra property, were defined from scratch in this way.
For example, one would define a structure `CompHaus` as follows:

```lean
structure CompHaus where
  toTop : TopCat
  [is_compact : CompactSpace toTop]
  [is_hausdorff : T2Space toTop]
```

and give it the category structure induced from topological spaces. Then the category of profinite
spaces was defined as follows:

```lean
structure Profinite where
  toCompHaus : CompHaus
  [isTotallyDisconnected : TotallyDisconnectedSpace toCompHaus]
```

The categories `Stonean` consisting of extremally disconnected compact Hausdorff spaces and
`LightProfinite` consisting of totally disconnected, second countable compact Hausdorff spaces were
defined in a similar way. This resulted in code duplication, and reducing this duplication was part
of the motivation for introducing `CompHausLike`.

Using `CompHausLike`, we can now define
`CompHaus := CompHausLike (fun _ ↦ True)`
`Profinite := CompHausLike (fun X ↦ TotallyDisconnectedSpace X)`.
`Stonean := CompHausLike (fun X ↦ ExtremallyDisconnected X)`.
`LightProfinite := CompHausLike  (fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X)`.

These four categories are important building blocks of condensed objects (see the files
`Condensed.Basic` and `Condensed.Light.Basic`). These categories share many properties and often,
one wants to argue about several of them simultaneously. This is the other part of the motivation
for introducing `CompHausLike`. On paper, one would say "let `C` be on of the categories `CompHaus`
or `Profinite`, then the following holds: ...". This was not possible in Lean using the old
definitions. Using the new definitions, this becomes a matter of identifying what common property
of `CompHaus` and `Profinite` is used in the proof in question, and then proving the theorem for
`CompHausLike P` satisfying that property, and it will automatically apply to both `CompHaus` and
`Profinite`.
-/

universe u

open CategoryTheory

attribute [local instance] ConcreteCategory.instFunLike

variable (P : TopCat.{u} → Prop)

structure CompHausLike where
  /-- The underlying topological space of an object of `CompHausLike P`. -/
  toTop : TopCat
  /-- The underlying topological space is compact. -/
  [is_compact : CompactSpace toTop]
  /-- The underlying topological space is T2. -/
  [is_hausdorff : T2Space toTop]
  /-- The underlying topological space satisfies P. -/
  prop : P toTop

namespace CompHausLike

attribute [instance] is_compact is_hausdorff

instance : CoeSort (CompHausLike P) (Type u) :=
  ⟨fun X => X.toTop⟩

instance category : Category (CompHausLike P) :=
  InducedCategory.category toTop

instance concreteCategory : ConcreteCategory (CompHausLike P) :=
  InducedCategory.concreteCategory _

instance hasForget₂ : HasForget₂ (CompHausLike P) TopCat :=
  InducedCategory.hasForget₂ _

variable (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]

class HasProp : Prop where
  hasProp : P (TopCat.of X)

variable [HasProp P X]

def of : CompHausLike P where
  toTop := TopCat.of X
  is_compact := ‹_›
  is_hausdorff := ‹_›
  prop := HasProp.hasProp

@[simp]
theorem coe_of : (CompHausLike.of P X : Type _) = X :=
  rfl

@[simp]
theorem coe_id (X : CompHausLike P) : (𝟙 ((forget (CompHausLike P)).obj X)) = id :=
  rfl

@[simp]
theorem coe_comp {X Y Z : CompHausLike P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget (CompHausLike P)).map f ≫ (forget (CompHausLike P)).map g) = g ∘ f :=
  rfl

instance (X : CompHausLike.{u} P) : TopologicalSpace ((forget (CompHausLike P)).obj X) :=
  inferInstanceAs (TopologicalSpace X.toTop)

instance (X : CompHausLike.{u} P) : CompactSpace ((forget (CompHausLike P)).obj X) :=
  inferInstanceAs (CompactSpace X.toTop)

instance (X : CompHausLike.{u} P) : T2Space ((forget (CompHausLike P)).obj X) :=
  inferInstanceAs (T2Space X.toTop)

variable {P}

@[simps]
def toCompHausLike {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    CompHausLike P ⥤ CompHausLike P' where
  obj X :=
    have : HasProp P' X := ⟨(h _ X.prop)⟩
    CompHausLike.of _ X
  map f := f

section

variable {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop)

def fullyFaithfulToCompHausLike : (toCompHausLike h).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : (toCompHausLike h).Full := (fullyFaithfulToCompHausLike h).full

instance : (toCompHausLike h).Faithful := (fullyFaithfulToCompHausLike h).faithful

end

variable (P)

@[simps!]
def compHausLikeToTop : CompHausLike.{u} P ⥤ TopCat.{u} :=
  inducedFunctor _ -- deriving Full, Faithful -- Porting note: deriving fails, adding manually.

example {P P' : TopCat → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    toCompHausLike h ⋙ compHausLikeToTop P' = compHausLikeToTop P := rfl

def fullyFaithfulCompHausLikeToTop : (compHausLikeToTop P).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : (compHausLikeToTop P).Full  :=
  inferInstanceAs (inducedFunctor _).Full

instance : (compHausLikeToTop P).Faithful :=
  inferInstanceAs (inducedFunctor _).Faithful

instance (X : CompHausLike P) : CompactSpace ((compHausLikeToTop P).obj X) :=
  inferInstanceAs (CompactSpace X.toTop)

instance (X : CompHausLike P) : T2Space ((compHausLikeToTop P).obj X) :=
  inferInstanceAs (T2Space X.toTop)

variable {P}

theorem epi_of_surjective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (hf : Function.Surjective f) :
    Epi f := by
  rw [← CategoryTheory.epi_iff_surjective] at hf
  exact (forget (CompHausLike P)).epi_of_epi_map hf

theorem mono_iff_injective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f := by
  constructor
  · intro hf x₁ x₂ h
    let g₁ : X ⟶ X := ⟨fun _ => x₁, continuous_const⟩
    let g₂ : X ⟶ X := ⟨fun _ => x₂, continuous_const⟩
    have : g₁ ≫ f = g₂ ≫ f := by ext; exact h
    exact ContinuousMap.congr_fun ((cancel_mono _).mp this) x₁
  · rw [← CategoryTheory.mono_iff_injective]
    apply (forget (CompHausLike P)).mono_of_mono_map

theorem isClosedMap {X Y : CompHausLike.{u} P} (f : X ⟶ Y) : IsClosedMap f := fun _ hC =>
  (hC.isCompact.image f.continuous).isClosed

theorem isIso_of_bijective {X Y : CompHausLike.{u} P} (f : X ⟶ Y) (bij : Function.Bijective f) :
    IsIso f := by
  let E := Equiv.ofBijective _ bij
  have hE : Continuous E.symm := by
    rw [continuous_iff_isClosed]
    intro S hS
    rw [← E.image_eq_preimage]
    exact isClosedMap f S hS
  refine ⟨⟨⟨E.symm, hE⟩, ?_, ?_⟩⟩
  · ext x
    apply E.symm_apply_apply
  · ext x
    apply E.apply_symm_apply

instance forget_reflectsIsomorphisms :
    (forget (CompHausLike.{u} P)).ReflectsIsomorphisms :=
  ⟨by intro A B f hf; rw [isIso_iff_bijective] at hf; exact isIso_of_bijective _ hf⟩

noncomputable def isoOfBijective {X Y : CompHausLike.{u} P} (f : X ⟶ Y)
    (bij : Function.Bijective f) : X ≅ Y :=
  letI := isIso_of_bijective _ bij
  asIso f

@[simps!]
def isoOfHomeo {X Y : CompHausLike.{u} P} (f : X ≃ₜ Y) : X ≅ Y :=
  (fullyFaithfulCompHausLikeToTop P).preimageIso (TopCat.isoOfHomeo f)

@[simps!]
def homeoOfIso {X Y : CompHausLike.{u} P} (f : X ≅ Y) : X ≃ₜ Y :=
  TopCat.homeoOfIso <| (compHausLikeToTop P).mapIso f

@[simps]
def isoEquivHomeo {X Y : CompHausLike.{u} P} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv _ := rfl
  right_inv _ := rfl

def const {P : TopCat.{u} → Prop}
    (T : CompHausLike.{u} P) {S : CompHausLike.{u} P} (s : S) : T ⟶ S :=
  ContinuousMap.const _ s

lemma const_comp {P : TopCat.{u} → Prop} {S T U : CompHausLike.{u} P}
    (s : S) (g : S ⟶ U) : T.const s ≫ g = T.const (g s) :=
  rfl

end CompHausLike
