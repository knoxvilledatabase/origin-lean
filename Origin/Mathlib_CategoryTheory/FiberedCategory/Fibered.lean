/-
Extracted from CategoryTheory/FiberedCategory/Fibered.lean
Genuine: 7 of 12 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!

# Fibered categories

This file defines what it means for a functor `p : 𝒳 ⥤ 𝒮` to be (pre)fibered.

## Main definitions

- `IsPreFibered p` expresses `𝒳` is fibered over `𝒮` via a functor `p : 𝒳 ⥤ 𝒮`, as in SGA VI.6.1.
  This means that any morphism in the base `𝒮` can be lifted to a Cartesian morphism in `𝒳`.

- `IsFibered p` expresses `𝒳` is fibered over `𝒮` via a functor `p : 𝒳 ⥤ 𝒮`, as in SGA VI.6.1.
  This means that it is prefibered, and that the composition of any two Cartesian morphisms is
  Cartesian.

In the literature one often sees the notion of a fibered category defined as the existence of
strongly Cartesian morphisms lying over any given morphism in the base. This is equivalent to the
notion above, and we give an alternate constructor `IsFibered.of_exists_isCartesian'` for
constructing a fibered category this way.

## Implementation

The constructor of `IsPreFibered` is called `exists_isCartesian'`. The reason for the prime is that
when wanting to apply this condition, it is recommended to instead use the lemma
`exists_isCartesian` (without the prime), which is more applicable with respect to non-definitional
equalities.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Category IsHomLift

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

class Functor.IsPreFibered (p : 𝒳 ⥤ 𝒮) : Prop where
  exists_isCartesian' {a : 𝒳} {R : 𝒮} (f : R ⟶ p.obj a) : ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ

protected lemma IsPreFibered.exists_isCartesian (p : 𝒳 ⥤ 𝒮) [p.IsPreFibered] {a : 𝒳} {R S : 𝒮}
    (ha : p.obj a = S) (f : R ⟶ S) : ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ := by
  subst ha; exact IsPreFibered.exists_isCartesian' f

class Functor.IsFibered (p : 𝒳 ⥤ 𝒮) : Prop extends IsPreFibered p where
  comp {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsCartesian p f φ] [IsCartesian p g ψ] : IsCartesian p (f ≫ g) (φ ≫ ψ)

-- INSTANCE (free from Core): (p

namespace Functor.IsPreFibered

variable {p : 𝒳 ⥤ 𝒮} [IsPreFibered p] {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S)

noncomputable def pullbackObj : 𝒳 :=
  Classical.choose (IsPreFibered.exists_isCartesian p ha f)

noncomputable def pullbackMap : pullbackObj ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (IsPreFibered.exists_isCartesian p ha f))

-- INSTANCE (free from Core): pullbackMap.IsCartesian

lemma pullbackObj_proj : p.obj (pullbackObj ha f) = R :=
  domain_eq p f (pullbackMap ha f)

end Functor.IsPreFibered

namespace Functor.IsFibered

open IsCartesian IsPreFibered

-- INSTANCE (free from Core): isStronglyCartesian_of_isCartesian

noncomputable def pullbackPullbackIso {p : 𝒳 ⥤ 𝒮} [IsFibered p]
    {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
      pullbackObj ha (g ≫ f) ≅ pullbackObj (pullbackObj_proj ha f) g :=
  domainUniqueUpToIso p (g ≫ f) (pullbackMap (pullbackObj_proj ha f) g ≫ pullbackMap ha f)
    (pullbackMap ha (g ≫ f))

end Functor.IsFibered

end CategoryTheory
