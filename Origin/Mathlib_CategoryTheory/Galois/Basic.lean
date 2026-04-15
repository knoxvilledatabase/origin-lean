/-
Extracted from CategoryTheory/Galois/Basic.lean
Genuine: 11 of 25 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core

/-!
# Definition and basic properties of Galois categories

We define the notion of a Galois category and a fiber functor as in SGA1, following
the definitions in Lenstra's notes (see below for a reference).

## Main definitions

* `PreGaloisCategory` : defining properties of Galois categories not involving a fiber functor
* `FiberFunctor`      : a fiber functor from a `PreGaloisCategory` to `FintypeCat`
* `GaloisCategory`    : a `PreGaloisCategory` that admits a `FiberFunctor`
* `IsConnected`       : an object of a category is connected if it is not initial
                        and does not have non-trivial subobjects

Any fiber functor `F` induces an equivalence with the category of finite, discrete `Aut F`-types.
This is proven in `Mathlib/CategoryTheory/Galois/Equivalence.lean`.

## Implementation details

We mostly follow Def 3.1 in Lenstra's notes. In axiom (G3)
we omit the factorisation of morphisms into epimorphisms and monomorphisms
as this is not needed for the proof of the fundamental theorem on Galois categories
(and then follows from it).

## References

* [lenstraGSchemes]: H. W. Lenstra. Galois theory for schemes.

-/

universe u₁ u₂ v₁ v₂ w t

namespace CategoryTheory

open Limits Functor

/-!
A category `C` is a PreGalois category if it satisfies all properties
of a Galois category in the sense of SGA1 that do not involve a fiber functor.
A Galois category should furthermore admit a fiber functor.

The only difference between `[PreGaloisCategory C] (F : C ⥤ FintypeCat) [FiberFunctor F]` and
`[GaloisCategory C]` is that the former fixes one fiber functor `F`.
-/

class PreGaloisCategory (C : Type u₁) [Category.{u₂, u₁} C] : Prop where
  /-- `C` has a terminal object (G1). -/
  hasTerminal : HasTerminal C := by infer_instance
  /-- `C` has pullbacks (G1). -/
  hasPullbacks : HasPullbacks C := by infer_instance
  /-- `C` has finite coproducts (G2). -/
  hasFiniteCoproducts : HasFiniteCoproducts C := by infer_instance
  /-- `C` has quotients by finite groups (G2). -/
  hasQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) C := by infer_instance
  /-- Every monomorphism in `C` induces an isomorphism on a direct summand (G3). -/
  monoInducesIsoOnDirectSummand {X Y : C} (i : X ⟶ Y) [Mono i] : ∃ (Z : C) (u : Z ⟶ Y),
    Nonempty (IsColimit (BinaryCofan.mk i u))

namespace PreGaloisCategory

class FiberFunctor {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) where
  /-- `F` preserves terminal objects (G4). -/
  preservesTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F := by
    infer_instance
  /-- `F` preserves pullbacks (G4). -/
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan F := by infer_instance
  /-- `F` preserves finite coproducts (G5). -/
  preservesFiniteCoproducts : PreservesFiniteCoproducts F := by infer_instance
  /-- `F` preserves epimorphisms (G5). -/
  preservesEpis : Functor.PreservesEpimorphisms F := by infer_instance
  /-- `F` preserves quotients by finite groups (G5). -/
  preservesQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F := by infer_instance
  /-- `F` reflects isomorphisms (G6). -/
  reflectsIsos : F.ReflectsIsomorphisms := by infer_instance

class IsConnected {C : Type u₁} [Category.{u₂, u₁} C] (X : C) : Prop where
  /-- `X` is not an initial object. -/
  notInitial : IsInitial X → False
  /-- `X` has no non-trivial subobjects. -/
  noTrivialComponent (Y : C) (i : Y ⟶ X) [Mono i] : (IsInitial Y → False) → IsIso i

class PreservesIsConnected {C : Type u₁} [Category.{u₂, u₁} C] {D : Type v₁}
    [Category.{v₂, v₁} D] (F : C ⥤ D) : Prop where
  /-- `F.obj X` is connected if `X` is connected. -/
  preserves : ∀ {X : C} [IsConnected X], IsConnected (F.obj X)

variable {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]

attribute [instance] hasTerminal hasPullbacks hasFiniteCoproducts hasQuotientsByFiniteGroups

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {G

end

namespace FiberFunctor

variable {C : Type u₁} [Category.{u₂, u₁} C] {F : C ⥤ FintypeCat.{w}} [PreGaloisCategory C]
  [FiberFunctor F]

attribute [instance] preservesTerminalObjects preservesPullbacks preservesEpis

  preservesFiniteCoproducts reflectsIsos preservesQuotientsByFiniteGroups

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {G

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): comp_right

end

end FiberFunctor

variable {C : Type u₁} [Category.{u₂, u₁} C]
  (F : C ⥤ FintypeCat.{w})

-- INSTANCE (free from Core): (X

lemma mulAction_naturality {X Y : C} (σ : Aut F) (f : X ⟶ Y) (x : F.obj X) :
    σ • F.map f x = F.map f (σ • x) :=
  NatTrans.naturality_apply σ.hom f x

lemma has_non_trivial_subobject_of_not_isConnected_of_not_initial (X : C) (hc : ¬ IsConnected X)
    (hi : IsInitial X → False) :
    ∃ (Y : C) (v : Y ⟶ X), (IsInitial Y → False) ∧ Mono v ∧ (¬ IsIso v) := by
  contrapose! hc
  exact ⟨hi, fun Y i hm hni ↦ hc Y i hni hm⟩

lemma card_fiber_eq_of_iso {X Y : C} (i : X ≅ Y) : Nat.card (F.obj X) = Nat.card (F.obj Y) := by
  have e : F.obj X ≃ F.obj Y := Iso.toEquiv (mapIso (F ⋙ FintypeCat.incl) i)
  exact Nat.card_eq_of_bijective e (Equiv.bijective e)

variable [PreGaloisCategory C] [FiberFunctor F]

lemma initial_iff_fiber_empty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X) := by
  rw [(IsInitial.isInitialIffObj F X).nonempty_congr]
  haveI : PreservesFiniteColimits (forget FintypeCat) := by
    change PreservesFiniteColimits FintypeCat.incl
    infer_instance
  haveI : ReflectsColimit (Functor.empty.{0} _) (forget FintypeCat) := by
    change ReflectsColimit (Functor.empty.{0} _) FintypeCat.incl
    infer_instance
  exact Concrete.initial_iff_empty_of_preserves_of_reflects (F.obj X)

lemma not_initial_iff_fiber_nonempty (X : C) : (IsInitial X → False) ↔ Nonempty (F.obj X) := by
  rw [← not_isEmpty_iff]
  refine ⟨fun h he ↦ ?_, fun h hin ↦ h <| (initial_iff_fiber_empty F X).mp ⟨hin⟩⟩
  exact Nonempty.elim ((initial_iff_fiber_empty F X).mpr he) h

lemma not_initial_of_inhabited {X : C} (x : F.obj X) (h : IsInitial X) : False :=
  ((initial_iff_fiber_empty F X).mp ⟨h⟩).false x

-- INSTANCE (free from Core): nonempty_fiber_of_isConnected

noncomputable def fiberEqualizerEquiv {X Y : C} (f g : X ⟶ Y) :
    F.obj (equalizer f g) ≃ { x : F.obj X // F.map f x = F.map g x } :=
  (PreservesEqualizer.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.equalizerIso (F.map f).hom (F.map g).hom).toEquiv
