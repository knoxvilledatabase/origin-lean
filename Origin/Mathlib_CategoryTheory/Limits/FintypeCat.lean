/-
Extracted from CategoryTheory/Limits/FintypeCat.lean
Genuine: 1 of 9 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# (Co)limits in the category of finite types

We show that finite (co)limits exist in `FintypeCat` and that they are preserved by the natural
inclusion `FintypeCat.incl`.
-/

open CategoryTheory Limits Functor

universe u

namespace CategoryTheory.Limits.FintypeCat

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): finiteLimitOfFiniteDiagram

-- INSTANCE (free from Core): inclusionCreatesFiniteLimits

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): hasFiniteLimits

-- INSTANCE (free from Core): inclusion_preservesFiniteLimits

-- INSTANCE (free from Core): :

noncomputable def productEquiv {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u}) :
    (∏ᶜ X : FintypeCat) ≃ ∀ i, X i :=
  have : Fintype ι := Fintype.ofFinite _
  haveI : Small.{u} ι :=
    ⟨ULift (Fin (Fintype.card ι)), ⟨(Fintype.equivFin ι).trans Equiv.ulift.symm⟩⟩
  let is₁ : FintypeCat.incl.obj (∏ᶜ fun i ↦ X i) ≅ (∏ᶜ fun i ↦ X i) :=
    PreservesProduct.iso FintypeCat.incl (fun i ↦ X i)
  let is₂ : (∏ᶜ fun i ↦ X i : Type _) ≅ (Shrink.{u} (∀ i, X i)) :=
    Types.Small.productIso (fun i ↦ X i)
  let e : (∀ i, X i) ≃ Shrink.{u} (∀ i, X i) := equivShrink _
  (equivEquivIso.symm is₁).trans ((equivEquivIso.symm is₂).trans e.symm)
