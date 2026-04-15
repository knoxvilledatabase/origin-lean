/-
Extracted from Logic/Function/Coequalizer.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Coequalizer of a pair of functions

The coequalizer of two functions `f g : α → β` is the pair (`μ`, `p : β → μ`) that
satisfies the following universal property: Every function `u : β → γ`
with `u ∘ f = u ∘ g` factors uniquely via `p`.

In this file we define the coequalizer and provide the basic API.
-/

universe v

namespace Function

inductive Coequalizer.Rel {α β : Type*} (f g : α → β) : β → β → Prop where
  | intro (x : α) : Rel f g (f x) (g x)

def Coequalizer {α : Type*} {β : Type v} (f g : α → β) : Type v :=
  Quot (Function.Coequalizer.Rel f g)

namespace Coequalizer

variable {α β : Type*} (f g : α → β)

def mk (x : β) : Coequalizer f g :=
  Quot.mk _ x

lemma condition (x : α) : mk f g (f x) = mk f g (g x) :=
  Quot.sound (.intro x)

lemma mk_surjective : Function.Surjective (mk f g) :=
  Quot.exists_rep

def desc {γ : Type*} (u : β → γ) (hu : u ∘ f = u ∘ g) : Coequalizer f g → γ :=
  Quot.lift u (fun _ _ (.intro e) ↦ congrFun hu e)
