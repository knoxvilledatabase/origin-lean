/-
Extracted from RingTheory/Extension/Cotangent/Basis.lean
Genuine: 7 of 11 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Basis of cotangent space can be realized as a presentation

Let `S` be a finitely presented `R`-algebra and suppose `P : R[X] → S` generates `S` with
kernel `I`.

In this file we show `Algebra.Generators.exists_presentation_of_free`: If `I/I²` is free, there
exists an `R`-presentation `P'` of `S` extending `P` with kernel `I'`, such that `I'/I'²` is
free on the images of the relations of `P'`.

## References

- https://stacks.math.columbia.edu/tag/07CF
-/

open Pointwise MvPolynomial TensorProduct

namespace Algebra.Generators

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ : Type*}

noncomputable section

namespace PresentationOfFreeCotangent

variable {ι : Type*} (P : Generators R S ι) {σ : Type*}
  (b : Module.Basis σ S P.toExtension.Cotangent)

structure Aux where
  /-- A section of the projection `I → I/I²`. -/
  f : P.toExtension.Cotangent → P.toExtension.ker
  hf : ∀ (b : P.toExtension.Cotangent), Extension.Cotangent.mk (f b) = b
  /-- An element `g` that becomes invertible in `S = R[X₁, ..., Xₙ] / I`. -/
  g : P.Ring
  hgmem : g - 1 ∈ P.ker
  hg : g • P.ker ≤ Ideal.span (Set.range <| Subtype.val ∘ f ∘ b)

namespace Aux

variable {P} {b}

variable (D : Aux P b)

abbrev T :=
  MvPolynomial ι R ⧸ (Ideal.span <| Set.range <| Subtype.val ∘ D.f ∘ b)

set_option backward.isDefEq.respectTransparency false in

def hom : D.T →ₐ[R] S := Ideal.Quotient.liftₐ _ (aeval P.val) <| by
  simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
  intro i
  simpa only [Generators.toExtension_Ring, Generators.toExtension_commRing, Function.comp_apply,
    SetLike.mem_coe, RingHom.mem_ker, ← P.algebraMap_apply] using (D.f _).property

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): [Nontrivial

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

abbrev gbar : D.T := D.g

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

open Classical in

def presLeft : Presentation R D.T ι σ :=
  .naive (fun x ↦ if x = 0 then 0 else if x = -1 then -1 else
      Function.surjInv Ideal.Quotient.mk_surjective x) fun x ↦ by
    dsimp only; split_ifs
    · next h => subst h; rfl
    · next h => subst h; rfl
    · simp [Function.surjInv_eq]

def kerGen (i : σ) : D.presLeft.toExtension.ker :=
  ⟨(D.f (b i)).val, Presentation.mem_ker_naive _ _ i⟩

set_option backward.isDefEq.respectTransparency false in

def fhom : D.presLeft.Hom P where
  val i := X i
  aeval_val i := by simp [RingHom.algebraMap_toAlgebra, presLeft, hom, T]

set_option backward.isDefEq.respectTransparency false in
