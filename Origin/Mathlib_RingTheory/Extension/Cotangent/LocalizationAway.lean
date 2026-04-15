/-
Extracted from RingTheory/Extension/Cotangent/LocalizationAway.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cotangent and localization away

Let `R → S → T` be algebras such that `T` is the localization of `S` away from one
element, where `S` is generated over `R` by `P : R[X] → S` with kernel `I` and
`Q : S[Y] → T` is the canonical `S`-presentation of `T` with kernel `K`.
Denote by `J` the kernel of the composition `R[X,Y] → T`.

This file proves `J/J² ≃ₗ[T] T ⊗[S] (I/I²) × K/K²`. For this we establish the exact sequence:
```
0 → T ⊗[S] (I/I²) → J/J² → K/K² → 0
```
and use that `K/K²` is free, so the sequence splits. The first part of the file
shows the exactness on the left and the rest of the file deduces the exact sequence
and the splitting from the Jacobi Zariski sequence.

## Main results

- `Algebra.Generators.liftBaseChange_injective`:
  `T ⊗[S] (I/I²) → J/J²` is injective if `T` is the localization of `S` away from an element.
- `Algebra.Generators.cotangentCompLocalizationAwayEquiv`: `J/J² ≃ₗ[T] T ⊗[S] (I/I²) × K/K²`.
-/

open TensorProduct MvPolynomial

namespace Algebra.Generators

variable {R S T ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

variable (g : S) [IsLocalization.Away g T] (P : Generators R S ι)

lemma comp_localizationAway_ker (P : Generators R S ι) (f : P.Ring)
    (h : algebraMap P.Ring S f = g) :
    ((Generators.localizationAway T g).comp P).ker =
      Ideal.map ((Generators.localizationAway T g).toComp P).toAlgHom P.ker ⊔
        Ideal.span {rename Sum.inr f * X (Sum.inl ()) - 1} := by
  have : (localizationAway T g).ker = Ideal.map ((localizationAway T g).ofComp P).toAlgHom
      (Ideal.span {MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1}) := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_mul, map_one, ker_localizationAway,
      Hom.toAlgHom_X, toAlgHom_ofComp_rename, h, ofComp_val, Sum.elim_inl]
  rw [ker_comp_eq_sup, Algebra.Generators.map_toComp_ker, this,
    Ideal.comap_map_of_surjective _ (toAlgHom_ofComp_surjective _ P), ← RingHom.ker_eq_comap_bot,
    ← sup_assoc]
  simp

variable (T) in

noncomputable

def compLocalizationAwayAlgHom : ((Generators.localizationAway T g).comp P).Ring →ₐ[R]
      Localization.Away (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)) :=
  aeval (R := R) (S₁ := Localization.Away _)
    (Sum.elim
      (fun _ ↦ IsLocalization.Away.invSelf <| (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)))
      (fun i : ι ↦ algebraMap P.Ring _ (X i)))

set_option backward.isDefEq.respectTransparency false in
