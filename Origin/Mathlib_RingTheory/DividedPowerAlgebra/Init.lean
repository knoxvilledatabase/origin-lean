/-
Extracted from RingTheory/DividedPowerAlgebra/Init.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The universal divided power algebra

Let `R` be a (commutative) semiring and `M` be an `R`-module. In this file we define `Γ_R(M)`,
the universal divided power algebra of `M`, as the ring quotient of the polynomial ring
in the variables `ℕ × M` by the relation `DividedPowerAlgebra.Rel`.

`DividedPowerAlgebra R M` satisfies a weak universal property for morphisms to rings with
divided powers.

## Main definitions

* `DividedPowerAlgebra.Rel`: the type coding the basic relations that will give rise to the
  divided power algebra.

* `DividedPowerAlgebra R M`: the universal divided power algebra of the `R`-module `M`,
  defined as `RingQuot` of `DividedPowerAlgebra.Rel R M`.

* `DividedPowerAlgebra.dp R n m`: for `n : ℕ` and `m : M`, this is the equivalence class of
  `MvPolynomial.X (⟨n, m⟩)` in `DividedPowerAlgebra R M`.

  When that algebra is endowed with its canonical divided power structure (to be defined),
  the image of `MvPolynomial.X (n, m)`, for any `n : ℕ` and `m : M`, is equal to
  the `n`th divided power of the image of `m`.

  The API will be setup so that it is never (never say never…) necessary to lift to `MvPolynomial`.

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de
  caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline
  cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des
  modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

## TODO

* Add the weak universal property of `DividedPowerAlgebra R M`.
* Show in upcoming files that `DividedPowerAlgebra R M` has divided powers.


-/

noncomputable section

open Finset Ideal MvPolynomial RingQuot

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace DividedPowerAlgebra

inductive Rel : MvPolynomial (ℕ × M) R → MvPolynomial (ℕ × M) R → Prop
  | rfl_zero : Rel 0 0 -- Needed for technical reasons.
  | zero {a : M} : Rel (X (0, a)) 1
  | smul {r : R} {n : ℕ} {a : M} : Rel (X (n, r • a)) (r ^ n • X (n, a))
  | mul {m n : ℕ} {a : M} : Rel (X (m, a) * X (n, a)) (Nat.choose (m + n) m • X (m + n, a))
  | add {n : ℕ} {a b : M} :
    Rel (X (n, a + b)) ((Finset.antidiagonal n).sum fun k => X (k.1, a) * X (k.2, b))

def RelI : Ideal (MvPolynomial (ℕ × M) R) := ofRel (DividedPowerAlgebra.Rel R M)

end DividedPowerAlgebra

abbrev DividedPowerAlgebra := RingQuot (DividedPowerAlgebra.Rel R M)

namespace DividedPowerAlgebra

open MvPolynomial

variable {R M}

lemma mkAlgHom_surjective : Function.Surjective (mkAlgHom R (Rel R M)) :=
  RingQuot.mkAlgHom_surjective _ _

lemma mkAlgHom_C (a : R) :
    mkAlgHom R (Rel R M) (C a) = algebraMap R (DividedPowerAlgebra R M) a := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

lemma mkRingHom_C (a : R) :
    mkRingHom (Rel R M) (C a) = algebraMap R (DividedPowerAlgebra R M) a := by
  rw [← mkAlgHom_C, mkAlgHom, AlgHom.coe_mk]

variable (R) in

def dp (n : ℕ) (m : M) : DividedPowerAlgebra R M := mkAlgHom R (Rel R M) (X ⟨n, m⟩)

protected theorem induction_on' {P : DividedPowerAlgebra R M → Prop} (f : DividedPowerAlgebra R M)
    (h_C : ∀ a, P (mkAlgHom R (Rel R M) (C a))) (h_add : ∀ f g, P f → P g → P (f + g))
    (h_dp : ∀ (f : DividedPowerAlgebra R M) (n : ℕ) (m : M), P f → P (f * dp R n m)) : P f := by
  obtain ⟨F, hf⟩ := RingQuot.mkRingHom_surjective (DividedPowerAlgebra.Rel R M) f
  rw [← hf]
  induction F using MvPolynomial.induction_on generalizing f with
  | C a =>
      convert h_C a using 1
      rw [mkAlgHom, AlgHom.coe_mk]
  | add g1 g2 hg1 hg2 =>
      rw [map_add]
      exact h_add _ _ (hg1 ((mkRingHom (Rel R M)) g1) rfl) (hg2 ((mkRingHom (Rel R M)) g2) rfl)
  | mul_X g nm h =>
      have h' : (mkRingHom (Rel R M)) (X nm) = dp R nm.1 nm.2 := by
        simp only [dp_def, Prod.mk.eta, mkAlgHom, AlgHom.coe_mk]
      rw [_root_.map_mul, h']
      exact h_dp _ _ _ (h (mkRingHom (Rel R M) g) rfl)
