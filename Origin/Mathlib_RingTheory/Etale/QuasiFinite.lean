/-
Extracted from RingTheory/Etale/QuasiFinite.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Etale local structure of finite maps

We construct etale neighborhoods that split fibers of finite algebras.

## Main results
- `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`:
  Let `S` be a module-finite `R`-algebra, and `q` a prime lying over `p`.
  We may construct an etale `R`-algebra `R'` and a prime `P` lying over `p` with `κ(P) = κ(p)`,
  such that `R' ⊗[R] S = A × B` and there exists a unique prime in `A` lying over `P`.
  This prime will also lie over `q`.

-/

open TensorProduct

section BijectiveResidueField

variable {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]

noncomputable

def Ideal.fiberIsoOfBijectiveResidueField
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p))) :
    q.primesOver (R' ⊗[R] S) ≃o p.primesOver S :=
  let e : q.Fiber (R' ⊗[R] S) ≃ₐ[p.ResidueField] p.Fiber S :=
    ((Algebra.TensorProduct.cancelBaseChange _ _ q.ResidueField _ _).restrictScalars _).trans
      (Algebra.TensorProduct.congr (.symm <| .ofBijective (Algebra.ofId _ _) H) .refl)
  (PrimeSpectrum.primesOverOrderIsoFiber ..).trans <|
    (PrimeSpectrum.comapEquiv e.toRingEquiv).trans (PrimeSpectrum.primesOverOrderIsoFiber ..).symm

lemma Ideal.comap_fiberIsoOfBijectiveResidueField_symm
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : p.primesOver S) :
    ((Ideal.fiberIsoOfBijectiveResidueField H).symm Q).1.comap
      (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) = Q.1 := by
  ext x
  simp [Ideal.fiberIsoOfBijectiveResidueField,
    PrimeSpectrum.primesOverOrderIsoFiber, PrimeSpectrum.preimageOrderIsoFiber,
    PrimeSpectrum.preimageEquivFiber]
