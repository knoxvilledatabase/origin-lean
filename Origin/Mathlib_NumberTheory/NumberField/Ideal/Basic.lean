/-
Extracted from NumberTheory/NumberField/Ideal/Basic.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic results on integral ideals of a number field

We study results about integral ideals of a number field `K`.

## Main definitions and results

* `Ideal.rootsOfUnityMapQuot` : For `I` an integral ideal of `K`, the group morphism from the
  group of roots of unity of `K` of order `n` to `(𝓞 K ⧸ I)ˣ`.

* `Ideal.rootsOfUnityMapQuot_injective`: If the ideal `I` is nontrivial and its norm is coprime
  with `n`, then the map `Ideal.rootsOfUnityMapQuot` is injective.

* `NumberField.torsionOrder_dvd_absNorm_sub_one`: If the norm of the (nonzero) prime ideal `P` is
  coprime with the order of the torsion of `K`, then the norm of `P` is congruent to `1` modulo
  `torsionOrder K`.

-/

open Ideal NumberField Units

variable {K : Type*} [Field K] {I : Ideal (𝓞 K)}

section torsionMapQuot

-- DISSOLVED: IsPrimitiveRoot.not_coprime_norm_of_mk_eq_one

variable (I)

def Ideal.rootsOfUnityMapQuot (n : ℕ) : (rootsOfUnity n (𝓞 K)) →* ((𝓞 K) ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).restrict _
