/-
Extracted from GroupTheory/FiniteAbelian/Duality.lean
Genuine: 1 of 3 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Duality for finite abelian groups

Let `G` be a finite abelian group.

For `M` a commutative monoid that has enough `n`th roots of unity, where `n` is the exponent of `G`,
the main results in this file are:
* `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`: Homomorphisms `G →* Mˣ` separate
  elements of `G`.
* `CommGroup.monoidHom_mulEquiv_self_of_hasEnoughRootsOfUnity`: `G` is isomorphic to `G →* Mˣ`.
* `CommGroup.monoidHomMonoidHomEquiv`: `G` is isomorphic to its double dual `(G →* Mˣ) →* Mˣ`.
* `CommGroup.subgroupOrderIsoSubgroupMonoidHom`: the order reversing bijection that sends a
  subgroup of `G` to its dual subgroup in `G →* Mˣ`.
-/

namespace CommGroup

open MonoidHom

private

lemma dvd_exponent {ι G : Type*} [Finite ι] [Monoid G] {n : ι → ℕ}
    (e : G ≃* ((i : ι) → Multiplicative (ZMod (n i)))) (i : ι) :
    n i ∣ Monoid.exponent G := by
  classical -- to get `DecidableEq ι`
  have : n i = orderOf (e.symm <| Pi.mulSingle i <| .ofAdd 1) := by
    simpa only [MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
      using (ZMod.addOrderOf_one (n i)).symm
  exact this ▸ Monoid.order_dvd_exponent _

variable (G M : Type*) [CommGroup G] [Finite G] [CommMonoid M]

private

-- DISSOLVED: exists_apply_ne_one_aux

variable [hM : HasEnoughRootsOfUnity M (Monoid.exponent G)]

-- DISSOLVED: exists_apply_ne_one_of_hasEnoughRootsOfUnity

variable {M} in
