/-
Extracted from GroupTheory/FiniteAbelian/Duality.lean
Genuine: 2 of 4 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Duality for finite abelian groups

Let `G` be a finite abelian group and let `M` be a commutative monoid that has enough `n`th roots
of unity, where `n` is the exponent of `G`. The main results in this file are
* `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`: Homomorphisms `G →* Mˣ` separate
  elements of `G`.
* `CommGroup.monoidHom_mulEquiv_self_of_hasEnoughRootsOfUnity`: `G` is isomorphic to `G →* Mˣ`.
-/

namespace CommGroup

open MonoidHom

private

lemma dvd_exponent {ι G : Type*} [Finite ι] [CommGroup G] {n : ι → ℕ}
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

variable [HasEnoughRootsOfUnity M (Monoid.exponent G)]

-- DISSOLVED: exists_apply_ne_one_of_hasEnoughRootsOfUnity

theorem monoidHom_mulEquiv_of_hasEnoughRootsOfUnity : Nonempty ((G →* Mˣ) ≃* G) := by
  classical -- to get `DecidableEq ι`
  obtain ⟨ι, _, n, ⟨h₁, h₂⟩⟩ := equiv_prod_multiplicative_zmod_of_finite G
  let e := h₂.some
  let e' := Pi.monoidHomMulEquiv (fun i ↦ Multiplicative (ZMod (n i))) Mˣ
  let e'' := MulEquiv.monoidHomCongr e (.refl Mˣ)
  have : ∀ i, NeZero (n i) := fun i ↦ NeZero.of_gt (h₁ i)
  have inst i : HasEnoughRootsOfUnity M <| Nat.card <| Multiplicative <| ZMod (n i) := by
    have hdvd : Nat.card (Multiplicative (ZMod (n i))) ∣ Monoid.exponent G := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
        using dvd_exponent e i
    exact HasEnoughRootsOfUnity.of_dvd M hdvd
  let E i := (IsCyclic.monoidHom_equiv_self (Multiplicative (ZMod (n i))) M).some
  exact ⟨e''.trans <| e'.trans <| (MulEquiv.piCongrRight E).trans e.symm⟩

end CommGroup
