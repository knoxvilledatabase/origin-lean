/-
Extracted from FieldTheory/AbelRuffini.lean
Genuine: 14 of 15 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Abel-Ruffini Theorem

This file proves one direction of the Abel-Ruffini theorem, namely that if an element is solvable
by radicals, then its minimal polynomial has solvable Galois group.

## Main definitions

* `solvableByRad F E` : the intermediate field of solvable-by-radicals elements

## Main results

* The Abel-Ruffini Theorem `isSolvable_gal_of_irreducible`: An irreducible polynomial with a root
  that is solvable by radicals has a solvable Galois group.
-/

open Polynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem gal_zero_isSolvable : IsSolvable (0 : F[X]).Gal := by infer_instance

theorem gal_one_isSolvable : IsSolvable (1 : F[X]).Gal := by infer_instance

theorem gal_C_isSolvable (x : F) : IsSolvable (C x).Gal := by infer_instance

theorem gal_X_isSolvable : IsSolvable (X : F[X]).Gal := by infer_instance

theorem gal_X_sub_C_isSolvable (x : F) : IsSolvable (X - C x).Gal := by infer_instance

theorem gal_X_pow_isSolvable (n : ℕ) : IsSolvable (X ^ n : F[X]).Gal := by infer_instance

theorem gal_mul_isSolvable {p q : F[X]} (_ : IsSolvable p.Gal) (_ : IsSolvable q.Gal) :
    IsSolvable (p * q).Gal :=
  solvable_of_solvable_injective (Gal.restrictProd_injective p q)

theorem gal_prod_isSolvable {s : Multiset F[X]} (hs : ∀ p ∈ s, IsSolvable (Gal p)) :
    IsSolvable s.prod.Gal := by
  apply Multiset.induction_on' s
  · exact gal_one_isSolvable
  · intro p t hps _ ht
    rw [Multiset.insert_eq_cons, Multiset.prod_cons]
    exact gal_mul_isSolvable (hs p hps) ht

theorem gal_isSolvable_of_splits {p q : F[X]}
    (_ : Fact ((p.map (algebraMap F q.SplittingField)).Splits)) (hq : IsSolvable q.Gal) :
    IsSolvable p.Gal :=
  haveI : IsSolvable (q.SplittingField ≃ₐ[F] q.SplittingField) := hq
  solvable_of_surjective (AlgEquiv.restrictNormalHom_surjective q.SplittingField)

theorem gal_isSolvable_tower (p q : F[X]) (hpq : (p.map (algebraMap F q.SplittingField)).Splits)
    (hp : IsSolvable p.Gal) (hq : IsSolvable (q.map (algebraMap F p.SplittingField)).Gal) :
    IsSolvable q.Gal := by
  let K := p.SplittingField
  let L := q.SplittingField
  haveI : Fact ((p.map (algebraMap F L)).Splits) := ⟨hpq⟩
  let ϕ : Gal(L/K) ≃* (q.map (algebraMap F K)).Gal :=
    (IsSplittingField.algEquiv L (q.map (algebraMap F K))).autCongr
  have ϕ_inj : Function.Injective ϕ.toMonoidHom := ϕ.injective
  haveI : IsSolvable Gal(K/F) := hp
  haveI : IsSolvable Gal(L/K) := solvable_of_solvable_injective ϕ_inj
  exact isSolvable_of_isScalarTower F p.SplittingField q.SplittingField

section GalXPowSubC

set_option backward.isDefEq.respectTransparency false in

theorem gal_X_pow_sub_one_isSolvable (n : ℕ) : IsSolvable (X ^ n - 1 : F[X]).Gal := by
  by_cases hn : n = 0
  · rw [hn, pow_zero, sub_self]
    exact gal_zero_isSolvable
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - 1 : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hn' 1
  apply isSolvable_of_comm
  intro σ τ
  ext a ha
  simp only [mem_rootSet_of_ne hn'', map_sub, aeval_X_pow, aeval_one, sub_eq_zero] at ha
  have key : ∀ σ : (X ^ n - 1 : F[X]).Gal, ∃ m : ℕ, σ a = a ^ m := by
    intro σ
    lift n to ℕ+ using hn'
    exact map_rootsOfUnity_eq_pow_self σ.toAlgHom (rootsOfUnity.mkOfPowEq a ha)
  obtain ⟨c, hc⟩ := key σ
  obtain ⟨d, hd⟩ := key τ
  rw [σ.mul_apply, τ.mul_apply, hc, map_pow, hd, map_pow, hc, ← pow_mul, pow_mul']

set_option backward.isDefEq.respectTransparency false in

theorem gal_X_pow_sub_C_isSolvable_aux (n : ℕ) (a : F)
    (h : ((X ^ n - 1 : F[X]).map (RingHom.id F)).Splits) : IsSolvable (X ^ n - C a).Gal := by
  by_cases ha : a = 0
  · rw [ha, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  have ha' : algebraMap F (X ^ n - C a).SplittingField a ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (RingHom.injective _) a) ha
  by_cases hn : n = 0
  · rw [hn, pow_zero, ← C_1, ← C_sub]
    exact gal_C_isSolvable (1 - a)
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : X ^ n - C a ≠ 0 := X_pow_sub_C_ne_zero hn' a
  have hn''' : (X ^ n - 1 : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hn' 1
  have mem_range : ∀ {c : (X ^ n - C a).SplittingField},
      (c ^ n = 1 → (∃ d, algebraMap F (X ^ n - C a).SplittingField d = c)) := fun {c} hc =>
    RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one F c
      (Splits.degree_eq_one_of_irreducible (h.of_dvd (map_ne_zero hn''')
        (minpoly.dvd F c (by rwa [map_id, map_sub, sub_eq_zero, aeval_X_pow, aeval_one])))
          (minpoly.irreducible ((SplittingField.instNormal (X ^ n - C a)).isIntegral c))))
  apply isSolvable_of_comm
  intro σ τ
  ext b hb
  rw [mem_rootSet_of_ne hn'', map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at hb
  have hb' : b ≠ 0 := by
    intro hb'
    rw [hb', zero_pow hn] at hb
    exact ha' hb.symm
  have key : ∀ σ : (X ^ n - C a).Gal, ∃ c, σ b = b * algebraMap F _ c := by
    intro σ
    have key : (σ b / b) ^ n = 1 := by rw [div_pow, ← map_pow, hb, σ.commutes, div_self ha']
    obtain ⟨c, hc⟩ := mem_range key
    use c
    rw [hc, mul_div_cancel₀ (σ b) hb']
  obtain ⟨c, hc⟩ := key σ
  obtain ⟨d, hd⟩ := key τ
  rw [σ.mul_apply, τ.mul_apply, hc, map_mul, τ.commutes, hd, map_mul, σ.commutes, hc,
    mul_assoc, mul_assoc, mul_right_inj' hb', mul_comm]

-- DISSOLVED: splits_X_pow_sub_one_of_X_pow_sub_C

theorem gal_X_pow_sub_C_isSolvable (n : ℕ) (x : F) : IsSolvable (X ^ n - C x).Gal := by
  by_cases hx : x = 0
  · rw [hx, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  apply gal_isSolvable_tower (X ^ n - 1) (X ^ n - C x)
  · exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (SplittingField.splits _)
  · exact gal_X_pow_sub_one_isSolvable n
  · rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    apply gal_X_pow_sub_C_isSolvable_aux
    rw [map_id]
    have key := SplittingField.splits (X ^ n - 1 : F[X])
    rwa [Polynomial.map_sub, Polynomial.map_pow, map_X,
      Polynomial.map_one] at key

end GalXPowSubC

variable (F E) in

def solvableByRad : IntermediateField F E :=
  sInf {s | ∀ x, ∀ n ≠ 0, x ^ n ∈ s → x ∈ s}

variable (F) in
