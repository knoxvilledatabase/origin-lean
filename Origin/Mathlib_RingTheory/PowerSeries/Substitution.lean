/-
Extracted from RingTheory/PowerSeries/Substitution.lean
Genuine: 34 of 38 | Dissolved: 3 | Infrastructure: 1
-/
import Origin.Core

/-! # Substitutions in power series

A (possibly multivariate) power series can be substituted into
a (univariate) power series if and only if its constant coefficient is nilpotent.

This is a particularization of the substitution of multivariate power series
to the case of univariate power series.

Because of the special API for `PowerSeries`, some results for `MvPowerSeries`
do not immediately apply and a “primed” version is provided here.

-/

namespace PowerSeries

variable
  {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S]

open MvPowerSeries.WithPiTopology

abbrev HasSubst (a : MvPowerSeries τ S) : Prop :=
  IsNilpotent (MvPowerSeries.constantCoeff a)

theorem hasSubst_iff {a : MvPowerSeries τ S} :
    HasSubst a ↔ MvPowerSeries.HasSubst (Function.const Unit a) :=
  ⟨fun ha ↦ MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (Function.const Unit ha),
   fun ha ↦ (ha.const_coeff ())⟩

theorem HasSubst.const {a : MvPowerSeries τ S} (ha : HasSubst a) :
    MvPowerSeries.HasSubst (fun () ↦ a) :=
  hasSubst_iff.mp ha

theorem hasSubst_iff_hasEval_of_discreteTopology
    [TopologicalSpace S] [DiscreteTopology S] {a : MvPowerSeries τ S} :
    HasSubst a ↔ PowerSeries.HasEval a := by
  rw [hasSubst_iff, MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology, hasEval_iff,
    Function.const_def]

theorem HasSubst.hasEval [TopologicalSpace S] {a : MvPowerSeries τ S} (ha : HasSubst a) :
    HasEval a := isTopologicallyNilpotent_of_constantCoeff_isNilpotent ha

theorem HasSubst.of_constantCoeff_zero {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff a = 0) : HasSubst a := by
  simp [HasSubst, ha]

theorem HasSubst.of_constantCoeff_zero' {a : PowerSeries S}
    (ha : PowerSeries.constantCoeff a = 0) : HasSubst a :=
  HasSubst.of_constantCoeff_zero ha

protected theorem HasSubst.X (t : τ) :
    HasSubst (MvPowerSeries.X t : MvPowerSeries τ S) := by
  simp [HasSubst]

protected theorem HasSubst.X' : HasSubst (X : R⟦X⟧) :=
  HasSubst.X _

-- DISSOLVED: HasSubst.X_pow

-- DISSOLVED: HasSubst.monomial

-- DISSOLVED: HasSubst.monomial'

theorem HasSubst.zero : HasSubst (0 : MvPowerSeries τ R) := by
  rw [hasSubst_iff]
  exact MvPowerSeries.HasSubst.zero

theorem HasSubst.zero' : HasSubst (0 : PowerSeries R) :=
  PowerSeries.HasSubst.zero

variable {f g : MvPowerSeries τ R}

theorem HasSubst.add (hf : HasSubst f) (hg : HasSubst g) :
    HasSubst (f + g) :=
  (Commute.all _ _).isNilpotent_add hf hg

theorem HasSubst.mul_left (hf : HasSubst f) :
    HasSubst (f * g) := by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right hf

theorem HasSubst.mul_right (hf : HasSubst f) :
    HasSubst (g * f) := by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_left hf

theorem HasSubst.smul (r : MvPowerSeries τ S) {a : MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (r • a) :=
  ha.mul_right

noncomputable def HasSubst.ideal : Ideal (MvPowerSeries τ S) where
  carrier := setOf HasSubst
  add_mem' := HasSubst.add
  zero_mem' := HasSubst.zero
  smul_mem' := HasSubst.smul

theorem HasSubst.smul' (a : A) (hf : HasSubst f) :
    HasSubst (a • f) := by
  simp only [HasSubst, MvPowerSeries.constantCoeff_smul]
  exact IsNilpotent.smul hf _

theorem HasSubst.smul_X (a : A) (t : τ) :
    HasSubst (a • (MvPowerSeries.X t) : MvPowerSeries τ R) :=
  (HasSubst.X t).smul' _

theorem HasSubst.smul_X' (a : A) : HasSubst (a • X : R⟦X⟧) :=
  HasSubst.X'.smul' _

lemma HasSubst.eventually_coeff_pow_eq_zero {f : A⟦X⟧} (hf : HasSubst f) (n : ℕ) :
    ∀ᶠ m in .atTop, ∀ n' ≤ n, coeff n' (f ^ m) = 0 := by
  obtain ⟨k, hk⟩ := id hf
  refine Filter.eventually_of_mem (Filter.Ici_mem_atTop (k * (n + 1))) fun m hm n' hn' ↦
    coeff_of_lt_order _ ?_
  obtain ⟨m, rfl⟩ := le_iff_exists_add.mp (Set.mem_Ici.mp hm)
  grw [pow_add, ← order_mul_ge, pow_mul, ← le_order_pow_of_constantCoeff_eq_zero _
    (by rwa [map_pow]), ← _root_.le_add_right le_rfl, Nat.cast_lt]
  lia

variable {υ : Type*} {T : Type*} [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]

noncomputable def subst (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f

variable {a : MvPowerSeries τ S} {b : S⟦X⟧}

noncomputable def substAlgHom (ha : HasSubst a) :
    PowerSeries R →ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.substAlgHom ha.const

theorem coe_substAlgHom (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a :=
  MvPowerSeries.coe_substAlgHom ha.const

attribute [local instance] DiscreteTopology.instContinuousSMul in

theorem substAlgHom_eq_aeval
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) :
    (substAlgHom ha : R⟦X⟧ →ₐ[R] MvPowerSeries τ S) = PowerSeries.aeval ha.hasEval := by
  ext1 f
  simpa [substAlgHom] using congr_fun (MvPowerSeries.substAlgHom_eq_aeval ha.const) f

theorem subst_add (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [← coe_substAlgHom ha, map_add]

theorem subst_sub (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f - g) = subst a f - subst a g := by
  rw [← coe_substAlgHom ha, map_sub]

theorem subst_pow (ha : HasSubst a) (f : PowerSeries R) (n : ℕ) :
    subst a (f ^ n) = (subst a f) ^ n := by
  rw [← coe_substAlgHom ha, map_pow]

theorem subst_mul (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha, map_mul]

theorem subst_smul [Algebra A S] [IsScalarTower A R S]
    (ha : HasSubst a) (r : A) (f : PowerSeries R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha, AlgHom.map_smul_of_tower]

theorem coeff_subst_finite (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    (fun (d : ℕ) ↦ coeff d f • MvPowerSeries.coeff e (a ^ d)).HasFiniteSupport := by
  rw [Function.HasFiniteSupport]
  convert (MvPowerSeries.coeff_subst_finite ha.const f e).image
    (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv
  rw [← Equiv.preimage_eq_iff_eq_image, ← Function.support_comp_eq_preimage]
  apply congr_arg
  rw [← Equiv.eq_comp_symm]
  ext
  simp [coeff]

theorem coeff_subst_finite' (hb : HasSubst b) (f : PowerSeries R) (e : ℕ) :
    (fun (d : ℕ) ↦ coeff d f • (PowerSeries.coeff e (b ^ d))).HasFiniteSupport :=
  coeff_subst_finite hb f _

theorem coeff_subst (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (subst a f) =
      finsum (fun (d : ℕ) ↦
        coeff d f • (MvPowerSeries.coeff e (a ^ d))) := by
  rw [subst, MvPowerSeries.coeff_subst ha.const f e, ← finsum_comp_equiv
    (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.symm]
  apply finsum_congr
  intro
  congr <;> simp

theorem coeff_subst' {b : S⟦X⟧} (hb : HasSubst b) (f : R⟦X⟧) (e : ℕ) :
    coeff e (f.subst b) =
      finsum (fun (d : ℕ) ↦
        coeff d f • PowerSeries.coeff e (b ^ d)) := by
  simp [PowerSeries.coeff, coeff_subst hb]

theorem constantCoeff_subst (ha : HasSubst a) (f : PowerSeries R) :
    MvPowerSeries.constantCoeff (subst a f) =
      finsum (fun d ↦ coeff d f • MvPowerSeries.constantCoeff (a ^ d)) := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]
