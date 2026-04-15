/-
Extracted from RingTheory/ClassGroup.lean
Genuine: 26 | Conflates: 0 | Dissolved: 5 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.RingTheory.DedekindDomain.Ideal

/-!
# The ideal class group

This file defines the ideal class group `ClassGroup R` of fractional ideals of `R`
inside its field of fractions.

## Main definitions
 - `toPrincipalIdeal` sends an invertible `x : K` to an invertible fractional ideal
 - `ClassGroup` is the quotient of invertible fractional ideals modulo `toPrincipalIdeal.range`
 - `ClassGroup.mk0` sends a nonzero integral ideal in a Dedekind domain to its class

## Main results
 - `ClassGroup.mk0_eq_mk0_iff` shows the equivalence with the "classical" definition,
   where `I ~ J` iff `x I = y J` for `x y ≠ (0 : R)`

## Implementation details

The definition of `ClassGroup R` involves `FractionRing R`. However, the API should be completely
identical no matter the choice of field of fractions for `R`.
-/

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

open scoped nonZeroDivisors

open IsLocalization IsFractionRing FractionalIdeal Units

section

variable (R K)

irreducible_def toPrincipalIdeal : Kˣ →* (FractionalIdeal R⁰ K)ˣ :=
  { toFun := fun x =>
      ⟨spanSingleton _ x, spanSingleton _ x⁻¹, by
        simp only [spanSingleton_one, Units.mul_inv', spanSingleton_mul_spanSingleton], by
        simp only [spanSingleton_one, Units.inv_mul', spanSingleton_mul_spanSingleton]⟩
    map_mul' := fun x y =>
      ext (by simp only [Units.val_mk, Units.val_mul, spanSingleton_mul_spanSingleton])
    map_one' := ext (by simp only [spanSingleton_one, Units.val_mk, Units.val_one]) }

variable {R K}

@[simp]
theorem coe_toPrincipalIdeal (x : Kˣ) :
    (toPrincipalIdeal R K x : FractionalIdeal R⁰ K) = spanSingleton _ (x : K) := by
  simp only [toPrincipalIdeal]; rfl

@[simp]
theorem toPrincipalIdeal_eq_iff {I : (FractionalIdeal R⁰ K)ˣ} {x : Kˣ} :
    toPrincipalIdeal R K x = I ↔ spanSingleton R⁰ (x : K) = I := by
  simp only [toPrincipalIdeal]; exact Units.ext_iff

theorem mem_principal_ideals_iff {I : (FractionalIdeal R⁰ K)ˣ} :
    I ∈ (toPrincipalIdeal R K).range ↔ ∃ x : K, spanSingleton R⁰ x = I := by
  simp only [MonoidHom.mem_range, toPrincipalIdeal_eq_iff]
  constructor <;> rintro ⟨x, hx⟩
  · exact ⟨x, hx⟩
  · refine ⟨Units.mk0 x ?_, hx⟩
    rintro rfl
    simp [I.ne_zero.symm] at hx

instance PrincipalIdeals.normal : (toPrincipalIdeal R K).range.Normal :=
  Subgroup.normal_of_comm _

end

variable (R)

variable [IsDomain R]

def ClassGroup :=
  (FractionalIdeal R⁰ (FractionRing R))ˣ ⧸ (toPrincipalIdeal R (FractionRing R)).range

noncomputable instance : CommGroup (ClassGroup R) :=
  QuotientGroup.Quotient.commGroup (toPrincipalIdeal R (FractionRing R)).range

noncomputable instance : Inhabited (ClassGroup R) := ⟨1⟩

variable {R}

noncomputable def ClassGroup.mk : (FractionalIdeal R⁰ K)ˣ →* ClassGroup R :=
  (QuotientGroup.mk' (toPrincipalIdeal R (FractionRing R)).range).comp
    (Units.map (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)))

theorem ClassGroup.Quot_mk_eq_mk (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    Quot.mk _ I = ClassGroup.mk I := by
  rw [ClassGroup.mk, canonicalEquiv_self, RingEquiv.coe_monoidHom_refl, Units.map_id]
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [MonoidHom.comp_apply]
  rw [MonoidHom.id_apply, QuotientGroup.mk'_apply]
  rfl

theorem ClassGroup.mk_eq_mk {I J : (FractionalIdeal R⁰ <| FractionRing R)ˣ} :
    ClassGroup.mk I = ClassGroup.mk J ↔
      ∃ x : (FractionRing R)ˣ, I * toPrincipalIdeal R (FractionRing R) x = J := by
  erw [QuotientGroup.mk'_eq_mk', canonicalEquiv_self, Units.map_id, Set.exists_range_iff]
  rfl

-- DISSOLVED: ClassGroup.mk_eq_mk_of_coe_ideal

-- DISSOLVED: ClassGroup.mk_eq_one_of_coe_ideal

variable (K)

@[elab_as_elim]
theorem ClassGroup.induction {P : ClassGroup R → Prop}
    (h : ∀ I : (FractionalIdeal R⁰ K)ˣ, P (ClassGroup.mk I)) (x : ClassGroup R) : P x :=
  QuotientGroup.induction_on x fun I => by
    have : I = (Units.mapEquiv (canonicalEquiv R⁰ K (FractionRing R)).toMulEquiv)
      (Units.mapEquiv (canonicalEquiv R⁰ (FractionRing R) K).toMulEquiv I) := by
      simp [← Units.eq_iff]
    rw [congr_arg (QuotientGroup.mk (s := (toPrincipalIdeal R (FractionRing R)).range)) this]
    exact h _

noncomputable def ClassGroup.equiv :
    ClassGroup R ≃* (FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range := by
  haveI : Subgroup.map
    (Units.mapEquiv (canonicalEquiv R⁰ (FractionRing R) K).toMulEquiv).toMonoidHom
    (toPrincipalIdeal R (FractionRing R)).range = (toPrincipalIdeal R K).range := by
    ext I
    simp only [Subgroup.mem_map, mem_principal_ideals_iff]
    constructor
    · rintro ⟨I, ⟨x, hx⟩, rfl⟩
      refine ⟨FractionRing.algEquiv R K x, ?_⟩
      simp only [RingEquiv.toMulEquiv_eq_coe, MulEquiv.coe_toMonoidHom, coe_mapEquiv, ← hx,
        RingEquiv.coe_toMulEquiv, canonicalEquiv_spanSingleton]
      rfl
    · rintro ⟨x, hx⟩
      refine ⟨Units.mapEquiv (canonicalEquiv R⁰ K (FractionRing R)).toMulEquiv I,
        ⟨(FractionRing.algEquiv R K).symm x, ?_⟩, Units.ext ?_⟩
      · simp only [RingEquiv.toMulEquiv_eq_coe, coe_mapEquiv, ← hx, RingEquiv.coe_toMulEquiv,
          canonicalEquiv_spanSingleton]
        rfl
      · simp only [RingEquiv.toMulEquiv_eq_coe, MulEquiv.coe_toMonoidHom, coe_mapEquiv,
          RingEquiv.coe_toMulEquiv, canonicalEquiv_canonicalEquiv, canonicalEquiv_self,
          RingEquiv.refl_apply]
  exact @QuotientGroup.congr (FractionalIdeal R⁰ (FractionRing R))ˣ _ (FractionalIdeal R⁰ K)ˣ _
    (toPrincipalIdeal R (FractionRing R)).range (toPrincipalIdeal R K).range _ _
    (Units.mapEquiv (FractionalIdeal.canonicalEquiv R⁰ (FractionRing R) K).toMulEquiv) this

@[simp]
theorem ClassGroup.equiv_mk (K' : Type*) [Field K'] [Algebra R K'] [IsFractionRing R K']
    (I : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.equiv K' (ClassGroup.mk I) =
      QuotientGroup.mk' _ (Units.mapEquiv (↑(FractionalIdeal.canonicalEquiv R⁰ K K')) I) := by
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [ClassGroup.equiv, ClassGroup.mk, MonoidHom.comp_apply, QuotientGroup.congr_mk']
  congr
  rw [← Units.eq_iff, Units.coe_mapEquiv, Units.coe_mapEquiv, Units.coe_map]
  exact FractionalIdeal.canonicalEquiv_canonicalEquiv _ _ _ _ _

@[simp]
theorem ClassGroup.mk_canonicalEquiv (K' : Type*) [Field K'] [Algebra R K'] [IsFractionRing R K']
    (I : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.mk (Units.map (↑(canonicalEquiv R⁰ K K')) I : (FractionalIdeal R⁰ K')ˣ) =
      ClassGroup.mk I := by
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [ClassGroup.mk, MonoidHom.comp_apply, ← MonoidHom.comp_apply (Units.map _),
      ← Units.map_comp, ← RingEquiv.coe_monoidHom_trans,
      FractionalIdeal.canonicalEquiv_trans_canonicalEquiv]
  rfl

noncomputable def FractionalIdeal.mk0 [IsDedekindDomain R] :
    (Ideal R)⁰ →* (FractionalIdeal R⁰ K)ˣ where
  toFun I := Units.mk0 I (coeIdeal_ne_zero.mpr <| mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  map_one' := by simp
  map_mul' x y := by simp

@[simp]
theorem FractionalIdeal.coe_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    (FractionalIdeal.mk0 K I : FractionalIdeal R⁰ K) = I := rfl

theorem FractionalIdeal.canonicalEquiv_mk0 [IsDedekindDomain R] (K' : Type*) [Field K']
    [Algebra R K'] [IsFractionRing R K'] (I : (Ideal R)⁰) :
    FractionalIdeal.canonicalEquiv R⁰ K K' (FractionalIdeal.mk0 K I) =
    FractionalIdeal.mk0 K' I := by
  simp only [FractionalIdeal.coe_mk0, FractionalIdeal.canonicalEquiv_coeIdeal]

@[simp]
theorem FractionalIdeal.map_canonicalEquiv_mk0 [IsDedekindDomain R] (K' : Type*) [Field K']
    [Algebra R K'] [IsFractionRing R K'] (I : (Ideal R)⁰) :
    Units.map (↑(FractionalIdeal.canonicalEquiv R⁰ K K')) (FractionalIdeal.mk0 K I) =
      FractionalIdeal.mk0 K' I :=
  Units.ext (FractionalIdeal.canonicalEquiv_mk0 K K' I)

noncomputable def ClassGroup.mk0 [IsDedekindDomain R] : (Ideal R)⁰ →* ClassGroup R :=
  ClassGroup.mk.comp (FractionalIdeal.mk0 (FractionRing R))

@[simp]
theorem ClassGroup.mk_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    ClassGroup.mk (FractionalIdeal.mk0 K I) = ClassGroup.mk0 I := by
  rw [ClassGroup.mk0, MonoidHom.comp_apply, ← ClassGroup.mk_canonicalEquiv K (FractionRing R),
    FractionalIdeal.map_canonicalEquiv_mk0]

@[simp]
theorem ClassGroup.equiv_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    ClassGroup.equiv K (ClassGroup.mk0 I) =
      QuotientGroup.mk' (toPrincipalIdeal R K).range (FractionalIdeal.mk0 K I) := by
  rw [ClassGroup.mk0, MonoidHom.comp_apply, ClassGroup.equiv_mk]
  congr 1
  simp [← Units.eq_iff]

theorem ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring [IsDedekindDomain R] {I J : (Ideal R)⁰} :
    ClassGroup.mk0 I =
      ClassGroup.mk0 J ↔ ∃ (x : _) (_ : x ≠ (0 : K)), spanSingleton R⁰ x * I = J := by
  refine (ClassGroup.equiv K).injective.eq_iff.symm.trans ?_
  simp only [ClassGroup.equiv_mk0, QuotientGroup.mk'_eq_mk', mem_principal_ideals_iff,
    Units.ext_iff, Units.val_mul, FractionalIdeal.coe_mk0, exists_prop]
  constructor
  · rintro ⟨X, ⟨x, hX⟩, hx⟩
    refine ⟨x, ?_, ?_⟩
    · rintro rfl; simp [X.ne_zero.symm] at hX
    simpa only [hX, mul_comm] using hx
  · rintro ⟨x, hx, eq_J⟩
    refine ⟨Units.mk0 _ (spanSingleton_ne_zero_iff.mpr hx), ⟨x, rfl⟩, ?_⟩
    simpa only [mul_comm] using eq_J

variable {K}

-- DISSOLVED: ClassGroup.mk0_eq_mk0_iff

noncomputable def ClassGroup.integralRep (I : FractionalIdeal R⁰ (FractionRing R)) :
    Ideal R := I.num

-- DISSOLVED: ClassGroup.integralRep_mem_nonZeroDivisors

-- DISSOLVED: ClassGroup.mk0_integralRep

theorem ClassGroup.mk0_surjective [IsDedekindDomain R] :
    Function.Surjective (ClassGroup.mk0 : (Ideal R)⁰ → ClassGroup R) := by
  rintro ⟨I⟩
  refine ⟨⟨ClassGroup.integralRep I.1, ClassGroup.integralRep_mem_nonZeroDivisors I.ne_zero⟩, ?_⟩
  rw [ClassGroup.mk0_integralRep, ClassGroup.Quot_mk_eq_mk]

theorem ClassGroup.mk_eq_one_iff {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk I = 1 ↔ (I : Submodule R K).IsPrincipal := by
  rw [← (ClassGroup.equiv K).injective.eq_iff]
  simp only [equiv_mk, canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl, QuotientGroup.mk'_apply,
    _root_.map_one, QuotientGroup.eq_one_iff, MonoidHom.mem_range, Units.ext_iff,
    coe_toPrincipalIdeal, coe_mapEquiv, MulEquiv.refl_apply]
  refine ⟨fun ⟨x, hx⟩ => ⟨⟨x, by rw [← hx, coe_spanSingleton]⟩⟩, ?_⟩
  intro hI
  obtain ⟨x, hx⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hI
  have hx' : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ x := by
    apply Subtype.coe_injective
    simp only [val_eq_coe, hx, coe_spanSingleton]
  refine ⟨Units.mk0 x ?_, ?_⟩
  · intro x_eq; apply Units.ne_zero I; simp [hx', x_eq]
  · simp [hx']

theorem ClassGroup.mk0_eq_one_iff [IsDedekindDomain R] {I : Ideal R} (hI : I ∈ (Ideal R)⁰) :
    ClassGroup.mk0 ⟨I, hI⟩ = 1 ↔ I.IsPrincipal :=
  ClassGroup.mk_eq_one_iff.trans (coeSubmodule_isPrincipal R _)

theorem ClassGroup.mk0_eq_mk0_inv_iff [IsDedekindDomain R] {I J : (Ideal R)⁰} :
    ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ ↔
      ∃ x ≠ (0 : R), I * J = Ideal.span {x} := by
  rw [eq_inv_iff_mul_eq_one, ← _root_.map_mul, ClassGroup.mk0_eq_one_iff,
    Submodule.isPrincipal_iff, Submonoid.coe_mul]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨a, ?_, ha⟩, fun ⟨a, _, ha⟩ ↦ ⟨a, ha⟩⟩
  by_contra!
  rw [this, Submodule.span_zero_singleton] at ha
  exact nonZeroDivisors.coe_ne_zero _ <| J.prop _ ha

noncomputable instance [IsPrincipalIdealRing R] : Fintype (ClassGroup R) where
  elems := {1}
  complete := by
    refine ClassGroup.induction (R := R) (FractionRing R) (fun I => ?_)
    rw [Finset.mem_singleton]
    exact ClassGroup.mk_eq_one_iff.mpr (I : FractionalIdeal R⁰ (FractionRing R)).isPrincipal

theorem card_classGroup_eq_one [IsPrincipalIdealRing R] : Fintype.card (ClassGroup R) = 1 := by
  rw [Fintype.card_eq_one_iff]
  use 1
  refine ClassGroup.induction (R := R) (FractionRing R) (fun I => ?_)
  exact ClassGroup.mk_eq_one_iff.mpr (I : FractionalIdeal R⁰ (FractionRing R)).isPrincipal

theorem card_classGroup_eq_one_iff [IsDedekindDomain R] [Fintype (ClassGroup R)] :
    Fintype.card (ClassGroup R) = 1 ↔ IsPrincipalIdealRing R := by
  constructor; swap; · intros; convert card_classGroup_eq_one (R := R)
  rw [Fintype.card_eq_one_iff]
  rintro ⟨I, hI⟩
  have eq_one : ∀ J : ClassGroup R, J = 1 := fun J => (hI J).trans (hI 1).symm
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; exact bot_isPrincipal
  · exact (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hI)).mp (eq_one _)
