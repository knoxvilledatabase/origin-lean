/-
Extracted from AlgebraicGeometry/EllipticCurve/VariableChange.lean
Genuine: 31 | Conflates: 0 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Change of variables of Weierstrass curves

This file defines admissible linear change of variables of Weierstrass curves.

## Main definitions

 * `WeierstrassCurve.VariableChange`: a change of variables of Weierstrass curves.
 * `WeierstrassCurve.VariableChange.instGroup`: change of variables form a group.
 * `WeierstrassCurve.variableChange`: the Weierstrass curve induced by a change of variables.
 * `WeierstrassCurve.instMulActionVariableChange`: change of variables act on Weierstrass curves.

## Main statements

 * `WeierstrassCurve.variableChange_j`: the j-invariant of an elliptic curve is invariant under an
    admissible linear change of variables.

## References

 * [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, change of variables
-/

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow])

universe s u v w

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section VariableChange

/-! ### Variable changes -/

@[ext]
structure VariableChange (R : Type u) [CommRing R] where
  /-- The `u` coefficient of an admissible linear change of variables, which must be a unit. -/
  u : Rˣ
  /-- The `r` coefficient of an admissible linear change of variables. -/
  r : R
  /-- The `s` coefficient of an admissible linear change of variables. -/
  s : R
  /-- The `t` coefficient of an admissible linear change of variables. -/
  t : R

namespace VariableChange

variable (C C' : VariableChange R)

def id : VariableChange R :=
  ⟨1, 0, 0, 0⟩

def comp : VariableChange R where
  u := C.u * C'.u
  r := C.r * C'.u ^ 2 + C'.r
  s := C'.u * C.s + C'.s
  t := C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t

def inv : VariableChange R where
  u := C.u⁻¹
  r := -C.r * C.u⁻¹ ^ 2
  s := -C.s * C.u⁻¹
  t := (C.r * C.s - C.t) * C.u⁻¹ ^ 3

lemma id_comp (C : VariableChange R) : comp id C = C := by
  simp only [comp, id, zero_add, zero_mul, mul_zero, one_mul]

lemma comp_id (C : VariableChange R) : comp C id = C := by
  simp only [comp, id, add_zero, mul_zero, one_mul, mul_one, one_pow, Units.val_one]

lemma comp_left_inv (C : VariableChange R) : comp (inv C) C = id := by
  rw [comp, id, inv]
  ext <;> dsimp only
  · exact C.u.inv_mul
  · linear_combination -C.r * pow_mul_pow_eq_one 2 C.u.inv_mul
  · linear_combination -C.s * C.u.inv_mul
  · linear_combination (C.r * C.s - C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul
      + -C.r * C.s * pow_mul_pow_eq_one 2 C.u.inv_mul

lemma comp_assoc (C C' C'' : VariableChange R) : comp (comp C C') C'' = comp C (comp C' C'') := by
  ext <;> simp only [comp, Units.val_mul] <;> ring1

instance instGroup : Group (VariableChange R) where
  one := id
  inv := inv
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  inv_mul_cancel := comp_left_inv
  mul_assoc := comp_assoc

end VariableChange

variable (C : VariableChange R)

@[simps]
def variableChange : WeierstrassCurve R where
  a₁ := C.u⁻¹ * (W.a₁ + 2 * C.s)
  a₂ := C.u⁻¹ ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2)
  a₃ := C.u⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t)
  a₄ := C.u⁻¹ ^ 4 * (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2
    - 2 * C.s * C.t)
  a₆ := C.u⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
    - C.r * C.t * W.a₁)

lemma variableChange_id : W.variableChange VariableChange.id = W := by
  rw [VariableChange.id, variableChange, inv_one, Units.val_one]
  ext <;> (dsimp only; ring1)

lemma variableChange_comp (C C' : VariableChange R) (W : WeierstrassCurve R) :
    W.variableChange (C.comp C') = (W.variableChange C').variableChange C := by
  simp only [VariableChange.comp, variableChange]
  ext <;> simp only [mul_inv, Units.val_mul]
  · linear_combination ↑C.u⁻¹ * C.s * 2 * C'.u.inv_mul
  · linear_combination
      C.s * (-C'.s * 2 - W.a₁) * C.u⁻¹ ^ 2 * ↑C'.u⁻¹ * C'.u.inv_mul
        + (C.r * 3 - C.s ^ 2) * C.u⁻¹ ^ 2 * pow_mul_pow_eq_one 2 C'.u.inv_mul
  · linear_combination
      C.r * (C'.s * 2 + W.a₁) * C.u⁻¹ ^ 3 * ↑C'.u⁻¹ * pow_mul_pow_eq_one 2 C'.u.inv_mul
        + C.t * 2 * C.u⁻¹ ^ 3 * pow_mul_pow_eq_one 3 C'.u.inv_mul
  · linear_combination
      C.s * (-W.a₃ - C'.r * W.a₁ - C'.t * 2) * C.u⁻¹ ^ 4 * C'.u⁻¹ ^ 3 * C'.u.inv_mul
        + C.u⁻¹ ^ 4 * C'.u⁻¹ ^ 2 * (C.r * C'.r * 6 + C.r * W.a₂ * 2 - C'.s * C.r * W.a₁ * 2
          - C'.s ^ 2 * C.r * 2) * pow_mul_pow_eq_one 2 C'.u.inv_mul
        - C.u⁻¹ ^ 4 * ↑C'.u⁻¹ * (C.s * C'.s * C.r * 2 + C.s * C.r * W.a₁ + C'.s * C.t * 2
          + C.t * W.a₁) * pow_mul_pow_eq_one 3 C'.u.inv_mul
        + C.u⁻¹ ^ 4 * (C.r ^ 2 * 3 - C.s * C.t * 2) * pow_mul_pow_eq_one 4 C'.u.inv_mul
  · linear_combination
      C.r * C.u⁻¹ ^ 6 * C'.u⁻¹ ^ 4 * (C'.r * W.a₂ * 2 - C'.r * C'.s * W.a₁ + C'.r ^ 2 * 3 + W.a₄
          - C'.s * C'.t * 2 - C'.s * W.a₃ - C'.t * W.a₁) * pow_mul_pow_eq_one 2 C'.u.inv_mul
        - C.u⁻¹ ^ 6 * C'.u⁻¹ ^ 3 * C.t * (C'.r * W.a₁ + C'.t * 2 + W.a₃)
          * pow_mul_pow_eq_one 3 C'.u.inv_mul
        + C.r ^ 2 * C.u⁻¹ ^ 6 * C'.u⁻¹ ^ 2 * (C'.r * 3 + W.a₂ - C'.s * W.a₁ - C'.s ^ 2)
          * pow_mul_pow_eq_one 4 C'.u.inv_mul
        - C.r * C.t * C.u⁻¹ ^ 6 * ↑C'.u⁻¹ * (C'.s * 2 + W.a₁) * pow_mul_pow_eq_one 5 C'.u.inv_mul
        + C.u⁻¹ ^ 6 * (C.r ^ 3 - C.t ^ 2) * pow_mul_pow_eq_one 6 C'.u.inv_mul

instance instMulActionVariableChange : MulAction (VariableChange R) (WeierstrassCurve R) where
  smul := fun C W => W.variableChange C
  one_smul := variableChange_id
  mul_smul := variableChange_comp

@[simp]
lemma variableChange_b₂ : (W.variableChange C).b₂ = C.u⁻¹ ^ 2 * (W.b₂ + 12 * C.r) := by
  simp only [b₂, variableChange_a₁, variableChange_a₂]
  ring1

@[simp]
lemma variableChange_b₄ :
    (W.variableChange C).b₄ = C.u⁻¹ ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2) := by
  simp only [b₂, b₄, variableChange_a₁, variableChange_a₃, variableChange_a₄]
  ring1

@[simp]
lemma variableChange_b₆ : (W.variableChange C).b₆ =
    C.u⁻¹ ^ 6 * (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3) := by
  simp only [b₂, b₄, b₆, variableChange_a₃, variableChange_a₆]
  ring1

@[simp]
lemma variableChange_b₈ : (W.variableChange C).b₈ = C.u⁻¹ ^ 8 *
    (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄ + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4) := by
  simp only [b₂, b₄, b₆, b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1

@[simp]
lemma variableChange_c₄ : (W.variableChange C).c₄ = C.u⁻¹ ^ 4 * W.c₄ := by
  simp only [c₄, variableChange_b₂, variableChange_b₄]
  ring1

@[simp]
lemma variableChange_c₆ : (W.variableChange C).c₆ = C.u⁻¹ ^ 6 * W.c₆ := by
  simp only [c₆, variableChange_b₂, variableChange_b₄, variableChange_b₆]
  ring1

@[simp]
lemma variableChange_Δ : (W.variableChange C).Δ = C.u⁻¹ ^ 12 * W.Δ := by
  simp only [b₂, b₄, b₆, b₈, Δ, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]
  ring1

variable [W.IsElliptic]

instance : (W.variableChange C).IsElliptic := by
  rw [isElliptic_iff, variableChange_Δ]
  exact (C.u⁻¹.isUnit.pow 12).mul W.isUnit_Δ

set_option linter.docPrime false in

@[simp]
lemma variableChange_Δ' : (W.variableChange C).Δ' = C.u⁻¹ ^ 12 * W.Δ' := by
  simp_rw [Units.ext_iff, Units.val_mul, coe_Δ', variableChange_Δ, Units.val_pow_eq_pow_val]

set_option linter.docPrime false in

lemma coe_variableChange_Δ' : ((W.variableChange C).Δ' : R) = C.u⁻¹ ^ 12 * W.Δ' := by
  simp_rw [coe_Δ', variableChange_Δ]

set_option linter.docPrime false in

lemma inv_variableChange_Δ' : (W.variableChange C).Δ'⁻¹ = C.u ^ 12 * W.Δ'⁻¹ := by
  rw [variableChange_Δ', mul_inv, inv_pow, inv_inv]

set_option linter.docPrime false in

lemma coe_inv_variableChange_Δ' : (↑(W.variableChange C).Δ'⁻¹ : R) = C.u ^ 12 * W.Δ'⁻¹ := by
  rw [inv_variableChange_Δ', Units.val_mul, Units.val_pow_eq_pow_val]

@[simp]
lemma variableChange_j : (W.variableChange C).j = W.j := by
  rw [j, coe_inv_variableChange_Δ', variableChange_c₄, j, mul_pow, ← pow_mul, ← mul_assoc,
    mul_right_comm (C.u.val ^ 12), ← mul_pow, C.u.mul_inv, one_pow, one_mul]

end VariableChange

section BaseChange

/-! ### Maps and base changes of variable changes -/

variable {A : Type v} [CommRing A] (φ : R →+* A)

namespace VariableChange

variable (C : VariableChange R)

@[simps]
def map : VariableChange A :=
  ⟨Units.map φ C.u, φ C.r, φ C.s, φ C.t⟩

variable (A)

abbrev baseChange [Algebra R A] : VariableChange A :=
  C.map <| algebraMap R A

variable {A}

@[simp]
lemma map_id : C.map (RingHom.id R) = C :=
  rfl

lemma map_map {A : Type v} [CommRing A] (φ : R →+* A) {B : Type w} [CommRing B] (ψ : A →+* B) :
    (C.map φ).map ψ = C.map (ψ.comp φ) :=
  rfl

@[simp]
lemma map_baseChange {S : Type s} [CommRing S] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] {B : Type w} [CommRing B] [Algebra R B] [Algebra S B]
    [IsScalarTower R S B] (ψ : A →ₐ[S] B) : (C.baseChange A).map ψ = C.baseChange B :=
  congr_arg C.map <| ψ.comp_algebraMap_of_tower R

lemma map_injective {φ : R →+* A} (hφ : Function.Injective φ) :
    Function.Injective <| map (φ := φ) := fun _ _ h => by
  rcases mk.inj h with ⟨h, _, _, _⟩
  replace h := (Units.mk.inj h).left
  ext <;> apply_fun _ using hφ <;> assumption

private lemma id_map : (id : VariableChange R).map φ = id := by
  simp only [id, map]
  ext <;> simp only [map_one, Units.val_one, map_zero]

private lemma comp_map (C' : VariableChange R) : (C.comp C').map φ = (C.map φ).comp (C'.map φ) := by
  simp only [comp, map]
  ext <;> map_simp <;> simp only [Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

def mapHom : VariableChange R →* VariableChange A where
  toFun := map φ
  map_one' := id_map φ
  map_mul' := comp_map φ

end VariableChange

lemma map_variableChange (C : VariableChange R) :
    (W.map φ).variableChange (C.map φ) = (W.variableChange C).map φ := by
  simp only [map, variableChange, VariableChange.map]
  ext <;> map_simp <;> simp only [Units.coe_map, Units.coe_map_inv, MonoidHom.coe_coe]

end BaseChange

end WeierstrassCurve
