/-
Extracted from NumberTheory/DirichletCharacter/Basic.lean
Genuine: 3 of 8 | Dissolved: 1 | Infrastructure: 4
-/
import Origin.Core

/-!
# Dirichlet Characters

Let `R` be a commutative monoid with zero. A Dirichlet character `χ` of level `n` over `R` is a
multiplicative character from `ZMod n` to `R` sending non-units to 0. We then obtain some properties
of `toUnitHom χ`, the restriction of `χ` to a group homomorphism `(ZMod n)ˣ →* Rˣ`.

Main definitions:

- `DirichletCharacter`: The type representing a Dirichlet character.
- `changeLevel`: Extend the Dirichlet character χ of level `n` to level `m`, where `n` divides `m`.
- `conductor`: The conductor of a Dirichlet character.
- `IsPrimitive`: If the level is equal to the conductor.

## Tags

dirichlet character, multiplicative character
-/

/-!
### Definitions
-/

abbrev DirichletCharacter (R : Type*) [CommMonoidWithZero R] (n : ℕ) := MulChar (ZMod n) R

open MulChar

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)

namespace DirichletCharacter

/-!
### Changing levels
-/

noncomputable def changeLevel {n m : ℕ} (hm : n ∣ m) :
    DirichletCharacter R n →* DirichletCharacter R m where
  toFun ψ := MulChar.ofUnitHom (ψ.toUnitHom.comp (ZMod.unitsMap hm))
  map_one' := by ext; simp
  map_mul' ψ₁ ψ₂ := by ext; simp

lemma changeLevel_toUnitHom {m : ℕ} (hm : n ∣ m) :
    (changeLevel hm χ).toUnitHom = χ.toUnitHom.comp (ZMod.unitsMap hm) := by
  simp [changeLevel]

-- DISSOLVED: changeLevel_injective
