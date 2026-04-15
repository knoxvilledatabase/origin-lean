/-
Extracted from NumberTheory/MulChar/Basic.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Multiplicative characters of finite rings and fields

Let `R` and `R'` be commutative rings.
A *multiplicative character* of `R` with values in `R'` is a morphism of
monoids from the multiplicative monoid of `R` into that of `R'`
that sends non-units to zero.

We use the namespace `MulChar` for the definitions and results.

## Main results

We show that the multiplicative characters form a group (if `R'` is commutative);
see `MulChar.commGroup`. We also provide an equivalence with the
homomorphisms `Rˣ →* R'ˣ`; see `MulChar.equivToUnitHom`.

We define a multiplicative character to be *quadratic* if its values
are among `0`, `1` and `-1`, and we prove some properties of quadratic characters.

Finally, we show that the sum of all values of a nontrivial multiplicative
character vanishes; see `MulChar.IsNontrivial.sum_eq_zero`.

## Tags

multiplicative character
-/

open scoped Ring

/-!
### Definitions related to multiplicative characters

Even though the intended use is when domain and target of the characters
are commutative rings, we define them in the more general setting when
the domain is a commutative monoid and the target is a commutative monoid
with zero. (We need a zero in the target, since non-units are supposed
to map to zero.)

In this setting, there is an equivalence between multiplicative characters
`R → R'` and group homomorphisms `Rˣ → R'ˣ`, and the multiplicative characters
have a natural structure as a commutative group.
-/

section Defi

variable (R : Type*) [CommMonoid R]

variable (R' : Type*) [CommMonoidWithZero R']

structure MulChar extends MonoidHom R R' where
  map_nonunit' : ∀ a : R, ¬IsUnit a → toFun a = 0

-- INSTANCE (free from Core): MulChar.instFunLike

class MulCharClass (F : Type*) (R R' : outParam Type*) [CommMonoid R]
    [CommMonoidWithZero R'] [FunLike F R R'] : Prop extends MonoidHomClass F R R' where
  map_nonunit : ∀ (χ : F) {a : R} (_ : ¬IsUnit a), χ a = 0

initialize_simps_projections MulChar (toFun → apply, -toMonoidHom)

end Defi

namespace MulChar

attribute [scoped simp] MulCharClass.map_nonunit

section Group

variable {R : Type*} [CommMonoid R]

variable {R' : Type*} [CommMonoidWithZero R']

variable (R R') in
