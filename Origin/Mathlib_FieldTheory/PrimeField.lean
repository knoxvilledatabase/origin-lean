/-
Extracted from FieldTheory/PrimeField.lean
Genuine: 1 of 4 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-!
# Prime fields

A prime field is a field that does not contain any nontrivial subfield. Prime fields are `ℚ` in
characteristic `0` and `ZMod p` in characteristic `p` with `p` a prime number. Any field `K`
contains a unique prime field: it is the smallest field contained in `K`.

## Results

* The fields `ℚ` and `ZMod p` are prime fields. These are stated as the instances that says that
  the corresponding `Subfield` type is a `Subsingleton`.
* `Subfield.bot_eq_of_charZero` : the smallest subfield of a field of characteristic `0` is (the
  image of) `ℚ`.
* `Subfield.bot_eq_of_zMod_algebra`: the smallest subfield of a field of characteristic `p` is (the
  image of) `ZMod p`.

-/

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (p

-- DISSOLVED: Subfield.bot_eq_of_charZero

theorem Subfield.bot_eq_of_zMod_algebra {K : Type*} (p : ℕ) [hp : Fact (Nat.Prime p)]
    [Field K] [Algebra (ZMod p) K] :
    (⊥ : Subfield K) = (algebraMap (ZMod p) K).fieldRange := by
  rw [eq_comm, eq_bot_iff, ← Subfield.map_bot (algebraMap (ZMod p) K),
    subsingleton_iff_bot_eq_top.mpr inferInstance, ← RingHom.fieldRange_eq_map]
