/-
Extracted from RingTheory/FractionalIdeal/Operations.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# More operations on fractional ideals

## Main definitions
* `map` is the pushforward of a fractional ideal along an algebra morphism

Let `K` be the localization of `R` at `R⁰ = R \ {0}` (i.e. the field of fractions).
* `FractionalIdeal R⁰ K` is the type of fractional ideals in the field of fractions
* `Div (FractionalIdeal R⁰ K)` instance:
  the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statement

  * `isNoetherian` states that every fractional ideal of a Noetherian integral domain is Noetherian

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

open IsLocalization Pointwise nonZeroDivisors

namespace FractionalIdeal

open Set Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]

variable [Algebra R P]

variable {P' : Type*} [CommRing P'] [Algebra R P']

variable {P'' : Type*} [CommRing P''] [Algebra R P'']

theorem _root_.IsFractional.map (g : P →ₐ[R] P') {I : Submodule R P} :
    IsFractional S I → IsFractional S (Submodule.map g.toLinearMap I)
  | ⟨a, a_nonzero, hI⟩ =>
    ⟨a, a_nonzero, fun b hb => by
      obtain ⟨b', b'_mem, hb'⟩ := Submodule.mem_map.mp hb
      rw [AlgHom.toLinearMap_apply] at hb'
      obtain ⟨x, hx⟩ := hI b' b'_mem
      use x
      rw [← g.commutes, hx, map_smul, hb']⟩

def map (g : P →ₐ[R] P') : FractionalIdeal S P → FractionalIdeal S P' := fun I =>
  ⟨Submodule.map g.toLinearMap I, I.isFractional.map g⟩
