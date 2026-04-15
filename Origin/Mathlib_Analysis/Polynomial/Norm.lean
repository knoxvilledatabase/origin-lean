/-
Extracted from Analysis/Polynomial/Norm.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sup Norm of Polynomials

In this file we define the sup norm on `Polynomial`s based on their coefficients as well as several
basic results about this norm. We note that this is often called the _(naive) height_ of the
polynomial in the literature.

The sup norm is related to the Mahler measure of the polynomial. See
`Mathlib/Analysis/Polynomial/MahlerMeasure.lean`.

## Main definitions

- `Polynomial.supNorm p`: the sup norm of the coefficients of the polynomial, equal to the
  maximum of the norm of its coefficients (or zero for the zero polynomial)

## A Note on Naming

In the literature, the sup norm is often called the _(naive) height_ of a polynomial and the
`l^1` norm is often called the _length_ of the polynomial. Unfortunately, these terms are
extremely overloaded and Mathlib defines _height_ differently.

### TODOs

All other `l^p` norms can be defined on Polynomials as well. In the literature, the `l^1` norm is
sometimes called the polynomial's _length_. The `l^2` norm sometimes arises due to Parseval's
theorem implying that the squared `l^2` norm of a complex polynomial is the integral of the norm of
the polynomial's value on the unit circle.
-/

variable {A : Type*} [SeminormedRing A] (p : Polynomial A)

namespace Polynomial

noncomputable def supNorm : ℝ := p.gaussNorm (SeminormedRing.toRingSeminorm A) 1

lemma supNorm_def' : p.supNorm =
    if hp : p.support.Nonempty then p.support.sup' hp (norm ∘ p.coeff) else 0 := by
  split_ifs with h
  · simp only [supNorm, gaussNorm, h, ↓reduceDIte, one_pow, mul_one, Function.comp_apply]
    congr
  · simp [supNorm, gaussNorm, h]
