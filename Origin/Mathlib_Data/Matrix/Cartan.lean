/-
Extracted from Data/Matrix/Cartan.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cartan matrices

This file defines Cartan matrices for simple Lie algebras, both the exceptional types
(E₆, E₇, E₈, F₄, G₂) and the classical infinite families (A, B, C, D).

## Main definitions

### Exceptional types
* `CartanMatrix.E₆` : The Cartan matrix of type E₆
* `CartanMatrix.E₇` : The Cartan matrix of type E₇
* `CartanMatrix.E₈` : The Cartan matrix of type E₈
* `CartanMatrix.F₄` : The Cartan matrix of type F₄
* `CartanMatrix.G₂` : The Cartan matrix of type G₂

### Classical types
* `CartanMatrix.A` : The Cartan matrix of type Aₙ₋₁ (corresponding to sl(n))
* `CartanMatrix.B` : The Cartan matrix of type Bₙ (corresponding to so(2n+1))
* `CartanMatrix.C` : The Cartan matrix of type Cₙ (corresponding to sp(2n))
* `CartanMatrix.D` : The Cartan matrix of type Dₙ (corresponding to so(2n))

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) plates I -- IX
* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*] Chapter 11

## Tags

cartan matrix, lie algebra, dynkin diagram
-/

namespace CartanMatrix

open Matrix

/-! ### Exceptional Cartan matrices -/

def E₆ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 2,  0, -1,  0,  0,  0;
      0,  2,  0, -1,  0,  0;
     -1,  0,  2, -1,  0,  0;
      0, -1, -1,  2, -1,  0;
      0,  0,  0, -1,  2, -1;
      0,  0,  0,  0, -1,  2]

def E₇ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0;
      0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0, -1,  2]

def E₈ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2]

def F₄ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 2, -1,  0,  0;
     -1,  2, -2,  0;
      0, -1,  2, -1;
      0,  0, -1,  2]

def G₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![ 2, -3;
     -1,  2]

/-! ### Classical Cartan matrices -/

def A (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1
    else 0

def B (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then
      if j.val = n - 1 then -2 else -1
    else if j.val + 1 = i.val then -1
    else 0

def C (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if i.val + 1 = j.val then -1
    else if j.val + 1 = i.val then
      if i.val = n - 1 then -2 else -1
    else 0

def D (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if i = j then 2
    else if n ≤ 2 then 0
    else if i.val + 1 = j.val ∧ j.val + 2 < n then -1
    else if j.val + 1 = i.val ∧ i.val + 2 < n then -1
    else if i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n) then -1
    else if j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n) then -1
    else 0

/-! ### Properties -/

section Properties

variable (n : ℕ)
