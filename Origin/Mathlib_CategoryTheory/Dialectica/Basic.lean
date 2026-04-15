/-
Extracted from CategoryTheory/Dialectica/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dialectica category

We define the category `Dial` of the Dialectica interpretation, after [dialectica1989].

## Background

Dialectica categories are important models of linear type theory. They satisfy most of the
distinctions that linear logic was meant to introduce and many models do not satisfy, like the
independence of constants. Many linear type theories are being used at the
moment--[nLab] describes some of them: for quantum systems, for effects in programming, for linear
dependent types. In particular, dialectica categories are connected to polynomial functors, being a
slightly more sophisticated version of polynomial types, as discussed, for instance, in Moss and
von Glehn's [*Dialectica models of type theory*]. As such they are related to the polynomial
constructions being [developed][Poly] by Awodey, Riehl, and Hazratpour. For the non-dependent
version developed here several applications are known to Petri Nets, small cardinals
in Set Theory, state in imperative programming, and others, see [Dialectica Categories].

## References

* [Valeria de Paiva, The Dialectica Categories.][dialectica1989]
  ([pdf](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf))

[nLab]: https://ncatlab.org/nlab/show/linear+type+theory
[*Dialectica models of type theory*]: https://arxiv.org/abs/2105.00283
[Poly]: https://github.com/sinhp/Poly
[Dialectica Categories]: https://github.com/vcvpaiva/DialecticaCategories

-/

noncomputable section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]

variable (C) in

structure Dial where
  /-- The source object -/
  src : C
  /-- The target object -/
  tgt : C
  /-- A subobject of `src ⨯ tgt`, interpreted as a relation -/
  rel : Subobject (src ⨯ tgt)

namespace Dial

local notation "π₁" => prod.fst

local notation "π₂" => prod.snd

local notation "π(" a ", " b ")" => prod.lift a b
