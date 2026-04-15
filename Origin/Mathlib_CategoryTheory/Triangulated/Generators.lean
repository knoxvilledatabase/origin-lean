/-
Extracted from CategoryTheory/Triangulated/Generators.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Generators in triangulated categories

We define the notions of strong and classical generators in (pre)triangulated categories.
This is not to be confused with `ObjectProperty.IsStrongGenerator` defined in
`CategoryTheory/Generator`.

## Main definitions

- `ObjectProperty.triangEnvelopeIter P n`: The object property of all objects reachable from `P`
  by shifts, binary products, retracts and at most `n` extensions.
- `ObjectProperty.triangEnvelope P`: The triangulated envelope of `P`, i.e., the object property
  of all objects reachable from `P` by shifts, binary products, retracts and extensions. This is
  the smallest triangulated object property closed under retracts that contains `P`, see
  `ObjectProperty.triangEnvelope_le_iff`.
- `ObjectProperty.IsStrongTriangulatedGenerator P`: `P` is a strong triangulated generator if
  there exists `n` such that every object is in `P.triangEnvelopeIter n`.
- `ObjectProperty.IsClassicalTriangulatedGenerator P`: `P` is a classical triangulated generator
  if every object is in `P.triangEnvelope`.

## Main results

- `ObjectProperty.triangEnvelope_le_iff`: The universal property of `P.triangEnvelope`: it is
  the smallest triangulated object property closed under retracts that contains `P`.
- `ObjectProperty.IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator`: A strong
  triangulated generator is a classical triangulated generator.

## TODO

* Prove that if `C` has a strong generator and `P` is a classical generator, then `P` is a
  strong generator (stacks 0FXA).

## References

* [Bondal and Van den Bergh, *Generators and representability of functors in commutative and
  noncommutative geometry*][bondal_vandenbergh_2003]
* [Stacks 09SJ](https://stacks.math.columbia.edu/tag/09SJ)

-/

namespace CategoryTheory.ObjectProperty

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

abbrev triangEnvelopeIter (n : ℕ) : ObjectProperty C :=
  ((P.shiftClosure ℤ).binaryProductsClosure.retractClosure.extensionProductIter n).retractClosure
