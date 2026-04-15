/-
Extracted from Algebra/Homology/Embedding/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Embeddings of complex shapes

Given two complex shapes `c : ComplexShape ι` and `c' : ComplexShape ι'`,
an embedding from `c` to `c'` (`e : c.Embedding c'`) consists of the data
of an injective map `f : ι → ι'` such that for all `i₁ i₂ : ι`,
`c.Rel i₁ i₂` implies `c'.Rel (e.f i₁) (e.f i₂)`.
We define a type class `e.IsRelIff` to express that this implication is an equivalence.
Other type classes `e.IsTruncLE` and `e.IsTruncGE` are introduced in order to
formalize truncation functors.

This notion first appeared in the Liquid Tensor Experiment, and was developed there
mostly by Johan Commelin, Adam Topaz and Joël Riou. It shall be used in order to
relate the categories `CochainComplex C ℕ` and `ChainComplex C ℕ` to `CochainComplex C ℤ`.
It shall also be used in the construction of the canonical t-structure on the derived
category of an abelian category (TODO).

## Description of the API

- The extension functor `e.extendFunctor C : HomologicalComplex C c ⥤ HomologicalComplex C c'`
  (extending by the zero object outside of the image of `e.f`) is defined in
  the file `Embedding.Extend`;
- assuming `e.IsRelIff`, the restriction functor
  `e.restrictionFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c`
  is defined in the file `Embedding.Restriction`;
- the stupid truncation functor
  `e.stupidTruncFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'`
  which is the composition of the two previous functors is defined in the file
  `Embedding.StupidTrunc`.
- assuming `e.IsTruncGE`, we have truncation functors
  `e.truncGE'Functor C : HomologicalComplex C c' ⥤ HomologicalComplex C c` and
  `e.truncGEFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'`
  (see the file `Embedding.TruncGE`), and a natural
  transformation `e.πTruncGENatTrans : 𝟭 _ ⟶ e.truncGEFunctor C` which is a quasi-isomorphism
  in degrees in the image of `e.f` (TODO);
- assuming `e.IsTruncLE`, we have truncation functors
  `e.truncLE'Functor C : HomologicalComplex C c' ⥤ HomologicalComplex C c` and
  `e.truncLEFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'`, and a natural
  transformation `e.ιTruncLENatTrans : e.truncGEFunctor C ⟶ 𝟭 _` which is a quasi-isomorphism
  in degrees in the image of `e.f` (TODO);

-/

assert_not_exists Nat.instAddMonoidWithOne Nat.instMulZeroClass

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

namespace ComplexShape

structure Embedding where
  /-- the map between the underlying types of indices -/
  f : ι → ι'
  injective_f : Function.Injective f
  rel {i₁ i₂ : ι} (h : c.Rel i₁ i₂) : c'.Rel (f i₁) (f i₂)

namespace Embedding

variable {c c'}

variable (e : Embedding c c')
