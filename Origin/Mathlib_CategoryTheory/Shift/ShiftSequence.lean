/-
Extracted from CategoryTheory/Shift/ShiftSequence.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! Sequences of functors from a category equipped with a shift

Let `F : C ⥤ A` be a functor from a category `C` that is equipped with a
shift by an additive monoid `M`. In this file, we define a typeclass
`F.ShiftSequence M` which includes the data of a sequence of functors
`F.shift a : C ⥤ A` for all `a : A`. For each `a : A`, we have
an isomorphism `F.isoShift a : shiftFunctor C a ⋙ F ≅ F.shift a` which
satisfies some coherence relations. This allows to state results
(e.g. the long exact sequence of a homology functor (TODO)) using
functors `F.shift a` rather than `shiftFunctor C a ⋙ F`. The reason
for this design is that we can often choose functors `F.shift a` that
have better definitional properties than `shiftFunctor C a ⋙ F`.
For example, if `C` is the derived category (TODO) of an abelian
category `A` and `F` is the homology functor in degree `0`, then
for any `n : ℤ`, we may choose `F.shift n` to be the homology functor
in degree `n`.

-/

open CategoryTheory Category ZeroObject Limits

variable {C A : Type*} [Category* C] [Category* A] (F : C ⥤ A)
  (M : Type*) [AddMonoid M] [HasShift C M]
  {G : Type*} [AddGroup G] [HasShift C G]

namespace CategoryTheory

namespace Functor

class ShiftSequence where
  /-- a sequence of functors -/
  sequence : M → C ⥤ A
  /-- `sequence 0` identifies to the given functor -/
  isoZero : sequence 0 ≅ F
  /-- compatibility isomorphism with the shift -/
  shiftIso (n a a' : M) (ha' : n + a = a') : shiftFunctor C n ⋙ sequence a ≅ sequence a'
  shiftIso_zero (a : M) : shiftIso 0 a a (zero_add a) =
    isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _
  shiftIso_add : ∀ (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a''),
    shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerRight (shiftFunctorAdd C m n) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (shiftIso n a a' ha') ≪≫ shiftIso m a' a'' ha''
