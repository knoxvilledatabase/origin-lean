/-
Extracted from Topology/Category/Compactum.lean
Genuine: 7 of 13 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!

# Compacta and Compact Hausdorff Spaces

Recall that, given a monad `M` on `Type*`, an *algebra* for `M` consists of the following data:
- A type `X : Type*`
- A "structure" map `M X → X`.

This data must also satisfy a distributivity and unit axiom, and algebras for `M` form a category
in an evident way.

See the file `Mathlib/CategoryTheory/Monad/Algebra.lean` for a general version, as well as the
following link.
https://ncatlab.org/nlab/show/monad

This file proves the equivalence between the category of *compact Hausdorff topological spaces*
and the category of algebras for the *ultrafilter monad*.

## Notation:

Here are the main objects introduced in this file.
- `Compactum` is the type of compacta, which we define as algebras for the ultrafilter monad.
- `compactumToCompHaus` is the functor `Compactum ⥤ CompHaus`. Here `CompHaus` is the usual
  category of compact Hausdorff spaces.
- `compactumToCompHaus.isEquivalence` is a term of type `IsEquivalence compactumToCompHaus`.

The proof of this equivalence is a bit technical. But the idea is quite simply that the structure
map `Ultrafilter X → X` for an algebra `X` of the ultrafilter monad should be considered as the map
sending an ultrafilter to its limit in `X`. The topology on `X` is then defined by mimicking the
characterization of open sets in terms of ultrafilters.

Any `X : Compactum` is endowed with a coercion to `Type*`, as well as the following instances:
- `TopologicalSpace X`.
- `CompactSpace X`.
- `T2Space X`.

Any morphism `f : X ⟶ Y` of is endowed with a coercion to a function `X → Y`, which is shown to
be continuous in `continuous_of_hom`.

The function `Compactum.ofTopologicalSpace` can be used to construct a `Compactum` from a
topological space which satisfies `CompactSpace` and `T2Space`.

We also add wrappers around structures which already exist. Here are the main ones, all in the
`Compactum` namespace:

- `forget : Compactum ⥤ Type*` is the forgetful functor, which induces a `ConcreteCategory`
  instance for `Compactum`.
- `free : Type* ⥤ Compactum` is the left adjoint to `forget`, and the adjunction is in `adj`.
- `str : Ultrafilter X → X` is the structure map for `X : Compactum`.
  The notation `X.str` is preferred.
- `join : Ultrafilter (Ultrafilter X) → Ultrafilter X` is the monadic join for `X : Compactum`.
  Again, the notation `X.join` is preferred.
- `incl : X → Ultrafilter X` is the unit for `X : Compactum`. The notation `X.incl` is preferred.

## References

- E. Manes, Algebraic Theories, Graduate Texts in Mathematics 26, Springer-Verlag, 1976.
- https://ncatlab.org/nlab/show/ultrafilter

-/

universe u

open CategoryTheory Filter Ultrafilter TopologicalSpace CategoryTheory.Limits FiniteInter

open scoped Topology

local notation "β" => ofTypeMonad Ultrafilter

def Compactum :=
  Monad.Algebra β deriving Category, Inhabited

namespace Compactum

def forget : Compactum ⥤ Type _ :=
  Monad.forget _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def free : Type _ ⥤ Compactum :=
  Monad.free _

def adj : free ⊣ forget :=
  Monad.adj _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def str (X : Compactum) : Ultrafilter X → X :=
  X.a

def join (X : Compactum) : Ultrafilter (Ultrafilter X) → Ultrafilter X :=
  (β).μ.app _

def incl (X : Compactum) : X → Ultrafilter X :=
  (β).η.app _
