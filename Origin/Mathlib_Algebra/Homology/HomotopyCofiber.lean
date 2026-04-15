/-
Extracted from Algebra/Homology/HomotopyCofiber.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! The homotopy cofiber of a morphism of homological complexes

In this file, we construct the homotopy cofiber of a morphism `φ : F ⟶ G`
between homological complexes in `HomologicalComplex C c`. In degree `i`,
it is isomorphic to `(F.X j) ⊞ (G.X i)` if there is a `j` such that `c.Rel i j`,
and `G.X i` otherwise. (This is also known as the mapping cone of `φ`. Under
the name `CochainComplex.mappingCone`, a specific API shall be developed
for the case of cochain complexes indexed by `ℤ`.)

When we assume `hc : ∀ j, ∃ i, c.Rel i j` (which holds in the case of chain complexes,
or cochain complexes indexed by `ℤ`), then for any homological complex `K`,
there is a bijection `HomologicalComplex.homotopyCofiber.descEquiv φ K hc`
between `homotopyCofiber φ ⟶ K` and the tuples `(α, hα)` with
`α : G ⟶ K` and `hα : Homotopy (φ ≫ α) 0`.

We shall also study the cylinder of a homological complex `K`: this is the
homotopy cofiber of the morphism  `biprod.lift (𝟙 K) (-𝟙 K) : K ⟶ K ⊞ K`.
Then, a morphism `K.cylinder ⟶ M` is determined by the data of two
morphisms `φ₀ φ₁ : K ⟶ M` and a homotopy `h : Homotopy φ₀ φ₁`,
see `cylinder.desc`. There is also a homotopy equivalence
`cylinder.homotopyEquiv K : HomotopyEquiv K.cylinder K`. From the construction of
the cylinder, we deduce the lemma `Homotopy.map_eq_of_inverts_homotopyEquivalences`
which asserts that if a functor inverts homotopy equivalences, then the images of
two homotopic maps are equal.

-/

open CategoryTheory Category Limits Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

class HasHomotopyCofiber (φ : F ⟶ G) : Prop where
  hasBinaryBiproduct (i j : ι) (hij : c.Rel i j) : HasBinaryBiproduct (F.X j) (G.X i)

-- INSTANCE (free from Core): [HasBinaryBiproducts

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

namespace homotopyCofiber

noncomputable def X (i : ι) : C :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (F.X (c.next i)) ⊞ (G.X i)
  else G.X i

noncomputable def XIsoBiprod (i j : ι) (hij : c.Rel i j) [HasBinaryBiproduct (F.X j) (G.X i)] :
    X φ i ≅ F.X j ⊞ G.X i :=
  eqToIso (by
    obtain rfl := c.next_eq' hij
    apply dif_pos hij)

noncomputable def XIso (i : ι) (hi : ¬ c.Rel i (c.next i)) :
    X φ i ≅ G.X i :=
  eqToIso (dif_neg hi)

noncomputable def sndX (i : ι) : X φ i ⟶ G.X i :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (XIsoBiprod φ _ _ hi).hom ≫ biprod.snd
  else
    (XIso φ i hi).hom

noncomputable def inrX (i : ι) : G.X i ⟶ X φ i :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    biprod.inr ≫ (XIsoBiprod φ _ _ hi).inv
  else
    (XIso φ i hi).inv
