/-
Extracted from CategoryTheory/Sites/DenseSubsite/Basic.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Dense subsites

We define `IsCoverDense` functors into sites as functors such that there exists a covering sieve
that factors through images of the functor for each object in `D`.

## Main results

- `CategoryTheory.Functor.IsCoverDense.Types.presheafHom`: If `G : C ⥤ (D, K)` is locally-full
  and cover-dense, then given any presheaf `ℱ` and sheaf `ℱ'` on `D`,
  and a morphism `α : G ⋙ ℱ ⟶ G ⋙ ℱ'`, we may glue them together to obtain
  a morphism of presheaves `ℱ ⟶ ℱ'`.
- `CategoryTheory.Functor.IsCoverDense.sheafIso`: If `ℱ` above is a sheaf and `α` is an iso,
  then the result is also an iso.
- `CategoryTheory.Functor.IsCoverDense.iso_of_restrict_iso`: If `G : C ⥤ (D, K)` is locally-full
  and cover-dense, then given any sheaves `ℱ, ℱ'` on `D`, and a morphism `α : ℱ ⟶ ℱ'`,
  then `α` is an iso if `G ⋙ ℱ ⟶ G ⋙ ℱ'` is iso.
- `CategoryTheory.Functor.IsDenseSubsite`:
  The functor `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)` if `G` is cover-dense,
  locally fully-faithful, and `S` is a cover of `C` iff the image of `S` in `D` is a cover.
- `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`: the equivalence of
  categories `Sheaf J A ≌ Sheaf K A` when `(C, J)` is a dense subsite of `(D, K)` and
  the pushforward functor `Sheaf K A ⥤ Sheaf J A` is an equivalence, which we show
  in two situations:
  * the sites are small and `A` has suitable limits (see the file
    `Mathlib/CategoryTheory/Sites/DenseSubsite/SheafEquiv.lean`).
  * the category `A` has limits of size `w` and `G` is `1`-hypercover cover dense
    relatively to the universe `w` (see the file
    `Mathlib/CategoryTheory/Sites/DenseSubsite/OneHypercoverDense.lean`).

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

universe w v u

namespace CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

variable {L : GrothendieckTopology E}

structure Presieve.CoverByImageStructure (G : C ⥤ D) {V U : D} (f : V ⟶ U) where
  obj : C
  lift : V ⟶ G.obj obj
  map : G.obj obj ⟶ U
  fac : lift ≫ map = f := by cat_disch

attribute [nolint docBlame] Presieve.CoverByImageStructure.obj Presieve.CoverByImageStructure.lift

  Presieve.CoverByImageStructure.map Presieve.CoverByImageStructure.fac

attribute [reassoc (attr := simp)] Presieve.CoverByImageStructure.fac

def Presieve.coverByImage (G : C ⥤ D) (U : D) : Presieve U := fun _ f =>
  Nonempty (Presieve.CoverByImageStructure G f)

def Sieve.coverByImage (G : C ⥤ D) (U : D) : Sieve U :=
  ⟨Presieve.coverByImage G U, fun ⟨⟨Z, f₁, f₂, (e : _ = _)⟩⟩ g =>
    ⟨⟨Z, g ≫ f₁, f₂, show (g ≫ f₁) ≫ f₂ = g ≫ _ by rw [Category.assoc, ← e]⟩⟩⟩

theorem Presieve.in_coverByImage (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X) :
    Presieve.coverByImage G X f :=
  ⟨⟨Y, 𝟙 _, f, by simp⟩⟩

class Functor.IsCoverDense (G : C ⥤ D) (K : GrothendieckTopology D) : Prop where
  is_cover : ∀ U : D, Sieve.coverByImage G U ∈ K U

lemma Functor.is_cover_of_isCoverDense (G : C ⥤ D) (K : GrothendieckTopology D)
    [G.IsCoverDense K] (U : D) : Sieve.coverByImage G U ∈ K U := by
  apply Functor.IsCoverDense.is_cover

attribute [nolint docBlame] CategoryTheory.Functor.IsCoverDense.is_cover

open Presieve Opposite

namespace Functor

namespace IsCoverDense

variable {K}

variable {A : Type*} [Category* A] (G : C ⥤ D)

theorem ext [G.IsCoverDense K] (ℱ : Sheaf K Type*) (X : D) {s t : ℱ.obj.obj (op X)}
    (h : ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.obj.map f.op s = ℱ.obj.map f.op t) : s = t := by
  apply ((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property
    (Sieve.coverByImage G X) (G.is_cover_of_isCoverDense K X)).isSeparatedFor.ext
  rintro Y _ ⟨Z, f₁, f₂, ⟨rfl⟩⟩
  simp [h f₂]

variable {G}

theorem functorPullback_pushforward_covering [G.IsCoverDense K] [G.IsLocallyFull K] {X : C}
    (T : K (G.obj X)) : (T.val.functorPullback G).functorPushforward G ∈ K (G.obj X) := by
  refine K.transitive T.2 _ fun Y iYX hiYX ↦ ?_
  apply K.transitive (G.is_cover_of_isCoverDense _ _) _
  rintro W _ ⟨Z, iWZ, iZY, rfl⟩
  rw [Sieve.pullback_comp]; apply K.pullback_stable; clear W iWZ
  apply K.superset_covering ?_ (G.functorPushforward_imageSieve_mem _ (iZY ≫ iYX))
  rintro W _ ⟨V, iVZ, iWV, ⟨iVX, e⟩, rfl⟩
  exact ⟨_, iVX, iWV, by simpa [e] using T.1.downward_closed hiYX (G.map iVZ ≫ iZY), by simp [e]⟩
