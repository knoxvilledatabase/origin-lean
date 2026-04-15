/-
Extracted from Combinatorics/Matroid/Map.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Maps between matroids

This file defines maps and comaps, which move a matroid on one type to a matroid on another
using a function between the types. The constructions are (up to isomorphism)
just combinations of restrictions and parallel extensions, so are not mathematically difficult.

Because a matroid `M : Matroid α` is defined with am embedded ground set `M.E : Set α`
which contains all the structure of `M`, there are several types of map and comap
one could reasonably ask for;
for instance, we could map `M : Matroid α` to a `Matroid β` using either
a function `f : α → β`, a function `f : ↑M.E → β` or indeed a function `f : ↑M.E → ↑E`
for some `E : Set β`. We attempt to give definitions that capture most reasonable use cases.

`Matroid.map` and `Matroid.comap` are defined in terms of bare functions rather than
functions defined on subtypes, so are often easier to work in practice than the subtype variants.
In fact, the statement that `N = Matroid.map M f _` for some `f : α → β`
is equivalent to the existence of an isomorphism from `M` to `N`,
except in the trivial degenerate case where `M` is an empty matroid on a nonempty type and `N`
is an empty matroid on an empty type.
This can be simpler to use than an actual formal isomorphism, which requires subtypes.

## Main definitions

In the definitions below, `M` and `N` are matroids on `α` and `β` respectively.

* For `f : α → β`, `Matroid.comap N f` is the matroid on `α` with ground set `f ⁻¹' N.E`
  in which each `I` is independent if and only if `f` is injective on `I` and
  `f '' I` is independent in `N`.
  (For each nonloop `x` of `N`, the set `f ⁻¹' {x}` is a parallel class of `N.comap f`)

* `Matroid.comapOn N f E` is the restriction of `N.comap f` to `E` for some `E : Set α`.

* For an embedding `f : M.E ↪ β` defined on the subtype `↑M.E`,
  `Matroid.mapSetEmbedding M f` is the matroid on `β` with ground set `range f`
  whose independent sets are the images of those in `M`. This matroid is isomorphic to `M`.

* For a function `f : α → β` and a proof `hf` that `f` is injective on `M.E`,
  `Matroid.map f hf` is the matroid on `β` with ground set `f '' M.E`
  whose independent sets are the images of those in `M`. This matroid is isomorphic to `M`,
  and does not depend on the values `f` takes outside `M.E`.

* `Matroid.mapEmbedding f` is a version of `Matroid.map` where `f : α ↪ β` is a bundled embedding.
  It is defined separately because the global injectivity of `f` gives some nicer `simp` lemmas.

* `Matroid.mapEquiv f` is a version of `Matroid.map` where `f : α ≃ β` is a bundled equivalence.
  It is defined separately because we get even nicer `simp` lemmas.

* `Matroid.mapSetEquiv f` is a version of `Matroid.map` where `f : M.E ≃ E` is an equivalence on
  subtypes. It gives a matroid on `β` with ground set `E`.

* For `X : Set α`, `Matroid.restrictSubtype M X` is the `Matroid ↥X` with ground set
  `univ : Set ↥X`. This matroid is isomorphic to `M ↾ X`.

## Implementation details

The definition of `comap` is the only place where we need to actually define a matroid from scratch.
After `comap` is defined, we can define `map` and its variants indirectly in terms of `comap`.

If `f : α → β` is injective on `M.E`, the independent sets of `M.map f hf` are the images of
the independent set of `M`; i.e. `(M.map f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀`.
But if `f` is globally injective, we can phrase this more directly;
indeed, `(M.map f _).Indep I ↔ M.Indep (f ⁻¹' I) ∧ I ⊆ range f`.
If `f` is an equivalence we have `(M.map f _).Indep I ↔ M.Indep (f.symm '' I)`.
In order that these stronger statements can be `@[simp]`,
we define `mapEmbedding` and `mapEquiv` separately from `map`.

## Notes

For finite matroids, both maps and comaps are a special case of a construction of
Perfect [perfect1969matroid] in which a matroid structure can be transported across an arbitrary
bipartite graph that may not correspond to a function at all (See [oxley2011], Theorem 11.2.12).
It would have been nice to use this more general construction as a basis for the definition
of both `Matroid.map` and `Matroid.comap`.

Unfortunately, we can't do this, because the construction doesn't extend to infinite matroids.
Specifically, if `M₁` and `M₂` are matroids on the same type `α`,
and `f` is the natural function from `α ⊕ α` to `α`,
then the images under `f` of the independent sets of the direct sum `M₁ ⊕ M₂` are
the independent sets of a matroid if and only if the union of `M₁` and `M₂` is a matroid,
and unions do not exist for some pairs of infinite matroids: see [aignerhorev2012infinite].
For this reason, `Matroid.map` requires injectivity to be well-defined in general.

## TODO

* Bundled matroid isomorphisms.
* Maps of finite matroids across bipartite graphs.

## References

* [E. Aigner-Horev, J. Carmesin, J. Fröhlich, Infinite Matroid Union][aignerhorev2012infinite]
* [H. Perfect, Independence Spaces and Combinatorial Problems][perfect1969matroid]
* [J. Oxley, Matroid Theory][oxley2011]
-/

assert_not_exists Field

open Set Function Set.Notation

namespace Matroid

variable {α β : Type*} {f : α → β} {E I : Set α} {M : Matroid α} {N : Matroid β}

section comap

def comap (N : Matroid β) (f : α → β) : Matroid α :=
  IndepMatroid.matroid <|
  { E := f ⁻¹' N.E
    Indep := fun I ↦ N.Indep (f '' I) ∧ InjOn f I
    indep_empty := by simp
    indep_subset := fun _ _ h hIJ ↦ ⟨h.1.subset (image_mono hIJ), InjOn.mono hIJ h.2⟩
    indep_aug := by
      rintro I B ⟨hI, hIinj⟩ hImax hBmax
      obtain ⟨I', hII', hI', hI'inj⟩ := (not_maximal_subset_iff ⟨hI, hIinj⟩).1 hImax
      have h₁ : ¬(N ↾ range f).IsBase (f '' I) := by
        refine fun hB ↦ hII'.ne ?_
        have h_im := hB.eq_of_subset_indep (by simpa) (image_mono hII'.subset)
        rwa [hI'inj.image_eq_image_iff hII'.subset Subset.rfl] at h_im
      have h₂ : (N ↾ range f).IsBase (f '' B) := by
        refine Indep.isBase_of_forall_insert (by simpa using hBmax.1.1) ?_
        rintro _ ⟨⟨e, heB, rfl⟩, hfe⟩ hi
        rw [restrict_indep_iff, ← image_insert_eq] at hi
        have hinj : InjOn f (insert e B) := by
          rw [injOn_insert (fun heB ↦ hfe (mem_image_of_mem f heB))]
          exact ⟨hBmax.1.2, hfe⟩
        refine hBmax.not_prop_of_ssuperset (t := insert e B) (ssubset_insert ?_) ⟨hi.1, hinj⟩
        exact fun heB ↦ hfe <| mem_image_of_mem f heB
      obtain ⟨_, ⟨⟨e, he, rfl⟩, he'⟩, hei⟩ := Indep.exists_insert_of_not_isBase (by simpa) h₁ h₂
      have heI : e ∉ I := fun heI ↦ he' (mem_image_of_mem f heI)
      rw [← image_insert_eq, restrict_indep_iff] at hei
      exact ⟨e, ⟨he, heI⟩, hei.1, (injOn_insert heI).2 ⟨hIinj, he'⟩⟩

    indep_maximal := by
      rintro X - I ⟨hI, hIinj⟩ hIX
      obtain ⟨J, hJ⟩ := (N ↾ range f).existsMaximalSubsetProperty_indep (f '' X) (by simp)
        (f '' I) (by simpa) (image_mono hIX)
      simp only [restrict_indep_iff, image_subset_iff, maximal_subset_iff, and_imp,
        and_assoc] at hJ ⊢
      obtain ⟨hIJ, hJ, hJf, hJX, hJmax⟩ := hJ
      obtain ⟨J₀, hIJ₀, hJ₀X, hbj⟩ := hIinj.bijOn_image.exists_extend_of_subset hIX
        (image_mono hIJ) (image_subset_iff.2 <| preimage_mono hJX)
      obtain rfl : f '' J₀ = J := by rw [← image_preimage_eq_of_subset hJf, hbj.image_eq]
      refine ⟨J₀, hIJ₀, hJ, hbj.injOn, hJ₀X, fun K hK hKinj hKX hJ₀K ↦ ?_⟩
      rw [← hKinj.image_eq_image_iff hJ₀K Subset.rfl, hJmax hK (image_subset_range _ _)
        (image_mono hKX) (image_mono hJ₀K)]
    subset_ground := fun _ hI e heI ↦ hI.1.subset_ground ⟨e, heI, rfl⟩ }
