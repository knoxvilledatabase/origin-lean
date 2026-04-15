/-
Extracted from CategoryTheory/Presentable/Type.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Presentable objects in Type

In this file, we show that if `κ : Cardinal.{u}` is a regular cardinal,
then `X : Type u` is `κ`-presentable in the category of types iff
`HasCardinalLT X κ` holds, i.e. the cardinal number of `X` is less than `κ`.

-/

universe u

open CategoryTheory Limits Opposite ConcreteCategory

namespace HasCardinalLT

variable (X : Type u) (κ : Cardinal.{u})

set_option backward.isDefEq.respectTransparency false in

variable {X κ} in

lemma isCardinalPresentable (hX : HasCardinalLT X κ) [Fact κ.IsRegular] :
    IsCardinalPresentable X κ where
  preservesColimitOfShape J _ _ :=
    ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨by
      have := isFiltered_of_isCardinalFiltered J κ
      refine Types.FilteredColimit.isColimitOf' _ _ (fun f ↦ ?_) (fun j f g h ↦ ?_)
      · dsimp at f
        choose j g hg using fun x ↦ Types.jointly_surjective_of_isColimit hc (f x)
        refine ⟨IsCardinalFiltered.max j hX,
          TypeCat.ofHom (fun x ↦ F.map (IsCardinalFiltered.toMax j hX x) (g x)), ?_⟩
        dsimp
        ext x
        dsimp at j g hg x ⊢
        rw [← hg]
        exact congr_hom (c.w (IsCardinalFiltered.toMax j hX x)).symm (g x)
      · choose k a hk using fun x ↦
          (Types.FilteredColimit.isColimit_eq_iff' hc _ _).1 (congr_hom h x)
        dsimp at f g h k a hk ⊢
        replace hk : ∀ x, F.map (a x) (f x) = F.map (a x) (g x) := by assumption
        obtain ⟨l, b, c, hl⟩ : ∃ (l : J) (c : j ⟶ l) (b : ∀ x, k x ⟶ l),
            ∀ x, a x ≫ b x = c := by
          let φ (x : X) : j ⟶ IsCardinalFiltered.max k hX :=
            a x ≫ IsCardinalFiltered.toMax k hX x
          exact ⟨IsCardinalFiltered.coeq φ hX,
            IsCardinalFiltered.toCoeq φ hX,
            fun x ↦ IsCardinalFiltered.toMax k hX x ≫ IsCardinalFiltered.coeqHom φ hX,
            fun x ↦ by simpa [φ] using IsCardinalFiltered.coeq_condition φ hX x⟩
        refine ⟨l, b, by ext x; simp [← hl x, hk]⟩⟩⟩⟩

protected abbrev Set := { A : Set X // HasCardinalLT A κ }

namespace Set

-- INSTANCE (free from Core): [Fact

-- INSTANCE (free from Core): [Fact

lemma isFiltered_of_aleph0_le (hκ : Cardinal.aleph0 ≤ κ) :
    IsFiltered (HasCardinalLT.Set X κ) where
  nonempty := ⟨⟨∅, hasCardinalLT_of_finite _ _ hκ⟩⟩
  toIsFilteredOrEmpty := by
    have : IsDirectedOrder (HasCardinalLT.Set X κ) :=
      ⟨fun A B ↦ ⟨⟨A.val ∪ B.val, hasCardinalLT_union hκ A.prop B.prop⟩,
        Set.subset_union_left, Set.subset_union_right⟩⟩
    exact isFilteredOrEmpty_of_directed_le _
