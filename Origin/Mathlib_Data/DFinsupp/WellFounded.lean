/-
Extracted from Data/DFinsupp/WellFounded.lean
Genuine: 9 of 22 | Dissolved: 2 | Infrastructure: 11
-/
import Origin.Core

/-!
# Well-foundedness of the lexicographic and product orders on `DFinsupp` and `Pi`

The primary results are `DFinsupp.Lex.wellFounded` and the two variants that follow it,
which essentially say that if `(· > ·)` is a well order on `ι`, `(· < ·)` is well-founded on each
`α i`, and `0` is a bottom element in `α i`, then the lexicographic `(· < ·)` is well-founded
on `Π₀ i, α i`. The proof is modelled on the proof of `WellFounded.cutExpand`.

The results are used to prove `Pi.Lex.wellFounded` and two variants, which say that if
`ι` is finite and equipped with a linear order and `(· < ·)` is well-founded on each `α i`,
then the lexicographic `(· < ·)` is well-founded on `Π i, α i`, and the same is true for
`Π₀ i, α i` (`DFinsupp.Lex.wellFounded_of_finite`), because `DFinsupp` is order-isomorphic
to `pi` when `ι` is finite.

Finally, we deduce `DFinsupp.wellFoundedLT`, `Pi.wellFoundedLT`,
`DFinsupp.wellFoundedLT_of_finite` and variants, which concern the product order
rather than the lexicographic one. An order on `ι` is not required in these results,
but we deduce them from the well-foundedness of the lexicographic order by choosing
a well order on `ι` so that the product order `(· < ·)` becomes a subrelation
of the lexicographic `(· < ·)`.

All results are provided in two forms whenever possible: a general form where the relations
can be arbitrary (not the `(· < ·)` of a preorder, or not even transitive, etc.) and a specialized
form provided as `WellFoundedLT` instances where the `(d)Finsupp/pi` type (or their `Lex`
type synonyms) carries a natural `(· < ·)`.

Notice that the definition of `DFinsupp.Lex` says that `x < y` according to `DFinsupp.Lex r s`
iff there exists a coordinate `i : ι` such that `x i < y i` according to `s i`, and at all
`r`-smaller coordinates `j` (i.e. satisfying `r j i`), `x` remains unchanged relative to `y`;
in other words, coordinates `j` such that `¬ r j i` and `j ≠ i` are exactly where changes
can happen arbitrarily. This explains the appearance of `rᶜ ⊓ (≠)` in
`dfinsupp.acc_single` and `dfinsupp.well_founded`. When `r` is trichotomous (e.g. the `(· < ·)`
of a linear order), `¬ r j i ∧ j ≠ i` implies `r i j`, so it suffices to require `r.swap`
to be well-founded.
-/

variable {ι : Type*} {α : ι → Type*}

namespace DFinsupp

open Relation Prod

section Zero

variable [∀ i, Zero (α i)] (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop)

theorem lex_fibration [∀ (i) (s : Set ι), Decidable (i ∈ s)] :
    Fibration (InvImage (GameAdd (DFinsupp.Lex r s) (DFinsupp.Lex r s)) snd) (DFinsupp.Lex r s)
      fun x => piecewise x.2.1 x.2.2 x.1 := by
  rintro ⟨p, x₁, x₂⟩ x ⟨i, hr, hs⟩
  simp_rw [piecewise_apply] at hs hr
  split_ifs at hs with hp
  · refine ⟨⟨{ j | r j i → j ∈ p }, piecewise x₁ x { j | r j i }, x₂⟩,
      .fst ⟨i, fun j hj ↦ ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_setOf_eq]
    · simp only [if_pos hj]
    · split_ifs with hi
      · rwa [hr i hi, if_pos hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_setOf_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₂, if_pos (h₁ h₂)]
      · rw [Classical.not_imp] at h₁
        rw [hr j h₁.1, if_neg h₁.2]
  · refine ⟨⟨{ j | r j i ∧ j ∈ p }, x₁, piecewise x₂ x { j | r j i }⟩,
      .snd ⟨i, fun j hj ↦ ?_, ?_⟩, ?_⟩ <;> simp only [piecewise_apply, Set.mem_setOf_eq]
    · exact if_pos hj
    · split_ifs with hi
      · rwa [hr i hi, if_neg hp] at hs
      · assumption
    · ext1 j
      simp only [piecewise_apply, Set.mem_setOf_eq]
      split_ifs with h₁ h₂ <;> try rfl
      · rw [hr j h₁.1, if_pos h₁.2]
      · rw [hr j h₂, if_neg]
        simpa [h₂] using h₁

variable {r s}

theorem Lex.acc_of_single_erase [DecidableEq ι] {x : Π₀ i, α i} (i : ι)
    (hs : Acc (DFinsupp.Lex r s) <| single i (x i)) (hu : Acc (DFinsupp.Lex r s) <| x.erase i) :
    Acc (DFinsupp.Lex r s) x := by
  classical
    convert ← @Acc.of_fibration _ _ _ _ _ (lex_fibration r s) ⟨{i}, _⟩
      (InvImage.accessible snd <| hs.prod_gameAdd hu)
    convert piecewise_single_erase x i

theorem Lex.acc_zero (hbot : ∀ ⦃i a⦄, ¬s i a 0) : Acc (DFinsupp.Lex r s) 0 :=
  Acc.intro 0 fun _ ⟨_, _, h⟩ => (hbot h).elim

-- DISSOLVED: Lex.acc_of_single

theorem Lex.acc_single (hbot : ∀ ⦃i a⦄, ¬s i a 0) (hs : ∀ i, WellFounded (s i))
    [DecidableEq ι] {i : ι} (hi : Acc (rᶜ ⊓ (· ≠ ·)) i) :
    ∀ a, Acc (DFinsupp.Lex r s) (single i a) := by
  induction hi with | _ i _ ih
  refine fun a => WellFounded.induction (hs i)
    (C := fun x ↦ Acc (DFinsupp.Lex r s) (single i x)) a fun a ha ↦ ?_
  refine Acc.intro _ fun x ↦ ?_
  rintro ⟨k, hr, hs⟩
  rw [single_apply] at hs
  split_ifs at hs with hik
  swap
  · exact (hbot hs).elim
  subst hik
  classical
    refine Lex.acc_of_single hbot x fun j hj ↦ ?_
    obtain rfl | hij := eq_or_ne j i
    · exact ha _ hs
    by_cases h : r j i
    · rw [hr j h, single_eq_of_ne hij, single_zero]
      exact Lex.acc_zero hbot
    · exact ih _ ⟨h, hij⟩ _

-- DISSOLVED: Lex.acc

theorem Lex.wellFounded (hbot : ∀ ⦃i a⦄, ¬s i a 0) (hs : ∀ i, WellFounded (s i))
    (hr : WellFounded <| rᶜ ⊓ (· ≠ ·)) : WellFounded (DFinsupp.Lex r s) :=
  ⟨fun x => by classical exact Lex.acc hbot hs x fun i _ => hr.apply i⟩

theorem Lex.wellFounded' (hbot : ∀ ⦃i a⦄, ¬s i a 0) (hs : ∀ i, WellFounded (s i))
    [Std.Trichotomous r] (hr : WellFounded (Function.swap r)) : WellFounded (DFinsupp.Lex r s) :=
  Lex.wellFounded hbot hs <| Subrelation.wf
    (fun {i j} h ↦ Not.imp_symm (@Std.Trichotomous.trichotomous ι r _ i j h.left) h.right) hr

end Zero

-- INSTANCE (free from Core): Lex.wellFoundedLT

-- INSTANCE (free from Core): Colex.wellFoundedLT

end DFinsupp

open DFinsupp

variable (r : ι → ι → Prop) {s : ∀ i, α i → α i → Prop}

theorem Pi.Lex.wellFounded [IsStrictTotalOrder ι r] [Finite ι] (hs : ∀ i, WellFounded (s i)) :
    WellFounded (Pi.Lex r (fun {i} ↦ s i)) := by
  obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty (∀ i, α i)
  · convert emptyWf.wf
  letI : ∀ i, Zero (α i) := fun i => ⟨(hs i).min ⊤ ⟨x i, trivial⟩⟩
  haveI := IsTrans.swap r; haveI := Std.Irrefl.swap r; haveI := Fintype.ofFinite ι
  refine InvImage.wf equivFunOnFintype.symm (Lex.wellFounded' (fun i a => ?_) hs ?_)
  exacts [(hs i).not_lt_min ⊤ trivial, Finite.wellFounded_of_trans_of_irrefl (Function.swap r)]

-- INSTANCE (free from Core): Pi.Lex.wellFoundedLT

-- INSTANCE (free from Core): Pi.Colex.wellFoundedLT

-- INSTANCE (free from Core): Function.Lex.wellFoundedLT

theorem DFinsupp.Lex.wellFounded_of_finite [IsStrictTotalOrder ι r] [Finite ι] [∀ i, Zero (α i)]
    (hs : ∀ i, WellFounded (s i)) : WellFounded (DFinsupp.Lex r s) :=
  have := Fintype.ofFinite ι
  InvImage.wf equivFunOnFintype (Pi.Lex.wellFounded r hs)

-- INSTANCE (free from Core): DFinsupp.Lex.wellFoundedLT_of_finite

-- INSTANCE (free from Core): DFinsupp.Colex.wellFoundedLT_of_finite

protected theorem DFinsupp.wellFoundedLT [∀ i, Zero (α i)] [∀ i, Preorder (α i)]
    [∀ i, WellFoundedLT (α i)] (hbot : ∀ ⦃i⦄ ⦃a : α i⦄, ¬a < 0) : WellFoundedLT (Π₀ i, α i) :=
  ⟨by
    set β := fun i ↦ Antisymmetrization (α i) (· ≤ ·)
    set e : (i : ι) → α i → β i := fun i ↦ toAntisymmetrization (· ≤ ·)
    let _ : ∀ i, Zero (β i) := fun i ↦ ⟨e i 0⟩
    have : WellFounded (DFinsupp.Lex (Function.swap <| @WellOrderingRel ι)
        (fun _ ↦ (· < ·) : (i : ι) → β i → β i → Prop)) := by
      have := Std.Trichotomous.swap (@WellOrderingRel ι)
      refine Lex.wellFounded' ?_ (fun i ↦ IsWellFounded.wf) ?_
      · rintro i ⟨a⟩
        apply hbot
      · simp +unfoldPartialApp only [Function.swap]
        exact IsWellFounded.wf
    refine Subrelation.wf (fun h => ?_) <| InvImage.wf (mapRange e fun _ ↦ rfl) this
    have := IsStrictOrder.swap (@WellOrderingRel ι)
    obtain ⟨i, he, hl⟩ := lex_lt_of_lt_of_preorder (Function.swap WellOrderingRel) h
    exact ⟨i, fun j hj ↦ Quot.sound (he j hj), hl⟩⟩

-- INSTANCE (free from Core): DFinsupp.wellFoundedLT'

-- INSTANCE (free from Core): Pi.wellFoundedLT

-- INSTANCE (free from Core): Function.wellFoundedLT

-- INSTANCE (free from Core): DFinsupp.wellFoundedLT_of_finite
