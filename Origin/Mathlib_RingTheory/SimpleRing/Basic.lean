/-
Extracted from RingTheory/SimpleRing/Basic.lean
Genuine: 4 of 10 | Dissolved: 1 | Infrastructure: 5
-/
import Origin.Core

/-! # Basic Properties of Simple rings

A ring `R` is **simple** if it has only two two-sided ideals, namely `⊥` and `⊤`.

## Main results

- `IsSimpleRing.nontrivial`: simple rings are non-trivial.
- `DivisionRing.isSimpleRing`: division rings are simple.
- `RingHom.injective`: every ring homomorphism from a simple ring to a nontrivial ring is injective.
- `IsSimpleRing.iff_injective_ringHom`: a ring is simple iff every ring homomorphism to a nontrivial
  ring is injective.

-/

assert_not_exists Finset

variable (R : Type*) [NonUnitalNonAssocRing R]

namespace IsSimpleRing

variable {R}

-- INSTANCE (free from Core): [IsSimpleRing

lemma one_mem_of_ne_bot {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
    (hI : I ≠ ⊥) : (1 : A) ∈ I :=
  (eq_bot_or_eq_top I).resolve_left hI ▸ ⟨⟩

-- DISSOLVED: one_mem_of_ne_zero_mem

-- INSTANCE (free from Core): _root_.DivisionRing.isSimpleRing

protected theorem _root_.RingHom.injective
    {R S : Type*} [NonAssocRing R] [IsSimpleRing R] [NonAssocSemiring S] [Nontrivial S]
    (f : R →+* S) : Function.Injective f :=
  injective_ringHom_or_subsingleton_codomain f |>.resolve_right fun r => not_subsingleton _ r

universe u in

lemma iff_injective_ringHom_or_subsingleton_codomain (R : Type u) [NonAssocRing R] [Nontrivial R] :
    IsSimpleRing R ↔
    ∀ {S : Type u} [NonAssocSemiring S] (f : R →+* S), Function.Injective f ∨ Subsingleton S where
  mp _ _ _ := injective_ringHom_or_subsingleton_codomain
  mpr H := of_eq_bot_or_eq_top fun I => H I.ringCon.mk' |>.imp
    (fun h => le_antisymm
      (fun _ hx => TwoSidedIdeal.ker_eq_bot _ |>.2 h ▸ I.ker_ringCon_mk'.symm ▸ hx) bot_le)
    (fun h => le_antisymm le_top fun x _ => I.mem_iff _ |>.2 (Quotient.eq'.1 (h.elim x 0)))

universe u in

lemma iff_injective_ringHom (R : Type u) [NonAssocRing R] [Nontrivial R] :
    IsSimpleRing R ↔
    ∀ {S : Type u} [NonAssocSemiring S] [Nontrivial S] (f : R →+* S), Function.Injective f :=
  iff_injective_ringHom_or_subsingleton_codomain R |>.trans <|
    ⟨fun H _ _ _ f => H f |>.resolve_right (by simpa [not_subsingleton_iff_nontrivial]),
      fun H S _ f => subsingleton_or_nontrivial S |>.recOn Or.inr fun _ => Or.inl <| H f⟩

-- INSTANCE (free from Core): [IsSimpleRing

end IsSimpleRing
