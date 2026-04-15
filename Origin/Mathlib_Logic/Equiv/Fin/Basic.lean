/-
Extracted from Logic/Equiv/Fin/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equivalences for `Fin n`
-/

assert_not_exists MonoidWithZero

universe u

variable {m n : ℕ}

/-!
### Miscellaneous

This is currently not very sorted. PRs welcome!
-/

theorem Fin.preimage_apply_01_prod {α : Fin 2 → Type u} (s : Set (α 0)) (t : Set (α 1)) :
    (fun f : ∀ i, α i => (f 0, f 1)) ⁻¹' s ×ˢ t =
      Set.pi Set.univ (Fin.cons s <| Fin.cons t finZeroElim) := by
  ext f
  simp [Fin.forall_fin_two]

theorem Fin.preimage_apply_01_prod' {α : Type u} (s t : Set α) :
    (fun f : Fin 2 → α => (f 0, f 1)) ⁻¹' s ×ˢ t = Set.pi Set.univ ![s, t] :=
  @Fin.preimage_apply_01_prod (fun _ => α) s t
