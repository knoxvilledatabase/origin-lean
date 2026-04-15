/-
Extracted from CategoryTheory/Limits/Shapes/MultiequalizerPullback.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Multicoequalizers that are pushouts

In this file, we show that a multicoequalizer for
`I : MultispanIndex (.ofLinearOrder ι) C` is also
a pushout when `ι` has exactly two elements.

-/

namespace CategoryTheory.Limits.Multicofork.IsColimit

variable {C : Type*} [Category* C] {J : MultispanShape} [Unique J.L]
  {I : MultispanIndex J C} (c : Multicofork I)
  (h : {J.fst default, J.snd default} = Set.univ) (h' : J.fst default ≠ J.snd default)

namespace isPushout

variable (s : PushoutCocone (I.fst default) (I.snd default))

open Classical in

noncomputable def multicofork : Multicofork I :=
  Multicofork.ofπ _ s.pt
    (fun k ↦
      if hk : k = J.fst default then
        eqToHom (by simp [hk]) ≫ s.inl
      else
        eqToHom (by
          obtain rfl : k = J.snd default := by
            have := h.symm.le (Set.mem_univ k)
            push _ ∈ _ at this
            tauto
          rfl) ≫ s.inr)
    (by
      rw [Unique.forall_iff]
      simpa [h'.symm] using s.condition)
