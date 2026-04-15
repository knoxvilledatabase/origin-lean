/-
Extracted from Order/SetIsMax.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Maximal elements of subsets

Let `S : Set J` and `m : S`. If `m` is not a maximal element of `S`,
then `↑m : J` is not maximal in `J`.

-/

universe u

namespace Set

variable {J : Type u} [Preorder J] {S : Set J} (m : S)

lemma not_isMax_coe (hm : ¬ IsMax m) :
    ¬ IsMax m.1 :=
  fun h ↦ hm (fun _ hb ↦ h hb)

lemma not_isMin_coe (hm : ¬ IsMin m) :
    ¬ IsMin m.1 :=
  fun h ↦ hm (fun _ hb ↦ h hb)

end Set
