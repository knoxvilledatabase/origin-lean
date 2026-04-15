/-
Extracted from Analysis/Normed/Module/Extr.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# (Local) maximums in a normed space

In this file we prove the following lemma, see `IsMaxFilter.norm_add_sameRay`. If `f : α → E` is
a function such that `norm ∘ f` has a maximum along a filter `l` at a point `c` and `y` is a vector
on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has a maximum along `l` at `c`.

Then we specialize it to the case `y = f c` and to different special cases of `IsMaxFilter`:
`IsMaxOn`, `IsLocalMaxOn`, and `IsLocalMax`.

## Tags

local maximum, normed space
-/

variable {α X E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

variable {f : α → E} {l : Filter α} {s : Set α} {c : α} {y : E}

theorem IsMaxFilter.norm_add_self (h : IsMaxFilter (norm ∘ f) l c) :
    IsMaxFilter (fun x => ‖f x + f c‖) l c :=
  IsMaxFilter.norm_add_sameRay h SameRay.rfl

theorem IsMaxOn.norm_add_sameRay (h : IsMaxOn (norm ∘ f) s c) (hy : SameRay ℝ (f c) y) :
    IsMaxOn (fun x => ‖f x + y‖) s c :=
  IsMaxFilter.norm_add_sameRay h hy

theorem IsMaxOn.norm_add_self (h : IsMaxOn (norm ∘ f) s c) : IsMaxOn (fun x => ‖f x + f c‖) s c :=
  IsMaxFilter.norm_add_self h

end

variable {f : X → E} {s : Set X} {c : X} {y : E}

theorem IsLocalMaxOn.norm_add_sameRay (h : IsLocalMaxOn (norm ∘ f) s c) (hy : SameRay ℝ (f c) y) :
    IsLocalMaxOn (fun x => ‖f x + y‖) s c :=
  IsMaxFilter.norm_add_sameRay h hy

theorem IsLocalMaxOn.norm_add_self (h : IsLocalMaxOn (norm ∘ f) s c) :
    IsLocalMaxOn (fun x => ‖f x + f c‖) s c :=
  IsMaxFilter.norm_add_self h

theorem IsLocalMax.norm_add_sameRay (h : IsLocalMax (norm ∘ f) c) (hy : SameRay ℝ (f c) y) :
    IsLocalMax (fun x => ‖f x + y‖) c :=
  IsMaxFilter.norm_add_sameRay h hy

theorem IsLocalMax.norm_add_self (h : IsLocalMax (norm ∘ f) c) :
    IsLocalMax (fun x => ‖f x + f c‖) c :=
  IsMaxFilter.norm_add_self h
