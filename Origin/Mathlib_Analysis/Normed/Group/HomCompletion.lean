/-
Extracted from Analysis/Normed/Group/HomCompletion.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Completion of normed group homs

Given two (semi) normed groups `G` and `H` and a normed group hom `f : NormedAddGroupHom G H`,
we build and study a normed group hom
`f.completion : NormedAddGroupHom (completion G) (completion H)` such that the diagram

```
                   f
     G       ----------->     H

     |                        |
     |                        |
     |                        |
     V                        V

completion G -----------> completion H
            f.completion
```

commutes. The map itself comes from the general theory of completion of uniform spaces, but here
we want a normed group hom, study its operator norm and kernel.

The vertical maps in the above diagrams are also normed group homs constructed in this file.

## Main definitions and results:

* `NormedAddGroupHom.completion`: see the discussion above.
* `NormedAddCommGroup.toCompl : NormedAddGroupHom G (completion G)`: the canonical map from
  `G` to its completion, as a normed group hom
* `NormedAddGroupHom.completion_toCompl`: the above diagram indeed commutes.
* `NormedAddGroupHom.norm_completion`: `‖f.completion‖ = ‖f‖`
* `NormedAddGroupHom.ker_le_ker_completion`: the kernel of `f.completion` contains the image of
  the kernel of `f`.
* `NormedAddGroupHom.ker_completion`: the kernel of `f.completion` is the closure of the image of
  the kernel of `f` under an assumption that `f` is quantitatively surjective onto its image.
* `NormedAddGroupHom.extension` : if `H` is complete, the extension of
  `f : NormedAddGroupHom G H` to a `NormedAddGroupHom (completion G) H`.
-/

noncomputable section

open Set NormedAddGroupHom UniformSpace

section Completion

variable {G : Type*} [SeminormedAddCommGroup G] {H : Type*} [SeminormedAddCommGroup H]
  {K : Type*} [SeminormedAddCommGroup K]

def NormedAddGroupHom.completion (f : NormedAddGroupHom G H) :
    NormedAddGroupHom (Completion G) (Completion H) :=
  .ofLipschitz (f.toAddMonoidHom.completion f.continuous) f.lipschitz.completion_map
