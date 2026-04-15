/-
Extracted from Combinatorics/Matroid/Circuit.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Matroid IsCircuits

A 'Circuit' of a matroid `M` is a minimal set `C` that is dependent in `M`.
A matroid is determined by its set of circuits, and often the circuits
offer a more compact description of a matroid than the collection of independent sets or bases.
In matroids arising from graphs, circuits correspond to graphical cycles.

## Main Declarations

* `Matroid.IsCircuit M C` means that `C` is minimally dependent in `M`.
* For an `Indep`endent set `I` whose closure contains an element `e ∉ I`,
  `Matroid.fundCircuit M e I` is the unique circuit contained in `insert e I`.
* `Matroid.Indep.fundCircuit_isCircuit` states that `Matroid.fundCircuit M e I` is indeed a circuit.
* `Matroid.IsCircuit.eq_fundCircuit_of_subset` states that `Matroid.fundCircuit M e I` is the
  unique circuit contained in `insert e I`.
* `Matroid.dep_iff_superset_isCircuit` states that the dependent subsets of the ground set
  are precisely those that contain a circuit.
* `Matroid.ext_isCircuit` : a matroid is determined by its collection of circuits.
* `Matroid.IsCircuit.strong_multi_elimination` : the strong circuit elimination rule for an
  infinite collection of circuits.
* `Matroid.IsCircuit.strong_elimination` : the strong circuit elimination rule for two circuits.
* `Matroid.finitary_iff_forall_isCircuit_finite` : finitary matroids are precisely those whose
  circuits are all finite.
* `Matroid.IsCocircuit M C` means that `C` is minimally dependent in `M✶`,
  or equivalently that `M.E \ C` is a hyperplane of `M`.
* `Matroid.fundCocircuit M B e` is the unique cocircuit that intersects the base `B` precisely
  in the element `e`.
* `Matroid.IsBase.mem_fundCocircuit_iff_mem_fundCircuit` : `e` is in the fundamental circuit
  for `B` and `f` iff `f` is in the fundamental cocircuit for `B` and `e`.

## Implementation Details

Since `Matroid.fundCircuit M e I` is only sensible if `I` is independent and `e ∈ M.closure I \ I`,
to avoid hypotheses being explicitly included in the definition,
junk values need to be chosen if either hypothesis fails.
The definition is chosen so that the junk values satisfy
`M.fundCircuit e I = {e}` for `e ∈ I` or `e ∉ M.E` and
`M.fundCircuit e I = insert e I` if `e ∈ M.E \ M.closure I`.
These make the useful statement `e ∈ M.fundCircuit e I ⊆ insert e I` true unconditionally.
-/

variable {α : Type*} {M : Matroid α} {C C' I X Y R : Set α} {e f x y : α}

open Set

namespace Matroid

def IsCircuit (M : Matroid α) := Minimal M.Dep

lemma IsCircuit.dep (hC : M.IsCircuit C) : M.Dep C :=
  hC.prop

lemma IsCircuit.not_indep (hC : M.IsCircuit C) : ¬ M.Indep C :=
  hC.dep.not_indep

lemma IsCircuit.minimal (hC : M.IsCircuit C) : Minimal M.Dep C :=
  hC
