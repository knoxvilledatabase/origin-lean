/-
Extracted from Topology/Algebra/Group/AddTorsor.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topological torsors of additive groups

This file defines topological torsors of additive groups, that is, torsors where `+ᵥ` and `-ᵥ` are
continuous.
-/

open Topology

section AddTorsor

variable {V P α : Type*} [AddGroup V] [TopologicalSpace V] [AddTorsor V P] [TopologicalSpace P]

variable (P) in

class IsTopologicalAddTorsor extends ContinuousVAdd V P where
  continuous_vsub : Continuous (fun x : P × P => x.1 -ᵥ x.2)

export IsTopologicalAddTorsor (continuous_vsub)

attribute [fun_prop] continuous_vsub

variable [IsTopologicalAddTorsor P]

theorem Filter.Tendsto.vsub {l : Filter α} {f g : α → P} {x y : P} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (f -ᵥ g) l (𝓝 (x -ᵥ y)) :=
  (continuous_vsub.tendsto (x, y)).comp (hf.prodMk_nhds hg)

variable [TopologicalSpace α]
