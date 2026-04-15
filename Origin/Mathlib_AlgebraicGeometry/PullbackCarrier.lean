/-
Extracted from AlgebraicGeometry/PullbackCarrier.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Underlying topological space of fibre product of schemes

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes. In this file we describe the underlying
topological space of `pullback f g`, i.e. the fiber product `X ×[S] Y`.

## Main results

- `AlgebraicGeometry.Scheme.Pullback.carrierEquiv`: The bijective correspondence between the points
  of `X ×[S] Y` and pairs `(z, p)` of triples `z = (x, y, s)` with `f x = s = g y` and
  prime ideals `q` of `κ(x) ⊗[κ(s)] κ(y)`.
- `AlgebraicGeometry.Scheme.Pullback.exists_preimage`: For every triple `(x, y, s)` with
  `f x = s = g y`, there exists `z : X ×[S] Y` lying above `x` and `y`.

We also give the ranges of `pullback.fst`, `pullback.snd` and `pullback.map`.

-/

open CategoryTheory Limits TopologicalSpace IsLocalRing TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Pullback

structure Triplet {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  /-- The point of `X`. -/
  x : X
  /-- The point of `Y`. -/
  y : Y
  /-- The point of `S` below `x` and `y`. -/
  s : S
  hx : f x = s
  hy : g y = s

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

namespace Triplet
