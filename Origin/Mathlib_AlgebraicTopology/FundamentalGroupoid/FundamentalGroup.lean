/-
Extracted from AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean
Genuine: 7 of 9 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Fundamental group of a space

Given a topological space `X` and a basepoint `x`, the fundamental group is the automorphism group
of `x` i.e. the group with elements being loops based at `x` (quotiented by homotopy equivalence).
-/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ : X}

noncomputable section

open CategoryTheory

variable (X)

def FundamentalGroup (x : X) :=
  End (FundamentalGroupoid.mk x)

-- INSTANCE (free from Core): (x

-- INSTANCE (free from Core): (x

variable {X}

namespace FundamentalGroup

def fundamentalGroupMulEquivOfPath (p : Path x₀ x₁) :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  ((Groupoid.isoEquivHom ..).symm ⟦p⟧).conj

variable (x₀ x₁)

def fundamentalGroupMulEquivOfPathConnected [PathConnectedSpace X] :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x₀ x₁)

abbrev toArrow {x : X} (p : FundamentalGroup X x) :
    FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x :=
  p

abbrev toPath {x : X} (p : FundamentalGroup X x) : Path.Homotopic.Quotient x x :=
  toArrow p

abbrev fromArrow {x : X}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) :
    FundamentalGroup X x :=
  p

abbrev fromPath {x : X} (p : Path.Homotopic.Quotient x x) : FundamentalGroup X x :=
  fromArrow p
