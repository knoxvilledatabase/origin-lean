/-
Extracted from AlgebraicTopology/SimplicialSet/CompStruct.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Edges and "triangles" in simplicial sets

Given a simplicial set `X`, we introduce two types:
* Given `0`-simplices `x₀` and `x₁`, we define `Edge x₀ x₁`
  which is the type of `1`-simplices with faces `x₁` and `x₀` respectively;
* Given `0`-simplices `x₀`, `x₁`, `x₂`, edges `e₀₁ : Edge x₀ x₁`, `e₁₂ : Edge x₁ x₂`,
  `e₀₂ : Edge x₀ x₂`, a structure `CompStruct e₀₁ e₁₂ e₀₂` which records the
  data of a `2`-simplex with faces `e₁₂`, `e₀₂` and `e₀₁` respectively. This data
  will allow to obtain relations in the homotopy category of `X`.

(This API parallels similar definitions for `2`-truncated simplicial sets.
The definitions in this file are definitionally equal to their `2`-truncated
counterparts.)

-/

universe v u

open CategoryTheory Simplicial

namespace SSet

variable {X Y : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}

variable (x₀ x₁) in

def Edge := ((truncation 2).obj X).Edge x₀ x₁

namespace Edge

def ofTruncated (e : ((truncation 2).obj X).Edge x₀ x₁) :
    Edge x₀ x₁ := e

def toTruncated (e : Edge x₀ x₁) :
    ((truncation 2).obj X).Edge x₀ x₁ :=
  e

def edge (e : Edge x₀ x₁) : X _⦋1⦌ := e.toTruncated.edge
