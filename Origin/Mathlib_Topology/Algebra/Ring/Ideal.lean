/-
Extracted from Topology/Algebra/Ring/Ideal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ideals and quotients of topological rings

In this file we define `Ideal.closure` to be the topological closure of an ideal in a topological
ring. We also define a `TopologicalSpace` structure on the quotient of a topological ring by an
ideal and prove that the quotient is a topological ring.
-/

open Topology

section Ring

variable {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]

protected def Ideal.closure (I : Ideal R) : Ideal R :=
  {
    AddSubmonoid.topologicalClosure
      I.toAddSubmonoid with
    carrier := closure I
    smul_mem' := fun c _ hx => map_mem_closure (mulLeft_continuous _) hx fun _ => I.mul_mem_left c }
