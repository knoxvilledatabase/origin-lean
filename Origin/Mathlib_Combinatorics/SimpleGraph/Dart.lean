/-
Extracted from Combinatorics/SimpleGraph/Dart.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Darts in graphs

A `Dart` or half-edge or bond in a graph is an ordered pair of adjacent vertices, regarded as an
oriented edge. This file defines darts and proves some of their basic properties.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

structure Dart extends V × V where
  adj : G.Adj fst snd
  deriving DecidableEq

initialize_simps_projections Dart (+toProd, -fst, -snd)

attribute [simp] Dart.adj

variable {G}

theorem Dart.ext_iff (d₁ d₂ : G.Dart) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd := by
  cases d₁; cases d₂; simp
