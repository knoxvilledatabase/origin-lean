/-
Extracted from Data/Semiquot.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Semiquotients

A data type for semiquotients, which are classically equivalent to
nonempty sets, but are useful for programming; the idea is that
a semiquotient set `S` represents some (particular but unknown)
element of `S`. This can be used to model nondeterministic functions,
which return something in a range of values (represented by the
predicate `S`) but are not completely determined.
-/

structure Semiquot (α : Type*) where mk' ::
  /-- Set containing some element of `α` -/
  s : Set α
  /-- Assertion of non-emptiness via `Trunc` -/
  val : Trunc s

namespace Semiquot

variable {α : Type*} {β : Type*}

-- INSTANCE (free from Core): :

def mk {a : α} {s : Set α} (h : a ∈ s) : Semiquot α :=
  ⟨s, Trunc.mk ⟨a, h⟩⟩

theorem ext_s {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s := by
  refine ⟨congr_arg _, fun h => ?_⟩
  obtain ⟨_, v₁⟩ := q₁; obtain ⟨_, v₂⟩ := q₂; congr
  exact Subsingleton.helim (congrArg Trunc (congrArg Set.Elem h)) v₁ v₂

theorem ext {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ ∀ a, a ∈ q₁ ↔ a ∈ q₂ :=
  ext_s.trans Set.ext_iff

theorem exists_mem (q : Semiquot α) : ∃ a, a ∈ q :=
  let ⟨⟨a, h⟩, _⟩ := q.2.exists_rep
  ⟨a, h⟩

theorem eq_mk_of_mem {q : Semiquot α} {a : α} (h : a ∈ q) : q = @mk _ a q.1 h :=
  ext_s.2 rfl

theorem nonempty (q : Semiquot α) : q.s.Nonempty :=
  q.exists_mem

protected def pure (a : α) : Semiquot α :=
  mk (Set.mem_singleton a)
