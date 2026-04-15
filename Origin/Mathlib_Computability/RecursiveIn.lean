/-
Extracted from Computability/RecursiveIn.lean
Genuine: 24 of 24 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Oracle computability

This file defines oracle computability using partial recursive functions.

## Main definitions

* `Nat.RecursiveIn O f`: A partial function `f : ℕ →. ℕ` is partial recursive given access to
  oracles in the set `O`.
* `RecursiveIn O f`: Lifts `Nat.RecursiveIn` to partial functions between `Primcodable` types.
* `ComputableIn O f`: A total function `f : α → σ` is computable given access to oracles in `O`.

## Main results

* `Nat.Partrec.recursiveIn`: Every partial recursive function is recursive in any oracle set.
* `partrec_iff_forall_recursiveIn_singleton`: A function is partial recursive iff it is recursive
  in every singleton oracle set.
* `recursiveIn_empty_iff`: Being recursive in the empty set is equivalent to being
  partial recursive.
* `RecursiveIn.mono`: Monotonicity of `RecursiveIn` with respect to oracle sets.

## Implementation notes

The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.

## References

* [Piergiorgio Odifreddi,
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural
  Numbers*][odifreddi1989]

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

open Encodable Primrec Nat.Partrec Part

variable {α β γ σ : Type*}

namespace Nat

protected inductive RecursiveIn (O : Set (ℕ →. ℕ)) : (ℕ →. ℕ) → Prop
  | zero : Nat.RecursiveIn O fun _ => 0
  | succ : Nat.RecursiveIn O Nat.succ
  | left : Nat.RecursiveIn O fun n => (Nat.unpair n).1
  | right : Nat.RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : ∀ g ∈ O, Nat.RecursiveIn O g
  | pair {f h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun n => h n >>= f
  | prec {f h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) :
      Nat.RecursiveIn O fun a =>
        Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)

end Nat

def RecursiveIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α →. σ) : Prop :=
  Nat.RecursiveIn O fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

lemma RecursiveIn.iff_nat {f : ℕ →. ℕ} {O} : RecursiveIn O f ↔ Nat.RecursiveIn O f := by
  simp [RecursiveIn, Part.map_id']

def RecursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β →. σ) : Prop :=
  RecursiveIn O (fun p : α × β => f p.1 p.2)

def ComputableIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α → σ) : Prop :=
  RecursiveIn O (fun a => Part.some (f a))

def ComputableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β → σ) : Prop :=
  ComputableIn O (fun p : α × β => f p.1 p.2)

namespace Nat.RecursiveIn

variable {f g : ℕ →. ℕ}

theorem of_eq {O} (hf : Nat.RecursiveIn O f) (H : ∀ n, f n = g n) :
    Nat.RecursiveIn O g :=
  (funext H : f = g) ▸ hf

theorem of_eq_tot {g : ℕ → ℕ} {O} (hf : Nat.RecursiveIn O f)
    (H : ∀ n, g n ∈ f n) : Nat.RecursiveIn O g :=
  of_eq hf fun n => eq_some_iff.2 (H n)

theorem subst {O O'} {f : ℕ →. ℕ} (hf : Nat.RecursiveIn O f)
    (hO : ∀ g, g ∈ O → Nat.RecursiveIn O' g) : Nat.RecursiveIn O' f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf

theorem partrec_of_oracle {f : ℕ →. ℕ} {O}
    (hO : ∀ g ∈ O, Nat.Partrec g) (hf : Nat.RecursiveIn O f) : Nat.Partrec f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g gIn => exact hO g gIn
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

end Nat.RecursiveIn

lemma Nat.Partrec.recursiveIn {f : ℕ →. ℕ} {O} (pF : Nat.Partrec f) :
    Nat.RecursiveIn O f := by
  induction pF with
  | zero | succ | left | right => constructor
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

lemma Partrec.recursiveIn [Primcodable α] [Primcodable σ] {f : α →. σ} {O}
    (hf : Partrec f) : RecursiveIn O f :=
  Nat.Partrec.recursiveIn hf

theorem Nat.Primrec.recursiveIn {O} {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    Nat.RecursiveIn O (fun n => f n) :=
  Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec hf)

theorem Computable.computableIn [Primcodable α] [Primcodable β] {f : α → β} {O}
    (hf : Computable f) : ComputableIn O f :=
  hf.partrec.recursiveIn

theorem Primrec.computableIn [Primcodable α] [Primcodable σ]
    {f : α → σ} {O} (hf : Primrec f) : ComputableIn O f :=
  (Primrec.to_comp hf).computableIn

nonrec theorem Primrec₂.computableIn₂ [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} {O} (hf : Primrec₂ f) : ComputableIn₂ O f :=
  hf.computableIn

protected theorem ComputableIn.recursiveIn [Primcodable α] [Primcodable σ]
    {f : α → σ} {O} (hf : ComputableIn O f) :
    RecursiveIn O (fun a => Part.some (f a)) := hf

protected theorem ComputableIn₂.recursiveIn₂ [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} {O} (hf : ComputableIn₂ O f) :
    RecursiveIn₂ O fun a => (f a : β →. σ) := hf

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

variable {f : α →. σ} {O : Set (ℕ →. ℕ)}

namespace RecursiveIn

lemma of_eq {f g : α →. σ} (hf : RecursiveIn O f)
    (H : ∀ x, f x = g x) : RecursiveIn O g :=
  (funext H : f = g) ▸ hf

lemma of_eq_tot {f : α →. σ} {g : α → σ}
    (hf : RecursiveIn O f) (H : ∀ n, g n ∈ f n) : RecursiveIn O (g : α →. σ) :=
  of_eq hf fun n => eq_some_iff.2 (H n)

lemma oracle : ∀ g ∈ O, RecursiveIn O g := by
  intro g hg; rw [iff_nat]; exact .oracle g hg

protected theorem some : RecursiveIn O (Part.some : α →. α) :=
  Partrec.some.recursiveIn

protected theorem none : RecursiveIn O (fun _ : α => (Part.none : Part σ)) :=
  Partrec.none.recursiveIn

theorem subst {O O'} {f : α →. σ} (hf : RecursiveIn O f)
    (hO : ∀ g, g ∈ O → RecursiveIn O' g) : RecursiveIn O' f :=
  Nat.RecursiveIn.subst hf (by simpa only [RecursiveIn.iff_nat] using hO)
