/-
Extracted from Data/Fin/Fin2.lean
Genuine: 18 | Conflates: 0 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic

noncomputable section

/-!
# Inductive type variant of `Fin`

`Fin` is defined as a subtype of `ℕ`. This file defines an equivalent type, `Fin2`, which is
defined inductively. This is useful for its induction principle and different definitional
equalities.

## Main declarations

* `Fin2 n`: Inductive type variant of `Fin n`. `fz` corresponds to `0` and `fs n` corresponds to
  `n`.
* `Fin2.toNat`, `Fin2.optOfNat`, `Fin2.ofNat'`: Conversions to and from `ℕ`. `ofNat' m` takes a
  proof that `m < n` through the class `Fin2.IsLT`.
* `Fin2.add k`: Takes `i : Fin2 n` to `i + k : Fin2 (n + k)`.
* `Fin2.left`: Embeds `Fin2 n` into `Fin2 (n + k)`.
* `Fin2.insertPerm a`: Permutation of `Fin2 n` which cycles `0, ..., a - 1` and leaves
  `a, ..., n - 1` unchanged.
* `Fin2.remapLeft f`: Function `Fin2 (m + k) → Fin2 (n + k)` by applying `f : Fin m → Fin n` to
  `0, ..., m - 1` and sending `m + i` to `n + i`.
-/

open Nat

universe u

inductive Fin2 : ℕ → Type
  /-- `0` as a member of `Fin (n + 1)` (`Fin 0` is empty) -/
  | fz {n} : Fin2 (n + 1)
  /-- `n` as a member of `Fin (n + 1)` -/
  | fs {n} : Fin2 n → Fin2 (n + 1)

namespace Fin2

@[elab_as_elim]
protected def cases' {n} {C : Fin2 (succ n) → Sort u} (H1 : C fz) (H2 : ∀ n, C (fs n)) :
    ∀ i : Fin2 (succ n), C i
  | fz => H1
  | fs n => H2 n

def elim0 {C : Fin2 0 → Sort u} : ∀ i : Fin2 0, C i := nofun

def toNat : ∀ {n}, Fin2 n → ℕ
  | _, @fz _ => 0
  | _, @fs _ i => succ (toNat i)

def optOfNat : ∀ {n}, ℕ → Option (Fin2 n)
  | 0, _ => none
  | succ _, 0 => some fz
  | succ m, succ k => fs <$> @optOfNat m k

def add {n} (i : Fin2 n) : ∀ k, Fin2 (n + k)
  | 0 => i
  | succ k => fs (add i k)

def left (k) : ∀ {n}, Fin2 n → Fin2 (k + n)
  | _, @fz _ => fz
  | _, @fs _ i => fs (left k i)

def insertPerm : ∀ {n}, Fin2 n → Fin2 n → Fin2 n
  | _, @fz _, @fz _ => fz
  | _, @fz _, @fs _ j => fs j
  | _, @fs (succ _) _, @fz _ => fs fz
  | _, @fs (succ _) i, @fs _ j =>
    match insertPerm i j with
    | fz => fz
    | fs k => fs (fs k)

def remapLeft {m n} (f : Fin2 m → Fin2 n) : ∀ k, Fin2 (m + k) → Fin2 (n + k)
  | 0, i => f i
  | _k + 1, @fz _ => fz
  | _k + 1, @fs _ i => fs (remapLeft f _ i)

class IsLT (m n : ℕ) : Prop where
  /-- The unique field of `Fin2.IsLT`, a proof that `m < n`. -/
  h : m < n

instance IsLT.zero (n) : IsLT 0 (succ n) :=
  ⟨succ_pos _⟩

instance IsLT.succ (m n) [l : IsLT m n] : IsLT (succ m) (succ n) :=
  ⟨succ_lt_succ l.h⟩

def ofNat' : ∀ {n} (m) [IsLT m n], Fin2 n
  | 0, _, h => absurd h.h (Nat.not_lt_zero _)
  | succ _, 0, _ => fz
  | succ n, succ m, h => fs (@ofNat' n m ⟨lt_of_succ_lt_succ h.h⟩)

def castSucc {n} : Fin2 n → Fin2 (n + 1)
  | fz   => fz
  | fs k => fs <| castSucc k

def last : {n : Nat} → Fin2 (n+1)
  | 0   => fz
  | n+1 => fs (@last n)

def rev {n : Nat} : Fin2 n → Fin2 n
  | .fz   => last
  | .fs i => i.rev.castSucc

@[simp] lemma rev_last {n} : rev (@last n) = fz := by
  induction n <;> simp_all [rev, castSucc, last]

@[simp] lemma rev_castSucc {n} (i : Fin2 n) : rev (castSucc i) = fs (rev i) := by
  induction i <;> simp_all [rev, castSucc, last]

@[simp] lemma rev_rev {n} (i : Fin2 n) : i.rev.rev = i := by
  induction i <;> simp_all [rev]

theorem rev_involutive {n} : Function.Involutive (@rev n) := rev_rev

@[inherit_doc] local prefix:arg "&" => ofNat'

instance : Inhabited (Fin2 1) :=
  ⟨fz⟩

instance instFintype : ∀ n, Fintype (Fin2 n)
  | 0   => ⟨∅, Fin2.elim0⟩
  | n+1 =>
    let ⟨elems, compl⟩ := instFintype n
    { elems    := elems.map ⟨Fin2.fs, @fs.inj _⟩ |>.cons .fz (by simp)
      complete := by rintro (_|i) <;> simp [compl] }

end Fin2
