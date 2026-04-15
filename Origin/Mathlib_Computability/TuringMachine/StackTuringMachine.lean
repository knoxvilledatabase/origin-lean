/-
Extracted from Computability/TuringMachine/StackTuringMachine.lean
Genuine: 29 of 34 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Turing machines

The files `PostTuringMachine.lean` and `StackTuringMachine.lean` define
a sequence of simple machine languages, starting with Turing machines and working
up to more complex languages based on Wang B-machines.

`PostTuringMachine.lean` covers the TM0 model and TM1 model;
`StackTuringMachine.lean` adds the TM2 model.

## Naming conventions

Each model of computation in this file shares a naming convention for the elements of a model of
computation. These are the parameters for the language:

* `Γ` is the alphabet on the tape.
* `Λ` is the set of labels, or internal machine states.
* `σ` is the type of internal memory, not on the tape. This does not exist in the TM0 model, and
  later models achieve this by mixing it into `Λ`.
* `K` is used in the TM2 model, which has multiple stacks, and denotes the number of such stacks.

All of these variables denote "essentially finite" types, but for technical reasons it is
convenient to allow them to be infinite anyway. When using an infinite type, we will be interested
in proving that only finitely many values of the type are ever interacted with.

Given these parameters, there are a few common structures for the model that arise:

* `Stmt` is the set of all actions that can be performed in one step. For the TM0 model this set is
  finite, and for later models it is an infinite inductive type representing "possible program
  texts".
* `Cfg` is the set of instantaneous configurations, that is, the state of the machine together with
  its environment.
* `Machine` is the set of all machines in the model. Usually this is approximately a function
  `Λ → Stmt`, although different models have different ways of halting and other actions.
* `step : Cfg → Option Cfg` is the function that describes how the state evolves over one step.
  If `step c = none`, then `c` is a terminal state, and the result of the computation is read off
  from `c`. Because of the type of `step`, these models are all deterministic by construction.
* `init : Input → Cfg` sets up the initial state. The type `Input` depends on the model;
  in most cases it is `List Γ`.
* `eval : Machine → Input → Part Output`, given a machine `M` and input `i`, starts from
  `init i`, runs `step` until it reaches an output, and then applies a function `Cfg → Output` to
  the final state to obtain the result. The type `Output` depends on the model.
* `Supports : Machine → Finset Λ → Prop` asserts that a machine `M` starts in `S : Finset Λ`, and
  can only ever jump to other states inside `S`. This implies that the behavior of `M` on any input
  cannot depend on its values outside `S`. We use this to allow `Λ` to be an infinite set when
  convenient, and prove that only finitely many of these states are actually accessible. This
  formalizes "essentially finite" mentioned above.
-/

assert_not_exists MonoidWithZero

open List (Vector)

open Relation

open Nat (iterate)

open Function (update iterate_succ iterate_succ_apply iterate_succ' iterate_succ_apply'

  iterate_zero_apply)

namespace Turing

/-!
## The TM2 model

The TM2 model removes the tape entirely from the TM1 model, replacing it with an arbitrary (finite)
collection of stacks, each with elements of different types (the alphabet of stack `k : K` is
`Γ k`). The statements are:

* `push k (f : σ → Γ k) q` puts `f a` on the `k`-th stack, then does `q`.
* `pop k (f : σ → Option (Γ k) → σ) q` changes the state to `f a (S k).head`, where `S k` is the
  value of the `k`-th stack, and removes this element from the stack, then does `q`.
* `peek k (f : σ → Option (Γ k) → σ) q` changes the state to `f a (S k).head`, where `S k` is the
  value of the `k`-th stack, then does `q`.
* `load (f : σ → σ) q` reads nothing but applies `f` to the internal state, then does `q`.
* `branch (f : σ → Bool) qtrue qfalse` does `qtrue` or `qfalse` according to `f a`.
* `goto (f : σ → Λ)` jumps to label `f a`.
* `halt` halts on the next step.

The configuration is a tuple `(l, var, stk)` where `l : Option Λ` is the current label to run or
`none` for the halting state, `var : σ` is the (finite) internal state, and `stk : ∀ k, List (Γ k)`
is the collection of stacks. (Note that unlike the `TM0` and `TM1` models, these are not
`ListBlank`s, they have definite ends that can be detected by the `pop` command.)

Given a designated stack `k` and a value `L : List (Γ k)`, the initial configuration has all the
stacks empty except the designated "input" stack; in `eval` this designated stack also functions
as the output stack.
-/

namespace TM2

variable {K : Type*}

variable (Γ : K → Type*)

variable (Λ : Type*)

variable (σ : Type*)

inductive Stmt
  | push : ∀ k, (σ → Γ k) → Stmt → Stmt
  | peek : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt
  | pop : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt
  | load : (σ → σ) → Stmt → Stmt
  | branch : (σ → Bool) → Stmt → Stmt → Stmt
  | goto : (σ → Λ) → Stmt
  | halt : Stmt

open Stmt

-- INSTANCE (free from Core): Stmt.inhabited

structure Cfg where
  /-- The current label to run (or `none` for the halting state) -/
  l : Option Λ
  /-- The internal state -/
  var : σ
  /-- The (finite) collection of internal stacks -/
  stk : ∀ k, List (Γ k)

-- INSTANCE (free from Core): Cfg.inhabited

variable {Γ Λ σ}

variable [DecidableEq K]

def stepAux : Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → Cfg Γ Λ σ
  | push k f q, v, S => stepAux q v (update S k (f v :: S k))
  | peek k f q, v, S => stepAux q (f v (S k).head?) S
  | pop k f q, v, S => stepAux q (f v (S k).head?) (update S k (S k).tail)
  | load a q, v, S => stepAux q (a v) S
  | branch f q₁ q₂, v, S => cond (f v) (stepAux q₁ v S) (stepAux q₂ v S)
  | goto f, v, S => ⟨some (f v), v, S⟩
  | halt, v, S => ⟨none, v, S⟩

def step (M : Λ → Stmt Γ Λ σ) : Cfg Γ Λ σ → Option (Cfg Γ Λ σ)
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, S⟩ => some (stepAux (M l) v S)

attribute [simp] stepAux.eq_1 stepAux.eq_2 stepAux.eq_3

  stepAux.eq_4 stepAux.eq_5 stepAux.eq_6 stepAux.eq_7 step.eq_1 step.eq_2

def Reaches (M : Λ → Stmt Γ Λ σ) : Cfg Γ Λ σ → Cfg Γ Λ σ → Prop :=
  ReflTransGen fun a b ↦ b ∈ step M a

end

def SupportsStmt (S : Finset Λ) : Stmt Γ Λ σ → Prop
  | push _ _ q => SupportsStmt S q
  | peek _ _ q => SupportsStmt S q
  | pop _ _ q => SupportsStmt S q
  | load _ q => SupportsStmt S q
  | branch _ q₁ q₂ => SupportsStmt S q₁ ∧ SupportsStmt S q₂
  | goto l => ∀ v, l v ∈ S
  | halt => True

open scoped Classical in

noncomputable def stmts₁ : Stmt Γ Λ σ → Finset (Stmt Γ Λ σ)
  | Q@(push _ _ q) => insert Q (stmts₁ q)
  | Q@(peek _ _ q) => insert Q (stmts₁ q)
  | Q@(pop _ _ q) => insert Q (stmts₁ q)
  | Q@(load _ q) => insert Q (stmts₁ q)
  | Q@(branch _ q₁ q₂) => insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
  | Q@(goto _) => {Q}
  | Q@halt => {Q}

theorem stmts₁_self {q : Stmt Γ Λ σ} : q ∈ stmts₁ q := by
  cases q <;> simp only [Finset.mem_insert_self, Finset.mem_singleton_self, stmts₁]

theorem stmts₁_trans {q₁ q₂ : Stmt Γ Λ σ} : q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ := by
  classical
  intro h₁₂ q₀ h₀₁
  induction q₂ with (
    simp only [stmts₁] at h₁₂ ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at h₁₂)
  | branch f q₁ q₂ IH₁ IH₂ =>
    rcases h₁₂ with (rfl | h₁₂ | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (IH₁ h₁₂))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (IH₂ h₁₂))
  | goto l => subst h₁₂; exact h₀₁
  | halt => subst h₁₂; exact h₀₁
  | load _ q IH | _ _ _ q IH =>
    rcases h₁₂ with (rfl | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.mem_insert_of_mem (IH h₁₂)

theorem stmts₁_supportsStmt_mono {S : Finset Λ} {q₁ q₂ : Stmt Γ Λ σ} (h : q₁ ∈ stmts₁ q₂)
    (hs : SupportsStmt S q₂) : SupportsStmt S q₁ := by
  induction q₂ with
    simp only [stmts₁, SupportsStmt, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      at h hs
  | branch f q₁ q₂ IH₁ IH₂ => rcases h with (rfl | h | h); exacts [hs, IH₁ h hs.1, IH₂ h hs.2]
  | goto l => subst h; exact hs
  | halt => subst h; trivial
  | load _ _ IH | _ _ _ _ IH => rcases h with (rfl | h) <;> [exact hs; exact IH h hs]

open scoped Classical in

noncomputable def stmts (M : Λ → Stmt Γ Λ σ) (S : Finset Λ) : Finset (Option (Stmt Γ Λ σ)) :=
  Finset.insertNone (S.biUnion fun q ↦ stmts₁ (M q))

theorem stmts_trans {M : Λ → Stmt Γ Λ σ} {S : Finset Λ} {q₁ q₂ : Stmt Γ Λ σ} (h₁ : q₁ ∈ stmts₁ q₂) :
    some q₂ ∈ stmts M S → some q₁ ∈ stmts M S := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h₂ ↦ ⟨_, ls, stmts₁_trans h₂ h₁⟩

end

variable [Inhabited Λ]

def Supports (M : Λ → Stmt Γ Λ σ) (S : Finset Λ) :=
  default ∈ S ∧ ∀ q ∈ S, SupportsStmt S (M q)

theorem stmts_supportsStmt {M : Λ → Stmt Γ Λ σ} {S : Finset Λ} {q : Stmt Γ Λ σ}
    (ss : Supports M S) : some q ∈ stmts M S → SupportsStmt S q := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h ↦ stmts₁_supportsStmt_mono h (ss.2 _ ls)

variable [DecidableEq K]

theorem step_supports (M : Λ → Stmt Γ Λ σ) {S : Finset Λ} (ss : Supports M S) :
    ∀ {c c' : Cfg Γ Λ σ}, c' ∈ step M c → c.l ∈ Finset.insertNone S → c'.l ∈ Finset.insertNone S
  | ⟨some l₁, v, T⟩, c', h₁, h₂ => by
    replace h₂ := ss.2 _ (Finset.some_mem_insertNone.1 h₂)
    simp only [step, Option.mem_def, Option.some.injEq] at h₁; subst c'
    revert h₂; induction M l₁ generalizing v T with intro hs
    | branch p q₁' q₂' IH₁ IH₂ =>
      unfold stepAux; cases p v
      · exact IH₂ _ _ hs.2
      · exact IH₁ _ _ hs.1
    | goto => exact Finset.some_mem_insertNone.2 (hs _)
    | halt => apply Multiset.mem_cons_self
    | load _ _ IH | _ _ _ _ IH => exact IH _ _ hs

variable [Inhabited σ]

def init (k : K) (L : List (Γ k)) : Cfg Γ Λ σ :=
  ⟨some default, default, update (fun _ ↦ []) k L⟩

def eval (M : Λ → Stmt Γ Λ σ) (k : K) (L : List (Γ k)) : Part (List (Γ k)) :=
  (StateTransition.eval (step M) (init k L)).map fun c ↦ c.stk k

end TM2

/-!
## TM2 emulator in TM1

To prove that TM2 computable functions are TM1 computable, we need to reduce each TM2 program to a
TM1 program. So suppose a TM2 program is given. This program has to maintain a whole collection of
stacks, but we have only one tape, so we must "multiplex" them all together. Pictorially, if stack
1 contains `[a, b]` and stack 2 contains `[c, d, e, f]` then the tape looks like this:

```
 bottom:  ... | _ | T | _ | _ | _ | _ | ...
 stack 1: ... | _ | b | a | _ | _ | _ | ...
 stack 2: ... | _ | f | e | d | c | _ | ...
```

where a tape element is a vertical slice through the diagram. Here the alphabet is
`Γ' := Bool × ∀ k, Option (Γ k)`, where:

* `bottom : Bool` is marked only in one place, the initial position of the TM, and represents the
  tail of all stacks. It is never modified.
* `stk k : Option (Γ k)` is the value of the `k`-th stack, if in range, otherwise `none` (which is
  the blank value). Note that the head of the stack is at the far end; this is so that push and pop
  don't have to do any shifting.

In "resting" position, the TM is sitting at the position marked `bottom`. For non-stack actions,
it operates in place, but for the stack actions `push`, `peek`, and `pop`, it must shuttle to the
end of the appropriate stack, make its changes, and then return to the bottom. So the states are:

* `normal (l : Λ)`: waiting at `bottom` to execute function `l`
* `go k (s : StAct k) (q : Stmt₂)`: travelling to the right to get to the end of stack `k` in
  order to perform stack action `s`, and later continue with executing `q`
* `ret (q : Stmt₂)`: travelling to the left after having performed a stack action, and executing
  `q` once we arrive

Because of the shuttling, emulation overhead is `O(n)`, where `n` is the current maximum of the
length of all stacks. Therefore a program that takes `k` steps to run in TM2 takes `O((m+k)k)`
steps to run when emulated in TM1, where `m` is the length of the input.
-/

namespace TM2to1

theorem stk_nth_val {K : Type*} {Γ : K → Type*} {L : ListBlank (∀ k, Option (Γ k))} {k S} (n)
    (hL : ListBlank.map (proj k) L = ListBlank.mk (List.map some S).reverse) :
    L.nth n k = S.reverse[n]? := by
  rw [← proj_map_nth, hL, ← List.map_reverse, ListBlank.nth_mk,
    List.getI_eq_getElem?_getD, List.getElem?_map]
  cases S.reverse[n]? <;> rfl

variable (K : Type*)

variable (Γ : K → Type*)

variable {Λ σ : Type*}

def Γ' :=
  Bool × ∀ k, Option (Γ k)

variable {K Γ}

-- INSTANCE (free from Core): Γ'.inhabited

-- INSTANCE (free from Core): Γ'.fintype

def addBottom (L : ListBlank (∀ k, Option (Γ k))) : ListBlank (Γ' K Γ) :=
  ListBlank.cons (true, L.head) (L.tail.map ⟨Prod.mk false, rfl⟩)

set_option backward.isDefEq.respectTransparency false in

theorem addBottom_map (L : ListBlank (∀ k, Option (Γ k))) :
    (addBottom L).map ⟨Prod.snd, by rfl⟩ = L := by
  simp only [addBottom, ListBlank.map_cons]
  convert ListBlank.cons_head_tail L
  generalize ListBlank.tail L = L'
  refine L'.induction_on fun l ↦ ?_; simp

set_option backward.isDefEq.respectTransparency false in

theorem addBottom_modifyNth (f : (∀ k, Option (Γ k)) → ∀ k, Option (Γ k))
    (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    (addBottom L).modifyNth (fun a ↦ (a.1, f a.2)) n = addBottom (L.modifyNth f n) := by
  cases n <;>
    simp only [addBottom, ListBlank.head_cons, ListBlank.modifyNth, ListBlank.tail_cons]
  congr; symm; apply ListBlank.map_modifyNth; intro; rfl

set_option backward.isDefEq.respectTransparency false in

theorem addBottom_nth_snd (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    ((addBottom L).nth n).2 = L.nth n := by
  conv => rhs; rw [← addBottom_map L, ListBlank.nth_map]

theorem addBottom_nth_succ_fst (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    ((addBottom L).nth (n + 1)).1 = false := by
  rw [ListBlank.nth_succ, addBottom, ListBlank.tail_cons, ListBlank.nth_map]

theorem addBottom_head_fst (L : ListBlank (∀ k, Option (Γ k))) : (addBottom L).head.1 = true := by
  rw [addBottom, ListBlank.head_cons]

variable (K Γ σ) in

inductive StAct (k : K)
  | push : (σ → Γ k) → StAct k
  | peek : (σ → Option (Γ k) → σ) → StAct k
  | pop : (σ → Option (Γ k) → σ) → StAct k

-- INSTANCE (free from Core): StAct.inhabited

open StAct

def stRun {k : K} : StAct K Γ σ k → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | push f => TM2.Stmt.push k f
  | peek f => TM2.Stmt.peek k f
  | pop f => TM2.Stmt.pop k f

def stVar {k : K} (v : σ) (l : List (Γ k)) : StAct K Γ σ k → σ
  | push _ => v
  | peek f => f v l.head?
  | pop f => f v l.head?

def stWrite {k : K} (v : σ) (l : List (Γ k)) : StAct K Γ σ k → List (Γ k)
  | push f => f v :: l
  | peek _ => l
  | pop _ => l.tail
