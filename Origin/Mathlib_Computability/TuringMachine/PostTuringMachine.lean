/-
Extracted from Computability/TuringMachine/PostTuringMachine.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
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

open StateTransition

namespace Turing

/-!
## The TM0 model

A TM0 Turing machine is essentially a Post-Turing machine, adapted for type theory.

A Post-Turing machine with symbol type `Γ` and label type `Λ` is a function
`Λ → Γ → Option (Λ × Stmt)`, where a `Stmt` can be either `move left`, `move right` or `write a`
for `a : Γ`. The machine works over a "tape", a doubly-infinite sequence of elements of `Γ`, and
an instantaneous configuration, `Cfg`, is a label `q : Λ` indicating the current internal state of
the machine, and a `Tape Γ` (which is essentially `ℤ →₀ Γ`). The evolution is described by the
`step` function:

* If `M q T.head = none`, then the machine halts.
* If `M q T.head = some (q', s)`, then the machine performs action `s : Stmt` and then transitions
  to state `q'`.

The initial state takes a `List Γ` and produces a `Tape Γ` where the head of the list is the head
of the tape and the rest of the list extends to the right, with the left side all blank. The final
state takes the entire right side of the tape right or equal to the current position of the
machine. (This is actually a `ListBlank Γ`, not a `List Γ`, because we don't know, at this level
of generality, where the output ends. If equality to `default : Γ` is decidable we can trim the list
to remove the infinite tail of blanks.)
-/

namespace TM0

variable (Γ : Type*)

variable (Λ : Type*)

inductive Stmt
  | move : Dir → Stmt
  | write : Γ → Stmt

-- INSTANCE (free from Core): Stmt.inhabited
