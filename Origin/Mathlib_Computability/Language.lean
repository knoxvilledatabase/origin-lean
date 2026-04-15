/-
Extracted from Computability/Language.lean
Genuine: 1 of 17 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core

/-!
# Languages

This file contains the definition and operations on formal languages over an alphabet.
Note that "strings" are implemented as lists over the alphabet.

Union and concatenation define a [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
over the languages.

In addition to that, we define a reversal of a language and prove that it behaves well
with respect to other language operations.

## Notation

* `l + m`: union of languages `l` and `m`
* `l - m`: difference of languages `l` and `m`
* `l * m`: language of strings `x ++ y` such that `x ∈ l` and `y ∈ m`
* `l ^ n`: language of strings consisting of `n` members of `l` concatenated together
* `1`: language consisting of only the empty string. This is because it is the unit of the `*`
  operator.
* `l∗`: Kleene star – language of strings consisting of arbitrarily many members of `l`
  concatenated together. Note that this notation uses the Unicode asterisk operator `∗`, as opposed
  to the more common ASCII asterisk `*`.
* `lᶜ`: complement, language of strings `x` such that `x ∉ l`
* `l ⊓ m`: intersection of languages `l` and `m`

## Main definitions

* `Language α`: a set of strings over the alphabet `α`
* `l.map f`: transform a language `l` over `α` into a language over `β`
  by translating through `f : α → β`

## Main theorems

* `Language.self_eq_mul_add_iff`: Arden's lemma – if a language `l` satisfies the equation
  `l = m * l + n`, and `m` doesn't contain the empty string,
  then `l` is the language `m∗ * n`

-/

open List Set Computability

universe v

variable {α β γ : Type*}

def Language (α) :=
  Set (List α)

deriving CompleteAtomicBooleanAlgebra

namespace Language

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {l m : Language α} {a b x : List α}

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
