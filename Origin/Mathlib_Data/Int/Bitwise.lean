/-
Extracted from Data/Int/Bitwise.lean
Genuine: 10 of 12 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Bitwise operations on integers

Possibly only of archaeological significance.

## Recursors
* `Int.bitCasesOn`: Parity disjunction. Something is true/defined on `ℤ` if it's true/defined for
  even and for odd values.
-/

namespace Int

def div2 : ℤ → ℤ
  | (n : ℕ) => n.div2
  | -[n+1] => negSucc n.div2

def bodd : ℤ → Bool
  | (n : ℕ) => n.bodd
  | -[n+1] => not (n.bodd)

def bit (b : Bool) : ℤ → ℤ :=
  cond b (2 * · + 1) (2 * ·)

def natBitwise (f : Bool → Bool → Bool) (m n : ℕ) : ℤ :=
  cond (f false false) -[Nat.bitwise (fun x y => not (f x y)) m n+1] (Nat.bitwise f m n)

def bitwise (f : Bool → Bool → Bool) : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => natBitwise f m n
  | (m : ℕ), -[n+1] => natBitwise (fun x y => f x (not y)) m n
  | -[m+1], (n : ℕ) => natBitwise (fun x y => f (not x) y) m n
  | -[m+1], -[n+1] => natBitwise (fun x y => f (not x) (not y)) m n

def lnot : ℤ → ℤ
  | (m : ℕ) => -[m+1]
  | -[m+1] => m

def lor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => m ||| n
  | (m : ℕ), -[n+1] => -[Nat.ldiff n m+1]
  | -[m+1], (n : ℕ) => -[Nat.ldiff m n+1]
  | -[m+1], -[n+1] => -[m &&& n+1]

def land : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => m &&& n
  | (m : ℕ), -[n+1] => Nat.ldiff m n
  | -[m+1], (n : ℕ) => Nat.ldiff n m
  | -[m+1], -[n+1] => -[m ||| n+1]

def ldiff : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => Nat.ldiff m n
  | (m : ℕ), -[n+1] => m &&& n
  | -[m+1], (n : ℕ) => -[m ||| n+1]
  | -[m+1], -[n+1] => Nat.ldiff n m

protected def xor : ℤ → ℤ → ℤ
  | (m : ℕ), (n : ℕ) => (m ^^^ n)
  | (m : ℕ), -[n+1] => -[(m ^^^ n)+1]
  | -[m+1], (n : ℕ) => -[(m ^^^ n)+1]
  | -[m+1], -[n+1] => (m ^^^ n)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

/-! ### bitwise ops -/
