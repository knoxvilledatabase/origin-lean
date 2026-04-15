/-
Extracted from Data/PNat/Xgcd.lean
Genuine: 20 of 22 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Euclidean algorithm for ℕ

This file sets up a version of the Euclidean algorithm that only works with natural numbers.
Given `0 < a, b`, it computes the unique `(w, x, y, z, d)` such that the following identities hold:
* `a = (w + x) d`
* `b = (y + z) d`
* `w * z = x * y + 1`
`d` is then the gcd of `a` and `b`, and `a' := a / d = w + x` and `b' := b / d = y + z` are coprime.

This story is closely related to the structure of SL₂(ℕ) (as a free monoid on two generators) and
the theory of continued fractions.

## Main declarations

* `XgcdType`: Helper type in defining the gcd. Encapsulates `(wp, x, y, zp, ap, bp)`. where `wp`
  `zp`, `ap`, `bp` are the variables getting changed through the algorithm.
* `IsSpecial`: States `wp * zp = x * y + 1`
* `IsReduced`: States `ap = a ∧ bp = b`

## Notes

See `Nat.Xgcd` for a very similar algorithm allowing values in `ℤ`.
-/

open Nat

namespace PNat

structure XgcdType where
  /-- `wp` is a variable which changes through the algorithm. -/
  wp : ℕ
  /-- `x` satisfies `a / d = w + x` at the final step. -/
  x : ℕ
  /-- `y` satisfies `b / d = z + y` at the final step. -/
  y : ℕ
  /-- `zp` is a variable which changes through the algorithm. -/
  zp : ℕ
  /-- `ap` is a variable which changes through the algorithm. -/
  ap : ℕ
  /-- `bp` is a variable which changes through the algorithm. -/
  bp : ℕ
  deriving Inhabited

namespace XgcdType

variable (u : XgcdType)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def mk' (w : ℕ+) (x : ℕ) (y : ℕ) (z : ℕ+) (a : ℕ+) (b : ℕ+) : XgcdType :=
  mk w.val.pred x y z.val.pred a.val.pred b.val.pred

def w : ℕ+ :=
  succPNat u.wp

def z : ℕ+ :=
  succPNat u.zp

def a : ℕ+ :=
  succPNat u.ap

def b : ℕ+ :=
  succPNat u.bp

def r : ℕ :=
  (u.ap + 1) % (u.bp + 1)

def q : ℕ :=
  (u.ap + 1) / (u.bp + 1)

def qp : ℕ :=
  u.q - 1

def vp : ℕ × ℕ :=
  ⟨u.wp + u.x + u.ap + u.wp * u.ap + u.x * u.bp, u.y + u.zp + u.bp + u.y * u.ap + u.zp * u.bp⟩

def v : ℕ × ℕ :=
  ⟨u.w * u.a + u.x * u.b, u.y * u.a + u.z * u.b⟩

def succ₂ (t : ℕ × ℕ) : ℕ × ℕ :=
  ⟨t.1.succ, t.2.succ⟩

theorem v_eq_succ_vp : u.v = succ₂ u.vp := by
  ext <;> dsimp [v, vp, w, z, a, b, succ₂] <;> ring_nf

def IsSpecial : Prop :=
  u.wp + u.zp + u.wp * u.zp = u.x * u.y

def IsSpecial' : Prop :=
  u.w * u.z = succPNat (u.x * u.y)

theorem isSpecial_iff : u.IsSpecial ↔ u.IsSpecial' := by
  dsimp [IsSpecial, IsSpecial']
  let ⟨wp, x, y, zp, ap, bp⟩ := u
  constructor <;> intro h <;> simp only [w, succPNat, succ_eq_add_one, z] at * <;>
    simp only [← coe_inj, mul_coe, mk_coe] at *
  · simp_all [← h]; ring
  · simp only [Nat.mul_add, Nat.add_mul, one_mul, mul_one, ← Nat.add_assoc,
      Nat.add_right_cancel_iff] at h
    rw [← h]; ring

def IsReduced : Prop :=
  u.ap = u.bp

def IsReduced' : Prop :=
  u.a = u.b

theorem isReduced_iff : u.IsReduced ↔ u.IsReduced' :=
  succPNat_inj.symm

def flip : XgcdType where
  wp := u.zp
  x := u.y
  y := u.x
  zp := u.wp
  ap := u.bp
  bp := u.ap
