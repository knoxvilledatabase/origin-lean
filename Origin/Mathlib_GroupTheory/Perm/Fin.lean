/-
Extracted from GroupTheory/Perm/Fin.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Permutations of `Fin n`
-/

assert_not_exists LinearMap

open Equiv

def Equiv.Perm.decomposeFin {n : ℕ} : Perm (Fin n.succ) ≃ Fin n.succ × Perm (Fin n) :=
  ((Equiv.permCongr <| finSuccEquiv n).trans Equiv.Perm.decomposeOption).trans
    (Equiv.prodCongr (finSuccEquiv n).symm (Equiv.refl _))
