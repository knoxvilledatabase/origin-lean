/-
Extracted from RingTheory/TotallySplit.lean
Genuine: 3 of 9 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Totally split algebras

An `R`-algebra `S` is finite (totally) split if it is isomorphic to `Fin n → R` for some `n`.
Geometrically, this corresponds to a trivial covering.

Every totally split algebra is finite étale and conversely, every finite étale covering is étale
locally totally split (TODO, @chrisflav).
-/

open TensorProduct

class Algebra.IsFiniteSplit (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  nonempty_algEquiv_fun (R S) : ∃ n : ℕ, Nonempty (S ≃ₐ[R] Fin n → R)

namespace Algebra.IsFiniteSplit

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

-- INSTANCE (free from Core): {T

-- INSTANCE (free from Core): {ι

lemma of_algEquiv {S' : Type*} [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') [IsFiniteSplit R S] :
    IsFiniteSplit R S' := by
  obtain ⟨n, ⟨f⟩⟩ := nonempty_algEquiv_fun R S
  exact ⟨n, ⟨e.symm.trans f⟩⟩

-- INSTANCE (free from Core): :

lemma of_subsingleton [Subsingleton R] : IsFiniteSplit R S := by
  have : Subsingleton S := RingHom.codomain_trivial (algebraMap R S)
  exact ⟨0, ⟨default⟩⟩

-- INSTANCE (free from Core): [IsFiniteSplit

-- INSTANCE (free from Core): [IsFiniteSplit

-- INSTANCE (free from Core): [IsFiniteSplit

end IsFiniteSplit

end Algebra
