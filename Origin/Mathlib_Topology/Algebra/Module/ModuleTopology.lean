/-
Extracted from Topology/Algebra/Module/ModuleTopology.lean
Genuine: 10 of 15 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# A "module topology" for modules over a topological ring

If `R` is a topological ring acting on an additive abelian group `A`, we define the
*module topology* to be the finest topology on `A` making both the maps
`• : R × A → A` and `+ : A × A → A` continuous (with all the products having the
product topology). Note that `- : A → A` is also automatically continuous as it is `a ↦ (-1) • a`.

This topology was suggested by Will Sawin [here](https://mathoverflow.net/a/477763/1384).


## Mathematical details

I (buzzard) don't know of any reference for this other than Sawin's mathoverflow answer,
so I expand some of the details here.

First note that the definition makes sense in far more generality (for example `R` just needs to
be a topological space acting on an additive monoid).

Next note that there *is* a finest topology with this property! Indeed, topologies on a fixed
type form a complete lattice (infinite infs and sups exist). So if `τ` is the Inf of all
the topologies on `A` which make `+` and `•` continuous, then the claim is that `+` and `•`
are still continuous for `τ` (note that topologies are ordered so that finer topologies
are smaller). To show `+ : A × A → A` is continuous we equivalently need to show
that the pushforward of the product topology `τ × τ` along `+` is `≤ τ`, and because `τ` is
the greatest lower bound of the topologies making `•` and `+` continuous,
it suffices to show that it's `≤ σ` for any topology `σ` on `A` which makes `+` and `•` continuous.
However pushforward and products are monotone, so `τ × τ ≤ σ × σ`, and the pushforward of
`σ × σ` is `≤ σ` because that's precisely the statement that `+` is continuous for `σ`.
The proof for `•` follows mutatis mutandis.

A *topological module* for a topological ring `R` is an `R`-module `A` with a topology
making `+` and `•` continuous. The discussion so far has shown that the module topology makes
an `R`-module `A` into a topological module, and moreover is the finest topology with this property.

A crucial observation is that if `M` is a topological `R`-module, if `A` is an `R`-module with no
topology, and if `φ : A → M` is linear, then the pullback of `M`'s topology to `A` is a topology
making `A` into a topological module. Let's for example check that `•` is continuous.
If `U ⊆ A` is open then by definition of the pullback topology, `U = φ⁻¹(V)` for some open `V ⊆ M`,
and now the pullback of `U` under `•` is just the pullback along the continuous map
`id × φ : R × A → R × M` of the preimage of `V` under the continuous map `• : R × M → M`,
so it's open. The proof for `+` is similar.

As a consequence of this, we see that if `φ : A → M` is a linear map between topological `R`-modules
modules and if `A` has the module topology, then `φ` is automatically continuous.
Indeed the argument above shows that if `A → M` is linear then the module
topology on `A` is `≤` the pullback of the module topology on `M` (because it's the inf of a set
containing this topology) which is the definition of continuity.

We also deduce that the module topology is a functor from the category of `R`-modules
(`R` a topological ring) to the category of topological `R`-modules, and it is perhaps
unsurprising that this is an adjoint to the forgetful functor. Indeed, if `A` is an `R`-module
and `M` is a topological `R`-module, then the previous paragraph shows that
the linear maps `A → M` are precisely the continuous linear maps
from (`A` with its module topology) to `M`, so the module topology is a left adjoint
to the forgetful functor.

This file develops the theory of the module topology.

## Main theorems

* `IsTopologicalSemiring.toIsModuleTopology : IsModuleTopology R R`. The module
    topology on `R` is `R`'s topology.
* `IsModuleTopology.iso [IsModuleTopology R A] (e : A ≃L[R] B) : IsModuleTopology R B`. If `A` and
    `B` are `R`-modules with topologies, if `e` is a topological isomorphism between them,
    and if `A` has the module topology, then `B` has the module topology.
* `IsModuleTopology.instProd` : If `M` and `N` are `R`-modules each equipped with the module
  topology, then the product topology on `M × N` is the module topology.
* `IsModuleTopology.instPi` : Given a finite collection of `R`-modules each of which has
  the module topology, the product topology on the product module is the module topology.
* `IsModuleTopology.isTopologicalRing` : If `D` is an `R`-algebra equipped with the module
  topology, and `D` is finite as an `R`-module, then `D` is a topological ring (that is,
  addition, negation and multiplication are continuous).

Now say `φ : A →ₗ[R] B` is an `R`-linear map between `R`-modules equipped with
the module topology.

* `IsModuleTopology.continuous_of_linearMap φ` is the proof that `φ` is automatically
  continuous.
* `IsModuleTopology.isQuotientMap_of_surjective (hφ : Function.Surjective φ)`
  is the proof that if furthermore `φ` is surjective then it is a quotient map,
  that is, the module topology on `B` is the pushforward of the module topology
  on `A`.

Now say `ψ : A →ₗ[R] B →ₗ[R] C` is an `R`-bilinear map between `R`-modules equipped with
the module topology.

* `IsModuleTopology.continuous_bilinear_of_finite_left` : If `A` is finite then `A × B → C`
  is continuous.
* `IsModuleTopology.continuous_bilinear_of_finite_right` : If `B` is finite then `A × B → C`
  is continuous.

## TODO

* The module topology is a functor from the category of `R`-modules
  to the category of topological `R`-modules, and it's an adjoint to the forgetful functor.

-/

section basics

variable (R : Type*) [TopologicalSpace R] (A : Type*) [Add A] [SMul R A]

abbrev moduleTopology : TopologicalSpace A :=
  sInf {t | @ContinuousSMul R A _ _ t ∧ @ContinuousAdd A t _}

class IsModuleTopology [τA : TopologicalSpace A] : Prop where
  /-- Note that this should not be used directly, and `eq_moduleTopology`, which takes `R` and `A`
  explicitly, should be used instead. -/
  eq_moduleTopology' : τA = moduleTopology R A

theorem eq_moduleTopology [τA : TopologicalSpace A] [IsModuleTopology R A] :
    τA = moduleTopology R A :=
  IsModuleTopology.eq_moduleTopology' (R := R) (A := A)

-- INSTANCE (free from Core): (priority

theorem ModuleTopology.continuousSMul : @ContinuousSMul R A _ _ (moduleTopology R A) :=
  /- Proof: We need to prove that the product topology is finer than the pullback
     of the module topology. But the module topology is an Inf and thus a limit,
     and pullback is a right adjoint, so it preserves limits.
     We must thus show that the product topology is finer than an Inf, so it suffices
     to show it's a lower bound, which is not hard. All this is wrapped into
     `continuousSMul_sInf`.
  -/
  continuousSMul_sInf fun _ h ↦ h.1

theorem ModuleTopology.continuousAdd : @ContinuousAdd A (moduleTopology R A) _ :=
  continuousAdd_sInf fun _ h ↦ h.2

-- INSTANCE (free from Core): IsModuleTopology.toContinuousSMul

theorem IsModuleTopology.toContinuousAdd [TopologicalSpace A] [IsModuleTopology R A] :
    ContinuousAdd A := eq_moduleTopology R A ▸ ModuleTopology.continuousAdd R A

theorem moduleTopology_le [τA : TopologicalSpace A] [ContinuousSMul R A] [ContinuousAdd A] :
    moduleTopology R A ≤ τA := sInf_le ⟨inferInstance, inferInstance⟩

end basics

namespace IsModuleTopology

section basics

variable {R : Type*} [TopologicalSpace R]
  {A : Type*} [Add A] [SMul R A] [τA : TopologicalSpace A]

theorem of_continuous_id [ContinuousAdd A] [ContinuousSMul R A]
    (h : @Continuous A A τA (moduleTopology R A) id) :
    IsModuleTopology R A where
  -- The topologies are equal because each is finer than the other. One inclusion
  -- follows from the continuity hypothesis; the other is because the module topology
  -- is the inf of all the topologies making `A` a topological module.
  eq_moduleTopology' := le_antisymm (continuous_id_iff_le.1 h) (moduleTopology_le _ _)

-- INSTANCE (free from Core): instSubsingleton

end basics

section iso

variable {R S : Type*} [τR : TopologicalSpace R] [τS : TopologicalSpace S] [Semiring R] [Semiring S]

variable {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

variable {A : Type*} [AddCommMonoid A] [Module R A] [τA : TopologicalSpace A] [IsModuleTopology R A]

variable {B : Type*} [AddCommMonoid B] [Module R B] [τB : TopologicalSpace B]

variable {B' : Type*} [AddCommMonoid B'] [Module S B'] [τB' : TopologicalSpace B']

protected theorem isoₛₗ (hσ : Continuous σ) (hσ' : Continuous σ') (e : A ≃SL[σ] B') :
    IsModuleTopology S B' where
  eq_moduleTopology' := by
    -- get these in before I start putting new topologies on A and B and have to use `@`
    let g : A →ₛₗ[σ] B' := e
    let g' : B' →ₛₗ[σ'] A := e.symm
    let h : A →+ B' := e
    let h' : B' →+ A := e.symm
    simp_rw [e.toHomeomorph.symm.isInducing.1, eq_moduleTopology R A, moduleTopology, induced_sInf]
    apply congr_arg
    ext τ -- from this point on the definitions of `g`, `g'` etc. above don't work without `@`.
    rw [Set.mem_image]
    constructor
    · rintro ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
      exact ⟨continuousSMul_inducedₛₗ g' hσ', continuousAdd_induced h'⟩
    · rintro ⟨h1, h2⟩
      use τ.induced e
      rw [induced_compose]
      refine ⟨⟨continuousSMul_inducedₛₗ g hσ, continuousAdd_induced h⟩, ?_⟩
      nth_rw 2 [← induced_id (t := τ)]
      simp

protected theorem iso (e : A ≃L[R] B) : IsModuleTopology R B :=
  IsModuleTopology.isoₛₗ continuous_id continuous_id e

end iso

section self

variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [IsTopologicalSemiring R]

/-!
We now fix once and for all a topological semiring `R`.

We first prove that the module topology on `R` considered as a module over itself,
is `R`'s topology.
-/

-- INSTANCE (free from Core): _root_.IsTopologicalSemiring.toIsModuleTopology

end self

section MulOpposite

variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [IsTopologicalSemiring R]

-- INSTANCE (free from Core): _root_.IsTopologicalSemiring.toOppositeIsModuleTopology

end MulOpposite

section function

variable {R S : Type*} [τR : TopologicalSpace R] [τS : TopologicalSpace S] [Semiring R] [Semiring S]

variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]

variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B]
    [ContinuousAdd B] [ContinuousSMul R B]

variable {B' : Type*} [AddCommMonoid B'] [Module S B'] [aB' : TopologicalSpace B']
    [ContinuousAdd B'] [ContinuousSMul S B']
