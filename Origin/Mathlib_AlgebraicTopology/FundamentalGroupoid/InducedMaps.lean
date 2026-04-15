/-
Extracted from AlgebraicTopology/FundamentalGroupoid/InducedMaps.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Homotopic maps induce naturally isomorphic functors

## Main definitions

- `FundamentalGroupoidFunctor.homotopicMapsNatIso H` The natural isomorphism
  between the induced functors `f : π(X) ⥤ π(Y)` and `g : π(X) ⥤ π(Y)`, given a homotopy
  `H : f ∼ g`

- `FundamentalGroupoidFunctor.equivOfHomotopyEquiv hequiv` The equivalence of the categories
  `π(X)` and `π(Y)` given a homotopy equivalence `hequiv : X ≃ₕ Y` between them.
-/

noncomputable section

universe u v

open FundamentalGroupoid CategoryTheory FundamentalGroupoidFunctor

open scoped FundamentalGroupoid unitInterval

set_option backward.isDefEq.respectTransparency false in

theorem Path.Homotopic.map_trans_evalAt {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (F : f.Homotopy g) {x₁ x₂ : X} (p : Path x₁ x₂) :
    ((p.map (map_continuous f)).trans (F.evalAt x₂)).Homotopic
      ((F.evalAt x₁).trans (p.map (map_continuous g))) := by
  /- Let `G` be the continuous map on the unit square sending `(t, s)` to `F(t, p(s))`.
  Then our homotopy is the image under `G` of a homotopy
  between the two paths from `(0, 0)` to `(1, 1)` along the sides of the square. -/
  set G : C(I × I, Y) := F.toContinuousMap.comp (.prodMap (.id _) p)
  set p₁ : Path ((0, 0) : I × I) (1, 1) := .prod (.trans (.refl _) .id) (.trans .id (.refl _))
  set p₂ : Path ((0, 0) : I × I) (1, 1) := .prod (.trans .id (.refl _)) (.trans (.refl _) .id)
  set Fsq : p₁.Homotopy p₂ :=
    Path.Homotopic.prodHomotopy (.trans (.reflTrans _) (.symm <| .transRefl _))
      (.trans (.transRefl _) (.symm <| .reflTrans _))
  refine ⟨((Fsq.map G).pathCast ?H0 ?H1).cast ?hp ?hq⟩
  all_goals aesop (add simp Path.trans_apply)

namespace FundamentalGroupoidFunctor

open CategoryTheory

open scoped FundamentalGroupoid ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}

set_option backward.isDefEq.respectTransparency false in

set_option pp.proofs.withType true in

def homotopicMapsNatIso (H : ContinuousMap.Homotopy f g) : map f ⟶ map g where
  app x := ⟦H.evalAt x.as⟧
  naturality := by
    rintro ⟨x⟩ ⟨y⟩ p
    rcases Path.Homotopic.Quotient.mk_surjective p with ⟨p, rfl⟩
    simp only [map_map, map_obj_as, Path.Homotopic.Quotient.mk''_eq_mk, comp_eq,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_trans]
    rw [Path.Homotopic.Quotient.eq]
    exact .map_trans_evalAt _ _

-- INSTANCE (free from Core): (H

open scoped ContinuousMap

def equivOfHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (hequiv : X ≃ₕ Y) :
    πₓ (.of X) ≌ πₓ (.of Y) := by
  apply CategoryTheory.Equivalence.mk (map hequiv.toFun) (map hequiv.invFun)
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using (asIso (homotopicMapsNatIso hequiv.left_inv.some)).symm
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using asIso (homotopicMapsNatIso hequiv.right_inv.some)

end FundamentalGroupoidFunctor

/-!
### Old proof

The rest of the file contains definitions and theorems required to write the same proof
in a slightly different manner.

The proof was rewritten in 2025 for two reasons:

- the new proof is much more straightforward;
- the new proof is fully universe polymorphic.

TODO: review which of these definitions and theorems are useful for other reasons,
then deprecate the rest of them.
-/

namespace unitInterval

def path01 : Path (0 : I) 1 where
  toFun := id
  source' := rfl
  target' := rfl

def upath01 : Path (ULift.up 0 : ULift.{u} I) (ULift.up 1) where
  toFun := ULift.up
  source' := rfl
  target' := rfl

def uhpath01 : @fromTop (TopCat.of <| ULift.{u} I) (ULift.up (0 : I)) ⟶ fromTop (ULift.up 1) :=
  ⟦upath01⟧

end unitInterval

namespace ContinuousMap.Homotopy

open unitInterval (uhpath01)

section Casts

abbrev hcast {X : TopCat} {x₀ x₁ : X} (hx : x₀ = x₁) : fromTop x₀ ⟶ fromTop x₁ :=
  eqToHom <| FundamentalGroupoid.ext hx
