/-
Extracted from CategoryTheory/Galois/GaloisObjects.lean
Genuine: 9 of 12 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Galois objects in Galois categories

We define when a connected object of a Galois category `C` is Galois in a fiber-functor-independent
way and show equivalent characterisations.

## Main definitions

* `IsGalois` : Connected object `X` of `C` such that `X / Aut X` is terminal.

## Main results

* `galois_iff_pretransitive` : A connected object `X` is Galois if and only if `Aut X`
                               acts transitively on `F.obj X` for a fiber functor `F`.

-/

universe u₁ u₂ v₁ v₂ v w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

-- INSTANCE (free from Core): {G

class IsGalois {C : Type u₁} [Category.{u₂, u₁} C] [GaloisCategory C] (X : C) : Prop
    extends IsConnected X where
  quotientByAutTerminal : Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X)

variable {C : Type u₁} [Category.{u₂, u₁} C]

-- INSTANCE (free from Core): autMulFiber

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

noncomputable def quotientByAutTerminalEquivUniqueQuotient
    (X : C) [IsConnected X] :
    IsTerminal (colimit <| SingleObj.functor <| Aut.toEnd X) ≃
    Unique (MulAction.orbitRel.Quotient (Aut X) (F.obj X)) := by
  let J : SingleObj (Aut X) ⥤ C := SingleObj.functor (Aut.toEnd X)
  let e : (F ⋙ FintypeCat.incl).obj (colimit J) ≅ _ :=
    preservesColimitIso (F ⋙ FintypeCat.incl) J ≪≫
    (Equiv.toIso <| SingleObj.Types.colimitEquivQuotient (J ⋙ F ⋙ FintypeCat.incl))
  apply Equiv.trans
  · apply (IsTerminal.isTerminalIffObj (F ⋙ FintypeCat.incl) _).trans
      (isLimitEmptyConeEquiv _ (asEmptyCone _) (asEmptyCone _) e)
  exact Types.isTerminalEquivUnique _

lemma isGalois_iff_aux (X : C) [IsConnected X] :
    IsGalois X ↔ Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X) :=
  ⟨fun h ↦ h.quotientByAutTerminal, fun h ↦ ⟨h⟩⟩

theorem isGalois_iff_pretransitive (X : C) [IsConnected X] :
    IsGalois X ↔ MulAction.IsPretransitive (Aut X) (F.obj X) := by
  rw [isGalois_iff_aux, Equiv.nonempty_congr <| quotientByAutTerminalEquivUniqueQuotient F X]
  exact (MulAction.pretransitive_iff_unique_quotient_of_nonempty (Aut X) (F.obj X)).symm

noncomputable def isTerminalQuotientOfIsGalois (X : C) [IsGalois X] :
    IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X :=
  Nonempty.some IsGalois.quotientByAutTerminal

-- INSTANCE (free from Core): isPretransitive_of_isGalois

lemma stabilizer_normal_of_isGalois (X : C) [IsGalois X] (x : F.obj X) :
    Subgroup.Normal (MulAction.stabilizer (Aut F) x) where
  conj_mem n ninstab g := by
    rw [MulAction.mem_stabilizer_iff]
    change g • n • (g⁻¹ • x) = x
    have : ∃ (φ : Aut X), F.map φ.hom x = g⁻¹ • x :=
      MulAction.IsPretransitive.exists_smul_eq x (g⁻¹ • x)
    obtain ⟨φ, h⟩ := this
    rw [← h, mulAction_naturality, ninstab, h]
    simp

theorem evaluation_aut_surjective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) :
    Function.Surjective (fun f : Aut A ↦ F.map f.hom a) :=
  MulAction.IsPretransitive.exists_smul_eq a

theorem evaluation_aut_bijective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) :
    Function.Bijective (fun f : Aut A ↦ F.map f.hom a) :=
  ⟨evaluation_aut_injective_of_isConnected F A a, evaluation_aut_surjective_of_isGalois F A a⟩

noncomputable def evaluationEquivOfIsGalois (A : C) [IsGalois A] (a : F.obj A) : Aut A ≃ F.obj A :=
  Equiv.ofBijective _ (evaluation_aut_bijective_of_isGalois F A a)
