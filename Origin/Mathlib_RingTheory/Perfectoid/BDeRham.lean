/-
Extracted from RingTheory/Perfectoid/BDeRham.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# The de Rham Period Ring $\mathbb{B}_{dR}^+$ and $\mathbb{B}_{dR}$

In this file, we define the de Rham period ring $\mathbb{B}_{dR}^+$ and
the de Rham ring $\mathbb{B}_{dR}$. We define a generalized version of
these period rings following Scholze. When `R` is the ring of integers
of `ℂₚ` (`PadicComplexInt`), they coincide with the classical de Rham period rings.

## Main definitions

* `BDeRhamPlus` : The period ring $\mathbb{B}_{dR}^+$.
* `BDeRham` : The period ring $\mathbb{B}_{dR}$.

## TODO

1. Extend the θ map to $\mathbb{B}_{dR}^+$
2. Show that $\mathbb{B}_{dR}^+$ is a discrete valuation ring.
3. Show that ker θ is principal when the base ring is integral perfectoid.

Currently, the period ring `BDeRhamPlus` takes the ring of integers `R` as the input.
After the perfectoid theory is developed, we can modify it to
take a perfectoid field as the input.

## Reference

* [Fontaine, *Sur Certains Types de Représentations p-Adiques du Groupe de Galois d'un Corps Local;
  Construction d'un Anneau de Barsotti-Tate*][fontaine1982certains]
* [Fontaine, *Le corps des périodes p-adiques*][fontaine1994corps]
* [Scholze, *p-adic Hodge theory for rigid-analytic varieties*][scholze2013adic]

## Tags
Period rings, p-adic Hodge theory
-/

universe u

open Ideal WittVector

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

local notation "𝕎 " A:100 => WittVector p A

local notation A "♭" => PreTilt A p

noncomputable section

def fontaineThetaInvertP :
    Localization.Away (p : 𝕎 R♭) →+* Localization.Away (p : R) :=
  Localization.awayLift ((algebraMap R _).comp (fontaineTheta R p)) (p : 𝕎 R♭)
      (by simpa using IsLocalization.Away.algebraMap_isUnit (p : R))

def BDeRhamPlus : Type u :=
  AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) (Localization.Away (p : 𝕎 R♭))

deriving CommRing

def BDeRham : Type u :=
  Localization (M := BDeRhamPlus R p) <| Submonoid.closure <|
    AdicCompletion.of ((RingHom.ker (fontaineThetaInvertP R p))) _ ''
      {a | (RingHom.ker (fontaineThetaInvertP R p)) = Ideal.span {a}}

local notation "𝔹_dR^+(" R ")" => BDeRhamPlus R p

local notation "𝔹_dR(" R ")" => BDeRham R p

end
