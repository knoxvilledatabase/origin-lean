/-
Extracted from Algebra/Homology/SpectralObject/Cycles.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Kernel and cokernel of the differential of a spectral object

Let `X` be a spectral object indexed by the category `ι`
in the abelian category `C`. In this file, we introduce
the kernel `X.cycles` and the cokernel `X.opcycles` of `X.δ`.
These are defined when `f` and `g` are composable morphisms
in `ι` and for any integer `n`.
In the documentation, the kernel `X.cycles n f g` of
`δ : H^n(g) ⟶ H^{n+1}(f)` shall be denoted `Z^n(f, g)`,
and the cokernel `X.opcycles n f g` of `δ : H^{n-1}(g) ⟶ H^n(f)`
shall be denoted `opZ^n(f, g)`.
The definitions `cyclesMap` and `opcyclesMap` give the
functoriality of these definitions with respect
to morphisms in `ComposableArrows ι 2`.

We record that `Z^n(f, g)` is a kernel by the lemma
`kernelSequenceCycles_exact` and that `opZ^n(f, g)` is
a cokernel by the lemma `cokernelSequenceOpcycles_exact`.
We also provide a constructor `X.liftCycles` for morphisms
to cycles and `X.descOpcycles` for morphisms from opcycles.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]
-/

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

namespace SpectralObject

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ)

noncomputable def cycles : C := kernel (X.δ f g n (n + 1))

noncomputable def opcycles : C := cokernel (X.δ f g (n - 1) n)

noncomputable def iCycles :
    X.cycles f g n ⟶ (X.H n).obj (mk₁ g) :=
  kernel.ι _

noncomputable def pOpcycles :
    (X.H n).obj (mk₁ f) ⟶ X.opcycles f g n :=
  cokernel.π _

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

lemma isZero_opcycles (h : IsZero ((X.H n).obj (mk₁ f))) :
    IsZero (X.opcycles f g n) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (X.pOpcycles ..)]
  apply h.eq_of_src

lemma isZero_cycles (h : IsZero ((X.H n).obj (mk₁ g))) :
    IsZero (X.cycles f g n) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (X.iCycles ..)]
  apply h.eq_of_tgt

end

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ)

set_option backward.isDefEq.respectTransparency false in
