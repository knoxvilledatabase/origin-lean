/-
Extracted from Probability/Kernel/Category/Stoch.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Stoch

The category of measurable spaces with Markov kernels is a Markov category.

## Main declarations

`Stoch` is defined as the wide subcategory `WideSubcategory StochHom` of `SFinKer`, where
`StochHom` selects Markov kernels, and this construction provides in particular the instance
`MarkovCategory Stoch`.

## References
* [A synthetic approach to
Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]
-/

open CategoryTheory ProbabilityTheory MeasureTheory

open scoped MonoidalCategory SFinKer

universe u

abbrev StochHom : MorphismProperty SFinKer := fun _ _ κ => IsMarkovKernel κ.1

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {X}

abbrev Stoch := WideSubcategory StochHom

-- INSTANCE (free from Core): {X

noncomputable

-- INSTANCE (free from Core): :
