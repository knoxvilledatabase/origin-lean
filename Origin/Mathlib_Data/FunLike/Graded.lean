/-
Extracted from Data/FunLike/Graded.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Class of grading-preserving functions and isomorphisms

We define `GradedFunLike F 𝒜 ℬ` where `𝒜` and `ℬ` represent some sort of grading. This class
assumes `FunLike A B` where `A` and `B` are the underlying types.

We also define `GradedEquivLike E 𝒜 ℬ`, which is similar to `EquivLike`, where here `e : E` is
required to satisfy `x ∈ 𝒜 i ↔ e x ∈ ℬ i`.
-/

class GradedFunLike (F : Type*) {A B σ τ ι : outParam Type*}
    [SetLike σ A] [SetLike τ B] (𝒜 : outParam <| ι → σ) (ℬ : outParam <| ι → τ)
    [FunLike F A B] where
  map_mem (f : F) {i x} : x ∈ 𝒜 i → f x ∈ ℬ i

section GradedFunLike

variable {F A B σ τ ι : Type*}
  [SetLike σ A] [SetLike τ B] {𝒜 : ι → σ} {ℬ : ι → τ} [FunLike F A B] [GradedFunLike F 𝒜 ℬ]

lemma Graded.map_mem (f : F) {i x} (h : x ∈ 𝒜 i) : f x ∈ ℬ i :=
  GradedFunLike.map_mem f h

def Graded.subtypeMap (f : F) (i : ι) (x : 𝒜 i) : ℬ i :=
  ⟨f x, map_mem f x.2⟩

end GradedFunLike

class GradedEquivLike (E : Type*) {A B σ τ ι : outParam Type*}
    [SetLike σ A] [SetLike τ B] (𝒜 : outParam <| ι → σ) (ℬ : outParam <| ι → τ)
    [EquivLike E A B] where
  map_mem_iff (e : E) {i x} : e x ∈ ℬ i ↔ x ∈ 𝒜 i

section GradedEquivLike

variable (E : Type*) {A B σ τ ι : Type*} [SetLike σ A] [SetLike τ B]
  (𝒜 : ι → σ) (ℬ : ι → τ) [EquivLike E A B] [GradedEquivLike E 𝒜 ℬ]

-- INSTANCE (free from Core): (priority

variable {E 𝒜 ℬ}

lemma Graded.map_mem_iff (e : E) {i x} : e x ∈ ℬ i ↔ x ∈ 𝒜 i :=
  GradedEquivLike.map_mem_iff e

alias ⟨Graded.mem_of_map_mem, Graded.map_mem_of_mem⟩ := Graded.map_mem_iff
