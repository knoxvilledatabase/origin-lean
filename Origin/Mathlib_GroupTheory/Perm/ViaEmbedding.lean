/-
Extracted from GroupTheory/Perm/ViaEmbedding.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `Equiv.Perm.viaEmbedding`, a noncomputable analogue of `Equiv.Perm.viaFintypeEmbedding`.
-/

variable {α β : Type*}

namespace Equiv

namespace Perm

variable (e : Perm α) (ι : α ↪ β)

open scoped Classical in

noncomputable def viaEmbedding : Perm β :=
  extendDomain e (ofInjective ι.1 ι.2)

open scoped Classical in

theorem viaEmbedding_apply (x : α) : e.viaEmbedding ι (ι x) = ι (e x) :=
  extendDomain_apply_image e (ofInjective ι.1 ι.2) x

open scoped Classical in

theorem viaEmbedding_apply_of_notMem (x : β) (hx : x ∉ Set.range ι) : e.viaEmbedding ι x = x :=
  extendDomain_apply_not_subtype e (ofInjective ι.1 ι.2) hx

open scoped Classical in

noncomputable def viaEmbeddingHom : Perm α →* Perm β :=
  extendDomainHom (ofInjective ι.1 ι.2)

open scoped Classical in

theorem viaEmbeddingHom_injective : Function.Injective (viaEmbeddingHom ι) :=
  extendDomainHom_injective (ofInjective ι.1 ι.2)

end Perm

end Equiv
