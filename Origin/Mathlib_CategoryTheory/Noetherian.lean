/-
Extracted from CategoryTheory/Noetherian.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Artinian and Noetherian categories

An Artinian category is a category in which objects do not
have infinite decreasing sequences of subobjects.

A Noetherian category is a category in which objects do not
have infinite increasing sequences of subobjects.

Note: In the file, `Mathlib/CategoryTheory/Subobject/ArtinianObject.lean`,
it is shown that any nonzero Artinian object has a simple subobject.

## Future work
The Jordan-Hölder theorem, following https://stacks.math.columbia.edu/tag/0FCK.
-/

namespace CategoryTheory

open CategoryTheory.Limits

variable (C : Type*) [Category* C]

class Noetherian : Prop extends EssentiallySmall C where
  isNoetherianObject : ∀ X : C, IsNoetherianObject X

attribute [instance] Noetherian.isNoetherianObject

class Artinian : Prop extends EssentiallySmall C where
  isArtinianObject : ∀ X : C, IsArtinianObject X

attribute [instance] Artinian.isArtinianObject

end CategoryTheory
