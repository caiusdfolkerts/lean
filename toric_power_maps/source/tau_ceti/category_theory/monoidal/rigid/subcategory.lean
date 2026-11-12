module

public import TauCeti.AlgebraicGeometry.Modules.Dual

/-! ## Exact upstream proof body: `TauCeti.CategoryTheory.Monoidal.Rigid.Subcategory`
Original SHA256: e3b0af7cd93f85b185d6be12f1e2f625a398d8ee52f57ba77b0251c6a7fe2d5b.
-/
section SchemeCohomologySource52
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Duality in full monoidal subcategories

An exact pairing between two objects of a monoidal category restricts to any full monoidal
subcategory containing both objects: it is pulled back along the fully faithful monoidal
inclusion by `CategoryTheory.ExactPairing.ofFullyFaithful`. Its evaluation and coevaluation are
the ambient ones on underlying objects. Consequently an object and a chosen dual that both
satisfy a monoidal property remain dual to one another after imposing that property.

## Main declarations

* `CategoryTheory.ObjectProperty.exactPairingFullSubcategory`: an ambient exact pairing induces
  one in a full monoidal subcategory.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe v u

noncomputable section

namespace ObjectProperty

open _root_.CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {P : ObjectProperty C} [P.IsMonoidal]

/-- An exact pairing between the underlying objects of a full monoidal subcategory is an exact
pairing in that subcategory, obtained by pulling back along the inclusion `P.ι`. -/
instance _root_.CategoryTheory.ObjectProperty.exactPairingFullSubcategory
    (X Y : P.FullSubcategory) [ExactPairing X.obj Y.obj] :
    ExactPairing X Y :=
  letI : ExactPairing (P.ι.obj X) (P.ι.obj Y) := inferInstanceAs (ExactPairing X.obj Y.obj)
  .ofFullyFaithful P.ι X Y

/-- The coevaluation of an ambient exact pairing, restricted to a full monoidal subcategory, is
the ambient coevaluation on underlying objects. -/
@[simp]
theorem _root_.CategoryTheory.ObjectProperty.exactPairingFullSubcategory_coevaluation_hom
    (X Y : P.FullSubcategory) [ExactPairing X.obj Y.obj] :
    (@ExactPairing.coevaluation P.FullSubcategory _ _ X Y
      (exactPairingFullSubcategory X Y)).hom = η_ X.obj Y.obj := by
  -- `ofFullyFaithful` defines this pairing by taking the preimage of the ambient coevaluation.
  -- After exposing that definition, `map_preimage` cancels the fully faithful lift. The pinned
  -- subcategory API has no correctly typed simp lemma for the oplax unit `η P.ι`, so its
  -- identity constraint must be discharged by its stable definitional equality.
  change P.ι.map (P.ι.preimage (Functor.OplaxMonoidal.η P.ι ≫ η_ X.obj Y.obj ≫
    Functor.LaxMonoidal.μ P.ι X Y)) = _
  rw [Functor.map_preimage]
  simp [show Functor.OplaxMonoidal.η P.ι = 𝟙 _ from rfl]

/-- The evaluation of an ambient exact pairing, restricted to a full monoidal subcategory, is
the ambient evaluation on underlying objects. -/
@[simp]
theorem _root_.CategoryTheory.ObjectProperty.exactPairingFullSubcategory_evaluation_hom
    (X Y : P.FullSubcategory) [ExactPairing X.obj Y.obj] :
    (@ExactPairing.evaluation P.FullSubcategory _ _ X Y
      (exactPairingFullSubcategory X Y)).hom = ε_ X.obj Y.obj := by
  -- As above, unfolding `ofFullyFaithful` exposes the preimage construction; `map_preimage`
  -- and the inclusion functor's public constraint simp lemmas then recover the ambient map.
  change P.ι.map (P.ι.preimage (Functor.OplaxMonoidal.δ P.ι Y X ≫ ε_ X.obj Y.obj ≫
    Functor.LaxMonoidal.ε P.ι)) = _
  rw [Functor.map_preimage]
  simp

end ObjectProperty

end

end TauCeti

end
end SchemeCohomologySource52
