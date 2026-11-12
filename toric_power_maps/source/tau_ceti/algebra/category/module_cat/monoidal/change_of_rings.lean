module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism

/-! ## Exact upstream proof body: `TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings`
Original SHA256: e023fab48896474543af913450acbeecc3cdbfea4c29d5eaf5f12862bc894a3a.
-/
section SchemeCohomologySource23
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Braided restriction of scalars

Restriction of scalars along a morphism of commutative rings is compatible with the symmetric
braiding on module categories.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.ModuleCat

universe u

noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Restriction of scalars between module categories preserves the symmetric braiding. -/
instance restrictScalarsLaxBraided : (_root_.ModuleCat.restrictScalars f).LaxBraided where
  braided M N := by
    apply _root_.ModuleCat.MonoidalCategory.tensor_ext
    intro (m : M) (n : N)
    erw [_root_.ModuleCat.restrictScalars_μ_tmul]

end

end TauCeti.ModuleCat

end
end SchemeCohomologySource23
