module

public import TauCeti.AlgebraicGeometry.LineBundle.Basic
import all TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Coordinates for an explicitly chosen unit-sheaf trivialization

This interface lemma exposes the defining cancellation in the imported
rank-one coordinate construction. It avoids unfolding a private imported
implementation in the anticanonical ampleness proof.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Forming free rank-one coordinates from a unit-sheaf frame recovers
that same frame. -/
theorem trivializationCoordinateIso_of_unitIso {X : Scheme.{u}}
    (M : X.Modules) {U : X.Opens}
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    trivializationCoordinateIso M
      (TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U) ≪≫ e.symm) = e := by
  simp [trivializationCoordinateIso]

#print axioms trivializationCoordinateIso_of_unitIso

end AlgebraicGeometry.Scheme.Modules
