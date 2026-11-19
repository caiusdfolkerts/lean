module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import TauCeti.Geometry.Toric.Algebraic.Ray.Basic

/-!
# Intrinsic ray indices of a finite fan

Exact declaration bodies from the introductory `Ray` section of
TauCeti/Geometry/Toric/Algebraic/Fan/Ray.lean at commit
6b896c7c411221eb78639e4be8ead6e479a62893. Only the intrinsic index and its
cone inclusions are needed here; this file does not import the later fan
isomorphism theory. New source, pending an ordinary successful Lean check.
-/

@[expose] public section

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Phi : Fan i)

/-- A ray of a fan is a one-dimensional cone belonging to the fan. -/
abbrev Ray : Type _ :=
  {rho : Phi.cones //
    Module.finrank ℝ (Submodule.span ℝ (rho.1 : Set V)) = 1}

namespace Ray

/-- The cone of the fan underlying a fan ray. -/
abbrev toCone (rho : Phi.Ray) : Phi.cones := rho.1

/-- The cone underlying a fan ray has one-dimensional linear span. -/
@[simp]
theorem finrank_span (rho : Phi.Ray) :
    Module.finrank ℝ (Submodule.span ℝ (rho.toCone.1 : Set V)) = 1 :=
  rho.2

/-- A ray of a cone belonging to a fan is a ray of the fan. -/
def ofToricRay (sigma : Phi.cones) (rho : ToricRay sigma.1) : Phi.Ray :=
  ⟨⟨rho.toPointedCone, Phi.mem_of_isFaceOf sigma.2 rho.1.isFaceOf⟩, rho.2⟩

@[simp]
theorem toCone_ofToricRay (sigma : Phi.cones) (rho : ToricRay sigma.1) :
    (ofToricRay Phi sigma rho).toCone.1 = rho.toPointedCone :=
  (rfl)

/-- A toric ray, viewed as a fan ray, is contained in its original cone. -/
theorem toCone_ofToricRay_le (sigma : Phi.cones) (rho : ToricRay sigma.1) :
    (ofToricRay Phi sigma rho).toCone ≤ sigma := by
  exact Subtype.coe_le_coe.1 (toCone_ofToricRay Phi sigma rho ▸ rho.1.isFaceOf.le)

/-- A fan ray contained in a cone is a ray of that cone. -/
def toToricRay (rho : Phi.Ray) (sigma : Phi.cones) (h : rho.toCone ≤ sigma) :
    ToricRay sigma.1 :=
  ⟨⟨rho.toCone.1, Phi.isFaceOf_of_le sigma.2 rho.toCone.2 h⟩, rho.2⟩

@[simp]
theorem toPointedCone_toToricRay (rho : Phi.Ray) (sigma : Phi.cones)
    (h : rho.toCone ≤ sigma) :
    (rho.toToricRay Phi sigma h).toPointedCone = rho.toCone.1 :=
  (rfl)

/-- A fan ray is not the zero cone. -/
theorem toCone_ne_bot (rho : Phi.Ray) : rho.toCone.1 ≠ ⊥ := by
  exact (rho.toToricRay Phi rho.toCone le_rfl).toPointedCone_ne_bot

end Ray

end TauCeti.Toric.Fan
