module

public import ToricPower.LatticeStellarMultiplicityStep

/-!
# Multiplicity one is integral regularity

The primitive rays of a full-dimensional simplicial cone form a real
basis. If their integer determinant has absolute value at most one,
its nonvanishing forces it to be a unit. They therefore form an actual
integral basis of the original lattice, which proves regularity in the
original geometric sense.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

theorem isRegularCone_of_coneMultiplicity_le_one (lattice : IsIntegralLattice i)
    {C : PointedCone ℝ V} (toric : IsToricCone i C) (simplicial : C.IsSimplicial)
    (full : Submodule.span ℝ (C : Set V) = ⊤)
    (small : coneMultiplicity lattice C ≤ 1) : IsRegularCone i C := by
  letI := ToricRay.finite_of_fg toric.fg
  letI := Fintype.ofFinite (ToricRay C)
  let basis := fullConeIntegralBasis lattice toric simplicial full
  let realBasis := simplicialPrimitiveBasis lattice toric simplicial full
  let vectors := primitiveGenerator lattice toric
  have image (ρ : ToricRay C) : realBasis ρ = i (vectors ρ) :=
    simplicialPrimitiveBasis_apply _ _ _ _ _
  have nonzero : basis.det vectors ≠ 0 :=
    integralBasis_det_ne_zero lattice basis realBasis vectors image
  have unit : IsUnit (basis.det vectors) := by
    apply Int.isUnit_iff_natAbs_eq.mpr
    have positive : 0 < (basis.det vectors).natAbs := Int.natAbs_pos.mpr nonzero
    have bound : (basis.det vectors).natAbs ≤ 1 := by
      rw [← coneMultiplicity_eq_primitive_basis_det lattice toric simplicial full]
      exact small
    omega
  have basisConditions := basis.is_basis_iff_det.mpr unit
  let integral : Module.Basis (ToricRay C) ℤ N :=
    Module.Basis.mk basisConditions.1 basisConditions.2.ge
  have family : (integral : ToricRay C → N) = vectors := by
    funext ρ
    exact Module.Basis.mk_apply _ _ _
  have regular := isRegularCone_hull_image_basis lattice integral Set.univ
  have coneEquality : PointedCone.hull ℝ (i '' (integral '' Set.univ)) = C := by
    rw [Set.image_univ, family]
    exact toric.hull_primitiveGenerator lattice
  exact coneEquality ▸ regular

end ToricPower.FanSubdivision
end
