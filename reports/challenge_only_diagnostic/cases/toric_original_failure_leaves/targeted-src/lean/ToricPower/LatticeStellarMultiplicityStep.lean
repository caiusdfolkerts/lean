module

public import ToricPower.ConeMultiplicity
public import ToricPower.LatticeDeterminantDescent
public import ToricPower.FanMultiplicityDescent
public import ToricPower.FractionalPointAvoidsRegular

/-!
# The actual decreasing integral stellar step

For a singular full-dimensional simplicial cone, the half-open
fundamental parallelepiped supplies a primitive lattice point. Its
fractional coordinate bounds propagate across every adjacent cone.
Each new full-dimensional stellar cone therefore has strictly smaller
integer determinant than its old parent. The point avoids every regular
old cone, so this operation preserves the prescribed regular subfan.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- An integral background basis indexed by the rays of a full-dimensional
simplicial cone. Its vectors need not be the primitive ray vectors. -/
def fullConeIntegralBasis (lattice : IsIntegralLattice i)
    {C : PointedCone ℝ V} (toric : IsToricCone i C) (simplicial : C.IsSimplicial)
    (full : Submodule.span ℝ (C : Set V) = ⊤) :
    Module.Basis (ToricRay C) ℤ N := by
  have count : Nat.card (ToricRay C) = Module.finrank ℤ N :=
    (Module.finrank_eq_nat_card_basis (simplicialPrimitiveBasis lattice toric simplicial full)).symm.trans
      lattice.finrank_eq.symm
  exact (latticeBasis lattice).reindex (coneRayEnumeration lattice toric count).symm

theorem coneMultiplicity_eq_primitive_basis_det (lattice : IsIntegralLattice i)
    {C : PointedCone ℝ V} (toric : IsToricCone i C) (simplicial : C.IsSimplicial)
    (full : Submodule.span ℝ (C : Set V) = ⊤)
    [Fintype (ToricRay C)] [DecidableEq (ToricRay C)] :
    coneMultiplicity lattice C =
      ((fullConeIntegralBasis lattice toric simplicial full).det
        (primitiveGenerator lattice toric)).natAbs := by
  apply coneMultiplicity_eq_det_of_primitive_family lattice _ _
    (primitiveGenerator_isPrimitive lattice toric)
    (simplicial_primitiveGenerator_linearIndependent lattice toric simplicial) toric
  change C = PointedCone.hull ℝ (Set.range (i ∘ primitiveGenerator lattice toric))
  rw [Set.range_comp]
  exact (toric.hull_primitiveGenerator lattice).symm

/-- This constructs the complete arithmetic-and-geometric output used
by the already verified finite multiplicity descent. -/
theorem exists_stellarMultiplicityStep (fan : Fan i) (complete : fan.IsComplete)
    (simplicial : ∀ C ∈ fan.cones, C.IsSimplicial)
    (focus : PointedCone ℝ V) (focusMember : focus ∈ fan.cones)
    (fullFocus : Submodule.span ℝ (focus : Set V) = ⊤)
    (large : 1 < coneMultiplicity fan.lattice focus) :
    Nonempty (StellarMultiplicityStep fan (coneMultiplicity fan.lattice) focus) := by
  letI := ToricRay.finite_of_fg (fan.isToricCone focusMember).fg
  letI := Fintype.ofFinite (ToricRay focus)
  let realBasis := simplicialPrimitiveBasis fan.lattice (fan.isToricCone focusMember)
    (simplicial focus focusMember) fullFocus
  let basis := fullConeIntegralBasis fan.lattice (fan.isToricCone focusMember)
    (simplicial focus focusMember) fullFocus
  let vectors := primitiveGenerator fan.lattice (fan.isToricCone focusMember)
  have image (k : ToricRay focus) : realBasis k = i (vectors k) :=
    simplicialPrimitiveBasis_apply _ _ _ _ _
  have determinantLarge : 1 < (basis.det vectors).natAbs := by
    rw [← coneMultiplicity_eq_primitive_basis_det]
    exact large
  obtain ⟨q, primitive, nonzero, bounds⟩ :=
    exists_primitive_fractional_of_det_large fan.lattice basis realBasis vectors image determinantLarge
  have imageNonzero : i q ≠ 0 := by
    intro zero
    exact nonzero (fan.lattice.injective (zero.trans (map_zero i).symm))
  have member : i q ∈ focus :=
    (mem_simplicialCone_iff_coordinates_nonnegative fan.lattice (fan.isToricCone focusMember)
      (simplicial focus focusMember) fullFocus _).mpr (fun k => (bounds k).1)
  refine ⟨⟨q, imageNonzero, member, ?_, ?_⟩⟩
  · exact fractional_integral_point_avoids_regular fan simplicial ⟨focus,focusMember⟩
      fullFocus q imageNonzero member (fun k => (bounds k).2)
  · intro S SMember fullS
    rcases stellarFan_fullDimensional_cases fan complete simplicial q SMember fullS with old |
      ⟨C,CMember,fullC,memberC,j,positive,description⟩
    · exact Or.inl old
    · right
      letI := ToricRay.finite_of_fg (fan.isToricCone CMember).fg
      letI := Fintype.ofFinite (ToricRay C)
      let parentReal := simplicialPrimitiveBasis fan.lattice (fan.isToricCone CMember)
        (simplicial C CMember) fullC
      let parentBasis := fullConeIntegralBasis fan.lattice (fan.isToricCone CMember)
        (simplicial C CMember) fullC
      let parentVectors := primitiveGenerator fan.lattice (fan.isToricCone CMember)
      have parentImage (k : ToricRay C) : parentReal k = i (parentVectors k) :=
        simplicialPrimitiveBasis_apply _ _ _ _ _
      have smallerCoordinate : parentReal.repr (i q) j < 1 :=
        primitive_coordinates_lt_one_transfer fan simplicial ⟨focus,focusMember⟩ ⟨C,CMember⟩
          fullFocus fullC member memberC (fun k => (bounds k).2) j
      have replacementImage : (fun k => i (Function.update parentVectors j q k)) =
          Function.update parentReal j (i q) := by
        funext k
        by_cases equal : k = j
        · subst k
          simp
        · simp [Function.update_of_ne equal, parentImage]
      have replacementIndependent : LinearIndependent ℝ
          (fun k => i (Function.update parentVectors j q k)) := by
        rw [replacementImage]
        exact realBasis_update_independent parentReal j (i q) (ne_of_gt positive)
      have replacementPrimitive (k : ToricRay C) :
          TauCeti.IsPrimitive (Function.update parentVectors j q k) := by
        by_cases equal : k = j
        · subst k
          simpa only [Function.update_self] using primitive
        · rw [Function.update_of_ne equal]
          exact primitiveGenerator_isPrimitive _ _ _
      have replacementDescription : S = PointedCone.hull ℝ
          (Set.range (fun k => i (Function.update parentVectors j q k))) := by
        rw [replacementImage]
        exact description
      refine ⟨C,CMember,fullC,?_⟩
      rw [coneMultiplicity_eq_det_of_primitive_family fan.lattice parentBasis _
        replacementPrimitive replacementIndependent ((stellarFan fan q).isToricCone SMember)
        replacementDescription, coneMultiplicity_eq_primitive_basis_det fan.lattice
        (fan.isToricCone CMember) (simplicial C CMember) fullC]
      exact integralBasis_natAbs_det_update_lt fan.lattice parentBasis parentReal parentVectors
        parentImage j q positive smallerCoordinate

end ToricPower.FanSubdivision
end
