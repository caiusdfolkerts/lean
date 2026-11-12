module

public import ToricPower.ToricBoundaryCharacter
public import ToricPower.QuasicoherentPoleClearing

/-!
# The actual effective Cartier boundary of each toric chart

The local integral boundary characters are regular monomials. Their
principal opens are precisely the intersections with the chosen chart,
and their quotients are the actual Cartier transition units.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Multiplicative TauCeti.Toric

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

theorem toricChartBoundaryCharacter_face_ray (fan : Fan i) (regular : fan.IsRegular)
    (σ : fan.cones) {τ υ : fan.cones} (face : υ.val.IsFaceOf τ.val)
    (ρ : ToricRay υ.val) :
    toricChartBoundaryCharacter fan regular σ τ
        (primitiveGenerator fan.lattice (fan.isToricCone υ.property) ρ) =
      toricChartBoundaryCharacter fan regular σ υ
        (primitiveGenerator fan.lattice (fan.isToricCone υ.property) ρ) := by
  have h := toricChartBoundaryCharacter_ray fan regular σ τ (ToricRay.faceEmbedding face ρ)
  rw [primitiveGenerator_face fan.lattice (fan.isToricCone τ.property)
    (fan.isToricCone υ.property) face ρ] at h
  erw [ToricRay.toPointedCone_faceEmbedding face ρ] at h
  rw [toricChartBoundaryCharacter_ray]
  exact h

/-- The normalized boundary characters form a genuine Cartier atlas. -/
def toricChartBoundaryAtlas (fan : Fan i) (regular : fan.IsRegular)
    (σ : fan.cones) : ToricCharacterAtlas fan where
  equation := toricChartBoundaryCharacter fan regular σ
  positive τ υ := by
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice
      (fan.isToricCone (τ ⊓ υ).property)]
    intro ρ
    rw [AddMonoidHom.sub_apply,
      toricChartBoundaryCharacter_face_ray fan regular σ
        (fan.isFaceOf_of_le τ.property (τ ⊓ υ).property inf_le_left),
      toricChartBoundaryCharacter_face_ray fan regular σ
        (fan.isFaceOf_of_le υ.property (τ ⊓ υ).property inf_le_right), sub_self]
  negative τ υ := by
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice
      (fan.isToricCone (τ ⊓ υ).property)]
    intro ρ
    rw [AddMonoidHom.neg_apply, AddMonoidHom.sub_apply,
      toricChartBoundaryCharacter_face_ray fan regular σ
        (fan.isFaceOf_of_le τ.property (τ ⊓ υ).property inf_le_left),
      toricChartBoundaryCharacter_face_ray fan regular σ
        (fan.isFaceOf_of_le υ.property (τ ⊓ υ).property inf_le_right), sub_self, neg_zero]

/-- The local equation as an actual regular function on the chart open. -/
def toricBoundaryRegularEquation (fan : Fan i) (regular : fan.IsRegular)
    (σ τ : fan.cones) :
    Γ(fan.algebraicRealization, (fan.affineToricChartι τ).opensRange) :=
  chartCoordinateSectionsEquiv fan τ
    (MonoidAlgebra.single
      (ofAdd (⟨toricChartBoundaryCharacter fan regular σ τ,
        toricChartBoundaryCharacter_mem_dual fan regular σ τ⟩ : dualSemigroup fan.lattice τ.val))
      (1 : ℂ))

@[simp]
theorem toricBoundaryRegularEquation_self (fan : Fan i) (regular : fan.IsRegular)
    (σ : fan.cones) : toricBoundaryRegularEquation fan regular σ σ = 1 := by
  have hz : (⟨toricChartBoundaryCharacter fan regular σ σ,
      toricChartBoundaryCharacter_mem_dual fan regular σ σ⟩ :
      dualSemigroup fan.lattice σ.val) = 0 :=
    Subtype.ext (toricChartBoundaryCharacter_self fan regular σ)
  unfold toricBoundaryRegularEquation
  rw [hz]
  exact map_one (chartCoordinateSectionsEquiv fan σ)

/-- Principal opens commute with the actual global-section isomorphism of
an open immersion. -/
theorem openImmersion_basicOpen_global {A X : Scheme.{u}} (j : A ⟶ X)
    [IsOpenImmersion j] (s : Γ(A, ⊤)) :
    X.basicOpen ((IsOpenImmersion.ΓIsoTop j).hom s) = j ''ᵁ A.basicOpen s := by
  change X.basicOpen (X.presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op
    ((j.appIso ⊤).inv s)) = _
  rw [Scheme.basicOpen_res_eq]
  exact (Scheme.image_basicOpen j s).symm

theorem faceAffineToricSchemeMap_range_of_zeroFace (lattice : IsIntegralLattice i)
    {τ υ : PointedCone ℝ V} (finite : τ.FG) (face : υ.IsFaceOf τ)
    (m : dualSemigroup lattice τ)
    (zeroFace : τ ⊓ PointedCone.ofSubmodule (LinearMap.ker (lattice.realCharacter m)) = υ) :
    Set.range (faceAffineToricSchemeMap lattice face) =
      (PrimeSpectrum.basicOpen (MonoidAlgebra.single (ofAdd m) (1 : ℂ)) :
        Set (PrimeSpectrum (affineCoordinateRing lattice τ))) := by
  subst υ
  exact range_faceAffineToricSchemeMap lattice finite m

/-- The boundary equation vanishes exactly outside the desired chart. -/
theorem toricBoundaryRegularEquation_basicOpen (fan : Fan i) (regular : fan.IsRegular)
    (σ τ : fan.cones) :
    fan.algebraicRealization.basicOpen (toricBoundaryRegularEquation fan regular σ τ) =
      (fan.affineToricChartι τ).opensRange ⊓ (fan.affineToricChartι σ).opensRange := by
  let m : dualSemigroup fan.lattice τ.val :=
    ⟨toricChartBoundaryCharacter fan regular σ τ,
      toricChartBoundaryCharacter_mem_dual fan regular σ τ⟩
  let a : affineCoordinateRing fan.lattice τ.val := MonoidAlgebra.single (ofAdd m) 1
  let face := fan.isFaceOf_of_le τ.property (τ ⊓ σ).property inf_le_left
  let inclusion := faceAffineToricSchemeMap fan.lattice face
  letI : IsOpenImmersion inclusion :=
    (fan.isToricCone τ.property).rational.isOpenImmersion_faceAffineToricSchemeMap _ face
  have rangeEquality : inclusion.opensRange = PrimeSpectrum.basicOpen a := by
    apply Opens.ext
    exact faceAffineToricSchemeMap_range_of_zeroFace fan.lattice
      (fan.isToricCone τ.property).rational.fg face m
      (toricChartBoundaryCharacter_zeroFace fan regular σ τ)
  change fan.algebraicRealization.basicOpen ((IsOpenImmersion.ΓIsoTop
    (fan.affineToricChartι τ)).hom ((Scheme.ΓSpecIso (.of _)).inv a)) = _
  rw [openImmersion_basicOpen_global, basicOpen_eq_of_affine, ← rangeEquality,
    ← Scheme.Hom.opensRange_comp]
  change (faceAffineToricSchemeMap fan.lattice face ≫ fan.affineToricChartι τ).opensRange = _
  calc
    _ = (fan.affineToricChartι (τ ⊓ σ)).opensRange := by
      apply Opens.ext
      exact congrArg
        (fun mapping : fan.affineToricChart (τ ⊓ σ) ⟶ fan.algebraicRealization =>
          Set.range mapping)
        (Fan.faceAffineToricSchemeMap_comp_affineToricChartι face)
    _ = _ := chart_opensRange_intersection fan τ σ

/-- The rational value of an arbitrary regular character monomial. -/
theorem chartCoordinateGerm_regularMonomial (fan : Fan i) (nonempty : Nonempty fan.cones)
    (τ : fan.cones) (m : dualSemigroup fan.lattice τ.val) :
    letI := toricSchemeIntegral fan nonempty
    chartCoordinateGerm fan nonempty τ (MonoidAlgebra.single (ofAdd m) (1 : ℂ)) =
      (rationalCharacterUnit fan nonempty m.val : fan.algebraicRealization.functionField) := by
  letI := toricSchemeIntegral fan nonempty
  rw [chartCoordinateGerm_torus]
  erw [faceAffineCoordinateRingMap_single fan.lattice
    (fan.isToricCone τ.property).salient.bot_isFaceOf m (1 : ℂ)]
  rfl

theorem toricBoundaryRegularEquation_germ (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (σ τ : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan τ
    fan.algebraicRealization.germToFunctionField (fan.affineToricChartι τ).opensRange
      (toricBoundaryRegularEquation fan regular σ τ) =
        (rationalCharacterUnit fan nonempty (toricChartBoundaryCharacter fan regular σ τ) :
          fan.algebraicRealization.functionField) := by
  exact chartCoordinateGerm_regularMonomial fan nonempty τ
    ⟨_, toricChartBoundaryCharacter_mem_dual fan regular σ τ⟩

theorem regularGerm_restrict {X : Scheme.{u}} [IsIntegral X]
    {U W : X.Opens} [Nonempty U] [Nonempty W] (included : W ≤ U) (s : Γ(X, U)) :
    X.germToFunctionField W (PoleClearing.restrictRing included s) =
      X.germToFunctionField U s :=
  X.presheaf.germ_res_apply _ _ _ _

/-- The regular local equations have exactly the Cartier unit transition. -/
theorem toricBoundaryRegularEquation_transition (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (σ τ υ : fan.cones) :
    PoleClearing.restrictRing (inf_le_left :
        (fan.affineToricChartι τ).opensRange ⊓ (fan.affineToricChartι υ).opensRange ≤
          (fan.affineToricChartι τ).opensRange) (toricBoundaryRegularEquation fan regular σ τ) =
      ((toricChartBoundaryAtlas fan regular σ).transition τ υ :
        Γ(fan.algebraicRealization,
          (fan.affineToricChartι τ).opensRange ⊓ (fan.affineToricChartι υ).opensRange)) *
        PoleClearing.restrictRing inf_le_right (toricBoundaryRegularEquation fan regular σ υ) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan τ
  letI := chartOpen_nonempty fan υ
  letI := nonempty_integral_open_intersection
    (fan.affineToricChartι τ).opensRange (fan.affineToricChartι υ).opensRange
  apply fan.algebraicRealization.germToFunctionField_injective
    ((fan.affineToricChartι τ).opensRange ⊓ (fan.affineToricChartι υ).opensRange)
  rw [map_mul, regularGerm_restrict, regularGerm_restrict,
    toricBoundaryRegularEquation_germ fan nonempty regular σ τ,
    toricBoundaryRegularEquation_germ fan nonempty regular σ υ]
  have hu := congrArg Units.val
    ((toricChartBoundaryAtlas fan regular σ).transition_germ nonempty τ υ)
  simp only [TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField_apply,
    Units.coe_map] at hu
  change fan.algebraicRealization.germToFunctionField
    ((fan.affineToricChartι τ).opensRange ⊓ (fan.affineToricChartι υ).opensRange)
    ((toricChartBoundaryAtlas fan regular σ).transition τ υ) =
    (rationalCharacterUnit fan nonempty
      (toricChartBoundaryCharacter fan regular σ τ - toricChartBoundaryCharacter fan regular σ υ) :
        fan.algebraicRealization.functionField) at hu
  rw [hu]
  exact (congrArg Units.val (rationalCharacterUnit_sub_mul fan nonempty
    (toricChartBoundaryCharacter fan regular σ τ)
    (toricChartBoundaryCharacter fan regular σ υ))).symm

end ToricPower

end
