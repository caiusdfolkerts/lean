module

public import ToricPower.DivisorWeightCartierAtlas

/-!
# Actual Cartier sections and their character coefficients on every cone

On each smooth chart, the actual Cartier sheaf sections are identified
with finitely supported coefficients on exactly the admissible integral
characters. The identification is computed in the actual function field
and commutes with every face restriction. No maximal-cone or completeness
hypothesis occurs.

These are the sheaf-side inputs for the weight decomposition of the
finite affine Čech complex. This file by itself does not assert the final
reduced simplicial cohomology comparison.

The file is checked by the pinned Lean compiler with its complete local dependency closure.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidAlgebra
open TauCeti.Toric

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

private theorem openImmersionGerm_injective {Source Target : Scheme.{u}}
    [IsIntegral Target] [Nonempty Source] (inclusion : Source ⟶ Target)
    [IsOpenImmersion inclusion] : Function.Injective (openImmersionGerm inclusion) := by
  letI : Nonempty inclusion.opensRange := by
    obtain ⟨point⟩ := (inferInstance : Nonempty Source)
    exact ⟨⟨_, ⟨point, rfl⟩⟩⟩
  exact (Target.germToFunctionField_injective inclusion.opensRange).comp
    (IsOpenImmersion.ΓIsoTop inclusion).commRingCatIsoToRingEquiv.injective

private theorem denseTorusCoordinateRingEquiv_face (fan : Fan i) (cone : fan.cones)
    (p : affineCoordinateRing fan.lattice cone.val) :
    denseTorusCoordinateRingEquiv fan.lattice
      (faceAffineCoordinateRingMap fan.lattice
        ((fan.isToricCone cone.property).salient.bot_isFaceOf) p) =
      mapDomain (dualSemigroup fan.lattice cone.val).subtype.toMultiplicative p := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, mapDomain_add]
  | single m c =>
      change denseTorusCoordinateRingEquiv fan.lattice
        (faceAffineCoordinateRingMap fan.lattice
          ((fan.isToricCone cone.property).salient.bot_isFaceOf)
          (single (Multiplicative.ofAdd m.toAdd) c)) = _
      rw [faceAffineCoordinateRingMap_single fan.lattice
          ((fan.isToricCone cone.property).salient.bot_isFaceOf) m.toAdd c,
        denseTorusCoordinateRingEquiv_single,
        mapDomain_single]
      rfl

theorem toricCechChartOpen_mono (fan : Fan i) {face cone : fan.cones}
    (included : face ≤ cone) :
    (fan.affineToricChartι face).opensRange ≤ (fan.affineToricChartι cone).opensRange := by
  have same := chart_opensRange_intersection fan face cone
  rw [inf_eq_left.mpr included] at same
  exact same.le.trans inf_le_right

/-- The intrinsic Laurent algebra embeds in the actual function field
via the actual dense-torus chart. -/
def toricIntrinsicLaurentGerm (fan : Fan i) (nonempty : Nonempty fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    MonoidAlgebra ℂ (Multiplicative (N →+ ℤ)) →+* fan.algebraicRealization.functionField := by
  letI := toricSchemeIntegral fan nonempty
  exact (toricLaurentGerm fan nonempty).comp
    (denseTorusCoordinateRingEquiv fan.lattice).symm.toRingHom

theorem toricIntrinsicLaurentGerm_injective (fan : Fan i)
    (nonempty : Nonempty fan.cones) :
    Function.Injective (toricIntrinsicLaurentGerm fan nonempty) := by
  letI := toricSchemeIntegral fan nonempty
  have dense : Function.Injective (toricLaurentGerm fan nonempty) :=
    (openImmersionGerm_injective (fan.denseTorusι nonempty)).comp
      (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice ⊥)).injective
  exact dense.comp (denseTorusCoordinateRingEquiv fan.lattice).symm.injective

theorem chartCoordinateGerm_eq_intrinsicLaurent (fan : Fan i)
    (nonempty : Nonempty fan.cones) (cone : fan.cones)
    (p : affineCoordinateRing fan.lattice cone.val) :
    chartCoordinateGerm fan nonempty cone p =
      toricIntrinsicLaurentGerm fan nonempty
        (mapDomain (dualSemigroup fan.lattice cone.val).subtype.toMultiplicative p) := by
  rw [← denseTorusCoordinateRingEquiv_face]
  change chartCoordinateGerm fan nonempty cone p =
    toricLaurentGerm fan nonempty ((denseTorusCoordinateRingEquiv fan.lattice).symm
      ((denseTorusCoordinateRingEquiv fan.lattice)
        (faceAffineCoordinateRingMap fan.lattice
          ((fan.isToricCone cone.property).salient.bot_isFaceOf) p)))
  rw [AlgEquiv.symm_apply_apply]
  exact chartCoordinateGerm_torus fan nonempty cone p

theorem toricIntrinsicLaurentGerm_character (fan : Fan i)
    (nonempty : Nonempty fan.cones) (m : N →+ ℤ) :
    letI := toricSchemeIntegral fan nonempty
    toricIntrinsicLaurentGerm fan nonempty (single (Multiplicative.ofAdd m) 1) =
      (rationalCharacterUnit fan nonempty m : fan.algebraicRealization.functionField) := by
  letI := toricSchemeIntegral fan nonempty
  change toricLaurentGerm fan nonempty ((denseTorusCoordinateRingEquiv fan.lattice).symm
    (single (Multiplicative.ofAdd m) 1)) = _
  rw [denseTorusCoordinateRingEquiv_symm_single, denseTorusDualEquiv_symm_apply]
  rfl

/-- The literal admissible intrinsic character type for the actual chart. -/
abbrev ToricChartDivisorWeight (fan : Fan i) (b : fan.Ray → ℤ) (cone : fan.cones) :=
  ToricDivisorWeight fan.lattice (fan.isToricCone cone.property)
    (coneDivisorCoefficients fan b cone)

/-- Adding the actual local equation character identifies admissible
divisor characters with regular chart monomials. -/
def toricChartDivisorShiftEquiv (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (cone : fan.cones) :
    ToricChartDivisorWeight fan b cone ≃ Multiplicative (dualSemigroup fan.lattice cone.val) where
  toFun m := Multiplicative.ofAdd
    ⟨coneDivisorCharacter fan regular b cone + m.val, by
      rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice (fan.isToricCone cone.property)]
      intro ρ
      simpa only [AddMonoidHom.add_apply, coneDivisorCharacter_ray] using m.property ρ⟩
  invFun m := ⟨m.toAdd.val - coneDivisorCharacter fan regular b cone, by
    intro ρ
    have hm := (mem_dualSemigroup_iff_primitiveGenerator fan.lattice
      (fan.isToricCone cone.property) m.toAdd.val).mp m.toAdd.property ρ
    simp only [AddMonoidHom.sub_apply, coneDivisorCharacter_ray]
    omega⟩
  left_inv m := by
    apply Subtype.ext
    change (coneDivisorCharacter fan regular b cone + m.val) -
      coneDivisorCharacter fan regular b cone = m.val
    abel
  right_inv m := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    change coneDivisorCharacter fan regular b cone +
      (m.toAdd.val - coneDivisorCharacter fan regular b cone) = m.toAdd.val
    abel

/-- All coefficient families, with their literal support condition, give
the entire ordinary chart coordinate module after multiplying by the
Cartier equation. -/
def toricDivisorCoefficientRingEquiv (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (cone : fan.cones) :
    (ToricChartDivisorWeight fan b cone →₀ ℂ) ≃+
      affineCoordinateRing fan.lattice cone.val :=
  (Finsupp.domLCongr (R := ℂ) (toricChartDivisorShiftEquiv fan regular b cone)).toAddEquiv.trans
    MonoidAlgebra.coeffAddEquiv.symm

@[simp]
theorem toricDivisorCoefficientRingEquiv_single (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (cone : fan.cones)
    (m : ToricChartDivisorWeight fan b cone) (a : ℂ) :
    toricDivisorCoefficientRingEquiv fan regular b cone (Finsupp.single m a) =
      single (toricChartDivisorShiftEquiv fan regular b cone m) a := by
  simp [toricDivisorCoefficientRingEquiv, Finsupp.domLCongr_single]

/-- The actual Cartier frame on the chart open, evaluated on actual
sections. This is an additive equivalence, not a newly defined section
space. -/
def toricDivisorOpenFrameEquiv (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    affineCoordinateRing fan.lattice cone.val ≃+
      Γ((invariantCartierDivisor fan nonempty regular b).sheaf,
        (fan.affineToricChartι cone).opensRange) := by
  letI := toricSchemeIntegral fan nonempty
  exact (chartCoordinateSectionsEquiv fan cone).toAddEquiv.trans
    (((SheafOfModules.evaluation
      (fan.algebraicRealization.ringCatSheaf.over (fan.affineToricChartι cone).opensRange)
      (op (Over.mk (𝟙 (fan.affineToricChartι cone).opensRange)))).mapIso
        (invariantCartierSheafChartTrivialization fan nonempty regular b cone)).toLinearEquiv.toAddEquiv)

/-- Every actual section has a unique finite character expansion, with
exactly the divisor's ray inequalities as its support condition. -/
def toricDivisorSectionCoefficientsEquiv (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    (ToricChartDivisorWeight fan b cone →₀ ℂ) ≃+
      Γ((invariantCartierDivisor fan nonempty regular b).sheaf,
        (fan.affineToricChartι cone).opensRange) :=
  (toricDivisorCoefficientRingEquiv fan regular b cone).trans
    (toricDivisorOpenFrameEquiv fan nonempty regular b cone)

/-- The coefficient basis vector is literally the rational monomial
`a χ^m` under the actual Cartier-sheaf inclusion. -/
theorem toricDivisorSectionCoefficientsEquiv_single_value (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (cone : fan.cones)
    (m : ToricChartDivisorWeight fan b cone) (a : ℂ) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan cone
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (fan.affineToricChartι cone).opensRange
      (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular b).sheafι
        (fan.affineToricChartι cone).opensRange
        (toricDivisorSectionCoefficientsEquiv fan nonempty regular b cone (Finsupp.single m a))) =
      toricIntrinsicLaurentGerm fan nonempty (single (Multiplicative.ofAdd m.val) a) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  let atlas := (invariantDivisorCharacterAtlas fan regular b).cartierEquationAtlas nonempty
  letI : Nonempty (atlas.chart cone) := atlas.nonempty_chart cone
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv (atlas.chart cone)
    (Scheme.Modules.Hom.app atlas.cartierDivisor.sheafι (atlas.chart cone)
      ((atlas.chartTrivialization cone).hom.val.app
        (op (Over.mk (𝟙 (atlas.chart cone))))
        (chartCoordinateSectionsEquiv fan cone
          (toricDivisorCoefficientRingEquiv fan regular b cone (Finsupp.single m a))))) = _
  rw [toricDivisorCoefficientRingEquiv_single, atlas.chartTrivialization_value]
  change (((rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b cone))⁻¹ :
      fan.algebraicRealization.functionFieldˣ) : fan.algebraicRealization.functionField) *
      chartCoordinateGerm fan nonempty cone
        (single (toricChartDivisorShiftEquiv fan regular b cone m) a) = _
  rw [chartCoordinateGerm_eq_intrinsicLaurent, mapDomain_single,
    ← rationalCharacterUnit_neg, ← toricIntrinsicLaurentGerm_character, ← map_mul]
  congr 1
  rw [single_mul_single, one_mul]
  congr 1
  change -coneDivisorCharacter fan regular b cone +
    (coneDivisorCharacter fan regular b cone + m.val) = m.val
  abel

/-- The admissible characters restrict to a face without changing the
character. The proof uses the actual embedding of face rays. -/
def toricDivisorWeightFaceMap (fan : Fan i) (b : fan.Ray → ℤ)
    {face cone : fan.cones} (included : face ≤ cone) :
    ToricChartDivisorWeight fan b cone → ToricChartDivisorWeight fan b face :=
  fun m => ⟨m.val, by
    intro ρ
    let hface := fan.isFaceOf_of_le cone.property face.property included
    have h := m.property (ToricRay.faceEmbedding hface ρ)
    rw [coneDivisorCoefficients_face,
      primitiveGenerator_face fan.lattice (fan.isToricCone cone.property)
        (fan.isToricCone face.property) hface ρ] at h
    exact h⟩

/-- The actual restriction of the Cartier sheaf is the literal inclusion
of the same character coefficients on every face. -/
theorem toricDivisorSectionCoefficientsEquiv_restrict (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (b : fan.Ray → ℤ)
    {face cone : fan.cones} (included : face ≤ cone)
    (p : ToricChartDivisorWeight fan b cone →₀ ℂ) :
    letI := toricSchemeIntegral fan nonempty
    (invariantCartierDivisor fan nonempty regular b).sheaf.presheaf.map
      (homOfLE (toricCechChartOpen_mono fan included)).op
      (toricDivisorSectionCoefficientsEquiv fan nonempty regular b cone p) =
    toricDivisorSectionCoefficientsEquiv fan nonempty regular b face
      (Finsupp.mapDomain (toricDivisorWeightFaceMap fan b included) p) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan face
  letI := chartOpen_nonempty fan cone
  let D := invariantCartierDivisor fan nonempty regular b
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Finsupp.mapDomain_add, hp, hq]
  | single m a =>
    rw [Finsupp.mapDomain_single]
    apply D.sheafι_app_injective (fan.affineToricChartι face).opensRange
    apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv
      (fan.affineToricChartι face).opensRange).injective
    have naturality := ConcreteCategory.congr_hom
      (D.sheafι.mapPresheaf.naturality (homOfLE (toricCechChartOpen_mono fan included)).op)
      (toricDivisorSectionCoefficientsEquiv fan nonempty regular b cone (Finsupp.single m a))
    simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at naturality
    rw [naturality, TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map,
      toricDivisorSectionCoefficientsEquiv_single_value,
      toricDivisorSectionCoefficientsEquiv_single_value]
    rfl

end ToricPower
