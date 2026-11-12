module

public import ToricPower.DiagonalTargetRestriction
public import ToricPower.DiagonalLocalAugmentationForms
public import ToricPower.DivisorWeightTensorNaturality
public import ToricPower.SchemePullbackTensorCoherence
public import ToricPower.DiagonalAugmentationFrameTransport
public import ToricPower.DiagonalFactorFrameRestriction

/-!
# The coefficient of the actual diagonal augmentation

The zero Cartier sheaf is identified with the structure sheaf through its
specified rational-function inclusion. Tensor multiplication therefore has
the product of the two actual rational values. Restricting the two chosen
Cartier frames to an overlap gives the character with exponent
`-q_left - q_right`, independently of any choice of the zero-divisor frame.

Development source; the complete source and dependency chain must pass the
pinned Lean compiler before any verification claim is made.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement Opposite
open scoped TensorProduct

namespace ToricPower

universe u v

section TensorFrameSections

variable {X : Scheme.{u}}

/-- The inverse unit constraint sends one to the actual inserted pure
tensor `1 ⊗ 1`, rather than to an unspecified section of an isomorphic
rank-one sheaf. -/
theorem unitSheaf_leftUnitor_inv_one (U : (X).Opens) :
    Scheme.Modules.Hom.app (λ_ (SheafOfModules.unit X.ringCatSheaf)).inv U (1 : Γ(X, U)) =
      schemeTensorSection (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.unit X.ringCatSheaf) U (1 : Γ(X, U)) (1 : Γ(X, U)) := by
  have h := ConcreteCategory.congr_hom
    (Functor.LaxMonoidal.left_unitality_inv (Scheme.Modules.sectionsFunctor U)
      (SheafOfModules.unit X.ringCatSheaf)) (1 : Γ(X, U))
  rw [Scheme.Modules.sectionsFunctor_ε] at h
  replace h := h.symm
  change Scheme.Modules.Hom.app (λ_ (SheafOfModules.unit X.ringCatSheaf)).inv U
      (1 : Γ(X, U)) =
    (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U)
      (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf))
      ((1 : Γ(X, U)) ⊗ₜ[Γ(X, U)] (1 : Γ(X, U))) at h
  exact h

/-- A tensor frame, evaluated at one, is the actual sectionwise tensor
of the two frame sections. -/
theorem unitSheaf_tensor_frame_one {M N : X.Modules}
    (first : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (second : SheafOfModules.unit X.ringCatSheaf ⟶ N) (U : (X).Opens) :
    Scheme.Modules.Hom.app
        ((λ_ (SheafOfModules.unit X.ringCatSheaf)).inv ≫ (first ⊗ₘ second)) U (1 : Γ(X, U)) =
      schemeTensorSection M N U
        (Scheme.Modules.Hom.app first U (1 : Γ(X, U)))
        (Scheme.Modules.Hom.app second U (1 : Γ(X, U))) := by
  rw [schemeHom_comp_apply, unitSheaf_leftUnitor_inv_one]
  exact schemeTensorSection_naturality first second U (1 : Γ(X, U)) (1 : Γ(X, U))

/-- Multiplication on the unit sheaf has its specified value at one. -/
theorem unitSheaf_globalSectionsSmul_one (r : Γ(X, ⊤)) :
    Scheme.Modules.Hom.app
      (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r)
      ⊤ (1 : Γ(X, ⊤)) = r := by
  rw [Scheme.Modules.globalSectionsSmul_app]
  change X.presheaf.map (𝟙 (⊤ : X.Opens)).op r * 1 = r
  simp

/-- The genuine tensor map of actual restriction carries the two
restricted sections to their literal pure tensor over the image open. -/
theorem restriction_tensor_section {Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (M N : Y.Modules) (U : (X).Opens)
    (s : Γ(M, j ''ᵁ U)) (t : Γ(N, j ''ᵁ U)) :
    Scheme.Modules.Hom.app
        (Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor j) M N) U
        (schemeTensorSection (M.restrict j) (N.restrict j) U s t) =
      schemeTensorSection M N (j ''ᵁ U) s t := by
  exact TauCeti.SheafOfModules.pushforward_μ_app_tmul
    (Scheme.Modules.restrictRingCatSheafHom j) M N (op U) s t

/-- Transporting an open by an actual equality transports a pure tensor
by transporting its two actual sections. -/
theorem schemeTensorSection_eqToHom (M N : X.Modules) {U W : (X).Opens}
    (h : U = W) (s : Γ(M, W)) (t : Γ(N, W)) :
    (M ⊗ N).presheaf.map (eqToHom h).op (schemeTensorSection M N W s t) =
      schemeTensorSection M N U
        (M.presheaf.map (eqToHom h).op s) (N.presheaf.map (eqToHom h).op t) := by
  subst W
  simp

/-- A sheaf morphism respects the explicit equality transport between
two equal opens, on the actual section modules. -/
theorem schemeHom_app_eqToHom {M N : X.Modules} (f : M ⟶ N)
    {U W : (X).Opens} (h : U = W) (s : Γ(M, W)) :
    Scheme.Modules.Hom.app f U (M.presheaf.map (eqToHom h).op s) =
      N.presheaf.map (eqToHom h).op (Scheme.Modules.Hom.app f W s) := by
  subst W
  simp

end TensorFrameSections

section RationalNormalization

variable {X : Scheme.{u}} [IsIntegral X]

/-- Equality transport of Cartier sheaves preserves the specified
rational inclusion, also in the inverse direction. -/
theorem cartierEqToIso_inv_sheafι
    {D E : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X} (h : D = E) :
    (eqToIso (congrArg TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheaf h)).inv ≫
      D.sheafι = E.sheafι := by
  subst E
  simp

/-- The rational value of a Cartier section is unchanged by actual
restriction to a nonempty smaller open. -/
theorem cartierSheaf_rationalValue_restrict
    (D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X)
    {U W : (X).Opens} [Nonempty U] [Nonempty W] (h : U ≤ W)
    (s : Γ(D.sheaf, W)) :
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
        (Scheme.Modules.Hom.app D.sheafι U
          (D.sheaf.presheaf.map (homOfLE h).op s)) =
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv W
        (Scheme.Modules.Hom.app D.sheafι W s) := by
  have naturality := ConcreteCategory.congr_hom
    (D.sheafι.mapPresheaf.naturality (homOfLE h).op) s
  change Scheme.Modules.Hom.app D.sheafι U
      (D.sheaf.presheaf.map (homOfLE h).op s) =
    (TauCeti.AlgebraicGeometry.Scheme.rationalFunctions X).presheaf.map
      (homOfLE h).op (Scheme.Modules.Hom.app D.sheafι W s) at naturality
  rw [naturality, TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map]

end RationalNormalization

section ToricValues

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}

/-- The specified zero-coefficient Cartier trivialization identifies its
rational inclusion with the actual inclusion of regular functions.
No equality `coneDivisorCharacter 0 = 0` is used. -/
@[reassoc]
theorem invariantCartierZeroSheafIso_inv_toRationalFunctions
    (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) :
    letI := toricSchemeIntegral fan nonempty
    (invariantCartierZeroSheafIso fan nonempty regular).inv ≫
        TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions fan.algebraicRealization =
      (invariantCartierDivisor fan nonempty regular 0).sheafι := by
  letI := toricSchemeIntegral fan nonempty
  unfold invariantCartierZeroSheafIso
  rw [Iso.trans_inv, Category.assoc,
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.unitIsoSheafPrincipalCartierDivisor_inv_toRationalFunctions,
    Units.val_one, TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsMul_one,
    Category.comp_id]
  exact cartierEqToIso_inv_sheafι
    ((TauCeti.AlgebraicGeometry.Scheme.principalCartierDivisor_one
      fan.algebraicRealization).trans
      (invariantCartierDivisor_zero fan nonempty regular).symm)

/-- The inverse zero-divisor frame preserves the exact rational value of
each section, as a regular function on the same actual open. -/
theorem invariantCartierZeroSheafIso_inv_value
    (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (U : fan.algebraicRealization.Opens) [Nonempty U]
    (s : letI := toricSchemeIntegral fan nonempty;
      Γ((invariantCartierDivisor fan nonempty regular 0).sheaf, U)) :
    letI := toricSchemeIntegral fan nonempty
    fan.algebraicRealization.germToFunctionField U
        (Scheme.Modules.Hom.app (invariantCartierZeroSheafIso fan nonempty regular).inv U s) =
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
        (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular 0).sheafι U s) := by
  letI := toricSchemeIntegral fan nonempty
  rw [← TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_toRationalFunctions_app,
    ← schemeHom_comp_apply, invariantCartierZeroSheafIso_inv_toRationalFunctions]

/-- The actual chosen Cartier basis section over a cone open. -/
def toricCartierFrameSection
    (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (σ : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    Γ((invariantCartierDivisor fan nonempty regular b).sheaf,
      (fan.affineToricChartι σ).opensRange) := by
  letI := toricSchemeIntegral fan nonempty
  exact (invariantCartierSheafChartTrivialization fan nonempty regular b σ).hom.val.app
    (op (Over.mk (𝟙 (fan.affineToricChartι σ).opensRange)))
    (1 : Γ(fan.algebraicRealization, (fan.affineToricChartι σ).opensRange))

/-- Its rational value is the reciprocal of the actual chosen local
equation character, including every torus direction. -/
theorem toricCartierFrameSection_value
    (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (σ : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan σ
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv
        (fan.affineToricChartι σ).opensRange
        (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular b).sheafι
          (fan.affineToricChartι σ).opensRange
          (toricCartierFrameSection fan nonempty regular b σ)) =
      (rationalCharacterUnit fan nonempty (-coneDivisorCharacter fan regular b σ) :
        fan.algebraicRealization.functionField) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan σ
  let atlas := (invariantDivisorCharacterAtlas fan regular b).cartierEquationAtlas nonempty
  have value := atlas.chartTrivialization_value σ
    (1 : Γ(fan.algebraicRealization, (fan.affineToricChartι σ).opensRange))
  simp only [map_one, mul_one] at value
  rw [rationalCharacterUnit_neg]
  exact value

end ToricValues

section DiagonalValues

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "X" => fan.algebraicRealization
local notation "A" => fanArrangementMatrix fan basis rays

/-- The global augmentation's actual tensor multiplication has exactly
the product of the two rational section values. This calculation uses
the specified zero-Cartier isomorphism, including its normalization. -/
theorem diagonalTensorToStructure_value {d : ℕ} (c : NormalizedCell A d)
    (U : (X).Opens) [Nonempty U]
    (left : Γ(diagonalLeftSheaf fan nonempty regular basis rays c, U))
    (right : Γ(diagonalRightSheaf fan nonempty regular basis rays c, U)) :
    letI := toricSchemeIntegral fan nonempty
    (X).germToFunctionField U
        (Scheme.Modules.Hom.app (diagonalTensorToStructure fan nonempty regular basis rays c) U
          (schemeTensorSection _ _ U left right)) =
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
          (Scheme.Modules.Hom.app
            (invariantCartierDivisor fan nonempty regular
              (diagonalLeftCoefficients fan basis rays c)).sheafι U left) *
        TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
          (Scheme.Modules.Hom.app
            (invariantCartierDivisor fan nonempty regular
              (diagonalRightCoefficients fan basis rays c)).sheafι U right) := by
  letI := toricSchemeIntegral fan nonempty
  dsimp only [diagonalTensorToStructure]
  rw [schemeHom_comp_apply, schemeHom_comp_apply,
    invariantCartierZeroSheafIso_inv_value,
    toricCartierMonomialMap_value, rationalCharacterUnit_zero, Units.val_one, one_mul]
  exact invariantCartierTensorIso_value fan nonempty regular
    (diagonalLeftCoefficients fan basis rays c)
    (diagonalRightCoefficients fan basis rays c) U left right

/-- Restrict the two chosen cone frames to any common nonempty open.
Their tensor image under the actual global diagonal multiplication has
rational character `χ^(-q_left-q_right)`. -/
theorem diagonalTensorToStructure_restricted_frames_value
    {d : ℕ} (c : NormalizedCell A d) (σ τ : fan.cones)
    (U : (X).Opens) [Nonempty U]
    (left_le : U ≤ (fan.affineToricChartι σ).opensRange)
    (right_le : U ≤ (fan.affineToricChartι τ).opensRange) :
    letI := toricSchemeIntegral fan nonempty
    (X).germToFunctionField U
        (Scheme.Modules.Hom.app (diagonalTensorToStructure fan nonempty regular basis rays c) U
          (schemeTensorSection _ _ U
            ((diagonalLeftSheaf fan nonempty regular basis rays c).presheaf.map
              (homOfLE left_le).op
              (toricCartierFrameSection fan nonempty regular
                (diagonalLeftCoefficients fan basis rays c) σ))
            ((diagonalRightSheaf fan nonempty regular basis rays c).presheaf.map
              (homOfLE right_le).op
              (toricCartierFrameSection fan nonempty regular
                (diagonalRightCoefficients fan basis rays c) τ)))) =
      (rationalCharacterUnit fan nonempty
        (-coneDivisorCharacter fan regular (diagonalLeftCoefficients fan basis rays c) σ -
          coneDivisorCharacter fan regular (diagonalRightCoefficients fan basis rays c) τ) :
        (X).functionField) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan σ
  letI := chartOpen_nonempty fan τ
  rw [diagonalTensorToStructure_value]
  dsimp only [diagonalLeftSheaf, diagonalRightSheaf]
  rw [cartierSheaf_rationalValue_restrict, cartierSheaf_rationalValue_restrict,
    toricCartierFrameSection_value, toricCartierFrameSection_value,
    sub_eq_add_neg, rationalCharacterUnit_add, Units.val_mul]

/-- The actual intersection chart maps into the first cone open. -/
theorem toricOverlapChartOpen_le_left (σ τ : fan.cones) :
    (fan.affineToricChartι (σ ⊓ τ)).opensRange ≤ (fan.affineToricChartι σ).opensRange := by
  change Set.range (fan.affineToricChartι (σ ⊓ τ)) ⊆ Set.range (fan.affineToricChartι σ)
  rintro _ ⟨x, rfl⟩
  refine ⟨fan.affineToricOverlapLeft σ τ x, ?_⟩
  rw [← Scheme.Hom.comp_apply, fan.affineToricOverlapLeft_comp_affineToricChartι]
  rfl

/-- The actual intersection chart maps into the second cone open. -/
theorem toricOverlapChartOpen_le_right (σ τ : fan.cones) :
    (fan.affineToricChartι (σ ⊓ τ)).opensRange ≤ (fan.affineToricChartι τ).opensRange := by
  change Set.range (fan.affineToricChartι (σ ⊓ τ)) ⊆ Set.range (fan.affineToricChartι τ)
  rintro _ ⟨x, rfl⟩
  refine ⟨fan.affineToricOverlapRight σ τ x, ?_⟩
  rw [← Scheme.Hom.comp_apply, fan.affineToricOverlapRight_comp_affineToricChartι]
  rfl

/-- The literal pure tensor of the two cone frames after restricting
both actual sheaf sections to the actual overlap open. -/
def diagonalOverlapTensorFrameSection {d : ℕ} (c : NormalizedCell A d)
    (σ τ : fan.cones) :
    Γ(diagonalLeftSheaf fan nonempty regular basis rays c ⊗
        diagonalRightSheaf fan nonempty regular basis rays c,
      (fan.affineToricChartι (σ ⊓ τ)).opensRange) :=
  schemeTensorSection _ _ _
    ((diagonalLeftSheaf fan nonempty regular basis rays c).presheaf.map
      (homOfLE (toricOverlapChartOpen_le_left fan σ τ)).op
      (toricCartierFrameSection fan nonempty regular
        (diagonalLeftCoefficients fan basis rays c) σ))
    ((diagonalRightSheaf fan nonempty regular basis rays c).presheaf.map
      (homOfLE (toricOverlapChartOpen_le_right fan σ τ)).op
      (toricCartierFrameSection fan nonempty regular
        (diagonalRightCoefficients fan basis rays c) τ))

/-- The actual tensor augmentation on the actual overlap frame is the
specified regular overlap monomial. Germ injectivity upgrades the
rational calculation to equality of actual regular sections. -/
theorem diagonalTensorToStructure_overlap_frames
    (c : NormalizedCell A 0) (σ τ : fan.cones) :
    Scheme.Modules.Hom.app (diagonalTensorToStructure fan nonempty regular basis rays c)
        (fan.affineToricChartι (σ ⊓ τ)).opensRange
        (diagonalOverlapTensorFrameSection fan nonempty regular basis rays c σ τ) =
      chartCoordinateSectionsEquiv fan (σ ⊓ τ)
        (diagonalVertexCoefficient fan regular basis rays σ τ c) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan (σ ⊓ τ)
  apply (X).germToFunctionField_injective (fan.affineToricChartι (σ ⊓ τ)).opensRange
  rw [diagonalOverlapTensorFrameSection,
    diagonalTensorToStructure_restricted_frames_value]
  change _ = chartCoordinateGerm fan nonempty (σ ⊓ τ)
    (diagonalVertexCoefficient fan regular basis rays σ τ c)
  have germ := chartCoordinateGerm_monomial fan nonempty (σ ⊓ τ)
    (diagonalVertexOverlapCharacter fan regular basis rays σ τ c).val
    (diagonalVertexOverlapCharacter fan regular basis rays σ τ c).property
  exact (congrArg (fun m => (rationalCharacterUnit fan nonempty m :
    fan.algebraicRealization.functionField))
    (diagonalVertexOverlapCharacter_val fan regular basis rays σ τ c).symm).trans germ.symm

variable (σ τ : fan.cones)

local notation "overlap" => fan.affineToricChartι (σ ⊓ τ)
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "B" => affineCoordinateRing fan.lattice (σ.val ⊓ τ.val)
local notation "g" => Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ))

/-- The actual local adjoint in the actual product Cartier frame sends
the unit section to the precise affine overlap monomial. Every pullback,
restriction, tensor insertion, and zero-divisor normalization has been
retained in this calculation. -/
theorem diagonalChartFrameAdjunct_normalized_one (c : NormalizedCell A 0) :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackObjUnitIso g).inv ≫
          diagonalChartFrameAdjunct fan nonempty regular basis rays σ τ c) ⊤
        (1 : Γ(fan.affineToricChart (σ ⊓ τ), ⊤)) =
      (Scheme.ΓSpecIso (.of B)).inv
        (diagonalVertexCoefficient fan regular basis rays σ τ c) := by
  letI := toricSchemeIntegral fan nonempty
  rw [diagonalChartFrameAdjunct_normalized, ← Category.assoc,
    schemeHom_comp_apply, schemeHom_comp_apply, schemeHom_comp_apply,
    ]
  erw [unitSheaf_tensor_frame_one
      (diagonalRestrictedFirstFrameMap fan nonempty regular basis rays σ τ c)
      (diagonalRestrictedSecondFrameMap fan nonempty regular basis rays σ τ c) ⊤]
  erw [restriction_tensor_section overlap
      (diagonalLeftSheaf fan nonempty regular basis rays c)
      (diagonalRightSheaf fan nonempty regular basis rays c) ⊤]
  erw [diagonalRestrictedFirstFrameMap_top fan nonempty regular basis rays σ τ c,
    diagonalRestrictedSecondFrameMap_top fan nonempty regular basis rays σ τ c]
  erw [← schemeTensorSection_eqToHom
    (diagonalLeftSheaf fan nonempty regular basis rays c)
    (diagonalRightSheaf fan nonempty regular basis rays c)
    (overlap).image_top_eq_opensRange]
  erw [restrictFunctor_map_app overlap
    (diagonalTensorToStructure fan nonempty regular basis rays c) ⊤]
  erw [schemeHom_app_eqToHom
    (diagonalTensorToStructure fan nonempty regular basis rays c)
    (overlap).image_top_eq_opensRange]
  erw [restrictUnitIso_app overlap ⊤]
  change ((overlap).appIso ⊤).hom
      ((X).presheaf.map (eqToHom (overlap).image_top_eq_opensRange).op
        (Scheme.Modules.Hom.app
          (diagonalTensorToStructure fan nonempty regular basis rays c) (overlap).opensRange
          (diagonalOverlapTensorFrameSection fan nonempty regular basis rays c σ τ))) = _
  rw [diagonalTensorToStructure_overlap_frames]
  simp only [chartCoordinateSectionsEquiv, RingEquiv.trans_apply,
    commRingIsoToRingEquiv_apply, openImmersion_appIso_top_sections]
  rfl

/-- Equality of the actual normalized unit-sheaf maps follows from the
computed value at one. The scalar is the actual inverse Γ–Spec image of
the actual overlap coordinate-ring monomial. -/
theorem diagonalChartFrameAdjunct_normalized_scalar (c : NormalizedCell A 0) :
    (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        diagonalChartFrameAdjunct fan nonempty regular basis rays σ τ c =
      Scheme.Modules.globalSectionsSmul
        (SheafOfModules.unit (fan.affineToricChart (σ ⊓ τ)).ringCatSheaf)
        ((Scheme.ΓSpecIso (.of B)).inv
          (diagonalVertexCoefficient fan regular basis rays σ τ c)) := by
  apply unitSheafHom_ext_top
  exact (diagonalChartFrameAdjunct_normalized_one fan nonempty regular basis rays σ τ c).trans
    (unitSheaf_globalSectionsSmul_one
      ((Scheme.ΓSpecIso (.of B)).inv
        (diagonalVertexCoefficient fan regular basis rays σ τ c))).symm

/-- The unnormalized actual adjoint is the structure-sheaf pullback
comparison followed by multiplication by the calculated coefficient. -/
theorem diagonalChartFrameAdjunct_scalar (c : NormalizedCell A 0) :
    diagonalChartFrameAdjunct fan nonempty regular basis rays σ τ c =
      (Scheme.Modules.pullbackObjUnitIso g).hom ≫
        Scheme.Modules.globalSectionsSmul
          (SheafOfModules.unit (fan.affineToricChart (σ ⊓ τ)).ringCatSheaf)
          ((Scheme.ΓSpecIso (.of B)).inv
            (diagonalVertexCoefficient fan regular basis rays σ τ c)) := by
  apply (cancel_epi (Scheme.Modules.pullbackObjUnitIso g).inv).mp
  rw [Iso.inv_hom_id_assoc]
  exact diagonalChartFrameAdjunct_normalized_scalar fan nonempty regular basis rays σ τ c

/-- **The literal global augmentation coefficient.** The actual global
augmentation in the actual product Cartier frame is the actual affine
adjunct of multiplication by `χ^(-q_left-q_right)`. No coefficient,
frame-compatibility, or base-change assertion is assumed in the theorem. -/
@[reassoc]
theorem diagonalProductAugmentation_chart_frame (c : NormalizedCell A 0) :
    (diagonalProductCartierFrame fan nonempty regular basis rays σ τ c).hom ≫
        (Scheme.Modules.pullback chart).map
          (diagonalProductAugmentation fan nonempty regular basis rays c) ≫
        (diagonalStructureChartIso fan basis rays σ τ).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((Scheme.Modules.pullbackObjUnitIso g).hom ≫
          Scheme.Modules.globalSectionsSmul
            (SheafOfModules.unit (Spec (.of B)).ringCatSheaf)
            ((Scheme.ΓSpecIso (.of B)).inv
              (diagonalVertexCoefficient fan regular basis rays σ τ c))) := by
  rw [diagonalProductAugmentation_chart_frame_adjunct, diagonalChartFrameAdjunct_scalar]
  rfl

end DiagonalValues

end ToricPower

end
