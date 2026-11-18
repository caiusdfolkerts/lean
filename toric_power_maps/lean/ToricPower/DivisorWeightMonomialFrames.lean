module

public import ToricPower.DivisorWeightMonomialMaps
public import ToricPower.DivisorWeightGlobalFrames

/-!
# Actual monomial morphisms in the actual affine Cartier frames

The frame of `O(b)` on a regular cone is the rational character `χ^(-q_b)`.
Consequently multiplication by `χ^m` has affine coefficient
`χ^(q_c + m - q_b)` as a morphism from `O(b)` to `O(c)`. The equalities
below concern the actual sheaf morphisms and the actual affine coordinate
ring, not a separately postulated matrix representation.

Development source: these proof bodies require the pinned compiler before
any verification claim is made.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TauCeti.Toric MonoidAlgebra TopologicalSpace Opposite

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The regular chart monomial obtained after normalizing both Cartier
frames. Its semigroup membership is proved from the ray inequalities. -/
def normalizedToricMonomial (fan : Fan i) (regular : fan.IsRegular)
    (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ : fan.Ray,
      0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (cone : fan.cones) : affineCoordinateRing fan.lattice cone.val :=
  single (Multiplicative.ofAdd
    ⟨normalizedToricMonomialCharacter fan regular b c character cone,
      normalizedToricMonomialCharacter_mem fan regular b c character nonnegative cone⟩) 1

theorem normalizedToricMonomial_germ (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ : fan.Ray,
      0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    chartCoordinateGerm fan nonempty cone
      (normalizedToricMonomial fan regular b c character nonnegative cone) =
      (rationalCharacterUnit fan nonempty
        (normalizedToricMonomialCharacter fan regular b c character cone) :
          fan.algebraicRealization.functionField) := by
  letI := toricSchemeIntegral fan nonempty
  exact chartCoordinateGerm_monomial fan nonempty cone _ _

theorem normalizedToricMonomial_ratio (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    rationalCharacterUnit fan nonempty
        (normalizedToricMonomialCharacter fan regular b c character cone) =
      rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular c cone) *
        rationalCharacterUnit fan nonempty character *
        (rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b cone))⁻¹ := by
  letI := toricSchemeIntegral fan nonempty
  rw [normalizedToricMonomialCharacter, sub_eq_add_neg,
    rationalCharacterUnit_add, rationalCharacterUnit_add, rationalCharacterUnit_neg]

/-- Multiplication by the character, evaluated on the actual Cartier
frame over the chart open, has the displayed normalized coefficient. -/
theorem toricCartierMonomialMap_frame_sections (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ : fan.Ray,
      0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (cone : fan.cones) (a : affineCoordinateRing fan.lattice cone.val) :
    letI := toricSchemeIntegral fan nonempty
    let U := (fan.affineToricChartι cone).opensRange
    Scheme.Modules.Hom.app
      (toricCartierMonomialMap fan nonempty regular b c character nonnegative) U
      ((invariantCartierSheafChartTrivialization fan nonempty regular b cone).hom.val.app
        (op (Over.mk (𝟙 U))) (chartCoordinateSectionsEquiv fan cone a)) =
    (invariantCartierSheafChartTrivialization fan nonempty regular c cone).hom.val.app
      (op (Over.mk (𝟙 U)))
      (chartCoordinateSectionsEquiv fan cone
        (a * normalizedToricMonomial fan regular b c character nonnegative cone)) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  let U := (fan.affineToricChartι cone).opensRange
  let sourceAtlas := (invariantDivisorCharacterAtlas fan regular b).cartierEquationAtlas nonempty
  let targetAtlas := (invariantDivisorCharacterAtlas fan regular c).cartierEquationAtlas nonempty
  apply (invariantCartierDivisor fan nonempty regular c).sheafι_app_injective U
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U).injective
  rw [toricCartierMonomialMap_value]
  erw [sourceAtlas.chartTrivialization_value, targetAtlas.chartTrivialization_value]
  change (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) *
      ((((rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b cone))⁻¹ :
        fan.algebraicRealization.functionFieldˣ) : fan.algebraicRealization.functionField) *
        chartCoordinateGerm fan nonempty cone a) = _
  change _ = (((rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular c cone))⁻¹ :
      fan.algebraicRealization.functionFieldˣ) : fan.algebraicRealization.functionField) *
    chartCoordinateGerm fan nonempty cone
      (a * normalizedToricMonomial fan regular b c character nonnegative cone)
  rw [map_mul, normalizedToricMonomial_germ, normalizedToricMonomial_ratio,
    Units.val_mul, Units.val_mul]
  let q := rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular c cone)
  have cancellation : ((q⁻¹ : fan.algebraicRealization.functionFieldˣ) :
      fan.algebraicRealization.functionField) *
      (q : fan.algebraicRealization.functionField) = 1 := Units.inv_mul q
  calc
    _ = (1 : fan.algebraicRealization.functionField) *
      ((rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) *
        (((rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b cone))⁻¹ :
          fan.algebraicRealization.functionFieldˣ) : fan.algebraicRealization.functionField) *
        chartCoordinateGerm fan nonempty cone a) := by ring
    _ = _ := by rw [← cancellation]; ring

/-- The same formula on the actual affine scheme, including the
restriction comparison from the chart open to its affine presentation. -/
theorem toricCartierMonomialMap_affine_top (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ : fan.Ray,
      0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (cone : fan.cones) (a : affineCoordinateRing fan.lattice cone.val) :
    letI := toricSchemeIntegral fan nonempty
    Scheme.Modules.Hom.app
      ((toricCartierAffineFrame fan nonempty regular b cone).hom ≫
        (Scheme.Modules.restrictFunctor (fan.affineToricChartι cone)).map
          (toricCartierMonomialMap fan nonempty regular b c character nonnegative)) ⊤
      (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val) a) =
    Scheme.Modules.Hom.app (toricCartierAffineFrame fan nonempty regular c cone).hom ⊤
      (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
        (a * normalizedToricMonomial fan regular b c character nonnegative cone)) := by
  letI := toricSchemeIntegral fan nonempty
  have frame := cartierOverToAffineFrame_comp_top_sections (fan.affineToricChartι cone)
    (invariantCartierSheafChartTrivialization fan nonempty regular b cone)
    (toricCartierMonomialMap fan nonempty regular b c character nonnegative)
    (chartCoordinateSectionsEquiv fan cone a)
  simp only [chartCoordinateSectionsEquiv, RingEquiv.trans_apply,
    commRingIsoToRingEquiv_apply, openImmersion_appIso_top_sections] at frame
  erw [frame]
  erw [toricCartierMonomialMap_frame_sections fan nonempty regular b c character
    nonnegative cone a]
  exact (toricCartierAffineFrame_top fan nonempty regular c cone _).symm

/-- Equality of the actual affine sheaf morphisms. The coefficient is
the regular chart monomial `χ^(q_c+m-q_b)`. -/
@[reassoc]
theorem toricCartierMonomialMap_affine_frame (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ : fan.Ray,
      0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    (toricCartierAffineFrame fan nonempty regular b cone).hom ≫
      (Scheme.Modules.restrictFunctor (fan.affineToricChartι cone)).map
        (toricCartierMonomialMap fan nonempty regular b c character nonnegative) =
    Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (fan.affineToricChart cone).ringCatSheaf)
      (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
        (normalizedToricMonomial fan regular b c character nonnegative cone)) ≫
      (toricCartierAffineFrame fan nonempty regular c cone).hom := by
  letI := toricSchemeIntegral fan nonempty
  apply unitSheafHom_ext_top
  have h := toricCartierMonomialMap_affine_top fan nonempty regular b c character
    nonnegative cone 1
  simp only [map_one, one_mul] at h
  rw [h, schemeHom_comp_apply]
  congr 1
  rw [Scheme.Modules.globalSectionsSmul_app]
  change _ = (fan.affineToricChart cone).presheaf.map
    (𝟙 (⊤ : (fan.affineToricChart cone).Opens)).op _ * 1
  rw [CategoryTheory.op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, mul_one]

/-- The affine-frame version expressed using the actual pullback rather
than the isomorphic open-immersion restriction functor. -/
def toricCartierPullbackFrame (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    SheafOfModules.unit (fan.affineToricChart cone).ringCatSheaf ≅
      (Scheme.Modules.pullback (fan.affineToricChartι cone)).obj
        (invariantCartierDivisor fan nonempty regular b).sheaf :=
  toricCartierAffineFrame fan nonempty regular b cone ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback (fan.affineToricChartι cone)).app _

@[reassoc]
theorem toricCartierMonomialMap_pullback_frame (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ : fan.Ray,
      0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    (toricCartierPullbackFrame fan nonempty regular b cone).hom ≫
      (Scheme.Modules.pullback (fan.affineToricChartι cone)).map
        (toricCartierMonomialMap fan nonempty regular b c character nonnegative) =
    Scheme.Modules.globalSectionsSmul
      (SheafOfModules.unit (fan.affineToricChart cone).ringCatSheaf)
      (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
        (normalizedToricMonomial fan regular b c character nonnegative cone)) ≫
      (toricCartierPullbackFrame fan nonempty regular c cone).hom := by
  letI := toricSchemeIntegral fan nonempty
  dsimp only [toricCartierPullbackFrame, Iso.trans_hom]
  have natural := (Scheme.Modules.restrictFunctorIsoPullback
    (fan.affineToricChartι cone)).hom.naturality
      (toricCartierMonomialMap fan nonempty regular b c character nonnegative)
  have composed := congrArg
    (fun h => (toricCartierAffineFrame fan nonempty regular b cone).hom ≫ h)
    natural.symm
  refine composed.trans ?_
  rw [← Category.assoc, toricCartierMonomialMap_affine_frame, Category.assoc]
  rfl

end ToricPower
