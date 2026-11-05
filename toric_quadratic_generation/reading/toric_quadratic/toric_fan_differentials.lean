module

public import PaperVerification.ToricFractionDifferentials
public import PaperVerification.ToricFanCartierCocycle
public import PaperVerification.ToricFanSectionCoordinates

@[expose] public section

/-!
# Actual generic and affine-chart differential forms on the fan scheme

The coefficient field is the actual generic stalk of the glued scheme.
Its algebra structures are explicitly induced by the previously proved
chart maps. The fraction-field assertion is transferred from the actual
open affine zero-cone chart. Full-chart Kähler bases are then constructed
through the literal polynomial character presentations.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra KaehlerDifferential
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

def fanFunctionFieldAlgebra : Algebra k («Σ».fanScheme k).functionField :=
  BaseSections.functionFieldAlgebra k («Σ».fanScheme k)

def torusFunctionFieldAlgebra :
    Algebra (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField :=
  («Σ».torusRationalMap k).toAlgebra

def chartFunctionFieldAlgebra (s : «Σ».ConeIndex) :
    Algebra (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fanScheme k).functionField :=
  («Σ».chartRationalMap k s).toAlgebra

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra

instance fanFunctionField_scalarTower :
    IsScalarTower k (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField :=
  IsScalarTower.of_algebraMap_eq fun r => («Σ».rationalScalar_eq_algebraMap k r).symm

instance chartFunctionField_scalarTower (s : «Σ».ConeIndex) :
    IsScalarTower k (monoidChartAlgebra k (dualConeMonoid s.val))
      («Σ».fanScheme k).functionField :=
  ⟨fun r a z => smul_assoc r (a : AddMonoidAlgebra k (Lattice n)) z⟩

instance chartTorusFunctionField_scalarTower (s : «Σ».ConeIndex) :
    IsScalarTower (monoidChartAlgebra k (dualConeMonoid s.val))
      (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField :=
  ⟨fun a r z => smul_assoc (a : AddMonoidAlgebra k (Lattice n)) r z⟩

/-- This localization is for the exact character map into the generic
stalk, not for an independently chosen isomorphic field. -/
theorem torusFunctionField_isFractionRing :
    IsFractionRing (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField := by
  let R := monoidChartAlgebra k (dualConeMonoid (∅ : Finset (Lattice n)))
  letI : IsDomain R := «Σ».chartRing_isDomain k ∅ «Σ».zeroConeIndex.property
  let j : Spec (CommRingCat.of R) ⟶ «Σ».fanScheme k := «Σ».torusOpenMap k
  letI : IsOpenImmersion j := «Σ».torusOpenMap_isOpenImmersion k
  letI : Algebra R («Σ».fanScheme k).functionField :=
    affineOpenCoordinateAlgebra (CommRingCat.of R) j
  letI : IsFractionRing R («Σ».fanScheme k).functionField :=
    affineOpenCoordinate_isFractionRing (CommRingCat.of R) j
  exact IsFractionRing.of_ringEquiv_left (zeroConeChartAlgEquiv k n).symm.toRingEquiv
    (fun _ => rfl)

attribute [local instance] torusFunctionField_isFractionRing

def genericLogDifferentialBasis (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Module.Basis (Fin n) («Σ».fanScheme k).functionField
      Ω[(«Σ».fanScheme k).functionField⁄k] :=
  fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b

def genericLogVolume (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    ⋀[(«Σ».fanScheme k).functionField]^n Ω[(«Σ».fanScheme k).functionField⁄k] :=
  fractionLogVolume k («Σ».fanScheme k).functionField b

def fullCharacterBasis (s : «Σ».fullCones) : Module.Basis (Fin n) ℤ (Lattice n) :=
  integralDualBasis («Σ».fullConeBasis s)

theorem fullChart_semigroup_eq (s : «Σ».fullCones) :
    dualConeMonoid s.val = coordinateConeMonoid («Σ».fullCharacterBasis s) Finset.univ := by
  rw [«Σ».fullConeBasis_ray_set s, dualConeMonoid_basis_eq]
  rfl

def fullChartCoordinate (s : «Σ».fullCones) (i : Fin n) :
    monoidChartAlgebra k (dualConeMonoid s.val) :=
  chartCharacter k _ («Σ».fullCharacterBasis s i) (by
    rw [«Σ».fullChart_semigroup_eq]
    exact basis_mem_fullCoordinateCone _ i)

def fullChartPolynomialPresentation (s : «Σ».fullCones) :
    MvPolynomial (Fin n) k ≃ₐ[k] monoidChartAlgebra k (dualConeMonoid s.val) :=
  (fullChartPolynomialEquiv k («Σ».fullCharacterBasis s)).symm.trans
    (Subalgebra.equivOfEq _ _
      (congrArg (monoidChartAlgebra k) («Σ».fullChart_semigroup_eq s)).symm)

@[simp] theorem fullChartPolynomialPresentation_X (s : «Σ».fullCones) (i : Fin n) :
    «Σ».fullChartPolynomialPresentation k s (MvPolynomial.X i) =
      «Σ».fullChartCoordinate k s i := by
  apply Subtype.ext
  rw [fullChartPolynomialPresentation, AlgEquiv.trans_apply,
    fullChartPolynomialEquiv_symm_X]
  rfl

/-- The actual module Ω of the actual affine coordinate ring. -/
def actualFullChartDifferentialBasis (s : «Σ».fullCones) :
    Module.Basis (Fin n) (monoidChartAlgebra k (dualConeMonoid s.val))
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k] :=
  polynomialDifferentialBasis k («Σ».fullChartPolynomialPresentation k s)

@[simp] theorem actualFullChartDifferentialBasis_apply (s : «Σ».fullCones) (i : Fin n) :
    «Σ».actualFullChartDifferentialBasis k s i =
      D k (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fullChartCoordinate k s i) := by
  rw [actualFullChartDifferentialBasis, polynomialDifferentialBasis_apply,
    fullChartPolynomialPresentation_X]

@[simp] theorem map_actualFullChartDifferentialBasis (s : «Σ».fullCones) (i : Fin n) :
    KaehlerDifferential.map k k (monoidChartAlgebra k (dualConeMonoid s.val))
        («Σ».fanScheme k).functionField («Σ».actualFullChartDifferentialBasis k s i) =
      D k («Σ».fanScheme k).functionField
        («Σ».rationalCharacter k («Σ».fullCharacterBasis s i)) := by
  rw [actualFullChartDifferentialBasis_apply, KaehlerDifferential.map_D]
  congr 1

/-- Coefficients of actual chart top forms in an actual generic logarithmic
volume. This definition uses only Kähler functoriality and the universal
exterior map; the support-coefficient formula is proved afterward. -/
def actualChartTopCoefficient (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) :
    (⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) →ₗ[
        monoidChartAlgebra k (dualConeMonoid s.val)] («Σ».fanScheme k).functionField :=
  ((basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀)).toLinearMap.restrictScalars _).comp
    (exteriorScalarExtensionMap (S := («Σ».fanScheme k).functionField)
      (KaehlerDifferential.map k k (monoidChartAlgebra k (dualConeMonoid s.val))
        («Σ».fanScheme k).functionField))

def chartVolumeCoefficient (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) : ((«Σ».fanScheme k).functionField)ˣ :=
  «Σ».rationalCharacter k (∑ i, «Σ».fullCharacterBasis s i) *
    Units.map (Int.castRingHom («Σ».fanScheme k).functionField).toMonoidHom
      (b₀.isUnit_det («Σ».fullCharacterBasis s)).unit

@[simp] theorem chartVolumeCoefficient_value
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) =
      («Σ».rationalCharacter k (∑ i, «Σ».fullCharacterBasis s i) : («Σ».fanScheme k).functionField) *
        (b₀.det («Σ».fullCharacterBasis s) : («Σ».fanScheme k).functionField) := rfl

theorem actualChartTopCoefficient_basis
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    «Σ».actualChartTopCoefficient k b₀ s
        (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
          («Σ».actualFullChartDifferentialBasis k s)) =
      («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) := by
  rw [actualChartTopCoefficient, LinearMap.comp_apply,
    exteriorScalarExtensionMap_wedge]
  simp_rw [«Σ».map_actualFullChartDifferentialBasis k s]
  change basisTopExteriorEquiv
      (fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b₀)
        (fractionRegularCoordinateVolume k («Σ».fanScheme k).functionField
          («Σ».fullCharacterBasis s)) = _
  rw [fractionRegularCoordinateVolume_eq_character, map_smul,
    fractionLogVolume_change_basis k («Σ».fanScheme k).functionField b₀
      («Σ».fullCharacterBasis s), map_smul]
  change _ * ((b₀.det («Σ».fullCharacterBasis s) : («Σ».fanScheme k).functionField) *
    basisTopExteriorEquiv
      (fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b₀)
      (exteriorPower.ιMulti («Σ».fanScheme k).functionField n
        (fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b₀))) = _
  rw [basisTopExteriorEquiv_basis, mul_one]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual scalar action inherited from the Laurent ring agrees with
regular evaluation through the actual full-chart map. -/
theorem fullChart_functionField_smul (s : «Σ».fullCones)
    (a : monoidChartAlgebra k (dualConeMonoid s.val))
    (z : («Σ».fanScheme k).functionField) :
    a • z = «Σ».chartRationalMap k («Σ».fullConeIndex s) a * z := by
  change «Σ».torusRationalMap k (a : AddMonoidAlgebra k (Lattice n)) * z = _
  exact congrArg (fun r => r * z)
    («Σ».chartRationalMap_eq_torusRationalMap k («Σ».fullConeIndex s) a).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Linearity and the genuine exterior basis determine every coefficient;
the scalar compatibility is proved through the actual chart morphism. -/
theorem actualChartTopCoefficient_apply
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    (ω : ⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) :
    «Σ».actualChartTopCoefficient k b₀ s ω =
      «Σ».chartRationalMap k («Σ».fullConeIndex s)
        (basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω) *
          «Σ».chartVolumeCoefficient k b₀ s := by
  calc
    _ = «Σ».actualChartTopCoefficient k b₀ s
        (basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω •
          exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
            («Σ».actualFullChartDifferentialBasis k s)) :=
      congrArg («Σ».actualChartTopCoefficient k b₀ s)
        (topExterior_eq_smul_basis («Σ».actualFullChartDifferentialBasis k s) ω)
    _ = basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω •
        «Σ».actualChartTopCoefficient k b₀ s
          (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
            («Σ».actualFullChartDifferentialBasis k s)) := map_smul _ _ _
    _ = basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω •
        («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) :=
      congrArg (fun z : («Σ».fanScheme k).functionField =>
        basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω • z)
        («Σ».actualChartTopCoefficient_basis k b₀ s)
    _ = _ := «Σ».fullChart_functionField_smul k s _ _

set_option backward.isDefEq.respectTransparency.types false in
theorem mem_range_actualChartTopCoefficient_iff
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    (z : («Σ».fanScheme k).functionField) :
    z ∈ LinearMap.range («Σ».actualChartTopCoefficient k b₀ s) ↔
      ∃ r : monoidChartAlgebra k (dualConeMonoid s.val),
        «Σ».chartRationalMap k («Σ».fullConeIndex s) r * «Σ».chartVolumeCoefficient k b₀ s = z := by
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω,
      («Σ».actualChartTopCoefficient_apply k b₀ s ω).symm⟩
  · rintro ⟨r, hr⟩
    refine ⟨r • exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
      («Σ».actualFullChartDifferentialBasis k s), ?_⟩
    calc
      _ = r • «Σ».actualChartTopCoefficient k b₀ s
          (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
            («Σ».actualFullChartDifferentialBasis k s)) := map_smul _ _ _
      _ = r • («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) :=
        congrArg (fun z : («Σ».fanScheme k).functionField => r • z)
          («Σ».actualChartTopCoefficient_basis k b₀ s)
      _ = «Σ».chartRationalMap k («Σ».fullConeIndex s) r *
          «Σ».chartVolumeCoefficient k b₀ s := «Σ».fullChart_functionField_smul k s r _
      _ = z := hr

set_option backward.isDefEq.respectTransparency.types false in
theorem actualChartTopCoefficient_injective
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    Function.Injective («Σ».actualChartTopCoefficient k b₀ s) := by
  intro ω η he
  apply (basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s)).injective
  apply «Σ».chartRationalMap_injective k («Σ».fullConeIndex s)
  apply mul_right_cancel₀ (Units.ne_zero («Σ».chartVolumeCoefficient k b₀ s))
  exact («Σ».actualChartTopCoefficient_apply k b₀ s ω).symm.trans
    (he.trans («Σ».actualChartTopCoefficient_apply k b₀ s η))

/-- The local character is computed from the actual differential volume.
This is the sign in the toric canonical divisor formula. -/
theorem canonical_cartierLatticePoint (s : «Σ».fullCones) :
    «Σ».cartierLatticePoint (fun _ => -1) s = ∑ i, «Σ».fullCharacterBasis s i := by
  simp only [cartierLatticePoint, neg_one_zsmul, Finset.sum_neg_distrib, neg_neg]
  rfl

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.actualChartTopCoefficient_basis

