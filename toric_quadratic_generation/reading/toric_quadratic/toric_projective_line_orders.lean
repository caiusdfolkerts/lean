module

public import PaperVerification.ToricProjectiveLineFan
public import PaperVerification.ToricPolynomialBoundary
public import PaperVerification.ToricOrbitChartMaps
public import PaperVerification.ToricFanAction

@[expose] public section

/-!
# Character orders on the actual two-chart projective line

Each smooth rank-one chart is identified with `Spec k[X]`, and its
primitive character is identified with the literal coordinate `X`.
Orders are consequently computed in the actual scheme local rings.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{u}} [IsIntegral X]
    (R S : CommRingCat.{u}) [IsDomain R] [IsDomain S]
    (j : Spec R ⟶ X) [IsOpenImmersion j]
    (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)]

/-- Actual affine coordinate maps commute with restriction along a
specified affine open morphism. -/
theorem affineOpenCoordinateMap_comp (r : R) :
    affineOpenCoordinateMap S (Spec.map φ ≫ j) (φ r) =
      affineOpenCoordinateMap R j r := by
  have hsec : (Scheme.ΓSpecIso S).inv (φ r) =
      (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) :=
    congrArg (fun g => g r) (Scheme.ΓSpecIso_inv_naturality φ)
  change openImmersionGlobalToFunctionField (Spec.map φ ≫ j)
      ((Scheme.ΓSpecIso S).inv (φ r)) =
    openImmersionGlobalToFunctionField j ((Scheme.ΓSpecIso R).inv r)
  rw [hsec]
  exact openImmersionGlobalToFunctionField_restrict
    (Spec.map φ) j ((Scheme.ΓSpecIso R).inv r)

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open scoped Classical

variable (k : Type u) [Field k]

/-- The actual affine-line chart map, including the algebra equivalence
which determines its coordinate. -/
def projectiveLinePolynomialChart (negative : Bool) :
    Spec (.of (Polynomial k)) ⟶ projectiveLineScheme k :=
  Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom ≫
    projectiveLineChart k negative

instance projectiveLinePolynomialChart_isOpenImmersion (negative : Bool) :
    IsOpenImmersion (projectiveLinePolynomialChart k negative) := by
  let s : projectiveLineFan.ConeIndex :=
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩
  let R : CommRingCat := .of (monoidChartAlgebra k (dualConeMonoid s.val))
  let S : CommRingCat := .of (Polynomial k)
  let j : Spec R ⟶ projectiveLineScheme k := projectiveLineFan.fanChartMap k s
  let φ : R ⟶ S :=
    (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom
  letI : IsOpenImmersion j := projectiveLineFan.fanChartMap_isOpenImmersion k s
  letI : IsOpenImmersion (Spec.map φ) := by
    dsimp [φ]
    infer_instance
  change IsOpenImmersion (Spec.map φ ≫ j)
  exact IsOpenImmersion.comp (Spec.map φ) j

def projectiveLineBoundaryPoint (negative : Bool) : projectiveLineScheme k :=
  projectiveLinePolynomialChart k negative (polynomialOrigin k)

/-- The primitive character of either one-dimensional cone is its
ordinary polynomial coordinate. -/
theorem projectiveLineChartRingEquiv_primitive (negative : Bool) :
    projectiveLineChartRingEquiv k negative
      (chartCharacter k (dualConeMonoid {projectiveLineRay negative})
        (projectiveLineRay negative) (by
          rw [mem_projectiveLineDualCone]
          cases negative <;> norm_num [projectiveLineRay])) = Polynomial.X := by
  apply (Polynomial.toFinsuppIsoAlg k).injective
  simp only [projectiveLineChartRingEquiv,AlgEquiv.trans_apply,
    monoidChartAlgebraEquiv_symm_character,AlgEquiv.apply_symm_apply,
    AddMonoidAlgebra.domCongr_single]
  cases negative <;>
    simp [projectiveLineSemigroupEquiv,projectiveLineRay,
      Polynomial.toFinsuppIsoAlg]

theorem projectiveLine_coordinate_rationalCharacter (negative : Bool) :
    affineOpenCoordinateMap (.of (Polynomial k))
      (projectiveLinePolynomialChart k negative) Polynomial.X =
        (projectiveLineFan.rationalCharacter k (projectiveLineRay negative) :
          (projectiveLineScheme k).functionField) := by
  let s : projectiveLineFan.ConeIndex :=
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩
  let R : CommRingCat := .of (monoidChartAlgebra k (dualConeMonoid s.val))
  let S : CommRingCat := .of (Polynomial k)
  let j : Spec R ⟶ projectiveLineScheme k := projectiveLineFan.fanChartMap k s
  let φ : R ⟶ S :=
    (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom
  letI : IsOpenImmersion j := projectiveLineFan.fanChartMap_isOpenImmersion k s
  letI : IsOpenImmersion (Spec.map φ) := by
    dsimp [φ]
    infer_instance
  have hm : projectiveLineRay negative∈dualConeMonoid s.val := by
    rw [mem_projectiveLineDualCone]
    cases negative <;> norm_num [projectiveLineRay]
  let r := chartCharacter k (dualConeMonoid s.val) (projectiveLineRay negative) hm
  rw [← projectiveLineChartRingEquiv_primitive k negative]
  exact (affineOpenCoordinateMap_comp R S j φ r).trans
      (projectiveLineFan.chartRationalMap_character k s
        (projectiveLineRay negative) hm)

theorem projectiveLine_character_as_power (negative : Bool) (m : Lattice 1) :
    projectiveLineFan.rationalCharacter k m =
      (projectiveLineFan.rationalCharacter k (projectiveLineRay negative)) ^
        (if negative then -m 0 else m 0) := by
  have hm : m = (if negative then -m 0 else m 0) • projectiveLineRay negative := by
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    cases negative <;> simp [projectiveLineRay,hi]
  nth_rw 1 [hm]
  exact (projectiveLineFan.rationalCharacterHom k).map_zpow
    (Multiplicative.ofAdd (projectiveLineRay negative)) _

/-- All character orders on each actual affine chart, for every integer
character and every actual scheme point. -/
theorem projectiveLine_character_order (negative : Bool) (m : Lattice 1)
    (p : PrimeSpectrum (Polynomial k)) :
    (projectiveLineScheme k).ord
      (projectiveLineFan.rationalCharacter k m : (projectiveLineScheme k).functionField)
      (projectiveLinePolynomialChart k negative p) =
      if p=polynomialOrigin k then (if negative then -m 0 else m 0) else 0 := by
  rw [projectiveLine_character_as_power k negative m,Units.val_zpow_eq_zpow_val,
    ← projectiveLine_coordinate_rationalCharacter k negative]
  exact affineLine_coordinate_zpow_order k
    (projectiveLinePolynomialChart k negative) _ p

theorem projectiveLine_character_order_boundary (negative : Bool) (m : Lattice 1) :
    (projectiveLineScheme k).ord
      (projectiveLineFan.rationalCharacter k m : (projectiveLineScheme k).functionField)
      (projectiveLineBoundaryPoint k negative) = if negative then -m 0 else m 0 := by
  simpa only [projectiveLineBoundaryPoint,if_pos rfl,ite_true] using
    projectiveLine_character_order k negative m (polynomialOrigin k)

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_character_order
