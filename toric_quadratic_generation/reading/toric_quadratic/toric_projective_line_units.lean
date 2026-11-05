module

public import PaperVerification.ToricProjectiveLineDegree
public import PaperVerification.ToricAffinePullbackSections
public import PaperVerification.ToricFanRegularCharacters
public import Mathlib.Algebra.Polynomial.Degree.Units

@[expose] public section

/-!
# Units on the actual affine-line charts

Every regular unit on either affine-line chart is an actual nonzero
constant, by the polynomial-unit theorem. Its rational value therefore
has zero order at every point of the complete curve, including the point
outside that chart. This is the key input for degree invariance under
an arbitrary isomorphism of line bundles.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) [Field k]

theorem projectiveLinePolynomialChart_image (negative : Bool) :
    (projectiveLinePolynomialChart k negative) ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens) =
      projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative) := by
  ext x
  change (∃ p : PrimeSpectrum (Polynomial k),p∈(⊤ : (Spec (.of (Polynomial k))).Opens) ∧
    projectiveLinePolynomialChart k negative p=x) ↔
      ∃ q,projectiveLineChart k negative q=x
  constructor
  · rintro ⟨p,hp,hpx⟩
    exact ⟨Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom p,hpx⟩
  · rintro ⟨q,hq⟩
    obtain ⟨p,hp⟩ :=
      (Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom).homeomorph.surjective q
    refine ⟨p,trivial,?_⟩
    change projectiveLineChart k negative
      ((Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom) p) = x
    exact (congrArg (projectiveLineChart k negative) hp).trans hq

theorem projectiveLine_constant_coordinate (negative : Bool) (c : k) :
    affineOpenCoordinateMap (.of (Polynomial k))
      (projectiveLinePolynomialChart k negative) (Polynomial.C c) =
        projectiveLineFan.rationalScalar k c := by
  let R := monoidChartAlgebra k (dualConeMonoid {projectiveLineRay negative})
  let j : Spec (.of R) ⟶ projectiveLineScheme k := projectiveLineChart k negative
  letI : IsOpenImmersion j := projectiveLineChart_isOpenImmersion k negative
  have h : affineOpenCoordinateMap (.of (Polynomial k))
      (projectiveLinePolynomialChart k negative)
      (projectiveLineChartRingEquiv k negative (algebraMap k R c)) =
      affineOpenCoordinateMap (.of R) j (algebraMap k R c) :=
    affineOpenCoordinateMap_comp (.of R) (.of (Polynomial k)) j
      (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom _
  rw [(projectiveLineChartRingEquiv k negative).commutes] at h
  exact h.trans (projectiveLineFan.chartRationalMap_eq_torusRationalMap k
    ⟨{projectiveLineRay negative},projectiveLineRayCone_mem negative⟩ _)

theorem projectiveLine_rationalScalar_order (c : kˣ) (x : projectiveLineScheme k) :
    (projectiveLineScheme k).ord (projectiveLineFan.rationalScalar k (c : k)) x=0 := by
  have hc : projectiveLineFan.rationalScalar k (c : k)≠0 :=
    Units.ne_zero (projectiveLineFan.rationalScalarUnit k c)
  obtain ⟨a,ha⟩ := (regular_unit_iff_stalkwise (projectiveLineScheme k) ⊤
    (projectiveLineFan.rationalScalar k (c : k)) hc).mpr (by
      constructor
      · intro y hy
        exact projectiveLineFan.rationalScalar_mem_regularAt k (c : k) y
      · intro y hy
        exact (map_inv₀ (projectiveLineFan.rationalScalar k) (c : k)) ▸
          projectiveLineFan.rationalScalar_mem_regularAt k ((c : k)⁻¹) y)
  rw [← ha]
  exact (projectiveLineScheme k).ord_of_isUnit a.isUnit (show x∈(⊤ : (projectiveLineScheme k).Opens) from trivial)

theorem projectiveLine_polynomialChartUnit_scalar (negative : Bool)
    (u : Γ(projectiveLineScheme k,
      (projectiveLinePolynomialChart k negative) ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens))ˣ) :
    letI := openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤
    ∃ c : kˣ,(projectiveLineScheme k).germToFunctionField
      ((projectiveLinePolynomialChart k negative) ''ᵁ ⊤) (u : Γ(projectiveLineScheme k,_)) =
        projectiveLineFan.rationalScalar k (c : k) := by
  let j := projectiveLinePolynomialChart k negative
  let R := CommRingCat.of (Polynomial k)
  let U := j ''ᵁ (⊤ : (Spec R).Opens)
  letI : Nonempty U := openImmersion_image_nonempty j ⊤
  let e : Γ(projectiveLineScheme k,U) ≃+* Polynomial k :=
    ((j.appIso ⊤) ≪≫ Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  have he : IsUnit (e (u : Γ(projectiveLineScheme k,U))) := u.isUnit.map e
  obtain ⟨r,hr,hp⟩ := Polynomial.isUnit_iff.mp he
  obtain ⟨c,hc⟩ := hr
  refine ⟨c,?_⟩
  have hu : (u : Γ(projectiveLineScheme k,U)) =
      affineChartSection R j (e (u : Γ(projectiveLineScheme k,U))) := by
    change (u : Γ(projectiveLineScheme k,U)) = e.symm (e (u : Γ(projectiveLineScheme k,U)))
    exact (e.symm_apply_apply _).symm
  rw [hu,affineChartSection_germ,← hp,← hc]
  exact projectiveLine_constant_coordinate k negative (c : k)

theorem projectiveLine_polynomialChartUnit_order (negative : Bool)
    (u : Γ(projectiveLineScheme k,
      (projectiveLinePolynomialChart k negative) ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens))ˣ)
    (x : projectiveLineScheme k) :
    letI := openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤
    (projectiveLineScheme k).ord
      ((projectiveLineScheme k).germToFunctionField
        ((projectiveLinePolynomialChart k negative) ''ᵁ ⊤) (u : Γ(projectiveLineScheme k,_))) x=0 := by
  letI := openImmersion_image_nonempty (projectiveLinePolynomialChart k negative) ⊤
  obtain ⟨c,hc⟩ := projectiveLine_polynomialChartUnit_scalar k negative u
  rw [hc]
  exact projectiveLine_rationalScalar_order k c x

theorem projectiveLine_fullChartUnit_order (negative : Bool)
    [Nonempty (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative))]
    (u : Γ(projectiveLineScheme k,
      projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative))ˣ)
    (x : projectiveLineScheme k) :
    (projectiveLineScheme k).ord
      ((projectiveLineScheme k).germToFunctionField
        (projectiveLineFan.fullChartOpen k (projectiveLineFullCone negative))
        (u : Γ(projectiveLineScheme k,_))) x=0 := by
  let j := projectiveLinePolynomialChart k negative
  let U := j ''ᵁ (⊤ : (Spec (.of (Polynomial k))).Opens)
  letI : Nonempty U := openImmersion_image_nonempty j ⊤
  let φ := (projectiveLineScheme k).presheaf.map
    (eqToHom (projectiveLinePolynomialChart_image k negative)).op
  have h := projectiveLine_polynomialChartUnit_order k negative (Units.map φ.hom u) x
  change (projectiveLineScheme k).ord
    ((projectiveLineScheme k).germToFunctionField U
      ((projectiveLineScheme k).presheaf.map
        (eqToHom (projectiveLinePolynomialChart_image k negative)).op
          (u : Γ(projectiveLineScheme k,_)))) x = 0 at h
  have hr := germToFunctionField_restrict (projectiveLineScheme k)
    (eqToHom (projectiveLinePolynomialChart_image k negative))
      (u : Γ(projectiveLineScheme k,_))
  exact (congrArg (fun r => (projectiveLineScheme k).ord r x) hr).symm.trans h

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_fullChartUnit_order
