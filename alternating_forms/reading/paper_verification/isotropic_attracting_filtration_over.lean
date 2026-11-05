module

public import PaperVerification.IsotropicAttractingSchemeFiltration
public import PaperVerification.GradedProjScalarMap

/-!
# The complete affine paving is over the original coefficient field

All closed-stage maps and affine-cell isomorphisms preserve the actual
structure morphism.  This is needed when passing to complex-valued points
or to the genuine dimension-graded Chow groups.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory _root_.HomogeneousLocalization
open scoped HomogeneousIdeal

namespace PaperVerification

namespace IsotropicAttractingCharts

open MvPolynomial
open AlternatingForms IsotropicAttractingCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K] {n t : ℕ}

def filtrationStructureMap (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    filtrationScheme (K := K) E c₁ c₂ ⟶ Spec (CommRingCat.of K) :=
  HomogeneousQuotientCharts.structureMap (filtrationIdeal E c₁ c₂)
    (filtrationIdeal_isHomogeneous E c₁ c₂)

theorem filtrationToOriginal_over (E : Set (PluckerIndex (t+2) n)) (c₁ c₂ : ℕ) :
    filtrationToOriginal (K := K) E c₁ c₂ ≫ isotropicStructureMap (canonicalForms c₁ c₂) =
      filtrationStructureMap E c₁ c₂ :=
  HomogeneousQuotientProjective.quotientProjMap_over _ _ _ _ _

theorem filtrationInclusion_over {E F : Set (PluckerIndex (t+2) n)}
    (hEF : E ⊆ F) (c₁ c₂ : ℕ) :
    filtrationInclusion (K := K) hEF c₁ c₂ ≫ filtrationStructureMap E c₁ c₂ =
      filtrationStructureMap F c₁ c₂ :=
  HomogeneousQuotientProjective.quotientProjMap_over _ _ _ _ _

theorem filtrationChartIsoCell_hom_over (E : Set (PluckerIndex (t+2) n))
    (p : PluckerIndex (t+2) n) (hE : EarlierSet p E) (c₁ c₂ : ℕ) :
    (filtrationChartIsoCell (K := K) E p hE c₁ c₂).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K
        (MvPolynomial (Coordinate (indexEmbedding p)) K ⧸
          isotropyIdeal (indexEmbedding p) c₁ c₂))) =
      (filtrationChart E p c₁ c₂).ι ≫ filtrationStructureMap E c₁ c₂ := by
  rw [filtrationChartIsoCell, Iso.trans_hom, Category.assoc,
    specAlgEquiv_hom_over]
  exact HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized_hom_over _ _ _

theorem filtrationChartIsoAffine_hom_over {k : ℕ}
    (E : Set (PluckerIndex (t+2) (2*k+1))) (p : PluckerIndex (t+2) (2*k+1))
    (hE : EarlierSet p E) (hp : IndependentPivots (indexEmbedding p)) :
    (filtrationChartIsoAffine (K := K) E p hE hp).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K
        (MvPolynomial {v : Coordinate (indexEmbedding p) //
          v ∉ Set.range (pivotEmbedding hp)} K))) =
      (filtrationChart E p (2*k+1) (2*k)).ι ≫
        filtrationStructureMap E (2*k+1) (2*k) := by
  rw [filtrationChartIsoAffine, Iso.trans_hom, Category.assoc,
    specAlgEquiv_hom_over]
  exact filtrationChartIsoCell_hom_over _ _ _ _ _

end IsotropicAttractingCharts
end PaperVerification
