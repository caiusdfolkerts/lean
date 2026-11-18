module

public import Continuation.Divisor.ProjectiveBase
public import Continuation.Divisor.ProjectiveComparison
public import Continuation.Divisor.MonomialStructuralMap

/-! # The actual projective embedding is over the original field -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

namespace Unimodular.Projectivity
open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricCharacters
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

section Monomial
variable {ι : Type u} {n : ℕ} (a : ι → Lattice n) (k : Type u) [Field k]

lemma homogeneousMonomial_gradeZero_scalars :
    (gradeZeroMap (homogeneousMonomialGradedMap a k)).comp
        (polynomialGradeZeroScalarMap k ι) = homogeneousWeightZeroMap a k := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  change homogeneousMonomialMap a k (MvPolynomial.C r) = AddMonoidAlgebra.single 0 r
  simp only [homogeneousMonomialMap, MvPolynomial.aeval_C]
  rfl

/-- Compatibility of actual scheme morphisms with their scalar fields. -/
theorem monomialProjectiveEmbedding_toSpec :
    monomialProjectiveEmbedding a k ≫ polynomialProjectiveToSpec k ι =
      monomialProjectiveToSpec a k := by
  unfold monomialProjectiveEmbedding polynomialProjectiveToSpec
  rw [← Category.assoc, projMap_toSpecZero, Category.assoc, ← Spec.map_comp]
  change Proj.toSpecZero (homogeneousWeightGrading a k) ≫
    Spec.map (CommRingCat.ofHom ((gradeZeroMap (homogeneousMonomialGradedMap a k)).comp
      (polynomialGradeZeroScalarMap k ι))) = monomialProjectiveToSpec a k
  rw [homogeneousMonomial_gradeZero_scalars]
  rfl
end Monomial

variable {n : ℕ} {F : PaperVerification.ToricGeometry.SmoothCompleteFan n}
  {P : LatticePolytope n} (D : VertexChartData F P) (k : Type u) [Field k]

namespace VertexChartData

theorem fanProjectiveEmbedding_toSpec :
    D.fanProjectiveEmbedding k ≫ polynomialProjectiveToSpec k (WeightIndex.{u} (F := F)) =
      F.fanSchemeStructureMap k := by
  unfold fanProjectiveEmbedding
  rw [Category.assoc, monomialProjectiveEmbedding_toSpec]
  exact F.monomialNormalFanIso_toSpec P D.weight k
    (fun j => (D.vertexCone j).val) D.dual_eq_difference
    (fun j => F.fullCones_mem (D.vertexCone j)) D.vertexCone_cover
    (fun j => D.weight_mem j.val)
    (fun j => by rw [D.vertexCone_weight]; exact D.normal (D.vertexCone j))

include D in
/-- Actual properness of the original fan scheme, obtained from the
closed immersion and the proved base-field compatibility. -/
theorem fanScheme_isProper : IsProper (F.fanSchemeStructureMap k) := by
  have h : IsProper (D.fanProjectiveEmbedding k ≫
      polynomialProjectiveToSpec k (WeightIndex.{u} (F := F))) := inferInstance
  rwa [D.fanProjectiveEmbedding_toSpec k] at h

#print axioms monomialProjectiveEmbedding_toSpec
#print axioms fanProjectiveEmbedding_toSpec
#print axioms fanScheme_isProper
end VertexChartData
end Unimodular.Projectivity
