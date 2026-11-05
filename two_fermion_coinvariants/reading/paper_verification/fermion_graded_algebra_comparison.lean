module

public import PaperVerification.FermionGradedComparison
public import PaperVerification.FermionHomogeneousDecomposition

/-!
# The canonical algebra comparison from an actual associated graded

The map on each successive quotient is the actual highest-component map.
Multiplicativity follows from bounded multiplication in the ambient algebra;
bijectivity follows from the separately proved piece comparisons and the
actual homogeneous direct-sum decomposition.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BasisFiltered

open scoped DirectSum

variable {R A Q Q₀ I J : Type*} [CommRing R]
  [Ring A] [Algebra R A] [Ring Q] [Algebra R Q] [Ring Q₀] [Algebra R Q₀]
  (b : Module.Basis I R A) (w : I → ℕ)
  (q : A →ₐ[R] Q) (q₀ : A →ₐ[R] Q₀)
  (hone : Homogeneous b w 0 (1 : A))
  (hmul : ∀ i j,Homogeneous b w (w i+w j) (b i*b j))
  (f g : J → A) (degree : J → ℕ)
  (hf : ∀ j,HasTop b w (degree j) (f j) (g j))
  (hker : q.toLinearMap.ker=Submodule.span R (Set.range f))
  (hker₀ : q₀.toLinearMap.ker=Submodule.span R (Set.range g))
  (hinitial : initialSubmodule b w q.toLinearMap.ker ≤ q₀.toLinearMap.ker)

include hmul in
theorem gradedProjection_mul (i j : ℕ) (x : boundPiece b w i) (y : boundPiece b w j) :
    FilteredAlgebra.gradedMul (quotientFiltration b w q hone hmul) i j
      (gradedProjection b w q hone hmul i x) (gradedProjection b w q hone hmul j y) =
    gradedProjection b w q hone hmul (i+j)
      ⟨(x : A)*y,bound_mul b w hmul x.property y.property⟩ := by
  rw [gradedProjection_apply,gradedProjection_apply,FilteredAlgebra.gradedMul_apply_mk,
    gradedProjection_apply]
  apply congrArg Submodule.Quotient.mk
  exact Subtype.ext (map_mul q (x : A) y).symm

/-- The associated-graded comparison on an individual actual degree piece,
viewed in the original homogeneous quotient algebra. -/
def gradedComparisonComponent (d : ℕ) :
    FilteredAlgebra.GradedPiece (quotientFiltration b w q hone hmul) d →ₗ[R] Q₀ :=
  ((homogeneousPiece b w d).map q₀.toLinearMap).subtype.comp
    (gradedPieceComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial d).toLinearMap

@[simp] theorem gradedComparisonComponent_projection (d : ℕ) (x : boundPiece b w d) :
    gradedComparisonComponent b w q q₀ hone hmul f g degree hf hker hker₀ hinitial d
      (gradedProjection b w q hone hmul d x)=q₀ (component b w d x) :=
  gradedPieceComparison_projection_coe b w q q₀ hone hmul f g degree hf hker hker₀ hinitial d x

theorem gradedComparisonComponent_one :
    gradedComparisonComponent b w q q₀ hone hmul f g degree hf hker hker₀ hinitial 0
      (FilteredAlgebra.gradedOne (quotientFiltration b w q hone hmul))=1 := by
  have hrep : gradedProjection b w q hone hmul 0
      ⟨1,homogeneous_bound b w hone⟩=
      FilteredAlgebra.gradedOne (quotientFiltration b w q hone hmul) := by
    rw [gradedProjection_apply,FilteredAlgebra.gradedOne_def]
    apply congrArg Submodule.Quotient.mk
    exact Subtype.ext (map_one q)
  rw [← hrep,gradedComparisonComponent_projection,
    component_of_homogeneous b w hone,if_pos rfl,map_one]

theorem gradedComparisonComponent_mul (i j : ℕ)
    (x : FilteredAlgebra.GradedPiece (quotientFiltration b w q hone hmul) i)
    (y : FilteredAlgebra.GradedPiece (quotientFiltration b w q hone hmul) j) :
    gradedComparisonComponent b w q q₀ hone hmul f g degree hf hker hker₀ hinitial (i+j)
      (FilteredAlgebra.gradedMul (quotientFiltration b w q hone hmul) i j x y) =
      gradedComparisonComponent b w q q₀ hone hmul f g degree hf hker hker₀ hinitial i x *
      gradedComparisonComponent b w q q₀ hone hmul f g degree hf hker hker₀ hinitial j y := by
  obtain ⟨a,rfl⟩ := gradedProjection_surjective b w q hone hmul i x
  obtain ⟨c,rfl⟩ := gradedProjection_surjective b w q hone hmul j y
  rw [gradedProjection_mul,gradedComparisonComponent_projection,
    gradedComparisonComponent_projection,gradedComparisonComponent_projection,
    component_mul_top b w hmul a.property c.property,map_mul]

/-- The actual associated-graded algebra maps to the original homogeneous
quotient by highest components of bounded representatives. -/
def gradedAlgebraComparison :
    FilteredAlgebra.AssociatedGraded (quotientFiltration b w q hone hmul) →ₐ[R] Q₀ :=
  DirectSum.toAlgebra R _
    (gradedComparisonComponent b w q q₀ hone hmul f g degree hf hker hker₀ hinitial)
    (gradedComparisonComponent_one b w q q₀ hone hmul f g degree hf hker hker₀ hinitial)
    (fun {i j} x y ↦ gradedComparisonComponent_mul b w q q₀ hone hmul
      f g degree hf hker hker₀ hinitial i j x y)

theorem gradedAlgebraComparison_toLinearMap :
    (gradedAlgebraComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial).toLinearMap =
      (DirectSum.coeLinearMap (fun d ↦ (homogeneousPiece b w d).map q₀.toLinearMap)).comp
        (DirectSum.lmap (fun d ↦
          (gradedPieceComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial d).toLinearMap)) := by
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro x
  change DirectSum.toModule R ℕ Q₀
    (gradedComparisonComponent b w q q₀ hone hmul f g degree hf hker hker₀ hinitial)
    (DirectSum.lof R ℕ _ d x) = _
  simp only [DirectSum.toModule_lof,LinearMap.comp_apply,DirectSum.lmap_lof,
    DirectSum.coeLinearMap_lof]
  rfl

/-- Bijectivity uses the actual internal grading of the homogeneous quotient,
which can be obtained from its proved homogeneous basis. -/
theorem gradedAlgebraComparison_bijective
    (hgrading : DirectSum.IsInternal (fun d ↦ (homogeneousPiece b w d).map q₀.toLinearMap)) :
    Function.Bijective (gradedAlgebraComparison b w q q₀ hone hmul
      f g degree hf hker hker₀ hinitial) := by
  let e := DFinsupp.mapRange.linearEquiv (fun d ↦
    gradedPieceComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial d)
  have hsum : Function.Bijective
      (DirectSum.coeLinearMap (fun d ↦ (homogeneousPiece b w d).map q₀.toLinearMap)) := hgrading
  have h := hsum.comp e.bijective
  change Function.Bijective
    (gradedAlgebraComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial).toLinearMap
  rw [gradedAlgebraComparison_toLinearMap]
  exact h

def associatedGradedComparison
    (hgrading : DirectSum.IsInternal (fun d ↦ (homogeneousPiece b w d).map q₀.toLinearMap)) :
    FilteredAlgebra.AssociatedGraded (quotientFiltration b w q hone hmul) ≃ₐ[R] Q₀ :=
  AlgEquiv.ofBijective
    (gradedAlgebraComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial)
    (gradedAlgebraComparison_bijective b w q q₀ hone hmul f g degree hf hker hker₀ hinitial hgrading)

@[simp] theorem associatedGradedComparison_of_projection
    (hgrading : DirectSum.IsInternal (fun d ↦ (homogeneousPiece b w d).map q₀.toLinearMap))
    (d : ℕ) (x : boundPiece b w d) :
    associatedGradedComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial hgrading
      (DirectSum.of (FilteredAlgebra.GradedPiece (quotientFiltration b w q hone hmul)) d
        (gradedProjection b w q hone hmul d x))=q₀ (component b w d x) := by
  change DirectSum.toModule R ℕ Q₀
    (gradedComparisonComponent b w q q₀ hone hmul f g degree hf hker hker₀ hinitial)
    (DirectSum.lof R ℕ _ d (gradedProjection b w q hone hmul d x)) = _
  rw [DirectSum.toModule_lof,gradedComparisonComponent_projection]

/-- The canonical algebra equivalence identifies each actual graded summand
exactly with the corresponding homogeneous target piece. -/
theorem associatedGradedComparison_range
    (hgrading : DirectSum.IsInternal (fun d ↦ (homogeneousPiece b w d).map q₀.toLinearMap))
    (d : ℕ) :
    LinearMap.range
      ((associatedGradedComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial hgrading).toLinearMap.comp
        (DirectSum.lof R ℕ (FilteredAlgebra.GradedPiece (quotientFiltration b w q hone hmul)) d)) =
      (homogeneousPiece b w d).map q₀.toLinearMap := by
  have he :
      (associatedGradedComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial hgrading).toLinearMap.comp
        (DirectSum.lof R ℕ (FilteredAlgebra.GradedPiece (quotientFiltration b w q hone hmul)) d) =
      ((homogeneousPiece b w d).map q₀.toLinearMap).subtype.comp
        (gradedPieceComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial d).toLinearMap := by
    apply LinearMap.ext
    intro x
    change DirectSum.toModule R ℕ Q₀
      (gradedComparisonComponent b w q q₀ hone hmul f g degree hf hker hker₀ hinitial)
      (DirectSum.lof R ℕ _ d x) = _
    rw [DirectSum.toModule_lof]
    rfl
  rw [he,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr
      (gradedPieceComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial d).surjective,
    Submodule.map_top,Submodule.range_subtype]

end PaperVerification.Fermion.BasisFiltered
