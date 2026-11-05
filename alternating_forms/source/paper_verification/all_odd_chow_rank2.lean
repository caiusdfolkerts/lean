module

public import paper_verification.actual_chow_rank5
import all paper_verification.actual_chow_rank5
public import paper_verification.isotropic_projective_geometry3
import all paper_verification.isotropic_projective_geometry3
public import paper_verification.actual_odd_affine_paving6
import all paper_verification.actual_odd_affine_paving6
public import paper_verification.oai_chow001_run2
import all paper_verification.oai_chow001_run2
public import paper_verification.symmetric_projective_geometry3
import all paper_verification.symmetric_projective_geometry3
public import paper_verification.oai_projective_boundary000_run1
import all paper_verification.oai_projective_boundary000_run1
public import paper_verification.relative_projective_geometry2
import all paper_verification.relative_projective_geometry2
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.Finsupp.Pi
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.BoundedFinitePavingChowRank -/


/-! A finite paving indexed only where its actual strata exist. This avoids
introducing an arbitrary dummy open after the last stage. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TotalChow
open AlgebraicGeometry CategoryTheory
open OAI.AlgebraicGeometry
open scoped BigOperators

section Filtration

variable (stage : ℕ → Scheme.{0}) [∀ m, AlgebraicGeometry.IsNoetherian (stage m)]
  (base : ∀ m, stage m ⟶ complexBase) [∀ m, LocallyOfFiniteType (base m)]
  (closed : ∀ m, stage (m+1) ⟶ stage m) [∀ m, IsClosedImmersion (closed m)]
  (over_base : ∀ m, closed m ≫ base m = base (m+1))
  (N : ℕ)
  (cell : ∀ m, m < N → (stage m).Opens)
  (complement : ∀ (m : ℕ) (hm : m < N),
    Set.range (closed m) = (Set.range (cell m hm).ι)ᶜ)
  (last_empty : IsEmpty (stage N))
  (budget : ℕ → ℕ)
  (cell_rank : ∀ (m : ℕ) (hm : m < N),
    Module.Finite ℚ (TotalChowQ ((cell m hm).ι ≫ base m)) ∧
      Module.finrank ℚ (TotalChowQ ((cell m hm).ι ≫ base m)) ≤ budget m)

include over_base complement last_empty cell_rank

/-- The inductive bound uses every stratum and reaches the original stage. -/
theorem boundedFinitePaving_total_rank :
    Module.Finite ℚ (TotalChowQ (base 0)) ∧
      Module.finrank ℚ (TotalChowQ (base 0)) ≤ ∑ m ∈ Finset.range N, budget m := by
  have h : ∀ m ≤ N, Module.Finite ℚ (TotalChowQ (base m)) ∧
      Module.finrank ℚ (TotalChowQ (base m)) ≤ ∑ j ∈ Finset.Ico m N, budget j := by
    intro m hm
    induction hm using Nat.decreasingInduction with
    | self =>
      letI := last_empty
      have he := finite_and_finrank_eq_zero_of_empty (base N)
      exact ⟨he.1,by simp only [he.2,Finset.Ico_self,Finset.sum_empty,le_refl]⟩
    | @of_succ m hm ih =>
      have hc := cell_rank m hm
      letI := hc.1
      letI : Module.Finite ℚ (TotalChowQ (closed m ≫ base m)) := by
        rw [over_base m]
        exact ih.1
      have hf := finite_of_closed_open (cell m hm).ι (closed m) (base m) (complement m hm)
      refine ⟨hf,?_⟩
      have hr := finrank_le_closed_add_open (cell m hm).ι (closed m) (base m) (complement m hm)
      rw [over_base m] at hr
      rw [Finset.sum_eq_sum_Ico_succ_bot hm]
      exact hr.trans ((Nat.add_le_add ih.2 hc.2).trans_eq (Nat.add_comm _ _))
  simpa only [Nat.Ico_zero_eq_range] using h 0 (Nat.zero_le N)

end Filtration

end PaperVerification.TotalChow
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.BoundedFinitePavingChowRank"

section ComponentSource_1
/- Original module: PaperVerification.IsotropicPavingChowRank -/


/-!
# The complete actual Chow-rank bound for the common-isotropic scheme

The strata and all the maps below are those of the original homogeneous
quotient.  The finite-dimensionality conclusion is derived from genuine
closed/open localization and the actual affine-space Chow calculation.
No cycle-class comparison, Chern-class relation, or abstract ring model is
assumed in this argument.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory MvPolynomial
open AlternatingForms IsotropicAttractingCoordinates TotalChow
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Equality of the literal homogeneous ideals transports the actual
Chow groups, including their structural morphisms. -/
theorem homogeneousQuotient_total_rank_congr {σ : Type}
    (I J : Ideal (MvPolynomial σ ℂ))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ))
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ ℂ)) (h : I = J)
    [AlgebraicGeometry.IsNoetherian (Proj (HomogeneousQuotientProjective.grading I hI))]
    [AlgebraicGeometry.IsNoetherian (Proj (HomogeneousQuotientProjective.grading J hJ))]
    (b : ℕ) :
    (Module.Finite ℚ (TotalChowQ (HomogeneousQuotientCharts.structureMap I hI)) ∧
      Module.finrank ℚ (TotalChowQ (HomogeneousQuotientCharts.structureMap I hI)) ≤ b) ↔
    (Module.Finite ℚ (TotalChowQ (HomogeneousQuotientCharts.structureMap J hJ)) ∧
      Module.finrank ℚ (TotalChowQ (HomogeneousQuotientCharts.structureMap J hJ)) ≤ b) := by
  subst J
  rfl

/-- The complete dimension-graded Chow group is finite dimensional and
has rank at most the number of independent coordinate pivots. Every
stratum is included, and the filtration terminates at the empty scheme. -/
theorem chain_total_chow_rank (k t : ℕ) (hs : t+2 ≤ k+1) :
    letI := chain_isNoetherian k t hs
    Module.Finite ℚ (TotalChowQ
      (isotropicStructureMap (t := t) (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))) ∧
      Module.finrank ℚ (TotalChowQ
        (isotropicStructureMap (t := t) (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))) ≤
        Nat.choose (2*k+2-(t+2)) (t+2) := by
  classical
  letI := chain_isNoetherian k t hs
  letI : Nonempty (PluckerIndex (t+2) (2*k+1)) := ⟨oddCoordinatePivot k t hs⟩
  let N := pivotCount (t+2) (2*k+1)
  let stage (m : ℕ) := filtrationScheme (K := ℂ)
    (pivotPrefix (t+2) (2*k+1) m) (2*k+1) (2*k)
  let base (m : ℕ) : stage m ⟶ complexBase :=
    filtrationStructureMap (pivotPrefix (t+2) (2*k+1) m) (2*k+1) (2*k)
  let presentation (m : ℕ) := HomogeneousQuotientProjective.projectivePresentation
    (filtrationIdeal (K := ℂ) (pivotPrefix (t+2) (2*k+1) m) (2*k+1) (2*k))
    (filtrationIdeal_isHomogeneous _ _ _)
  letI : ∀ m, AlgebraicGeometry.IsNoetherian (stage m) :=
    fun m => (presentation m).isNoetherian
  letI : ∀ m, LocallyOfFiniteType (base m) :=
    fun m => (presentation m).finiteType.1
  let closed (m : ℕ) : stage (m+1) ⟶ stage m :=
    filtrationInclusion (pivotPrefix_mono (t+2) (2*k+1) (Nat.le_succ m)) (2*k+1) (2*k)
  letI : ∀ m, IsClosedImmersion (closed m) := fun m =>
    filtrationInclusion_isClosedImmersion _ _ _
  let cell (m : ℕ) (hm : m < N) : (stage m).Opens :=
    filtrationChart (pivotPrefix (t+2) (2*k+1) m)
      (weightOrderedPivots (t+2) (2*k+1) ⟨m,hm⟩) (2*k+1) (2*k)
  have hover (m : ℕ) : closed m ≫ base m = base (m+1) :=
    filtrationInclusion_over _ _ _
  have hcomplement (m : ℕ) (hm : m < N) :
      Set.range (closed m) = (Set.range (cell m hm).ι)ᶜ := by
    dsimp only [cell]
    exact orderedFiltration_closed_open_complement (K := ℂ) ⟨m,hm⟩ (2*k+1) (2*k)
  have hempty : IsEmpty (stage N) := by
    refine ⟨fun x => ?_⟩
    have hx : filtrationToOriginal (K := ℂ) (pivotPrefix (t+2) (2*k+1) N)
        (2*k+1) (2*k) x ∈ Set.range
          (filtrationToOriginal (K := ℂ) (pivotPrefix (t+2) (2*k+1) N) (2*k+1) (2*k)) :=
      ⟨x,rfl⟩
    rw [filtration_image_final] at hx
    exact hx
  have hcell (m : ℕ) (hm : m < N) :
      Module.Finite ℚ (TotalChowQ ((cell m hm).ι ≫ base m)) ∧
        Module.finrank ℚ (TotalChowQ ((cell m hm).ι ≫ base m)) ≤ cellBudget k (t+2) m := by
    dsimp only [cell]
    let i : Fin N := ⟨m,hm⟩
    let p := weightOrderedPivots (t+2) (2*k+1) i
    let E := pivotPrefix (t+2) (2*k+1) m
    have hE : EarlierSet p E := pivotPrefix_earlier _ _ i
    by_cases hp : IndependentPivots (indexEmbedding p)
    · have h := finite_and_finrank_le_one_of_polynomialIso
        ((filtrationChart (K := ℂ) E p (2*k+1) (2*k)).ι ≫ base m)
        {v : Coordinate (indexEmbedding p) // v ∉ Set.range (pivotEmbedding hp)}
        (filtrationChartIsoAffine E p hE hp)
        (filtrationChartIsoAffine_hom_over E p hE hp)
      have hb : cellBudget k (t+2) m = 1 := by
        unfold cellBudget
        rw [dif_pos hm]
        exact if_pos hp
      rw [hb]
      exact h
    · letI := filtrationChart_isEmpty_of_not_independent (K := ℂ) E p hE hp
      have h := finite_and_finrank_eq_zero_of_empty
        ((filtrationChart (K := ℂ) E p (2*k+1) (2*k)).ι ≫ base m)
      refine ⟨h.1,?_⟩
      rw [h.2]
      exact Nat.zero_le _
  have h := boundedFinitePaving_total_rank stage base closed hover N cell hcomplement hempty
    (cellBudget k (t+2)) hcell
  rw [sum_cellBudget k (t+2) hs] at h
  have hI : filtrationIdeal (K := ℂ) (pivotPrefix (t+2) (2*k+1) 0) (2*k+1) (2*k) =
      isotropicPluckerIdeal (t := t) (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)) := by
    simp only [filtrationIdeal, pivotPrefix_zero, Set.image_empty, Ideal.span_empty, sup_bot_eq]
  letI := (presentation 0).isNoetherian
  letI : AlgebraicGeometry.IsNoetherian (Proj (HomogeneousQuotientProjective.grading
      (isotropicPluckerIdeal (t := t) (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))
      (isotropicPluckerIdeal_isHomogeneous _))) :=
    (chainProjectivePresentation k t hs).isNoetherian
  exact (homogeneousQuotient_total_rank_congr
    (filtrationIdeal (K := ℂ) (pivotPrefix (t+2) (2*k+1) 0) (2*k+1) (2*k))
    (isotropicPluckerIdeal (t := t) (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))
    (filtrationIdeal_isHomogeneous _ _ _)
    (isotropicPluckerIdeal_isHomogeneous _) hI _).mp h

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicPavingChowRank"

section ComponentSource_2
/- Original module: PaperVerification.OriginalOddChowRank -/


/-!
# The Chow-rank bound in the paper's literal coordinates

The attracting chart calculation uses the displayed permutation to the
anti-diagonal pencil. This file transports its actual Chow groups back to
both the Section 4 forms and the literal path pencil (2). The latter two
pencils generate exactly the same homogeneous ideal.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory MvPolynomial
open AlternatingForms TotalChow
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionFour_isNoetherian (k t : ℕ) (hs : t+2 ≤ k+1) :
    AlgebraicGeometry.IsNoetherian (Proj (isotropicProjectiveGrading (t := t)
      (sectionFourPluckerForms (K := ℂ) k))) := by
  letI : Nonempty (PluckerIndex (t+2) (2*k+1)) := ⟨oddCoordinatePivot k t hs⟩
  exact (HomogeneousQuotientProjective.projectivePresentation
    (isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := ℂ) k))
    (isotropicPluckerIdeal_isHomogeneous _)).isNoetherian

theorem originalOdd_isNoetherian (k t : ℕ) (hs : t+2 ≤ k+1) :
    AlgebraicGeometry.IsNoetherian (Proj (isotropicProjectiveGrading (t := t)
      (oddPluckerForms (K := ℂ) k))) := by
  letI : Nonempty (PluckerIndex (t+2) (2*k+1)) := ⟨oddCoordinatePivot k t hs⟩
  exact (HomogeneousQuotientProjective.projectivePresentation
    (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := ℂ) k))
    (isotropicPluckerIdeal_isHomogeneous _)).isNoetherian

/-- The complete genuine Chow group of the Section 4 scheme. -/
theorem sectionFour_total_chow_rank (k t : ℕ) (hs : t+2 ≤ k+1) :
    letI := sectionFour_isNoetherian k t hs
    Module.Finite ℚ (TotalChowQ (isotropicStructureMap (t := t)
      (sectionFourPluckerForms (K := ℂ) k))) ∧
      Module.finrank ℚ (TotalChowQ (isotropicStructureMap (t := t)
        (sectionFourPluckerForms (K := ℂ) k))) ≤
          Nat.choose (2*k+2-(t+2)) (t+2) := by
  letI := sectionFour_isNoetherian k t hs
  letI := chain_isNoetherian k t hs
  letI : Nonempty (PluckerIndex (t+2) (2*k+1)) := ⟨oddCoordinatePivot k t hs⟩
  letI : LocallyOfFiniteType (isotropicStructureMap (t := t)
      (sectionFourPluckerForms (K := ℂ) k)) :=
    (HomogeneousQuotientProjective.projectivePresentation
      (isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := ℂ) k))
      (isotropicPluckerIdeal_isHomogeneous _)).finiteType.1
  letI : LocallyOfFiniteType (isotropicStructureMap (t := t)
      (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k))) :=
    (chainProjectivePresentation k t hs).finiteType.1
  let C := totalChowEquiv (chainSectionFourIso (K := ℂ) k t) _ _
    (chainSectionFourIso_hom_over k t)
  have h := chain_total_chow_rank k t hs
  letI := h.1
  exact ⟨Module.Finite.equiv C,C.finrank_eq.symm.trans_le h.2⟩

/-- The same rank bound for the literal original path pencil (2), with
all genuine algebraic cycles and all gradings retained. -/
theorem originalOdd_total_chow_rank (k t : ℕ) (hs : t+2 ≤ k+1) :
    letI := originalOdd_isNoetherian k t hs
    Module.Finite ℚ (TotalChowQ (isotropicStructureMap (t := t)
      (oddPluckerForms (K := ℂ) k))) ∧
      Module.finrank ℚ (TotalChowQ (isotropicStructureMap (t := t)
        (oddPluckerForms (K := ℂ) k))) ≤
          Nat.choose (2*k+2-(t+2)) (t+2) := by
  letI := originalOdd_isNoetherian k t hs
  letI := sectionFour_isNoetherian k t hs
  letI : AlgebraicGeometry.IsNoetherian (Proj (HomogeneousQuotientProjective.grading
      (isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := ℂ) k))
      (isotropicPluckerIdeal_isHomogeneous _))) := sectionFour_isNoetherian k t hs
  letI : AlgebraicGeometry.IsNoetherian (Proj (HomogeneousQuotientProjective.grading
      (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := ℂ) k))
      (isotropicPluckerIdeal_isHomogeneous _))) := originalOdd_isNoetherian k t hs
  exact (homogeneousQuotient_total_rank_congr
    (isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := ℂ) k))
    (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := ℂ) k))
    (isotropicPluckerIdeal_isHomogeneous _) (isotropicPluckerIdeal_isHomogeneous _)
    (sectionFour_isotropicPluckerIdeal k t) _).mp (sectionFour_total_chow_rank k t hs)

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.OriginalOddChowRank"

section ComponentSource_3
/- Original module: PaperVerification.SymmetricProjectiveTotalChowRank -/


/-!
# The one-plane boundary: the actual Chow rank of projective space

The proof inducts on the dimension of the vector space, using its genuine
projective hyperplane and complementary affine space. The rank-zero base
is the empty projective spectrum, so no projective-bundle formula or Chern
relation is used or assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TotalChow

open AlgebraicGeometry CategoryTheory
open OAI.AlgebraicGeometry.Divisors.LineBundles
open SymmetricProjective.Scheme.BundleCycles

open SymmetricProjectiveEmpty

variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]

instance symmetricAlgebra_isNoetherian : IsNoetherianRing (SymmetricAlgebra ℂ M) := by
  letI := SymmetricProjective.Proper.BundleCycles.symmetricAlgebra_finiteType ℂ M
  exact Algebra.FiniteType.isNoetherianRing ℂ _

instance symmetricAffine_isNoetherian : AlgebraicGeometry.IsNoetherian
    (Spec (CommRingCat.of (SymmetricAlgebra ℂ M))) :=
  (AlgebraicGeometry.isNoetherian_Spec (R := CommRingCat.of (SymmetricAlgebra ℂ M))).mpr
    (symmetricAlgebra_isNoetherian M)

instance symmetricAffineToBase_finiteType : LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (SymmetricAlgebra ℂ M)))) := by
  letI := SymmetricProjective.Proper.BundleCycles.symmetricAlgebra_finiteType ℂ M
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- The actual affine symmetric spectrum of a finite complex vector
space has total Chow rank at most one. -/
theorem symmetricAffine_total_rank :
    letI := symmetricAffine_isNoetherian M
    Module.Finite ℚ (TotalChowQ
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (SymmetricAlgebra ℂ M))))) ∧
      Module.finrank ℚ (TotalChowQ
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (SymmetricAlgebra ℂ M))))) ≤ 1 := by
  letI := symmetricAffine_isNoetherian M
  letI := symmetricAffineToBase_finiteType M
  let b := Module.finBasis ℂ M
  let e := Scheme.Spec.mapIso
    (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv.toCommRingCatIso.op
  exact finite_and_finrank_le_one_of_polynomialIso _ _ e
    (AlternatingForms.specAlgEquiv_hom_over (SymmetricAlgebra.equivMvPolynomial b))

/-- Adding a scalar summand adds one genuine affine stratum. -/
theorem symmetricProjective_total_rank_step
    (hM : Module.Finite ℚ (TotalChowQ (symmetricProjectiveToBase ℂ M))) :
    Module.Finite ℚ (TotalChowQ (symmetricProjectiveToBase ℂ (ℂ × M))) ∧
      Module.finrank ℚ (TotalChowQ (symmetricProjectiveToBase ℂ (ℂ × M))) ≤
        Module.finrank ℚ (TotalChowQ (symmetricProjectiveToBase ℂ M)) + 1 := by
  let p := symmetricProjectiveToBase ℂ (ℂ × M)
  let j := SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion ℂ M
  let i := Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification ℂ M
  have hj : j ≫ p = symmetricProjectiveToBase ℂ M :=
    SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over _ _
  have hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap ℂ (SymmetricAlgebra ℂ M))) :=
    Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification_over ℂ M
  have hc : Set.range j = (Set.range i)ᶜ := by
    simpa only [Scheme.Hom.coe_opensRange] using
      SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion_range ℂ M
  have ha := symmetricAffine_total_rank M
  letI : Module.Finite ℚ (TotalChowQ (j ≫ p)) := by rw [hj]; exact hM
  letI : Module.Finite ℚ (TotalChowQ (i ≫ p)) := by rw [hi]; exact ha.1
  refine ⟨finite_of_closed_open i j p hc,?_⟩
  have h := finrank_le_closed_add_open i j p hc
  rw [hj,hi] at h
  exact h.trans (Nat.add_le_add_left ha.2 _)

/-- A coordinate vector space of rank n has projective Chow rank at most n,
including rank zero, whose actual projective spectrum is empty. -/
theorem coordinateProjective_total_rank (n : ℕ) :
    Module.Finite ℚ (TotalChowQ (symmetricProjectiveToBase ℂ (Fin n → ℂ))) ∧
      Module.finrank ℚ (TotalChowQ (symmetricProjectiveToBase ℂ (Fin n → ℂ))) ≤ n := by
  induction n with
  | zero =>
    letI := symmetricProjective_isEmpty_of_subsingleton ℂ (Fin 0 → ℂ)
    have h := finite_and_finrank_eq_zero_of_empty (symmetricProjectiveToBase ℂ (Fin 0 → ℂ))
    exact ⟨h.1,h.2.le⟩
  | succ n ih =>
    let e : (Fin (n+1) → ℂ) ≃ₗ[ℂ] ℂ × (Fin n → ℂ) :=
      LinearEquiv.piCongrLeft ℂ (fun _ => ℂ) (finSuccEquiv n) ≪≫ₗ
        LinearEquiv.piOptionEquivProd ℂ
    let E := symmetricProjectiveIso e
    have hover : E.hom ≫ symmetricProjectiveToBase ℂ (ℂ × (Fin n → ℂ)) =
        symmetricProjectiveToBase ℂ (Fin (n+1) → ℂ) :=
      SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over
        e.symm.toLinearMap e.symm.surjective
    let C := totalChowEquiv E _ _ hover
    have h := symmetricProjective_total_rank_step (Fin n → ℂ) ih.1
    letI := h.1
    refine ⟨Module.Finite.equiv C.symm,?_⟩
    rw [C.finrank_eq]
    exact h.2.trans (Nat.add_le_add_right ih.2 1)

/-- The result is independent of a chosen basis and concerns the actual
projective spectrum of the given finite vector space. -/
theorem symmetricProjective_total_rank :
    Module.Finite ℚ (TotalChowQ (symmetricProjectiveToBase ℂ M)) ∧
      Module.finrank ℚ (TotalChowQ (symmetricProjectiveToBase ℂ M)) ≤ Module.finrank ℂ M := by
  let e := symmetricProjectiveIso (Module.finBasis ℂ M).equivFun
  have hover : e.hom ≫ symmetricProjectiveToBase ℂ (Fin (Module.finrank ℂ M) → ℂ) =
      symmetricProjectiveToBase ℂ M :=
    SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over
      (Module.finBasis ℂ M).equivFun.symm.toLinearMap
      (Module.finBasis ℂ M).equivFun.symm.surjective
  let C := totalChowEquiv e _ _ hover
  have h := coordinateProjective_total_rank (Module.finrank ℂ M)
  letI := h.1
  exact ⟨Module.Finite.equiv C.symm,C.finrank_eq.trans_le h.2⟩

end PaperVerification.TotalChow
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SymmetricProjectiveTotalChowRank"

section ComponentSource_4
/- Original module: PaperVerification.OnePlaneChowRank -/


/-!
# The original one-plane boundary of the Chow rank theorem

Every alternating form vanishes on a line, so the original one-plane common
isotropic scheme is the full original Plücker projective space. The comparison
below uses its literal quotient ring and the genuine symmetric projective
hyperplane calculation, retaining the scalar morphism throughout.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TotalChow

open AlgebraicGeometry CategoryTheory
open AlternatingForms
open OAI.AlgebraicGeometry.Divisors.LineBundles
open SymmetricProjective.Scheme.BundleCycles

/-- The actual original one-plane Chow group has total rank at most the
ambient vector-space dimension. -/
theorem onePlane_total_chow_rank (n : ℕ) (hn : 0 < n) :
    letI := (onePlaneOriginalProjectivePresentation n hn).isNoetherian
    Module.Finite ℚ (TotalChowQ (onePlaneOriginalStructureMap (K := ℂ) n)) ∧
      Module.finrank ℚ (TotalChowQ (onePlaneOriginalStructureMap (K := ℂ) n)) ≤ n := by
  letI := (onePlaneOriginalProjectivePresentation n hn).isNoetherian
  letI := (onePlaneOriginalProjectivePresentation n hn).finiteType.1
  let b := Pi.basisFun ℂ (Fin n)
  let E := onePlaneOriginalProjIsoPolynomial (K := ℂ) n ≪≫
    SymmetricFreeProjectiveIso.projectiveIso b
  have hover : E.hom ≫ symmetricProjectiveToBase ℂ (Fin n → ℂ) =
      onePlaneOriginalStructureMap (K := ℂ) n := by
    change (_ ≫ _) ≫ _ = _
    rw [Category.assoc, SymmetricFreeProjectiveIso.projectiveIso_hom_over,
      onePlaneOriginalProjIsoPolynomial_hom_over]
  let C := totalChowEquiv E _ _ hover
  have h := coordinateProjective_total_rank n
  letI := h.1
  exact ⟨Module.Finite.equiv C.symm, C.finrank_eq.trans_le h.2⟩

end PaperVerification.TotalChow
end
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.OnePlaneChowRank"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.TotalChow.symmetricAffine_total_rank, "theorem"),
    (`PaperVerification.TotalChow.symmetricProjective_total_rank_step, "theorem"),
    (`PaperVerification.TotalChow.coordinateProjective_total_rank, "theorem"),
    (`PaperVerification.TotalChow.symmetricProjective_total_rank, "theorem"),
    (`PaperVerification.TotalChow.onePlane_total_chow_rank, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.sectionFour_isNoetherian, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.originalOdd_isNoetherian, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.sectionFour_total_chow_rank, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.originalOdd_total_chow_rank, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "ba481a0aa5aac928845b461b6a37532a"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:ba481a0aa5aac928845b461b6a37532a"
