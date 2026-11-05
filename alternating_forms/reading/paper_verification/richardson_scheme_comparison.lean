module

public import PaperVerification.RichardsonRingComparison
public import PaperVerification.AlternatingFormsSectionZeroScheme

/-!
# The actual Richardson rank scheme and its Plücker presentation

The ambient scheme and its polynomial charts are fixed first.  Opposite
flag conditions are imposed by their actual determinantal ideals on these
charts.  The comparison below identifies the resulting closed subscheme
with the Proj of the original interval Plücker ideal, over every field.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open _root_.HomogeneousLocalization

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem intervalPluckerIdeal_isHomogeneous
    (α β : Fin (t + 2) → Fin n) :
    (intervalPluckerIdeal (K := K) α β).IsHomogeneous
      (homogeneousSubmodule (PluckerIndex (t + 2) n) K) := by
  apply (matrixPluckerIdeal_isHomogeneous (by omega : 0 < t + 2)).sup
  apply Ideal.homogeneous_span
  rintro q ⟨I, hI, rfl⟩
  exact ⟨1, isHomogeneous_X K I⟩

/-- The literal grading on the paper's interval-coordinate quotient. -/
def richardsonProjectiveGrading (α β : Fin (t + 2) → Fin n) :=
  HomogeneousQuotientProjective.grading (intervalPluckerIdeal (K := K) α β)
    (intervalPluckerIdeal_isHomogeneous α β)

instance richardsonProjectiveGradedAlgebra (α β : Fin (t + 2) → Fin n) :
    GradedAlgebra (richardsonProjectiveGrading (K := K) α β) :=
  HomogeneousQuotientProjective.quotientGradedAlgebra _ _

theorem ambientPluckerIdeal_le_interval (α β : Fin (t + 2) → Fin n) :
    isotropicPluckerIdeal (t := t) (emptyAlternatingTuple (K := K) (n := n)) ≤
      intervalPluckerIdeal α β := by
  rw [isotropicPluckerIdeal_empty]
  exact le_sup_left

/-- The graded quotient retaining the original ambient Plücker coordinates. -/
abbrev richardsonAmbientGradedQuotient (α β : Fin (t + 2) → Fin n) :=
  HomogeneousQuotientProjective.quotientGradedHom
    (isotropicPluckerIdeal (t := t) (emptyAlternatingTuple (K := K) (n := n)))
    (intervalPluckerIdeal (K := K) α β)
    (isotropicPluckerIdeal_isHomogeneous emptyAlternatingTuple)
    (intervalPluckerIdeal_isHomogeneous α β) (ambientPluckerIdeal_le_interval α β)

/-- The canonical projective closed immersion into the ambient Grassmannian. -/
def richardsonAmbientImmersion (α β : Fin (t + 2) → Fin n) :
    Proj (richardsonProjectiveGrading (K := K) α β) ⟶
      ambientGrassmannian (K := K) t n :=
  HomogeneousQuotientProjective.quotientProjMap _ _ _ _
    (ambientPluckerIdeal_le_interval α β)

instance richardsonAmbientImmersion_isClosedImmersion
    (α β : Fin (t + 2) → Fin n) :
    IsClosedImmersion (richardsonAmbientImmersion (K := K) α β) :=
  HomogeneousQuotientProjective.quotientProjMap_isClosedImmersion _ _ _ _ _

/-- Independent local equations: actual minors for the two opposite flags. -/
def richardsonChartIdeal (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) : Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  richardsonChartRankIdeal (pluckerChartMatrix p) α β

theorem intervalPluckerIdeal_map_chart_eq
    (p : PluckerIndex (t + 2) n) (α β : Fin (t + 2) → Fin n) :
    (intervalPluckerIdeal (K := K) α β).map
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
        richardsonChartIdeal (K := K) p α β :=
  intervalPluckerIdeal_map_eq_richardsonChartRankIdeal (K := K)
    (pluckerChartMatrix (K := K) p) p.val (pluckerChartMatrix_pivot p) α β

abbrev RichardsonChartRing (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :=
  MvPolynomial (PluckerChartVariable p) K ⧸ richardsonChartIdeal p α β

/-- The original polynomial evaluated on the normalized chart, then
reduced by its independent opposite-flag rank equations. -/
def richardsonChartEvaluation (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    MvPolynomial (PluckerIndex (t + 2) n) K →ₐ[K] RichardsonChartRing (K := K) p α β :=
  (Ideal.Quotient.mkₐ K (richardsonChartIdeal p α β)).comp
    (matrixMinorEvaluation (pluckerChartMatrix p))

theorem richardsonChartEvaluation_surjective (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    Function.Surjective (richardsonChartEvaluation (K := K) p α β) :=
  (Ideal.Quotient.mkₐ_surjective K _).comp (matrixMinorEvaluation_chart_surjective p)

theorem richardsonChartEvaluation_kernel (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    RingHom.ker (richardsonChartEvaluation (K := K) p α β).toRingHom =
      intervalPluckerIdeal α β ⊔ Ideal.span {X p - 1} := by
  have h := Ideal.comap_map_of_surjective
    (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom
    (matrixMinorEvaluation_chart_surjective p) (intervalPluckerIdeal (K := K) α β)
  rw [intervalPluckerIdeal_map_chart_eq p α β, ← RingHom.ker_eq_comap_bot,
    matrixMinorEvaluation_chart_kernel] at h
  have hk : RingHom.ker (richardsonChartEvaluation (K := K) p α β).toRingHom =
      (richardsonChartIdeal (K := K) p α β).comap
        (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom := by
    ext q
    change (Ideal.Quotient.mkₐ K (richardsonChartIdeal p α β))
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q) = 0 ↔ _
    exact Ideal.Quotient.eq_zero_iff_mem
  have hgrass : (matrixPluckerIdeal (K := K) (s := t + 2) (n := n)) ≤
      intervalPluckerIdeal α β := le_sup_left
  rw [hk, h, pluckerBigCellIdeal, ← sup_assoc, sup_of_le_left hgrass]

/-- The actual normalized homogeneous quotient is the quotient by the
independently defined opposite flag minors. -/
def richardsonPluckerBigCellEquiv (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    (MvPolynomial (PluckerIndex (t + 2) n) K ⧸
      (intervalPluckerIdeal α β ⊔ Ideal.span {X p - 1})) ≃ₐ[K]
        RichardsonChartRing (K := K) p α β :=
  (Ideal.quotientEquivAlgOfEq K (richardsonChartEvaluation_kernel p α β).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (richardsonChartEvaluation_surjective p α β))

def richardsonProjChartRingEquiv (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    Away (richardsonProjectiveGrading (K := K) α β)
      (Ideal.Quotient.mk _ (X p)) ≃+* RichardsonChartRing (K := K) p α β :=
  (HomogeneousQuotientCharts.awayQuotientChartEquiv
    (intervalPluckerIdeal α β) (intervalPluckerIdeal_isHomogeneous α β) p).trans
    (richardsonPluckerBigCellEquiv p α β).toRingEquiv

def richardsonHomogeneousClass (α β : Fin (t + 2) → Fin n)
    {d : ℕ} (a : MvPolynomial (PluckerIndex (t + 2) n) K) (ha : a.IsHomogeneous d) :
    richardsonProjectiveGrading (K := K) α β d :=
  ⟨Ideal.Quotient.mk _ a, by
    change _ ∈ HomogeneousQuotientProjective.grading _ _ d
    rw [HomogeneousQuotientProjective.grading_eq_piece]
    exact ⟨a, ha, rfl⟩⟩

theorem richardsonChartRingEquiv_fraction (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) {d : ℕ}
    (a : MvPolynomial (PluckerIndex (t + 2) n) K) (ha : a.IsHomogeneous d) :
    richardsonProjChartRingEquiv p α β
      (HomogeneousChartDehomogenization.fraction
        (richardsonProjectiveGrading α β)
        (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
        (richardsonHomogeneousClass α β a ha)) =
      richardsonChartEvaluation p α β a := by
  rw [richardsonProjChartRingEquiv, RingEquiv.trans_apply,
    HomogeneousQuotientCharts.awayQuotientChartEquiv, RingEquiv.trans_apply]
  erw [HomogeneousChartDehomogenization.awayEquivNormalized_fraction]
  change richardsonPluckerBigCellEquiv p α β
    (HomogeneousQuotientCharts.normalizedQuotientEquiv _ p
      (HomogeneousChartDehomogenization.quotientMap _
        (Ideal.Quotient.mk _ a))) = _
  rw [HomogeneousQuotientCharts.normalizedQuotientEquiv_class]
  have h₁ := Ideal.quotientEquivAlgOfEq_mk K
    (richardsonChartEvaluation_kernel p α β).symm a
  have h₂ := Ideal.quotientKerAlgEquivOfSurjective_mk
    (f := richardsonChartEvaluation p α β)
    (richardsonChartEvaluation_surjective p α β) a
  exact (congrArg (Ideal.quotientKerAlgEquivOfSurjective
    (f := richardsonChartEvaluation p α β)
    (richardsonChartEvaluation_surjective p α β)) h₁).trans h₂

theorem richardsonAmbientAwayMap_fraction (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) {d : ℕ}
    (a : MvPolynomial (PluckerIndex (t + 2) n) K) (ha : a.IsHomogeneous d) :
    Away.map (richardsonAmbientGradedQuotient (K := K) α β)
      (Ideal.Quotient.mk _ (X p))
      (HomogeneousChartDehomogenization.fraction
        (isotropicProjectiveGrading (t := t) emptyAlternatingTuple)
        (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
        (chartHomogeneousClass emptyAlternatingTuple a ha)) =
      HomogeneousChartDehomogenization.fraction (richardsonProjectiveGrading α β)
        (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
        (richardsonHomogeneousClass α β a ha) := by
  simp only [HomogeneousChartDehomogenization.fraction, Away.map_mk]
  rfl

theorem richardsonChartRing_commutes (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    (richardsonProjChartRingEquiv (K := K) p α β).toRingHom.comp
        (Away.map (richardsonAmbientGradedQuotient α β) (Ideal.Quotient.mk _ (X p))) =
      (Ideal.Quotient.mk (richardsonChartIdeal p α β)).comp
        (ambientChartRingEquiv p).toRingHom := by
  ext z
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective
    (isotropicProjectiveGrading (t := t) (emptyAlternatingTuple (K := K) (n := n)))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) z
  change a ∈ HomogeneousQuotientProjective.grading _ _ (d • 1) at ha
  rw [HomogeneousQuotientProjective.grading_eq_piece] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hbd : b.IsHomogeneous d := by simpa using hb
  change richardsonProjChartRingEquiv p α β
      (Away.map (richardsonAmbientGradedQuotient α β) (Ideal.Quotient.mk _ (X p))
        (HomogeneousChartDehomogenization.fraction _
          (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
          (chartHomogeneousClass emptyAlternatingTuple b hbd))) = _
  erw [richardsonAmbientAwayMap_fraction, richardsonChartRingEquiv_fraction]
  change richardsonChartEvaluation p α β b =
    Ideal.Quotient.mk _
      (emptyIsotropicChartRingEquiv p
        (isotropicProjChartRingEquiv_arbitraryChar p emptyAlternatingTuple
          (HomogeneousChartDehomogenization.fraction _
            (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
            (chartHomogeneousClass emptyAlternatingTuple b hbd))))
  rw [isotropicChartRingEquiv_fraction]
  change Ideal.Quotient.mk _ (matrixMinorEvaluation (pluckerChartMatrix p) b) =
    Ideal.Quotient.mk _
      (emptyIsotropicChartRingEquiv p
        (Ideal.Quotient.mk _ (matrixMinorEvaluation (pluckerChartMatrix p) b)))
  rw [emptyIsotropicChartRingEquiv_mk]

/-- Each literal determinantal chart is an actual open chart of the Proj. -/
def richardsonAffineChartι (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    Spec (CommRingCat.of (RichardsonChartRing (K := K) p α β)) ⟶
      Proj (richardsonProjectiveGrading (K := K) α β) :=
  Spec.map (CommRingCat.ofHom (richardsonProjChartRingEquiv p α β).toRingHom) ≫
    Proj.awayι (richardsonProjectiveGrading α β) (Ideal.Quotient.mk _ (X p))
      (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) one_pos

instance richardsonAffineChartι_isOpenImmersion (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    IsOpenImmersion (richardsonAffineChartι (K := K) p α β) := by
  letI : IsIso (CommRingCat.ofHom (richardsonProjChartRingEquiv (K := K) p α β).toRingHom) :=
    (richardsonProjChartRingEquiv p α β).toCommRingCatIso.isIso_hom
  unfold richardsonAffineChartι
  infer_instance

theorem richardsonAffineChartι_opensRange (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    (richardsonAffineChartι (K := K) p α β).opensRange =
      Proj.basicOpen (richardsonProjectiveGrading α β) (Ideal.Quotient.mk _ (X p)) := by
  letI : IsIso (CommRingCat.ofHom (richardsonProjChartRingEquiv (K := K) p α β).toRingHom) :=
    (richardsonProjChartRingEquiv p α β).toCommRingCatIso.isIso_hom
  unfold richardsonAffineChartι
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

theorem richardsonAffineChart_ambient_commutes (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    richardsonAffineChartι (K := K) p α β ≫ richardsonAmbientImmersion α β =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal p α β))) ≫
        ambientAffineChartι p := by
  have hcomp :
      Proj.awayι (richardsonProjectiveGrading (K := K) α β)
          (Ideal.Quotient.mk _ (X p))
          (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) one_pos ≫
        richardsonAmbientImmersion α β =
      Spec.map (CommRingCat.ofHom
          (Away.map (richardsonAmbientGradedQuotient α β) (Ideal.Quotient.mk _ (X p)))) ≫
        Proj.awayι (isotropicProjectiveGrading (t := t) emptyAlternatingTuple)
          (Ideal.Quotient.mk _ (X p))
          (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) one_pos := by
    exact Proj.awayι_comp_map (richardsonAmbientGradedQuotient α β)
      (irrelevant_le_map_of_gradedSurjective _
        (HomogeneousQuotientProjective.quotientGradedHom_surjective _ _ _ _ _))
      one_pos (Ideal.Quotient.mk _ (X p))
      (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p)
  have hring :
      CommRingCat.ofHom
          (Away.map (richardsonAmbientGradedQuotient (K := K) α β) (Ideal.Quotient.mk _ (X p))) ≫
        CommRingCat.ofHom (richardsonProjChartRingEquiv p α β).toRingHom =
      CommRingCat.ofHom (ambientChartRingEquiv (K := K) p).toRingHom ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal p α β)) := by
    apply CommRingCat.hom_ext
    exact richardsonChartRing_commutes p α β
  unfold richardsonAffineChartι ambientAffineChartι
  rw [Category.assoc, hcomp, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp_assoc, hring]

theorem richardsonAffineChart_ambient_isPullback (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal (K := K) p α β))))
      (richardsonAffineChartι p α β) (ambientAffineChartι p)
      (richardsonAmbientImmersion α β) := by
  apply IsOpenImmersion.isPullback
  · exact richardsonAffineChart_ambient_commutes p α β
  · rw [ambientAffineChartι_opensRange, richardsonAffineChartι_opensRange]
    rfl

theorem richardsonProjBasicOpen_cover (α β : Fin (t + 2) → Fin n) :
    (⨆ p : PluckerIndex (t + 2) n, Proj.basicOpen (richardsonProjectiveGrading (K := K) α β)
      (Ideal.Quotient.mk (intervalPluckerIdeal α β) (X p))) = ⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover _ _
    (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)) Ideal.Quotient.mk_surjective
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)

def richardsonAffineChartCover (α β : Fin (t + 2) → Fin n) :
    (Proj (richardsonProjectiveGrading (K := K) α β)).AffineOpenCover where
  I₀ := PluckerIndex (t + 2) n
  X p := CommRingCat.of (RichardsonChartRing (K := K) p α β)
  f p := richardsonAffineChartι p α β
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((richardsonProjBasicOpen_cover α β).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (richardsonAffineChartι _ α β).opensRange
    rw [richardsonAffineChartι_opensRange]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((richardsonProjBasicOpen_cover α β).ge (Set.mem_univ x))).choose_spec

/-- The local opposite-flag zero scheme mapped into the ambient Grassmannian. -/
def richardsonRankChartZeroMap (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    Spec (CommRingCat.of (RichardsonChartRing (K := K) p α β)) ⟶
      ambientGrassmannian (K := K) t n :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal p α β))) ≫
    ambientAffineChartι p

/-- The independent opposite-Schubert rank ideal sheaf. -/
def richardsonRankZeroIdeal (α β : Fin (t + 2) → Fin n) :
    (ambientGrassmannian (K := K) t n).IdealSheafData :=
  ⨅ p : PluckerIndex (t + 2) n, (richardsonRankChartZeroMap (K := K) p α β).ker

abbrev richardsonRankZeroScheme (α β : Fin (t + 2) → Fin n) : Scheme :=
  (richardsonRankZeroIdeal (K := K) α β).subscheme

theorem richardsonRankZeroIdeal_eq_kernel (α β : Fin (t + 2) → Fin n) :
    richardsonRankZeroIdeal (K := K) α β = (richardsonAmbientImmersion α β).ker := by
  calc
    richardsonRankZeroIdeal α β =
        ⨅ p : PluckerIndex (t + 2) n,
          (richardsonAffineChartι p α β ≫ richardsonAmbientImmersion α β).ker := by
      apply iInf_congr
      intro p
      exact congrArg Scheme.Hom.ker (richardsonAffineChart_ambient_commutes p α β).symm
    _ = (richardsonAmbientImmersion α β).ker :=
      (richardsonAmbientImmersion α β).iInf_ker_openCover_map_comp
        (richardsonAffineChartCover α β).openCover

/-- The ideal sheaf restricts to the exact determinantal ideal on every
chart, certifying that the local flag-rank equations glue without alteration. -/
theorem richardsonRankZeroIdeal_chart (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    (richardsonRankZeroIdeal (K := K) α β).comap (ambientAffineChartι p) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal p α β)))).ker := by
  rw [richardsonRankZeroIdeal_eq_kernel]
  ext1
  funext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (richardsonAmbientImmersion α β)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal p α β))))
    (richardsonAffineChartι p α β) (ambientAffineChartι p)
    (richardsonAffineChart_ambient_isPullback p α β) W).symm

def richardsonToRankZero (α β : Fin (t + 2) → Fin n) :
    Proj (richardsonProjectiveGrading (K := K) α β) ⟶ richardsonRankZeroScheme (K := K) α β :=
  IsClosedImmersion.lift (richardsonRankZeroIdeal α β).subschemeι
    (richardsonAmbientImmersion α β) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, richardsonRankZeroIdeal_eq_kernel])

instance richardsonToRankZero_isIso (α β : Fin (t + 2) → Fin n) :
    IsIso (richardsonToRankZero (K := K) α β) :=
  IsClosedImmersion.isIso_lift (richardsonRankZeroIdeal α β).subschemeι
    (richardsonAmbientImmersion α β) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, richardsonRankZeroIdeal_eq_kernel])

/-- The paper's interval Proj is the actual independently specified
Richardson scheme of opposite flag-rank conditions. -/
def richardsonRankZeroIso (α β : Fin (t + 2) → Fin n) :
    Proj (richardsonProjectiveGrading (K := K) α β) ≅ richardsonRankZeroScheme (K := K) α β :=
  asIso (richardsonToRankZero α β)

theorem richardsonRankZeroIso_over_ambient (α β : Fin (t + 2) → Fin n) :
    (richardsonRankZeroIso (K := K) α β).hom ≫ (richardsonRankZeroIdeal α β).subschemeι =
      richardsonAmbientImmersion α β :=
  IsClosedImmersion.lift_fac _ _ _

end PaperVerification.AlternatingForms
