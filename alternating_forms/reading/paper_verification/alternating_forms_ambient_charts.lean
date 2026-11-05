module

public import PaperVerification.AlternatingFormsAmbientImmersion

/-!
# The affine chart maps of the ambient Grassmannian immersion

The local map is the literal quotient of the polynomial row chart by the
original alternating restriction equations.  The comparison is an equality
of scheme morphisms, proved on homogeneous fractions of all degrees.
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

variable {K : Type} [Field K] {t n m : ℕ}

/-- Removing the empty tuple's zero ideal from the polynomial row chart. -/
def emptyIsotropicChartRingEquiv (p : PluckerIndex (t + 2) n) :
    IsotropicChartRing p (emptyAlternatingTuple (K := K) (n := n)) ≃+*
      MvPolynomial (PluckerChartVariable p) K :=
  (Ideal.quotEquivOfEq (isotropicChartIdeal_empty p)).trans (RingEquiv.quotientBot _)

@[simp]
theorem emptyIsotropicChartRingEquiv_mk (p : PluckerIndex (t + 2) n)
    (a : MvPolynomial (PluckerChartVariable p) K) :
    emptyIsotropicChartRingEquiv p (Ideal.Quotient.mk _ a) = a := by
  simp [emptyIsotropicChartRingEquiv]

/-- The Grassmannian's actual degree-zero homogeneous chart is a polynomial ring. -/
def ambientChartRingEquiv (p : PluckerIndex (t + 2) n) :
    Away (isotropicProjectiveGrading (t := t)
      (emptyAlternatingTuple (K := K) (n := n)))
      (Ideal.Quotient.mk _ (X p)) ≃+* MvPolynomial (PluckerChartVariable p) K :=
  (isotropicProjChartRingEquiv_arbitraryChar p emptyAlternatingTuple).trans
    (emptyIsotropicChartRingEquiv p)

/-- The original homogeneous polynomial in its genuine quotient piece. -/
def chartHomogeneousClass (forms : Fin m → StrictPairs n → K)
    {d : ℕ} (a : MvPolynomial (PluckerIndex (t + 2) n) K)
    (ha : a.IsHomogeneous d) : isotropicProjectiveGrading (t := t) forms d :=
  ⟨Ideal.Quotient.mk _ a, by
    change _ ∈ HomogeneousQuotientProjective.grading _ _ d
    rw [HomogeneousQuotientProjective.grading_eq_piece]
    exact ⟨a, ha, rfl⟩⟩

theorem isotropicChartRingEquiv_fraction (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) {d : ℕ}
    (a : MvPolynomial (PluckerIndex (t + 2) n) K) (ha : a.IsHomogeneous d) :
    isotropicProjChartRingEquiv_arbitraryChar p forms
      (HomogeneousChartDehomogenization.fraction
        (isotropicProjectiveGrading (t := t) forms)
        (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
        (chartHomogeneousClass forms a ha)) =
      isotropicChartEvaluation p forms a := by
  rw [isotropicProjChartRingEquiv_arbitraryChar, RingEquiv.trans_apply,
    HomogeneousQuotientCharts.awayQuotientChartEquiv, RingEquiv.trans_apply]
  erw [HomogeneousChartDehomogenization.awayEquivNormalized_fraction]
  change isotropicPluckerBigCellEquiv_arbitraryChar p forms
    (HomogeneousQuotientCharts.normalizedQuotientEquiv _ p
      (HomogeneousChartDehomogenization.quotientMap _
        (Ideal.Quotient.mk _ a))) = _
  rw [HomogeneousQuotientCharts.normalizedQuotientEquiv_class]
  have h₁ := Ideal.quotientEquivAlgOfEq_mk K
    (isotropicChartEvaluation_kernel_arbitraryChar p forms).symm a
  have h₂ := Ideal.quotientKerAlgEquivOfSurjective_mk
    (f := isotropicChartEvaluation p forms)
    (isotropicChartEvaluation_surjective p forms) a
  exact (congrArg (Ideal.quotientKerAlgEquivOfSurjective
    (f := isotropicChartEvaluation p forms)
    (isotropicChartEvaluation_surjective p forms)) h₁).trans h₂

/-- The graded quotient hom underlying the ambient immersion. -/
abbrev ambientGradedQuotient (forms : Fin m → StrictPairs n → K) :=
  HomogeneousQuotientProjective.quotientGradedHom
    (isotropicPluckerIdeal (t := t) (emptyAlternatingTuple (K := K) (n := n)))
    (isotropicPluckerIdeal (t := t) forms)
    (isotropicPluckerIdeal_isHomogeneous emptyAlternatingTuple)
    (isotropicPluckerIdeal_isHomogeneous forms) (ambientPluckerIdeal_le forms)

theorem ambientAwayMap_fraction (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) {d : ℕ}
    (a : MvPolynomial (PluckerIndex (t + 2) n) K) (ha : a.IsHomogeneous d) :
    Away.map (ambientGradedQuotient forms) (Ideal.Quotient.mk _ (X p))
      (HomogeneousChartDehomogenization.fraction
        (isotropicProjectiveGrading (t := t) emptyAlternatingTuple)
        (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
        (chartHomogeneousClass emptyAlternatingTuple a ha)) =
      HomogeneousChartDehomogenization.fraction (isotropicProjectiveGrading (t := t) forms)
        (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
        (chartHomogeneousClass forms a ha) := by
  simp only [HomogeneousChartDehomogenization.fraction, Away.map_mk]
  rfl

/-- Exact covariance of the normalized affine chart rings under the ambient quotient. -/
theorem ambientChartRing_commutes (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    (isotropicProjChartRingEquiv_arbitraryChar p forms).toRingHom.comp
        (Away.map (ambientGradedQuotient forms) (Ideal.Quotient.mk _ (X p))) =
      (Ideal.Quotient.mk (isotropicChartIdeal p forms)).comp
        (ambientChartRingEquiv p).toRingHom := by
  ext z
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective
    (isotropicProjectiveGrading (t := t) (emptyAlternatingTuple (K := K) (n := n)))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) z
  change a ∈ HomogeneousQuotientProjective.grading _ _ (d • 1) at ha
  rw [HomogeneousQuotientProjective.grading_eq_piece] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hbd : b.IsHomogeneous d := by simpa using hb
  change isotropicProjChartRingEquiv_arbitraryChar p forms
      (Away.map (ambientGradedQuotient forms) (Ideal.Quotient.mk _ (X p))
        (HomogeneousChartDehomogenization.fraction _
          (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
          (chartHomogeneousClass emptyAlternatingTuple b hbd))) = _
  erw [ambientAwayMap_fraction, isotropicChartRingEquiv_fraction]
  change isotropicChartEvaluation p forms b =
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

/-- The original row-isotropy chart as an actual open immersion into X. -/
def isotropicAffineChartι (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    Spec (CommRingCat.of (IsotropicChartRing p forms)) ⟶
      Proj (isotropicProjectiveGrading (t := t) forms) :=
  Spec.map (CommRingCat.ofHom (isotropicProjChartRingEquiv_arbitraryChar p forms).toRingHom) ≫
    Proj.awayι (isotropicProjectiveGrading (t := t) forms) (Ideal.Quotient.mk _ (X p))
      (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) one_pos

instance isotropicAffineChartι_isOpenImmersion (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) : IsOpenImmersion (isotropicAffineChartι p forms) := by
  letI : IsIso (CommRingCat.ofHom (isotropicProjChartRingEquiv_arbitraryChar p forms).toRingHom) :=
    (isotropicProjChartRingEquiv_arbitraryChar p forms).toCommRingCatIso.isIso_hom
  unfold isotropicAffineChartι
  infer_instance

theorem isotropicAffineChartι_opensRange (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    (isotropicAffineChartι p forms).opensRange =
      Proj.basicOpen (isotropicProjectiveGrading (t := t) forms) (Ideal.Quotient.mk _ (X p)) := by
  letI : IsIso (CommRingCat.ofHom (isotropicProjChartRingEquiv_arbitraryChar p forms).toRingHom) :=
    (isotropicProjChartRingEquiv_arbitraryChar p forms).toCommRingCatIso.isIso_hom
  unfold isotropicAffineChartι
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

/-- The ambient polynomial Grassmannian chart, prior to imposing any form. -/
def ambientAffineChartι (p : PluckerIndex (t + 2) n) :
    Spec (CommRingCat.of (MvPolynomial (PluckerChartVariable p) K)) ⟶
      ambientGrassmannian (K := K) t n :=
  Spec.map (CommRingCat.ofHom (ambientChartRingEquiv p).toRingHom) ≫
    Proj.awayι (isotropicProjectiveGrading (t := t) emptyAlternatingTuple)
      (Ideal.Quotient.mk _ (X p))
      (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) one_pos

instance ambientAffineChartι_isOpenImmersion (p : PluckerIndex (t + 2) n) :
    IsOpenImmersion (ambientAffineChartι (K := K) p) := by
  letI : IsIso (CommRingCat.ofHom (ambientChartRingEquiv (K := K) p).toRingHom) :=
    (ambientChartRingEquiv p).toCommRingCatIso.isIso_hom
  unfold ambientAffineChartι
  infer_instance

theorem ambientAffineChartι_opensRange (p : PluckerIndex (t + 2) n) :
    (ambientAffineChartι (K := K) p).opensRange =
      Proj.basicOpen (isotropicProjectiveGrading (t := t)
        (emptyAlternatingTuple (K := K) (n := n))) (Ideal.Quotient.mk _ (X p)) := by
  letI : IsIso (CommRingCat.ofHom (ambientChartRingEquiv (K := K) p).toRingHom) :=
    (ambientChartRingEquiv p).toCommRingCatIso.isIso_hom
  unfold ambientAffineChartι
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

theorem isotropicAffineChart_ambient_commutes (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    isotropicAffineChartι p forms ≫ isotropicAmbientImmersion forms =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (isotropicChartIdeal p forms))) ≫
        ambientAffineChartι p := by
  have hcomp :
      Proj.awayι (isotropicProjectiveGrading (t := t) forms)
          (Ideal.Quotient.mk _ (X p))
          (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) one_pos ≫
        isotropicAmbientImmersion forms =
      Spec.map (CommRingCat.ofHom
          (Away.map (ambientGradedQuotient forms) (Ideal.Quotient.mk _ (X p)))) ≫
        Proj.awayι (isotropicProjectiveGrading (t := t) emptyAlternatingTuple)
          (Ideal.Quotient.mk _ (X p))
          (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) one_pos := by
    exact Proj.awayι_comp_map (ambientGradedQuotient forms)
      (irrelevant_le_map_of_gradedSurjective _
        (HomogeneousQuotientProjective.quotientGradedHom_surjective _ _ _ _ _))
      one_pos (Ideal.Quotient.mk _ (X p))
      (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p)
  have hring :
      CommRingCat.ofHom
          (Away.map (ambientGradedQuotient forms) (Ideal.Quotient.mk _ (X p))) ≫
        CommRingCat.ofHom (isotropicProjChartRingEquiv_arbitraryChar p forms).toRingHom =
      CommRingCat.ofHom (ambientChartRingEquiv (K := K) p).toRingHom ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (isotropicChartIdeal p forms)) := by
    apply CommRingCat.hom_ext
    exact ambientChartRing_commutes p forms
  unfold isotropicAffineChartι ambientAffineChartι
  rw [Category.assoc, hcomp, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp_assoc,
    hring]

/-- The literal row-quotient square is the restriction of the global
closed immersion to the corresponding ambient affine chart. -/
theorem isotropicAffineChart_ambient_isPullback (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (isotropicChartIdeal p forms))))
      (isotropicAffineChartι p forms) (ambientAffineChartι p)
      (isotropicAmbientImmersion forms) := by
  apply IsOpenImmersion.isPullback
  · exact isotropicAffineChart_ambient_commutes p forms
  · rw [ambientAffineChartι_opensRange, isotropicAffineChartι_opensRange,
      isotropicAmbientImmersion_preimage_chart]

/-- The row-isotropy affine schemes cover the original projective scheme. -/
def isotropicAffineChartCover (forms : Fin m → StrictPairs n → K) :
    (Proj (isotropicProjectiveGrading (t := t) forms)).AffineOpenCover where
  I₀ := PluckerIndex (t + 2) n
  X p := CommRingCat.of (IsotropicChartRing p forms)
  f p := isotropicAffineChartι p forms
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((isotropicProjBasicOpen_cover_arbitraryChar forms).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (isotropicAffineChartι _ forms).opensRange
    rw [isotropicAffineChartι_opensRange]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((isotropicProjBasicOpen_cover_arbitraryChar forms).ge (Set.mem_univ x))).choose_spec

end PaperVerification.AlternatingForms
