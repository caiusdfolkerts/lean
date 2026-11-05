module

public import paper_verification.ambient_base2
import all paper_verification.ambient_base2
public import paper_verification.literal005
import all paper_verification.literal005
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import paper_verification.literal001
import all paper_verification.literal001
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let opts ← getOptions
  if env.header.trustLevel != 0 then
    throwError "Header-cache environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "Header-cache environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "Header-cache environment unexpectedly uses server mode"
  logInfo "HEADER_CACHE_CHECKING_OPTIONS_VERIFIED"

section ComponentSource_0
/- Original module: PaperVerification.AlternatingFormsUniversalCharts -/


/-!
# Characteristic-free common-isotropic chart comparisons

The normalized determinant and row-isotropy identities are integral.  The
older chart wrappers unnecessarily requested `CharZero`.  Here those proofs
are replayed with only a coefficient field, without modifying the accepted
core.  Every quotient retains its original ideal and complete scheme structure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial Matrix AlgebraicGeometry CategoryTheory

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {t n m : ℕ}

theorem isotropicPluckerIdeal_map_chart_eq_arbitraryChar
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (isotropicPluckerIdeal forms).map
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
        isotropicChartIdeal p forms := by
  classical
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro q hq
    have h := isotropicPluckerIdeal_le_chartKernel p forms hq
    change (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms))
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q)=0 at h
    change matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q ∈ isotropicChartIdeal p forms
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l,ij⟩,rfl⟩
    obtain ⟨σ,hσ0,hσ1⟩ := exists_chart_row_permutation ij.val.1 ij.val.2
      (ne_of_lt ij.property)
    let J : Fin t → Fin n := fun z ↦ p.val (σ z.succ.succ)
    have hmem :
        matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)
          (pluckerIsotropyEquation (forms l) J) ∈
          (isotropicPluckerIdeal forms).map
            (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom :=
      Ideal.mem_map_of_mem _
        (Ideal.mem_sup_right (Ideal.subset_span ⟨(l,J),rfl⟩))
    have he := matrixMinorEvaluation_complementary_isotropy (forms l)
      (pluckerChartMatrix (K := K) p) p.val (pluckerChartMatrix_pivot p) σ
    rw [hσ0,hσ1] at he
    change alternatingRowPair (forms l) (pluckerChartMatrix p) ij.val.1 ij.val.2 ∈ _
    rw [←he]
    exact Ideal.mul_mem_left _ _ hmem


theorem isotropicChartEvaluation_kernel_arbitraryChar
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    RingHom.ker (isotropicChartEvaluation p forms).toRingHom =
      isotropicPluckerIdeal forms ⊔ Ideal.span {X p-1} := by
  have h := Ideal.comap_map_of_surjective
    (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom
    (matrixMinorEvaluation_chart_surjective p) (isotropicPluckerIdeal forms)
  rw [isotropicPluckerIdeal_map_chart_eq_arbitraryChar p forms,
    ←RingHom.ker_eq_comap_bot,matrixMinorEvaluation_chart_kernel] at h
  have hk : RingHom.ker (isotropicChartEvaluation p forms).toRingHom =
      (isotropicChartIdeal p forms).comap
        (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom := by
    ext q
    change (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms))
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q)=0 ↔ _
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hk,h,pluckerBigCellIdeal]
  have hle : matrixPluckerIdeal (K := K) (s := t+2) (n := n) ≤
      isotropicPluckerIdeal (t := t) forms := le_sup_left
  rw [←sup_assoc,sup_of_le_left hle]

/-- The actual normalized Plücker quotient is the affine scheme chart cut out
by the pairwise row restrictions. Both quotient ideals are stated literally. -/
def isotropicPluckerBigCellEquiv_arbitraryChar
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (MvPolynomial (PluckerIndex (t+2) n) K ⧸
      (isotropicPluckerIdeal forms ⊔ Ideal.span {X p-1})) ≃ₐ[K]
      (MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdeal p forms) :=
  (Ideal.quotientEquivAlgOfEq K (isotropicChartEvaluation_kernel_arbitraryChar p forms).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (isotropicChartEvaluation_surjective p forms))


def isotropicProjChartRingEquiv_arbitraryChar (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    HomogeneousLocalization.Away (isotropicProjectiveGrading (t := t) forms)
      (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p)) ≃+*
      IsotropicChartRing p forms :=
  (HomogeneousQuotientCharts.awayQuotientChartEquiv
    (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p).trans
    (isotropicPluckerBigCellEquiv_arbitraryChar p forms).toRingEquiv

/-- The literal open subscheme of the actual homogeneous quotient's
Proj is the spectrum of the original affine row-restriction equations. -/
def isotropicProjBasicOpenIso_arbitraryChar (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    (Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
      (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))).toScheme ≅
      Spec (CommRingCat.of (IsotropicChartRing p forms)) :=
  HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
      (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p ≪≫
    Scheme.Spec.mapIso (isotropicPluckerBigCellEquiv_arbitraryChar p forms).symm.toRingEquiv.toCommRingCatIso.op

/-- The original Plücker charts cover in every characteristic. -/
theorem isotropicProjBasicOpen_cover_arbitraryChar
    (forms : Fin m → StrictPairs n → K) :
    (⨆ p : PluckerIndex (t+2) n,
      Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
        (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))) = ⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover
    (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms)
    (Ideal.Quotient.mkₐ K (isotropicPluckerIdeal forms))
    Ideal.Quotient.mk_surjective
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)


end PaperVerification.AlternatingForms
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsUniversalCharts"

section ComponentSource_1
/- Original module: PaperVerification.AlternatingFormsAmbientImmersion -/


/-!
# The original common-isotropic scheme in the ambient Grassmannian

The ambient Grassmannian is the projective scheme of the original Plücker
ideal, expressed as the empty tuple of isotropy conditions.  Adding the
given alternating forms induces an actual closed immersion of schemes.
This file constructs that morphism independently of the later comparison
with the zero scheme of the tautological alternating section.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

/-- No equations beyond the original Grassmannian Plücker relations. -/
def emptyAlternatingTuple : Fin 0 → StrictPairs n → K := Fin.elim0

@[simp]
theorem isotropicPluckerIdeal_empty :
    isotropicPluckerIdeal (t := t) (emptyAlternatingTuple (K := K) (n := n)) =
      matrixPluckerIdeal := by
  simp [isotropicPluckerIdeal, emptyAlternatingTuple, Set.range_eq_empty]

@[simp]
theorem isotropicChartIdeal_empty (p : PluckerIndex (t + 2) n) :
    isotropicChartIdeal p (emptyAlternatingTuple (K := K) (n := n)) = ⊥ := by
  simp [isotropicChartIdeal, emptyAlternatingTuple, Set.range_eq_empty]

/-- The independently specified ambient Grassmannian scheme. -/
def ambientGrassmannian (t n : ℕ) : Scheme :=
  Proj (isotropicProjectiveGrading (t := t)
    (emptyAlternatingTuple (K := K) (n := n)))

theorem ambientPluckerIdeal_le (forms : Fin m → StrictPairs n → K) :
    isotropicPluckerIdeal (t := t) (emptyAlternatingTuple (K := K) (n := n)) ≤
      isotropicPluckerIdeal (t := t) forms := by
  rw [isotropicPluckerIdeal_empty]
  exact le_sup_left

/-- The canonical closed immersion into the ambient Grassmannian. -/
def isotropicAmbientImmersion (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ⟶ ambientGrassmannian (K := K) t n :=
  HomogeneousQuotientProjective.quotientProjMap _ _
    (isotropicPluckerIdeal_isHomogeneous (emptyAlternatingTuple (K := K) (n := n)))
    (isotropicPluckerIdeal_isHomogeneous forms) (ambientPluckerIdeal_le forms)

instance isotropicAmbientImmersion_isClosedImmersion
    (forms : Fin m → StrictPairs n → K) :
    IsClosedImmersion (isotropicAmbientImmersion (t := t) forms) :=
  HomogeneousQuotientProjective.quotientProjMap_isClosedImmersion _ _ _ _ _

@[simp]
theorem isotropicAmbientImmersion_preimage_chart
    (forms : Fin m → StrictPairs n → K) (p : PluckerIndex (t + 2) n) :
    isotropicAmbientImmersion forms ⁻¹ᵁ
      Proj.basicOpen
        (isotropicProjectiveGrading (t := t) (emptyAlternatingTuple (K := K) (n := n)))
        (Ideal.Quotient.mk _ (X p)) =
      Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
        (Ideal.Quotient.mk _ (X p)) := rfl

end PaperVerification.AlternatingForms
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsAmbientImmersion"

section ComponentSource_2
/- Original module: PaperVerification.AlternatingFormsAmbientCharts -/


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
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsAmbientCharts"

section ComponentSource_3
/- Original module: PaperVerification.AlternatingSectionAlgebra -/


/-!
# Restriction of an alternating form to local frame vectors

This construction retains the original coefficient formula.  It works over
any commutative ring and commutes with every coefficient-ring homomorphism.
The induced functional is on Mathlib's actual second exterior power.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingSectionAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]
variable {P N : Type*} [Fintype P]

/-- The two selected coordinate functionals, as a linear map. -/
def pairProjection (a b : N) : (N → R) →ₗ[R] (Fin 2 → R) where
  toFun v := ![v a, v b]
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' r v := by ext i; fin_cases i <;> rfl

/-- One coordinate two-form, with the conventional order of its two indices. -/
def pairForm (a b : N) : AlternatingMap R (N → R) R (Fin 2) :=
  Matrix.detRowAlternating.compLinearMap (pairProjection a b)

@[simp] theorem pairForm_apply (a b : N) (v : Fin 2 → N → R) :
    pairForm a b v = v 0 a * v 1 b - v 0 b * v 1 a := by
  change Matrix.det (fun i => ![v i a, v i b]) = _
  exact Matrix.det_fin_two _

/-- The alternating form determined by the displayed independent coefficients. -/
def coefficientForm (a b : P → N) (c : P → R) :
    AlternatingMap R (N → R) R (Fin 2) :=
  ∑ p, c p • pairForm (a p) (b p)

@[simp] theorem coefficientForm_apply (a b : P → N) (c : P → R)
    (v : Fin 2 → N → R) :
    coefficientForm a b c v =
      ∑ p, c p * (v 0 (a p) * v 1 (b p) - v 0 (b p) * v 1 (a p)) := by
  simp [coefficientForm, sum_apply, smul_eq_mul]

/-- Restriction of the coefficient form is functorial even when the ring changes. -/
theorem coefficientForm_map (φ : R →+* S) (a b : P → N) (c : P → R)
    (v : Fin 2 → N → R) :
    coefficientForm a b (fun p => φ (c p)) (fun i j => φ (v i j)) =
      φ (coefficientForm a b c v) := by
  simp only [coefficientForm_apply, map_sum, map_mul, map_sub]

/-- The universal-property map out of the actual second exterior power. -/
def exteriorFunctional (a b : P → N) (c : P → R) :
    ⋀[R]^2 (N → R) →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv (coefficientForm a b c)

@[simp] theorem exteriorFunctional_wedge (a b : P → N) (c : P → R)
    (v : Fin 2 → N → R) :
    exteriorFunctional a b c (exteriorPower.ιMulti R 2 v) =
      ∑ p, c p * (v 0 (a p) * v 1 (b p) - v 0 (b p) * v 1 (a p)) := by
  rw [exteriorFunctional, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    coefficientForm_apply]

end PaperVerification.AlternatingSectionAlgebra
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingSectionAlgebra"

section ComponentSource_4
/- Original module: PaperVerification.AlternatingSectionSpan -/


/-!
# Vanishing on a row span

An alternating form vanishes on the full module generated by a family
when it vanishes on every pair of generators.  The result holds over
arbitrary commutative rings, including nonreduced chart rings.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingSectionSpan

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype I]

/-- Bilinear isotropy is preserved under arbitrary linear combinations of
the given rows, without any field or independence hypothesis. -/
theorem alternatingForm_linear_combinations_zero
    (f : AlternatingMap R M R (Fin 2)) (A : I → M)
    (hA : ∀ i j, f ![A i, A j] = 0) (c : Fin 2 → I → R) :
    f (fun i ↦ ∑ j, c i j • A j) = 0 := by
  classical
  change f.toMultilinearMap (fun i ↦ ∑ j, c i j • A j) = 0
  rw [MultilinearMap.map_sum]
  apply Finset.sum_eq_zero
  intro e he
  rw [MultilinearMap.map_smul_univ]
  have hv : (fun i ↦ A (e i)) = ![A (e 0), A (e 1)] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  change _ • f ![A (e 0), A (e 1)] = 0
  rw [hA, smul_zero]

end PaperVerification.AlternatingSectionSpan
end
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingSectionSpan"

section ComponentSource_5
/- Original module: PaperVerification.AlternatingSectionImageIdeal -/


/-!
# The equation ideal of an alternating functional

For a finite free module, the image of the actual exterior-square functional
is the ideal generated by its values on pairs of basis vectors.  This is the
algebraic identification needed to compare the zero scheme of the section
with the paper's displayed row-pairing equations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace PaperVerification.AlternatingSectionImageIdeal

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The image of the universal exterior functional is generated by its
values on actual decomposable wedges. -/
theorem range_exteriorFunctional_eq_span_values
    (f : AlternatingMap R M R (Fin 2)) :
    LinearMap.range (exteriorPower.alternatingMapLinearEquiv f) =
      Submodule.span R (Set.range f) := by
  rw [LinearMap.range_eq_map, ← exteriorPower.ιMulti_span R 2 M,
    Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f v).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨exteriorPower.ιMulti R 2 v, ⟨v, rfl⟩,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f v⟩

/-- Membership in an equation ideal is preserved under arbitrary row
combinations, over any commutative coefficient ring. -/
theorem alternatingForm_linear_combinations_mem [Fintype I]
    (f : AlternatingMap R M R (Fin 2)) (A : I → M) (J : Submodule R R)
    (hA : ∀ i j, f ![A i, A j] ∈ J) (c : Fin 2 → I → R) :
    f (fun i ↦ ∑ j, c i j • A j) ∈ J := by
  classical
  change f.toMultilinearMap (fun i ↦ ∑ j, c i j • A j) ∈ J
  rw [MultilinearMap.map_sum]
  apply Submodule.sum_mem
  intro e he
  rw [MultilinearMap.map_smul_univ]
  have hv : (fun i ↦ A (e i)) = ![A (e 0), A (e 1)] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  exact J.smul_mem _ (hA (e 0) (e 1))

/-- The actual image ideal is generated by the displayed basis-row
pairings.  There is no radical, reduction, or field-valued-points passage. -/
theorem range_exteriorFunctional_eq_basis_ideal [Fintype I]
    (b : Module.Basis I R M) (f : AlternatingMap R M R (Fin 2)) :
    LinearMap.range (exteriorPower.alternatingMapLinearEquiv f) =
      Ideal.span (Set.range fun ij : I × I ↦ f ![b ij.1, b ij.2]) := by
  classical
  rw [range_exteriorFunctional_eq_span_values]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    have h := alternatingForm_linear_combinations_mem f b
      (Ideal.span (Set.range fun ij : I × I ↦ f ![b ij.1, b ij.2]))
      (fun i j ↦ Ideal.subset_span ⟨(i, j), rfl⟩)
      (fun i j ↦ b.repr (v i) j)
    change f v ∈ Ideal.span (Set.range fun ij : I × I ↦ f ![b ij.1, b ij.2])
    simpa only [b.sum_repr] using h
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact Submodule.subset_span ⟨![b i, b j], rfl⟩

end PaperVerification.AlternatingSectionImageIdeal
end
end
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingSectionImageIdeal"

section ComponentSource_6
/- Original module: PaperVerification.AlternatingSectionRowIdeal -/


/-!
# The genuine equation ideal in row coordinates

An alternating form restricted along a matrix of row vectors gives a
functional on the exterior square of the coefficient module.  Its image
ideal is exactly the ideal of all row-pairing equations, over any
commutative ring.  Independence of the rows is not required.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingSectionRowIdeal

variable {R I N : Type*} [CommRing R] [Fintype I]

/-- Restriction to the coefficient module of the prescribed row matrix. -/
def rowForm (f : AlternatingMap R (N → R) R (Fin 2)) (A : Matrix I N R) :
    AlternatingMap R (I → R) R (Fin 2) :=
  f.compLinearMap A.vecMulLinear

/-- A pair of coordinate basis vectors maps to exactly the selected rows. -/
theorem rowForm_basis_pair (f : AlternatingMap R (N → R) R (Fin 2))
    (A : Matrix I N R) (i j : I) :
    rowForm f A ![Pi.basisFun R I i, Pi.basisFun R I j] = f ![A i, A j] := by
  classical
  change f (fun k ↦ A.vecMulLinear (![Pi.basisFun R I i, Pi.basisFun R I j] k)) = _
  congr 1
  funext k
  fin_cases k
  · change Matrix.vecMul (Pi.basisFun R I i) A = A i
    simp only [Pi.basisFun_apply, Matrix.single_vecMul, one_smul]
    rfl
  · change Matrix.vecMul (Pi.basisFun R I j) A = A j
    simp only [Pi.basisFun_apply, Matrix.single_vecMul, one_smul]
    rfl

/-- The original row-pairing ideal is the image of the universal exterior
functional.  The equality is at the level of ideals, not only zero sets. -/
theorem range_rowExteriorFunctional_eq_ideal
    (f : AlternatingMap R (N → R) R (Fin 2)) (A : Matrix I N R) :
    LinearMap.range (exteriorPower.alternatingMapLinearEquiv (rowForm f A)) =
      Ideal.span (Set.range fun ij : I × I ↦ f ![A ij.1, A ij.2]) := by
  simpa only [rowForm_basis_pair] using
    AlternatingSectionImageIdeal.range_exteriorFunctional_eq_basis_ideal
      (Pi.basisFun R I) (rowForm f A)

end PaperVerification.AlternatingSectionRowIdeal
end
end
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingSectionRowIdeal"

section ComponentSource_7
/- Original module: PaperVerification.AlternatingSectionFamilyIdeal -/


/-!
# The equation ideal for a finite family of alternating forms

The source is the finite direct sum of genuine exterior squares, expressed
as a finite product.  Its functional is the sum of the individual original
forms.  The image ideal is exactly the ideal generated by all their row
pairings, without any independence or reducedness assumption.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace PaperVerification.AlternatingSectionFamilyIdeal

open AlternatingSectionRowIdeal

variable {R I N L : Type*} [CommRing R] [Fintype I] [Fintype L]

/-- The actual dual-section functional for the finite family. -/
def familyFunctional (f : L → AlternatingMap R (N → R) R (Fin 2))
    (A : Matrix I N R) : (L → ⋀[R]^2 (I → R)) →ₗ[R] R := by
  classical
  exact ∑ l : L,
    (exteriorPower.alternatingMapLinearEquiv (rowForm (f l) A)).comp (LinearMap.proj l)

/-- On one summand, the combined functional is the prescribed original form. -/
theorem familyFunctional_single [DecidableEq L]
    (f : L → AlternatingMap R (N → R) R (Fin 2)) (A : Matrix I N R)
    (l : L) (v : Fin 2 → I → R) :
    familyFunctional f A (Pi.single l (exteriorPower.ιMulti R 2 v)) =
      rowForm (f l) A v := by
  classical
  simp [familyFunctional, Pi.single_apply, apply_ite]

/-- Equality of the full defining ideal with the genuine functional image. -/
theorem range_familyFunctional_eq_ideal
    (f : L → AlternatingMap R (N → R) R (Fin 2)) (A : Matrix I N R) :
    LinearMap.range (familyFunctional f A) =
      Ideal.span (Set.range fun a : L × I × I ↦ f a.1 ![A a.2.1, A a.2.2]) := by
  classical
  let J := Ideal.span (Set.range fun a : L × I × I ↦ f a.1 ![A a.2.1, A a.2.2])
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change (familyFunctional f A) v ∈ J
    simp only [familyFunctional, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    apply Submodule.sum_mem
    intro l hl
    have hle : LinearMap.range
        (exteriorPower.alternatingMapLinearEquiv (rowForm (f l) A)) ≤ J := by
      rw [range_rowExteriorFunctional_eq_ideal]
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact Ideal.subset_span ⟨(l, i, j), rfl⟩
    exact hle ⟨v l, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l, i, j⟩, rfl⟩
    refine ⟨Pi.single l (exteriorPower.ιMulti R 2
      ![Pi.basisFun R I i, Pi.basisFun R I j]), ?_⟩
    rw [familyFunctional_single, rowForm_basis_pair]

end PaperVerification.AlternatingSectionFamilyIdeal
end
end
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingSectionFamilyIdeal"

section ComponentSource_8
/- Original module: PaperVerification.AlternatingFormsSectionEquationIdeal -/


/-!
# The original chart ideal is the image of the section functional

This comparison uses the normalized row matrix before imposing any
isotropy equations.  The finite family of original two-forms induces a
map from the direct sum of actual exterior squares to the polynomial
chart ring.  Its image is exactly the original `isotropicChartIdeal`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {t n m : ℕ}

/-- The original form with its coefficients in the polynomial chart ring. -/
def chartCoefficientForm (p : PluckerIndex (t + 2) n) (f : StrictPairs n → K) :
    AlternatingMap (MvPolynomial (PluckerChartVariable p) K)
      (Fin n → MvPolynomial (PluckerChartVariable p) K)
      (MvPolynomial (PluckerChartVariable p) K) (Fin 2) :=
  AlternatingSectionAlgebra.coefficientForm
    (fun a : StrictPairs n ↦ a.val.1) (fun a : StrictPairs n ↦ a.val.2)
    (fun a ↦ MvPolynomial.C (f a))

/-- The coefficient formula is the exact original alternating row pairing. -/
theorem chartCoefficientForm_rows (p : PluckerIndex (t + 2) n)
    (f : StrictPairs n → K) (i j : Fin (t + 2)) :
    chartCoefficientForm p f ![pluckerChartMatrix p i, pluckerChartMatrix p j] =
      alternatingRowPair f (pluckerChartMatrix p) i j := by
  simp only [chartCoefficientForm, AlternatingSectionAlgebra.coefficientForm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, alternatingRowPair,
    Algebra.smul_def, MvPolynomial.algebraMap_eq]

/-- The genuine finite-family functional in the original normalized chart. -/
def isotropicChartSectionFunctional (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    (Fin m → ⋀[MvPolynomial (PluckerChartVariable p) K]^2
      (Fin (t + 2) → MvPolynomial (PluckerChartVariable p) K)) →ₗ[
        MvPolynomial (PluckerChartVariable p) K] MvPolynomial (PluckerChartVariable p) K :=
  AlternatingSectionFamilyIdeal.familyFunctional
    (fun l ↦ chartCoefficientForm p (forms l)) (pluckerChartMatrix p)

/-- Equality of ideals identifies the section's zero equations with the
paper's original scheme equations, including all scheme structure. -/
theorem isotropicChartSectionFunctional_range
    (p : PluckerIndex (t + 2) n) (forms : Fin m → StrictPairs n → K) :
    LinearMap.range (isotropicChartSectionFunctional p forms) =
      isotropicChartIdeal p forms := by
  rw [isotropicChartSectionFunctional,
    AlternatingSectionFamilyIdeal.range_familyFunctional_eq_ideal]
  simp only [chartCoefficientForm_rows]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l, i, j⟩, rfl⟩
    exact alternatingRowPair_mem_chartIdeal p forms l i j
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l, ij⟩, rfl⟩
    exact Ideal.subset_span ⟨(l, ij.val.1, ij.val.2), rfl⟩

end PaperVerification.AlternatingForms
end
end
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsSectionEquationIdeal"

section ComponentSource_9
/- Original module: PaperVerification.AlternatingFormsSectionZeroScheme -/


/-!
# The independent zero scheme of the alternating section

On each polynomial Grassmannian chart, take the genuine image ideal of the
finite family of alternating functionals on the normalized tautological
frame.  Map its affine zero scheme into the ambient Grassmannian and glue
its ideal sheaves by their intersection.  This definition involves only
the ambient Grassmannian and the given forms; it does not refer to the
common-isotropic projective scheme or its defining homogeneous ideal.

The exact commuting chart maps prove that this ideal sheaf equals the
closed-image ideal of the original projective scheme.  Consequently the
comparison is an isomorphism over the ambient Grassmannian, retaining the
entire scheme structure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

/-- The zero ideal of the actual alternating functional on a polynomial
Grassmannian chart, before any isotropy equations have been imposed. -/
def ambientSectionChartIdeal (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  LinearMap.range (isotropicChartSectionFunctional p forms)

/-- The independently defined local zero scheme in the ambient Grassmannian. -/
def ambientSectionChartZeroMap (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    Spec (CommRingCat.of
      (MvPolynomial (PluckerChartVariable p) K ⧸ ambientSectionChartIdeal p forms)) ⟶
      ambientGrassmannian (K := K) t n :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ambientSectionChartIdeal p forms))) ≫
    ambientAffineChartι p

/-- The ideal sheaf obtained from the actual local section zero schemes. -/
def ambientSectionZeroIdeal (forms : Fin m → StrictPairs n → K) :
    (ambientGrassmannian (K := K) t n).IdealSheafData :=
  ⨅ p : PluckerIndex (t + 2) n, (ambientSectionChartZeroMap p forms).ker

/-- The actual closed subscheme determined by the section's local zero ideals. -/
def ambientSectionZeroScheme (forms : Fin m → StrictPairs n → K) : Scheme :=
  (ambientSectionZeroIdeal (t := t) forms).subscheme

/-- The image ideal of an arbitrary affine-chart quotient.  Keeping the ideal
as an explicit argument makes equality transport independent of the quotient
ring's inferred two-sidedness witness. -/
private def chartQuotientImageIdeal (p : PluckerIndex (t + 2) n)
    (I : Ideal (MvPolynomial (PluckerChartVariable p) K)) :
    (ambientGrassmannian (K := K) t n).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ ambientAffineChartι p).ker

private def affineQuotientImageIdeal (p : PluckerIndex (t + 2) n)
    (I : Ideal (MvPolynomial (PluckerChartVariable p) K)) :
    (Spec (CommRingCat.of (MvPolynomial (PluckerChartVariable p) K))).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker

/-- The independent section zero ideal agrees with the closed-image ideal
of the paper's original homogeneous quotient. -/
theorem ambientSectionZeroIdeal_eq_kernel (forms : Fin m → StrictPairs n → K) :
    ambientSectionZeroIdeal (t := t) forms = (isotropicAmbientImmersion forms).ker := by
  calc
    ambientSectionZeroIdeal forms =
        ⨅ p : PluckerIndex (t + 2) n,
          (isotropicAffineChartι p forms ≫ isotropicAmbientImmersion forms).ker := by
      apply iInf_congr
      intro p
      change chartQuotientImageIdeal p (isotropicChartSectionFunctional p forms).range = _
      rw [isotropicChartSectionFunctional_range]
      exact congrArg Scheme.Hom.ker (isotropicAffineChart_ambient_commutes p forms).symm
    _ = (isotropicAmbientImmersion forms).ker :=
      (isotropicAmbientImmersion forms).iInf_ker_openCover_map_comp
        (isotropicAffineChartCover forms).openCover

/-- The globally constructed ideal restricts to exactly the functional's
local zero ideal on every ambient chart.  Thus the intersection definition
introduces neither extra equations nor extra points on chart overlaps. -/
theorem ambientSectionZeroIdeal_chart (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    (ambientSectionZeroIdeal forms).comap (ambientAffineChartι p) =
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (ambientSectionChartIdeal p forms)))).ker := by
  rw [ambientSectionZeroIdeal_eq_kernel]
  change (isotropicAmbientImmersion forms).ker.comap (ambientAffineChartι p) =
    affineQuotientImageIdeal p (isotropicChartSectionFunctional p forms).range
  rw [isotropicChartSectionFunctional_range]
  ext1
  funext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (isotropicAmbientImmersion forms)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (isotropicChartIdeal p forms))))
    (isotropicAffineChartι p forms) (ambientAffineChartι p)
    (isotropicAffineChart_ambient_isPullback p forms) W).symm

/-- The canonical morphism from the original X to the independently
constructed section zero scheme. -/
def isotropicToSectionZero (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ⟶
      ambientSectionZeroScheme (t := t) forms :=
  IsClosedImmersion.lift (ambientSectionZeroIdeal forms).subschemeι
    (isotropicAmbientImmersion forms) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, ambientSectionZeroIdeal_eq_kernel])

instance isotropicToSectionZero_isIso (forms : Fin m → StrictPairs n → K) :
    IsIso (isotropicToSectionZero (t := t) forms) :=
  IsClosedImmersion.isIso_lift (ambientSectionZeroIdeal forms).subschemeι
    (isotropicAmbientImmersion forms) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, ambientSectionZeroIdeal_eq_kernel])

/-- A genuine scheme isomorphism from the original homogeneous quotient
to the zero scheme of the independently defined local section functionals. -/
def isotropicSectionZeroIso (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ≅ ambientSectionZeroScheme (t := t) forms :=
  asIso (isotropicToSectionZero forms)

/-- The scheme comparison preserves the actual embedding into the Grassmannian. -/
theorem isotropicSectionZeroIso_over_ambient (forms : Fin m → StrictPairs n → K) :
    (isotropicSectionZeroIso (t := t) forms).hom ≫
        (ambientSectionZeroIdeal forms).subschemeι =
      isotropicAmbientImmersion forms :=
  IsClosedImmersion.lift_fac _ _ _

end PaperVerification.AlternatingForms
end
end
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsSectionZeroScheme"


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
    (`PaperVerification.GradedSurjective, "definition"),
    (`PaperVerification.irrelevant_le_map_of_gradedSurjective, "theorem"),
    (`PaperVerification.gradedAwayMap_surjective, "theorem"),
    (`PaperVerification.gradedProjMap_chart_isPullback, "theorem"),
    (`PaperVerification.isClosedImmersion_projMap_of_gradedSurjective, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientGradedHom, "definition"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientGradedHom_surjective, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientProjMap, "definition"),
    (`PaperVerification.AlternatingForms.emptyAlternatingTuple, "definition"),
    (`PaperVerification.AlternatingForms.isotropicPluckerIdeal_empty, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicChartIdeal_empty, "theorem"),
    (`PaperVerification.AlternatingForms.ambientGrassmannian, "definition"),
    (`PaperVerification.AlternatingForms.isotropicAmbientImmersion, "definition"),
    (`PaperVerification.AlternatingForms.isotropicAmbientImmersion_preimage_chart, "theorem"),
    (`PaperVerification.AlternatingForms.ambientChartRingEquiv, "definition"),
    (`PaperVerification.AlternatingForms.ambientChartRing_commutes, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicAffineChart_ambient_commutes, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicAffineChart_ambient_isPullback, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicAffineChartCover, "definition"),
    (`PaperVerification.AlternatingForms.isotropicChartSectionFunctional, "definition"),
    (`PaperVerification.AlternatingForms.isotropicChartSectionFunctional_range, "theorem"),
    (`PaperVerification.AlternatingForms.ambientSectionChartIdeal, "definition"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroIdeal, "definition"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroScheme, "definition"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroIdeal_eq_kernel, "theorem"),
    (`PaperVerification.AlternatingForms.ambientSectionZeroIdeal_chart, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicSectionZeroIso, "definition"),
    (`PaperVerification.AlternatingForms.isotropicSectionZeroIso_over_ambient, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicPluckerIdeal_map_chart_eq_arbitraryChar, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicChartEvaluation_kernel_arbitraryChar, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicPluckerBigCellEquiv_arbitraryChar, "definition"),
    (`PaperVerification.AlternatingForms.isotropicProjChartRingEquiv_arbitraryChar, "definition"),
    (`PaperVerification.AlternatingForms.isotropicProjBasicOpenIso_arbitraryChar, "definition")
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
    ("nonce", toJson "5ac357a18a744428e05e5eaee4dcdc4a"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:5ac357a18a744428e05e5eaee4dcdc4a"
