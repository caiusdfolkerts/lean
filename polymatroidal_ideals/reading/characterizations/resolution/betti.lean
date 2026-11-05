import Characterizations.Resolution.KoszulStaircase
import Characterizations.Resolution.Degree
import Characterizations.Strands.DeletedBetti
import CommAlg.KoszulComplex.BettiNumbers

/-! # An actual linear free resolution forces genuine graded Tor concentration -/
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace Characterizations
open Classical Resolution MvPolynomial CommAlg.Polymatroid CommAlg.Koszul
open CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

namespace Resolution
lemma homogeneousPiece_coeff_homogeneous (B : Family V) (a : Exponent V) (i e : ℕ)
    (hdegree : a.degree = e+i) {z : KoszulRows (V := V) (monomialIdeal k B) i}
    (hz : z ∈ homogeneousPiece (k := k) B a i) :
    ∀ s, (z s).val.IsHomogeneous e := by
  change z ∈ Submodule.span k (monomialCoefficientBasis (k := k) B i ''
    {t | monomialDegree t = a}) at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨s, b⟩, hb, rfl⟩ := hx
    have hbd : b.val.degree = e := by
      have hd := congrArg Finsupp.degree hb
      change (b.val + faceExponent s.val).degree = a.degree at hd
      rw [map_add, Strands.degree_faceExponent, s.property, hdegree] at hd
      omega
    intro q
    rw [monomialCoefficientBasis_apply]
    by_cases hqs : s = q
    · subst q
      simp only [Finsupp.single_eq_same, monomialBasis_val]
      exact isHomogeneous_monomial (1 : k) hbd
    · simp only [Finsupp.single_eq_of_ne (Ne.symm hqs), ZeroMemClass.coe_zero]
      exact (homogeneousSubmodule V k e).zero_mem
  | zero => intro s; exact (homogeneousSubmodule V k e).zero_mem
  | add x y hx hy ihx ihy => intro s; exact (ihx s).add (ihy s)
  | smul c x hx ih => intro s; exact (homogeneousSubmodule V k e).smul_mem c (ih s)
end Resolution

namespace LinearResolution

lemma homogeneous_exact_above (B : Family V) {d : ℕ}
    (P : LinearResolution (monomialIdeal k B) d) (a : Exponent V) (i t : ℕ)
    (ht : 0 < t) (hdegree : a.degree = d+t+i) :
    (homogeneousComplex (k := k) B a).ExactAt i := by
  have hfill (z : homogeneousPiece (k := k) B a i)
      (hz : ∀ j (he : i = j+1), homogeneousDifferential (k := k) B a j (he ▸ z) = 0) :
      ∃ w : homogeneousPiece (k := k) B a (i+1), homogeneousDifferential B a i w = z := by
    have hh := Resolution.homogeneousPiece_coeff_homogeneous B a i (d+t) hdegree z.property
    have hcycle : ∀ j (he : i = j+1),
        rowDifferential (V := V) (k := k) (monomialIdeal k B) j (he ▸ z.val) = 0 := by
      intro j he
      subst i
      exact congrArg Subtype.val (hz j rfl)
    obtain ⟨w, hw⟩ := P.idealRows_boundary_above t ht i z.val hh hcycle
    refine ⟨⟨homogeneousProjection B a (i+1) w, homogeneousProjection_mem B a (i+1) w⟩, ?_⟩
    apply Subtype.ext
    change monomialDifferential (k := k) B i (homogeneousProjection B a (i+1) w) = z.val
    have hp := LinearMap.congr_fun (homogeneousProjection_differential B a i) w
    simp only [LinearMap.comp_apply] at hp
    rw [← hp]
    change homogeneousProjection B a i
      (rowDifferential (V := V) (k := k) (monomialIdeal k B) i w) = z.val
    rw [hw]
    exact CommAlg.Grading.projection_eq_self z.property
  cases i with
  | zero =>
    rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
    rw [homogeneousComplex_d, (homogeneousComplex (k := k) B a).shape 0 0 (by simp)]
    change ∀ z : homogeneousPiece (k := k) B a 0, (0 : homogeneousPiece (k := k) B a 0) = 0 →
      ∃ w : homogeneousPiece (k := k) B a 1, homogeneousDifferential B a 0 w = z
    intro z _
    exact hfill z (fun j he => by omega)
  | succ j =>
    rw [HomologicalComplex.exactAt_iff' _ (j+2) (j+1) j (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
    simp only [homogeneousComplex_d]
    change ∀ z : homogeneousPiece (k := k) B a (j+1), homogeneousDifferential B a j z = 0 →
      ∃ w : homogeneousPiece (k := k) B a (j+2), homogeneousDifferential B a (j+1) w = z
    intro z hz
    apply hfill z
    intro l he
    have heq : l = j := by omega
    subst l
    exact hz

lemma gradedBetti_degree (B : Family V) (hanti : Antichain B) {d : ℕ}
    (P : LinearResolution (monomialIdeal k B) d) (a : Exponent V) (i : ℕ)
    (h : GradedBettiNonzero (k := k) B a i) : a.degree = d+i := by
  have hdeg := LinearResolution.equigenerated_of_monomial B hanti P
  have hlow : d+i ≤ a.degree := by
    by_contra hlow
    have hn := (gradedBettiNonzero_iff_faces B a i).mp h
    apply ((CommAlg.Simplicial.nonzeroHomology_iff_not_exactIn _ _).mp hn)
    apply CommAlg.Simplicial.exactIn_of_no_face
    intro s hs hcard
    obtain ⟨b, hb, hba⟩ := hs.2
    have hd := Strands.degree_sub_faceExponent hs.1
    have hbd := degree_mono hba
    rw [hdeg b hb] at hbd
    omega
  by_contra heq
  let t := a.degree-(d+i)
  have ht : 0 < t := by dsimp [t]; omega
  have hsum : a.degree = d+t+i := by dsimp [t]; omega
  have hx := homogeneous_exact_above B P a i t ht hsum
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hx
  apply h
  exact (gradedTorIso (k := k) B a i).isZero_iff.mp hz

lemma bettiNumber_eq_zero_off_linear (B : Family V) (hanti : Antichain B) {d : ℕ}
    (P : LinearResolution (monomialIdeal k B) d) (a : Exponent V) (i : ℕ)
    (hoff : a.degree ≠ d+i) : bettiNumber (k := k) B a i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  exact hoff (gradedBetti_degree B hanti P a i ((bettiNumber_pos_iff B a i).mp hp))

end LinearResolution
end Characterizations
