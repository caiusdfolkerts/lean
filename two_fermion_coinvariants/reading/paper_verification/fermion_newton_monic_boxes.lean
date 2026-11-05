module

public import PaperVerification.FermionNewtonMonicComparison

/-!
# The complete rectangular basis for a general monic polynomial

The index inequalities are the actual signed heights. The basis vectors
are the original monomial classes in the original principal-colon quotient.
The generators are an actual regular sequence with nonzero highest forms
of exactly these degrees. No characteristic or dimension specialization is
used in this extension of the already verified homogeneous boxes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

 theorem homogeneous_contraction_span_ne_top
    (β : Fin n → F) (s : ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight (fun _ ↦ s) σ i) :
    Ideal.span (Set.range (columnContraction β (fun _ ↦ s) σ)) ≠ ⊤ := by
  have hker : Ideal.span (Set.range (columnContraction β (fun _ ↦ s) σ)) ≤
      RingHom.ker (constantCoeff : P (F := F) (n := n) →+* F) := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change constantCoeff (columnContraction β (fun _ ↦ s) σ i) = 0
    rw [MvPolynomial.constantCoeff_eq]
    have hh := constant_columnContraction_homogeneous β s σ (singleton_weight_ne_zero β hβ) i
    have hp := heightDegree_pos (fun _ ↦ s) σ hσ i (hheight i)
    exact hh.coeff_eq_zero (d := 0) (by simpa using hp.ne'.symm)
  intro htop
  have h : (1 : P (F := F) (n := n)) ∈
      RingHom.ker (constantCoeff : P (F := F) (n := n) →+* F) :=
    hker (by rw [htop]; trivial)
  exact one_ne_zero (by simpa only [RingHom.mem_ker, map_one] using h)

 theorem homogeneous_contractions_isRegular
    (β : Fin n → F) (s : ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight (fun _ ↦ s) σ i) :
    RingTheory.Sequence.IsRegular (P (F := F) (n := n))
      (List.ofFn (columnContraction β (fun _ ↦ s) σ)) := by
  refine ⟨columnContractions_isWeaklyRegular β (fun _ ↦ s) σ
    (compatible_constant s σ) hσ hβ hheight, ?_⟩
  rw [Filtered.ideal_ofList_ofFn, Ideal.smul_eq_mul, Ideal.mul_top]
  exact Ne.symm (homogeneous_contraction_span_ne_top β s σ hσ hβ hheight)

 theorem regular_sequence_entry_ne_zero
    (f : Fin n → P (F := F) (n := n))
    (hreg : RingTheory.Sequence.IsWeaklyRegular (P (F := F) (n := n)) (List.ofFn f))
    (hproper : Ideal.span (Set.range f) ≠ ⊤) (i : Fin n) : f i ≠ 0 := by
  intro hz
  have hr := hreg.regular_mod_prev i.val (by simpa only [List.length_ofFn] using i.isLt)
  rw [Ideal.smul_eq_mul, Ideal.mul_top, List.getElem_ofFn] at hr
  have hfi : f ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩ = 0 := hz
  rw [hfi] at hr
  have hone : (1 : P (F := F) (n := n)) ∈ Ideal.ofList ((List.ofFn f).take i.val) :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem _ (0 : P (F := F) (n := n))).mp hr 1
      (by simp only [zero_smul]; exact Ideal.zero_mem _)
  have hle : Ideal.ofList ((List.ofFn f).take i.val) ≤ Ideal.ofList (List.ofFn f) :=
    Ideal.span_mono (fun _ hp ↦ List.mem_of_mem_take hp)
  have hI := hle hone
  rw [Filtered.ideal_ofList_ofFn] at hI
  exact hproper (Ideal.eq_top_of_isUnit_mem _ hI isUnit_one)

 theorem polynomialContractions_isRegular
    (β : Fin n → F) (G : Polynomial F) (hG : G.Monic) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight (fun _ ↦ G.natDegree) σ i) :
    RingTheory.Sequence.IsRegular (P (F := F) (n := n))
      (List.ofFn (polynomialContraction β G σ)) := by
  exact Filtered.regular_of_regular_highest (fun _ ↦ 1)
    (polynomialContraction β G σ) (columnContraction β (fun _ ↦ G.natDegree) σ)
    (heightDegree (fun _ ↦ G.natDegree) σ)
    (fun i ↦ polynomialContraction_bound β G σ (singleton_weight_ne_zero β hβ) i)
    (fun i ↦ polynomialContraction_highest β G hG σ (singleton_weight_ne_zero β hβ) i
      (heightDegree_pos (fun _ ↦ G.natDegree) σ hσ i (hheight i)))
    (homogeneous_contractions_isRegular β G.natDegree σ hσ hβ hheight)

 def constantSpanRectangleBasis
    (β : Fin n → F) (s : ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight (fun _ ↦ s) σ i) :
    Module.Basis (RectangleIndex (heightDegree (fun _ ↦ s) σ)) F
      (P (F := F) (n := n) ⧸ Ideal.span (Set.range (columnContraction β (fun _ ↦ s) σ))) :=
  (contractionRectangleBasis β (fun _ ↦ s) σ (compatible_constant s σ) hσ hβ hheight).map
    (Ideal.quotientEquivAlgOfEq F
      (span_columnContractions_eq_contractionIdeal β (fun _ ↦ s) σ
        (compatible_constant s σ) hσ hβ).symm).toLinearEquiv

 @[simp] theorem constantSpanRectangleBasis_apply
    (β : Fin n → F) (s : ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight (fun _ ↦ s) σ i)
    (a : RectangleIndex (heightDegree (fun _ ↦ s) σ)) :
    constantSpanRectangleBasis β s σ hσ hβ hheight a =
      Ideal.Quotient.mk (Ideal.span (Set.range (columnContraction β (fun _ ↦ s) σ)))
        (monomial a.val 1) := by
  simp only [constantSpanRectangleBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    contractionRectangleBasis_apply, Ideal.quotientEquivAlgOfEq_mk]

 def monicSpanRectangleBasis
    (β : Fin n → F) (G : Polynomial F) (hG : G.Monic) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight (fun _ ↦ G.natDegree) σ i) :
    Module.Basis (RectangleIndex (heightDegree (fun _ ↦ G.natDegree) σ)) F
      (P (F := F) (n := n) ⧸ Ideal.span (Set.range (polynomialContraction β G σ))) :=
  Filtered.basisOfRegularHighestForms (fun _ ↦ 1)
    (polynomialContraction β G σ) (columnContraction β (fun _ ↦ G.natDegree) σ)
    (heightDegree (fun _ ↦ G.natDegree) σ)
    (fun i ↦ polynomialContraction_bound β G σ (singleton_weight_ne_zero β hβ) i)
    (fun i ↦ polynomialContraction_highest β G hG σ (singleton_weight_ne_zero β hβ) i
      (heightDegree_pos (fun _ ↦ G.natDegree) σ hσ i (hheight i)))
    (columnContractions_isWeaklyRegular β (fun _ ↦ G.natDegree) σ
      (compatible_constant G.natDegree σ) hσ hβ hheight)
    (fun a ↦ monomial a.val 1) (fun a ↦ Finsupp.weight (fun _ ↦ 1) a.val)
    (fun a ↦ isWeightedHomogeneous_monomial (fun _ ↦ 1) a.val 1 rfl)
    (constantSpanRectangleBasis β G.natDegree σ hσ hβ hheight)
    (constantSpanRectangleBasis_apply β G.natDegree σ hσ hβ hheight)

 @[simp] theorem monicSpanRectangleBasis_apply
    (β : Fin n → F) (G : Polynomial F) (hG : G.Monic) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight (fun _ ↦ G.natDegree) σ i)
    (a : RectangleIndex (heightDegree (fun _ ↦ G.natDegree) σ)) :
    monicSpanRectangleBasis β G hG σ hσ hβ hheight a =
      Ideal.Quotient.mk (Ideal.span (Set.range (polynomialContraction β G σ))) (monomial a.val 1) := by
  simp only [monicSpanRectangleBasis, Filtered.basisOfRegularHighestForms_apply]

 def monicRectangleBasis
    (β : Fin n → F) (G : Polynomial F) (hG : G.Monic) (hs : 0 < G.natDegree)
    (σ : Fin n → ℤ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight (fun _ ↦ G.natDegree) σ i) :
    Module.Basis (RectangleIndex (heightDegree (fun _ ↦ G.natDegree) σ)) F
      (P (F := F) (n := n) ⧸ principalColon (polynomialMomentIdeal β G) (differenceProduct σ)) :=
  (monicSpanRectangleBasis β G hG σ hσ hβ hheight).map
    (Ideal.quotientEquivAlgOfEq F
      (polynomial_principalColon_eq_span_contractions β G hG hs σ hσ hβ).symm).toLinearEquiv

 @[simp] theorem monicRectangleBasis_apply
    (β : Fin n → F) (G : Polynomial F) (hG : G.Monic) (hs : 0 < G.natDegree)
    (σ : Fin n → ℤ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight (fun _ ↦ G.natDegree) σ i)
    (a : RectangleIndex (heightDegree (fun _ ↦ G.natDegree) σ)) :
    monicRectangleBasis β G hG hs σ hσ hβ hheight a =
      Ideal.Quotient.mk (principalColon (polynomialMomentIdeal β G) (differenceProduct σ))
        (monomial a.val 1) := by
  simp only [monicRectangleBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    monicSpanRectangleBasis_apply, Ideal.quotientEquivAlgOfEq_mk]

/-- All of Proposition 2.1: the original rectangular monomials form a basis
of the original colon quotient, and its explicit generators are regular
with nonzero highest forms of the exact signed degrees. -/
theorem proposition_2_1
    (β : Fin n → F) (G : Polynomial F) (hG : G.Monic) (hs : 0 < G.natDegree)
    (σ : Fin n → ℤ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hheight : ∀ i, 0 < profileHeight (fun _ ↦ G.natDegree) σ i) :
    (∃ B : Module.Basis (RectangleIndex (heightDegree (fun _ ↦ G.natDegree) σ)) F
        (P (F := F) (n := n) ⧸ principalColon (polynomialMomentIdeal β G) (differenceProduct σ)),
      ∀ a, B a = Ideal.Quotient.mk (principalColon (polynomialMomentIdeal β G) (differenceProduct σ))
        (monomial a.val 1)) ∧
    RingTheory.Sequence.IsRegular (P (F := F) (n := n))
      (List.ofFn (polynomialContraction β G σ)) ∧
    Ideal.span (Set.range (polynomialContraction β G σ)) =
      principalColon (polynomialMomentIdeal β G) (differenceProduct σ) ∧
    ∀ i, (heightDegree (fun _ ↦ G.natDegree) σ i : ℤ) = profileHeight (fun _ ↦ G.natDegree) σ i ∧
      Filtered.Bound (fun _ ↦ 1) (heightDegree (fun _ ↦ G.natDegree) σ i) (polynomialContraction β G σ i) ∧
      weightedHomogeneousComponent (fun _ ↦ 1) (heightDegree (fun _ ↦ G.natDegree) σ i)
        (polynomialContraction β G σ i) ≠ 0 ∧
      (weightedHomogeneousComponent (fun _ ↦ 1) (heightDegree (fun _ ↦ G.natDegree) σ i)
        (polynomialContraction β G σ i)).totalDegree = heightDegree (fun _ ↦ G.natDegree) σ i := by
  refine ⟨⟨monicRectangleBasis β G hG hs σ hσ hβ hheight,
    monicRectangleBasis_apply β G hG hs σ hσ hβ hheight⟩,
    polynomialContractions_isRegular β G hG σ hσ hβ hheight,
    (polynomial_principalColon_eq_span_contractions β G hG hs σ hσ hβ).symm, ?_⟩
  intro i
  have hnonzero := regular_sequence_entry_ne_zero (columnContraction β (fun _ ↦ G.natDegree) σ)
    (columnContractions_isWeaklyRegular β (fun _ ↦ G.natDegree) σ
      (compatible_constant G.natDegree σ) hσ hβ hheight)
    (homogeneous_contraction_span_ne_top β G.natDegree σ hσ hβ hheight) i
  refine ⟨heightDegree_cast (fun _ ↦ G.natDegree) σ hσ i (hheight i).le,
    polynomialContraction_bound β G σ (singleton_weight_ne_zero β hβ) i, ?_⟩
  rw [polynomialContraction_highest β G hG σ (singleton_weight_ne_zero β hβ) i
    (heightDegree_pos (fun _ ↦ G.natDegree) σ hσ i (hheight i))]
  exact ⟨hnonzero, (constant_columnContraction_homogeneous β G.natDegree σ
    (singleton_weight_ne_zero β hβ) i).totalDegree hnonzero⟩

end PaperVerification.Fermion.Newton
