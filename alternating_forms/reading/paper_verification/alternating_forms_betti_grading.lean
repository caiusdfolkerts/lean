module

public import PaperVerification.AlternatingFormsBetti
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Faithfulness of the internal degree in Proposition 5.4

The actual polynomial action preserves the grading with both variables of
weight two.  The tensor resolution grading agrees on homogeneous pure
tensors with their tensor-product degree, including the shifts two and four.
These statements justify the internal degree in the derived-Tor comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.AlternatingForms

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

/-- The augmentation has degree zero when each polynomial variable has
weight two and the coefficient field is concentrated in degree zero. -/
theorem pairConstantCoefficient_positive_degree {p : PairPolynomial K} {q : ℕ}
    (hp : p.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q) (hq : q ≠ 0) :
    pairConstantCoefficient K p = 0 := by
  change MvPolynomial.constantCoeff p = 0
  by_contra h
  have hc : p.coeff 0 ≠ 0 := by
    simpa only [MvPolynomial.constantCoeff_eq] using h
  have h0q : 0 = q := by simpa only [map_zero] using hp hc
  exact hq h0q.symm

theorem quadraticPolynomialEvaluation_monomial (f g : ⋀[K]^2 M)
    (d : Fin 2 →₀ ℕ) (c : K) :
    quadraticPolynomialEvaluation f g (MvPolynomial.monomial d c) =
      c • ((f : ExteriorAlgebra K M) ^ d 0 * (g : ExteriorAlgebra K M) ^ d 1) := by
  classical
  unfold quadraticPolynomialEvaluation
  rw [AlgHom.comp_apply, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [Fin.prod_univ_two, centralTwoForm, Algebra.smul_def]

/-- Actual substitution of two exterior forms preserves the degree where
each polynomial variable is assigned weight two. -/
theorem quadraticPolynomialEvaluation_homogeneous (f g : ⋀[K]^2 M)
    {p : PairPolynomial K} {q : ℕ}
    (hp : p.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q) :
    quadraticPolynomialEvaluation f g p ∈ ⋀[K]^q M := by
  classical
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hdq := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [Finsupp.weight_eq_sum, Fin.sum_univ_two] at hdq
  rw [quadraticPolynomialEvaluation_monomial]
  apply Submodule.smul_mem
  simpa only [hdq] using
    (SetLike.mul_mem_graded (SetLike.pow_mem_graded (d 0) f.property)
      (SetLike.pow_mem_graded (d 1) g.property))

theorem exteriorPair_homogeneous_smul (f g : ⋀[K]^2 M)
    {p : PairPolynomial K} {q r : ℕ}
    (hp : p.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q)
    {a : ExteriorPairModule f g} (ha : (a : ExteriorAlgebra K M) ∈ ⋀[K]^r M) :
    ((p • a : ExteriorPairModule f g) : ExteriorAlgebra K M) ∈ ⋀[K]^(q + r) M := by
  change quadraticPolynomialEvaluation f g p * exteriorPairModuleEquiv f g a ∈
    ⋀[K]^(q + r) M
  exact SetLike.mul_mem_graded (quadraticPolynomialEvaluation_homogeneous f g hp)
    (show exteriorPairModuleEquiv f g a ∈ ⋀[K]^r M from ha)

variable [FiniteDimensional K M]

/-- The actual tensor complex has the grading of the free polynomial
resolution: its free basis vectors have internal degrees zero, two and four. -/
def exteriorTensorTermGrading (f g : ⋀[K]^2 M) : (i : ℕ) →
    TauCeti.InternalGrading K ((exteriorPolynomialTensorComplexOverK f g).X i)
  | 0 => exteriorKoszulTerm₀Grading.map (exteriorTensorTermEquiv f g 0).symm
  | 1 => exteriorKoszulTerm₁Grading.map (exteriorTensorTermEquiv f g 1).symm
  | 2 => exteriorKoszulTerm₂Grading.map (exteriorTensorTermEquiv f g 2).symm
  | _ + 3 => zeroInternalGrading

theorem exteriorTensorTermGrading_zero_mem_iff (f g : ⋀[K]^2 M) (q : ℤ)
    (x : (exteriorPolynomialTensorComplexOverK f g).X 0) :
    x ∈ (exteriorTensorTermGrading f g 0).piece q ↔
      exteriorTensorTermEquiv f g 0 x ∈ exteriorKoszulTerm₀Grading.piece q := by
  simp only [exteriorTensorTermGrading, TauCeti.InternalGrading.map_piece,
    Submodule.mem_map_equiv, LinearEquiv.symm_symm] <;> rfl

theorem exteriorTensorTermGrading_one_mem_iff (f g : ⋀[K]^2 M) (q : ℤ)
    (x : (exteriorPolynomialTensorComplexOverK f g).X 1) :
    x ∈ (exteriorTensorTermGrading f g 1).piece q ↔
      exteriorTensorTermEquiv f g 1 x ∈ exteriorKoszulTerm₁Grading.piece q := by
  simp only [exteriorTensorTermGrading, TauCeti.InternalGrading.map_piece,
    Submodule.mem_map_equiv, LinearEquiv.symm_symm] <;> rfl

theorem exteriorTensorTermGrading_two_mem_iff (f g : ⋀[K]^2 M) (q : ℤ)
    (x : (exteriorPolynomialTensorComplexOverK f g).X 2) :
    x ∈ (exteriorTensorTermGrading f g 2).piece q ↔
      exteriorTensorTermEquiv f g 2 x ∈ exteriorKoszulTerm₂Grading.piece q := by
  simp only [exteriorTensorTermGrading, TauCeti.InternalGrading.map_piece,
    Submodule.mem_map_equiv, LinearEquiv.symm_symm] <;> rfl

theorem exteriorTensorTermGrading_zero_tmul (f g : ⋀[K]^2 M)
    {p : PairPolynomial K} {q r : ℕ}
    (hp : p.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q)
    {a : ExteriorPairModule f g} (ha : (a : ExteriorAlgebra K M) ∈ ⋀[K]^r M) :
    a ⊗ₜ[PairPolynomial K] p ∈
      (exteriorTensorTermGrading f g 0).piece ((q + r : ℕ) : ℤ) := by
  rw [exteriorTensorTermGrading_zero_mem_iff f g _ _,
    exteriorTensorTermEquiv_zero_tmul f g a p]
  change ((p • a : ExteriorPairModule f g) : ExteriorAlgebra K M) ∈
    exteriorIntegerGrading.piece ((q + r : ℕ) : ℤ)
  rw [exteriorIntegerGrading_piece_nat]
  exact exteriorPair_homogeneous_smul f g hp ha

theorem exteriorTensorTermGrading_one_tmul (f g : ⋀[K]^2 M)
    {p : PairPolynomial K × PairPolynomial K} {q r : ℕ}
    (hp₁ : p.1.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q)
    (hp₂ : p.2.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q)
    {a : ExteriorPairModule f g} (ha : (a : ExteriorAlgebra K M) ∈ ⋀[K]^r M) :
    a ⊗ₜ[PairPolynomial K] p ∈
      (exteriorTensorTermGrading f g 1).piece ((q + r : ℕ) + 2 : ℤ) := by
  rw [exteriorTensorTermGrading_one_mem_iff f g _ _,
    exteriorTensorTermEquiv_one_tmul f g a _]
  rw [exteriorKoszulTerm₁Grading, TauCeti.InternalGrading.shift_piece,
    TauCeti.InternalGrading.prod_piece]
  change (p.1 • a : ExteriorPairModule f g) ∈
      exteriorIntegerGrading.piece (((q + r : ℕ) : ℤ) + 2 + -2) ∧
    (p.2 • a : ExteriorPairModule f g) ∈
      exteriorIntegerGrading.piece (((q + r : ℕ) : ℤ) + 2 + -2)
  have hq : ((q + r : ℕ) : ℤ) + 2 + -2 = ((q + r : ℕ) : ℤ) := by omega
  rw [hq, exteriorIntegerGrading_piece_nat]
  exact ⟨exteriorPair_homogeneous_smul f g hp₁ ha,
    exteriorPair_homogeneous_smul f g hp₂ ha⟩

theorem exteriorTensorTermGrading_two_tmul (f g : ⋀[K]^2 M)
    {p : PairPolynomial K} {q r : ℕ}
    (hp : p.IsWeightedHomogeneous (fun _ : Fin 2 => (2 : ℕ)) q)
    {a : ExteriorPairModule f g} (ha : (a : ExteriorAlgebra K M) ∈ ⋀[K]^r M) :
    a ⊗ₜ[PairPolynomial K] p ∈
      (exteriorTensorTermGrading f g 2).piece ((q + r : ℕ) + 4 : ℤ) := by
  rw [exteriorTensorTermGrading_two_mem_iff f g _ _,
    exteriorTensorTermEquiv_two_tmul f g a p]
  rw [exteriorKoszulTerm₂Grading, TauCeti.InternalGrading.shift_piece]
  change (p • a : ExteriorPairModule f g) ∈
    exteriorIntegerGrading.piece (((q + r : ℕ) : ℤ) + 4 + -4)
  have hq : ((q + r : ℕ) : ℤ) + 4 + -4 = ((q + r : ℕ) : ℤ) := by omega
  rw [hq, exteriorIntegerGrading_piece_nat]
  exact exteriorPair_homogeneous_smul f g hp ha

/-- The chosen degree on the actual tensor complex is also characterized
on its polynomial free generators.  Thus it is exactly the usual tensor
grading, with no change of degree in the homology comparison. -/
theorem exteriorTensorTermGrading_zero_generator (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (q : ℤ) :
    a ⊗ₜ[PairPolynomial K] (1 : PairPolynomial K) ∈
        (exteriorTensorTermGrading f g 0).piece q ↔
      (a : ExteriorAlgebra K M) ∈ exteriorIntegerGrading.piece q := by
  rw [exteriorTensorTermGrading_zero_mem_iff f g _ _,
    exteriorTensorTermEquiv_zero_tmul f g a 1, one_smul]
  rfl

theorem exteriorTensorTermGrading_two_generator (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (q : ℤ) :
    a ⊗ₜ[PairPolynomial K] (1 : PairPolynomial K) ∈
        (exteriorTensorTermGrading f g 2).piece (q + 4) ↔
      (a : ExteriorAlgebra K M) ∈ exteriorIntegerGrading.piece q := by
  rw [exteriorTensorTermGrading_two_mem_iff f g _ _,
    exteriorTensorTermEquiv_two_tmul f g a 1, one_smul]
  rw [exteriorKoszulTerm₂Grading, TauCeti.InternalGrading.shift_piece]
  change a ∈ exteriorIntegerGrading.piece (q + 4 + -4) ↔ _
  rw [show q + 4 + -4 = q by omega]

theorem exteriorTensorTermGrading_one_left_generator (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (q : ℤ) :
    a ⊗ₜ[PairPolynomial K] ((1, 0) : PairPolynomial K × PairPolynomial K) ∈
        (exteriorTensorTermGrading f g 1).piece (q + 2) ↔
      (a : ExteriorAlgebra K M) ∈ exteriorIntegerGrading.piece q := by
  rw [exteriorTensorTermGrading_one_mem_iff f g _ _,
    exteriorTensorTermEquiv_one_tmul f g a _]
  rw [exteriorKoszulTerm₁Grading, TauCeti.InternalGrading.shift_piece,
    TauCeti.InternalGrading.prod_piece]
  change (1 • a : ExteriorPairModule f g) ∈ exteriorIntegerGrading.piece (q + 2 + -2) ∧
    (0 • a : ExteriorPairModule f g) ∈ exteriorIntegerGrading.piece (q + 2 + -2) ↔ _
  have hq : q + 2 + -2 = q := by omega
  simp only [hq, one_smul, zero_smul, Submodule.zero_mem, and_true]

theorem exteriorTensorTermGrading_one_right_generator (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (q : ℤ) :
    a ⊗ₜ[PairPolynomial K] ((0, 1) : PairPolynomial K × PairPolynomial K) ∈
        (exteriorTensorTermGrading f g 1).piece (q + 2) ↔
      (a : ExteriorAlgebra K M) ∈ exteriorIntegerGrading.piece q := by
  rw [exteriorTensorTermGrading_one_mem_iff f g _ _,
    exteriorTensorTermEquiv_one_tmul f g a _]
  rw [exteriorKoszulTerm₁Grading, TauCeti.InternalGrading.shift_piece,
    TauCeti.InternalGrading.prod_piece]
  change (0 • a : ExteriorPairModule f g) ∈ exteriorIntegerGrading.piece (q + 2 + -2) ∧
    (1 • a : ExteriorPairModule f g) ∈ exteriorIntegerGrading.piece (q + 2 + -2) ↔ _
  have hq : q + 2 + -2 = q := by omega
  simp only [hq, one_smul, zero_smul, Submodule.zero_mem, true_and]

/-- The first actual tensor differential is homogeneous of degree zero. -/
theorem exteriorTensorFirst_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous
      ((exteriorPolynomialTensorComplexOverK f g).d 1 0).hom
      (exteriorTensorTermGrading f g 1).piece (exteriorTensorTermGrading f g 0).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  rw [exteriorTensorTermGrading_one_mem_iff f g q a] at ha
  rw [exteriorTensorTermGrading_zero_mem_iff f g _ _]
  have h := (exteriorKoszulFirst_homogeneous f g).map_mem ha
  have he := congrArg
    (fun k : (exteriorPolynomialTensorComplexOverK f g).X 1 ⟶
      (exteriorPairComplex f g).X 0 => k a) (exteriorTensorTermEquiv_comm f g 0)
  change exteriorKoszulFirst f g (exteriorTensorTermEquiv f g 1 a) =
    exteriorTensorTermEquiv f g 0 ((exteriorPolynomialTensorComplexOverK f g).d 1 0 a) at he
  rw [← he]
  exact h

/-- The second actual tensor differential has the same internal degree. -/
theorem exteriorTensorSecond_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous
      ((exteriorPolynomialTensorComplexOverK f g).d 2 1).hom
      (exteriorTensorTermGrading f g 2).piece (exteriorTensorTermGrading f g 1).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  rw [exteriorTensorTermGrading_two_mem_iff f g q a] at ha
  rw [exteriorTensorTermGrading_one_mem_iff f g _ _]
  have h := (exteriorKoszulSecond_homogeneous f g).map_mem ha
  have he := congrArg
    (fun k : (exteriorPolynomialTensorComplexOverK f g).X 2 ⟶
      (exteriorPairComplex f g).X 1 => k a) (exteriorTensorTermEquiv_comm f g 1)
  change exteriorKoszulSecond f g (exteriorTensorTermEquiv f g 2 a) =
    exteriorTensorTermEquiv f g 1 ((exteriorPolynomialTensorComplexOverK f g).d 2 1 a) at he
  rw [← he]
  exact h

theorem exteriorKoszulH₁_piece_negative (f g : ⋀[K]^2 M) {q : ℤ} (hq : q < 0) :
    (exteriorKoszulH₁Grading f g).piece q = ⊥ := by
  have hker :
      ((exteriorKoszulTerm₁Grading (K := K) (M := M)).ker
        (exteriorKoszulFirst_homogeneous f g)).piece q = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    rw [TauCeti.InternalGrading.mem_ker_piece,exteriorKoszulTerm₁Grading,
      TauCeti.InternalGrading.shift_piece,TauCeti.InternalGrading.prod_piece] at ha
    change a.1.1 ∈ exteriorIntegerGrading.piece (q + -2) ∧
      a.1.2 ∈ exteriorIntegerGrading.piece (q + -2) at ha
    rw [exteriorIntegerGrading_piece_negative (by omega : q + -2 < 0)] at ha
    apply Subtype.ext
    exact Prod.ext ha.1 ha.2
  unfold exteriorKoszulH₁Grading shortComplexH₁Grading
  rw [TauCeti.InternalGrading.quotient_piece, hker, Submodule.map_bot]

/-- Every negative internal degree is zero. Thus the Laurent presentation
of the Betti identities retains ordinary polynomial Hilbert series. -/
theorem exteriorBettiPolynomial_negative (f g : ⋀[K]^2 M) (i : ℕ)
    {q : ℤ} (hq : q < 0) : (exteriorBettiPolynomial f g i).coeff q = 0 := by
  cases i with
  | zero =>
    rw [exteriorBettiPolynomial_zero, finiteHilbertLaurent_coeff,
      exteriorKoszulH₀_piece_negative f g hq, finrank_bot, Nat.cast_zero]
  | succ i =>
    cases i with
    | zero =>
      rw [exteriorBettiPolynomial_one, finiteHilbertLaurent_coeff,
        exteriorKoszulH₁_piece_negative f g hq, finrank_bot, Nat.cast_zero]
    | succ i =>
      cases i with
      | zero =>
        rw [exteriorBettiPolynomial_two, finiteHilbertLaurent_coeff,
          exteriorKoszulH₂_piece_below f g (by omega), finrank_bot, Nat.cast_zero]
      | succ i =>
        rw [exteriorBettiPolynomial_above f g (by omega), AddMonoidAlgebra.coeff_zero] <;> rfl

theorem laurent_trunc_coefficient (F : LaurentPolynomial ℤ) (q : ℕ) :
    (LaurentPolynomial.trunc F).coeff q = F.coeff (q : ℤ) := rfl

theorem toLaurent_trunc_of_nonnegative (F : LaurentPolynomial ℤ)
    (hF : ∀ q : ℤ, q < 0 → F.coeff q = 0) :
    (LaurentPolynomial.trunc F).toLaurent = F := by
  ext q
  by_cases hq : 0 ≤ q
  · have hq' : q = (q.toNat : ℤ) := by omega
    rw [hq', toLaurent_coefficient_nat, laurent_trunc_coefficient]
  · rw [toLaurent_coefficient_negative _ (by omega), hF q (by omega)]

/-- The ordinary polynomial exists uniquely and has precisely the actual
Tor-component dimensions as its coefficients. -/
theorem exteriorBettiPolynomial_is_ordinary (f g : ⋀[K]^2 M) (i : ℕ) :
    ∃! B : Polynomial ℤ, B.toLaurent = exteriorBettiPolynomial f g i := by
  refine ⟨LaurentPolynomial.trunc (exteriorBettiPolynomial f g i),
    toLaurent_trunc_of_nonnegative _ (fun q hq ↦ exteriorBettiPolynomial_negative f g i hq), ?_⟩
  intro B hB
  apply Polynomial.toLaurent_injective
  rw [hB, toLaurent_trunc_of_nonnegative _
    (fun q hq ↦ exteriorBettiPolynomial_negative f g i hq)]

end PaperVerification.AlternatingForms
