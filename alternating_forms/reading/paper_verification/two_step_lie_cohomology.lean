module

public import PaperVerification.TwoStepChevalleyEilenberg
public import PaperVerification.TwoCentralExteriorGrading
public import PaperVerification.FoldedComplexHomologyHilbert
public import PaperVerification.AlternatingFormsKoszulHilbert

/-!
# Actual Chevalley--Eilenberg cohomology after Proposition 5.4

The cochain complex below uses the actual exterior powers of the dual of
the original two-step Lie algebra and its uniquely characterized CE
differential. Its cohomology is Mathlib's categorical homology. The Hilbert
formula is derived through actual homogeneous equivalences of kernels and
images, followed by the independently proved exterior Koszul formulas.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace PaperVerification.TwoStepLieCohomology

open AlternatingForms

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

/-- The paper's original two-step Lie algebra, with its actual bracket. -/
abbrev LieAlgebra (f g : ⋀[K]^2 M) := CentralLieCochainCoordinates.L f g

/-- All actual exterior cochains of that Lie algebra. -/
abbrev Cochains (f g : ⋀[K]^2 M) := ExteriorAlgebra K (Module.Dual K (LieAlgebra f g))

instance cochains_finite (f g : ⋀[K]^2 M) : FiniteDimensional K (Cochains f g) := by
  change FiniteDimensional K
    (ExteriorAlgebra K (Module.Dual K (CentralLieCochainCoordinates.L f g)))
  infer_instance

/-- Its ordinary exterior grading, extended by zero to negative integers. -/
def cochainGrading (f g : ⋀[K]^2 M) : TauCeti.InternalGrading K (Cochains f g) :=
  exteriorIntegerGrading

theorem differential_square (f g : ⋀[K]^2 M) :
    (TwoStepChevalleyEilenberg.differential f g).comp
      (TwoStepChevalleyEilenberg.differential f g) = 0 := by
  apply LinearMap.ext
  exact TwoStepChevalleyEilenberg.differential_square_zero f g

theorem differential_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous (TwoStepChevalleyEilenberg.differential f g)
      (cochainGrading f g).piece (cochainGrading f g).piece 1 :=
  TwoCentralExteriorGrading.homogeneous_of_exterior_degree_one _
    (fun _ _ hx ↦ TwoStepChevalleyEilenberg.differential_mem_exteriorPower f g hx)

/-- The genuine integer-indexed Chevalley--Eilenberg cochain complex. -/
def cochainComplex (f g : ⋀[K]^2 M) : CochainComplex (ModuleCat K) ℤ :=
  GradedDifferentialCochainComplex.cochainComplex (cochainGrading f g)
    (TwoStepChevalleyEilenberg.differential f g) (differential_square f g)
    (differential_homogeneous f g)

/-- Ordinary categorical cohomology of the actual CE cochain complex. -/
def cohomology (f g : ⋀[K]^2 M) (q : ℤ) : ModuleCat K :=
  (cochainComplex f g).homology q

/-- The literal total CE kernel/image quotient. -/
abbrev TotalCohomology (f g : ⋀[K]^2 M) :=
  LinearMap.ker (TwoStepChevalleyEilenberg.differential f g) ⧸
    LinearMap.range (SquareZeroHomologyConjugacy.complex
      (TwoStepChevalleyEilenberg.differential f g) (differential_square f g)).moduleCatToCycles

instance totalCohomology_finite (f g : ⋀[K]^2 M) :
    FiniteDimensional K (TotalCohomology f g) :=
  inferInstanceAs (FiniteDimensional K
    (LinearMap.ker (TwoStepChevalleyEilenberg.differential f g) ⧸
      LinearMap.range ((TwoStepChevalleyEilenberg.differential f g).codRestrict
        (LinearMap.ker (TwoStepChevalleyEilenberg.differential f g))
        (fun x ↦ LinearMap.congr_fun (differential_square f g) x))))

/-- The inherited grading of the original total CE kernel/image quotient. -/
def cohomologyGrading (f g : ⋀[K]^2 M) :
    TauCeti.InternalGrading K (TotalCohomology f g) :=
  SquareZeroHomologyGrading.homologyGrading (cochainGrading f g)
    (TwoStepChevalleyEilenberg.differential f g) (differential_square f g)
    (differential_homogeneous f g)

/-- Its degree-`q` piece is the actual categorical CE cohomology in degree
`q`, through the explicit homogeneous-cycle comparison. -/
def cohomologyEquiv (f g : ⋀[K]^2 M) (q : ℤ) :
    cohomology f g q ≃ₗ[K] (cohomologyGrading f g).piece q :=
  GradedDifferentialCochainComplex.cochainHomologyEquiv _ _ _ _ q

/-- Finiteness follows from the actual homogeneous subquotient of the
finite-dimensional exterior algebra. -/
instance cohomology_finite (f g : ⋀[K]^2 M) (q : ℤ) :
    FiniteDimensional K (cohomology f g q) :=
  Module.Finite.equiv (cohomologyEquiv f g q).symm

/-- The actual finite Poincare series, with coefficients justified below
as dimensions of categorical CE cohomology. -/
def poincarePolynomial (f g : ⋀[K]^2 M) : LaurentPolynomial ℤ :=
  finiteHilbertLaurent (cohomologyGrading f g)

theorem poincarePolynomial_coeff (f g : ⋀[K]^2 M) (q : ℤ) :
    (poincarePolynomial f g).coeff q = (Module.finrank K (cohomology f g q) : ℤ) :=
  congrArg (fun n : ℕ ↦ (n : ℤ)) (cohomologyEquiv f g q).finrank_eq.symm

/-- Actual CE cochains in Koszul coordinates; the two middle factors are
the original first Koszul term. -/
def coordinates (f g : ⋀[K]^2 M) :
    Cochains f g ≃ₗ[K]
      ExteriorAlgebra K M × ((ExteriorAlgebra K M × ExteriorAlgebra K M) × ExteriorAlgebra K M) :=
  (TwoStepChevalleyEilenberg.cochainEquiv f g).toLinearEquiv.symm.trans
    TwoCentralKoszulOperator.koszulCoordinates

/-- The actual CE operator is conjugate to the original folded Koszul
differential, on every cochain. -/
theorem coordinates_differential (f g : ⋀[K]^2 M) (x : Cochains f g) :
    coordinates f g (TwoStepChevalleyEilenberg.differential f g x) =
      FoldedComplexHomology.differential (exteriorKoszulFirst f g) (exteriorKoszulSecond f g)
        (coordinates f g x) := by
  change TwoCentralKoszulOperator.koszulCoordinates
    ((TwoStepChevalleyEilenberg.cochainEquiv f g).symm
      (TwoStepChevalleyEilenberg.cochainEquiv f g
        (TwoStepExteriorComplex.d f g ((TwoStepChevalleyEilenberg.cochainEquiv f g).symm x)))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact TwoCentralKoszulOperator.koszulCoordinates_operator f g _

/-- The coordinate equivalence preserves the genuine cohomological degree,
namely the original internal Koszul degree minus its position. -/
theorem coordinates_homogeneous (f g : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous (coordinates f g).toLinearMap
      (cochainGrading f g).piece
      (FoldedComplexHomologyGrading.totalGrading exteriorKoszulTerm₀Grading
        exteriorKoszulTerm₁Grading exteriorKoszulTerm₂Grading).piece 0 := by
  intro q x hx
  have hx' := (TwoCentralExteriorGrading.exteriorMap_homogeneous
    (CentralLieCochainCoordinates.oneCochainEquiv f g).symm.toLinearMap).map_mem hx
  have hh := TwoCentralExteriorGrading.koszulCoordinates_homogeneous.map_mem hx'
  change TwoCentralKoszulOperator.koszulCoordinates
    (ExteriorAlgebra.map (CentralLieCochainCoordinates.oneCochainEquiv f g).symm.toLinearMap x) ∈
      TwoCentralExteriorGrading.foldedExteriorGrading.piece (q + 0)
  simpa only [add_zero, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe] using hh

/-- The CE Poincare series is the Hilbert series of the actual folded
Koszul homology with its inherited grading. -/
theorem poincare_eq_folded (f g : ⋀[K]^2 M) :
    poincarePolynomial f g =
      finiteHilbertLaurent
        (FoldedComplexHomologyGrading.homologyGrading exteriorKoszulTerm₀Grading
          exteriorKoszulTerm₁Grading exteriorKoszulTerm₂Grading
          (exteriorKoszulFirst f g) (exteriorKoszulSecond f g) (exteriorKoszul_comp f g)
          (exteriorKoszulFirst_homogeneous f g) (exteriorKoszulSecond_homogeneous f g)) :=
  FoldedComplexHomologyHilbert.hilbert_conjugacy
    (cochainGrading f g)
    (FoldedComplexHomologyGrading.totalGrading exteriorKoszulTerm₀Grading
      exteriorKoszulTerm₁Grading exteriorKoszulTerm₂Grading)
    (TwoStepChevalleyEilenberg.differential f g)
    (FoldedComplexHomology.differential (exteriorKoszulFirst f g) (exteriorKoszulSecond f g))
    (differential_square f g)
    (FoldedComplexHomology.differential_sq _ _ (exteriorKoszul_comp f g))
    (differential_homogeneous f g)
    (FoldedComplexHomologyGrading.differential_homogeneous _ _ _ _ _
      (exteriorKoszulFirst_homogeneous f g) (exteriorKoszulSecond_homogeneous f g))
    (coordinates f g) (coordinates_differential f g) (coordinates_homogeneous f g)

/-- Codomain restriction of the second Koszul differential changes neither
its kernel nor any of its homogeneous elements. -/
def topDegreeEquiv (f g : ⋀[K]^2 M) (q : ℤ) :
    (FoldedComplexHomologyGrading.secondGrading exteriorKoszulTerm₁Grading
      exteriorKoszulTerm₂Grading (exteriorKoszulSecond f g)
      (exteriorKoszulSecond_homogeneous f g)).piece q ≃ₗ[K]
      (exteriorKoszulH₂Grading f g).piece q where
  toFun a := ⟨⟨a.val.val, Subtype.ext a.val.property⟩, by
    apply (mem_exteriorKoszulH₂_piece f g q _).2
    have ha := (exteriorKoszulTerm₂Grading.mem_ker_piece
      (exteriorKoszulSecond_homogeneous f g)).1 a.property
    simpa only [exteriorKoszulTerm₂Grading, TauCeti.InternalGrading.shift_piece] using ha⟩
  invFun a := ⟨⟨a.val.val, congrArg Subtype.val a.val.property⟩, by
    apply (exteriorKoszulTerm₂Grading.mem_ker_piece
      (exteriorKoszulSecond_homogeneous f g)).2
    simpa only [exteriorKoszulTerm₂Grading, TauCeti.InternalGrading.shift_piece] using
      (mem_exteriorKoszulH₂_piece f g q a.val).1 a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem top_hilbert_eq (f g : ⋀[K]^2 M) :
    finiteHilbertLaurent
      (FoldedComplexHomologyGrading.secondGrading exteriorKoszulTerm₁Grading
        exteriorKoszulTerm₂Grading (exteriorKoszulSecond f g)
        (exteriorKoszulSecond_homogeneous f g)) =
      finiteHilbertLaurent (exteriorKoszulH₂Grading f g) := by
  ext q
  exact congrArg (fun n : ℕ ↦ (n : ℤ)) (topDegreeEquiv f g q).finrank_eq

/-- The actual three Koszul homology polynomials give the full categorical
CE cohomology series, with the two required cohomological shifts. -/
theorem poincare_eq_koszul (f g : ⋀[K]^2 M) :
    poincarePolynomial f g =
      finiteHilbertLaurent (exteriorKoszulH₀Grading f g) +
        (LaurentPolynomial.T (-1) * finiteHilbertLaurent (exteriorKoszulH₁Grading f g) +
          LaurentPolynomial.T (-2) * finiteHilbertLaurent (exteriorKoszulH₂Grading f g)) := by
  rw [poincare_eq_folded]
  simpa only [top_hilbert_eq, FoldedComplexHomologyGrading.zerothGrading,
    FoldedComplexHomologyGrading.firstGrading, exteriorKoszulH₀Grading,
    exteriorKoszulH₁Grading, shortComplexH₀Grading, shortComplexH₁Grading,
    FoldedComplexHomology.middleToCycles, shortComplexToCycles] using
    FoldedComplexHomologyHilbert.hilbert_folded exteriorKoszulTerm₀Grading
      exteriorKoszulTerm₁Grading exteriorKoszulTerm₂Grading
      (exteriorKoszulFirst f g) (exteriorKoszulSecond f g) (exteriorKoszul_comp f g)
      (exteriorKoszulFirst_homogeneous f g) (exteriorKoszulSecond_homogeneous f g)

/-- The Poincare formula following Proposition 5.4, before the separate
identification of the middle Koszul polynomial with ordinary Tor. -/
theorem poincare_formula (f g : ⋀[K]^2 M) :
    poincarePolynomial f g = exteriorQuotientHilbert f g +
      (LaurentPolynomial.T (-1) * finiteHilbertLaurent (exteriorKoszulH₁Grading f g) +
        LaurentPolynomial.T ((Module.finrank K M : ℤ) + 2) *
          LaurentPolynomial.invert (exteriorQuotientHilbert f g)) := by
  rw [poincare_eq_koszul, exteriorKoszulH₂_hilbert, ← mul_assoc, ← LaurentPolynomial.T_add]
  congr 3
  ring

/-- No negative cohomological degrees are introduced by the Laurent
notation: the original exterior grading vanishes there. -/
theorem cohomologyGrading_piece_negative (f g : ⋀[K]^2 M) {q : ℤ} (hq : q < 0) :
    (cohomologyGrading f g).piece q = ⊥ :=
  SquareZeroHomologyGrading.homologyGrading_piece_eq_bot
    (cochainGrading f g) (TwoStepChevalleyEilenberg.differential f g)
    (differential_square f g) (differential_homogeneous f g)
    (exteriorIntegerGrading_piece_negative hq)

theorem poincarePolynomial_negative (f g : ⋀[K]^2 M) {q : ℤ} (hq : q < 0) :
    (poincarePolynomial f g).coeff q = 0 := by
  change (Module.finrank K ((cohomologyGrading f g).piece q) : ℤ) = 0
  rw [cohomologyGrading_piece_negative f g hq, finrank_bot, Nat.cast_zero]

/-- The actual categorical cohomology itself vanishes in negative degrees. -/
theorem cohomology_subsingleton_negative (f g : ⋀[K]^2 M) {q : ℤ} (hq : q < 0) :
    Subsingleton (cohomology f g q) := by
  haveI : Subsingleton ((cohomologyGrading f g).piece q) := by
    rw [cohomologyGrading_piece_negative f g hq]
    infer_instance
  constructor
  intro x y
  apply (cohomologyEquiv f g q).injective
  exact Subsingleton.elim _ _

/-- Evaluation at one is defined on Laurent polynomials since one is a
unit. -/
def evalAtOne : LaurentPolynomial ℤ →+* ℤ :=
  LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ)

@[simp] theorem evalAtOne_T (q : ℤ) : evalAtOne (LaurentPolynomial.T q) = 1 := by
  simp [evalAtOne]

@[simp] theorem evalAtOne_invert (P : LaurentPolynomial ℤ) :
    evalAtOne (LaurentPolynomial.invert P) = evalAtOne P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | C_mul_T q a => simp [evalAtOne]

/-- At one, evaluation is exactly the finite sum of all coefficients. -/
theorem evalAtOne_eq_sum (P : LaurentPolynomial ℤ) :
    evalAtOne P = P.coeff.sum (fun _ a ↦ a) := by
  have h : evalAtOne P = P.smeval (1 : ℤˣ) := by
    induction P using LaurentPolynomial.induction_on' with
    | add P Q hP hQ => simp only [map_add, LaurentPolynomial.smeval_add, hP, hQ]
    | C_mul_T q a =>
      rw [map_mul, LaurentPolynomial.smeval_C_mul_T_n]
      simp [evalAtOne, smul_eq_mul]
  rw [h]
  simp only [LaurentPolynomial.smeval, one_zpow, Units.val_one, smul_eq_mul, mul_one]

/-- The total dimension is the sum of the dimensions of the actual
categorical cohomology groups over their finite support. -/
def totalCohomologyDimension (f g : ⋀[K]^2 M) : ℤ :=
  ∑ q ∈ (poincarePolynomial f g).coeff.support, (Module.finrank K (cohomology f g q) : ℤ)

/-- Degrees outside this finite support contribute zero actual
cohomology dimension. -/
theorem cohomology_finrank_zero_of_not_support (f g : ⋀[K]^2 M) {q : ℤ}
    (hq : q ∉ (poincarePolynomial f g).coeff.support) :
    Module.finrank K (cohomology f g q) = 0 := by
  have hz := Finsupp.notMem_support_iff.1 hq
  rw [poincarePolynomial_coeff] at hz
  exact_mod_cast hz

theorem totalDimension_eq_eval (f g : ⋀[K]^2 M) :
    totalCohomologyDimension f g = evalAtOne (poincarePolynomial f g) := by
  rw [evalAtOne_eq_sum]
  change (∑ q ∈ (poincarePolynomial f g).coeff.support,
    (Module.finrank K (cohomology f g q) : ℤ)) =
      ∑ q ∈ (poincarePolynomial f g).coeff.support, (poincarePolynomial f g).coeff q
  exact Finset.sum_congr rfl (fun q _ ↦ (poincarePolynomial_coeff f g q).symm)

/-- The complete Poincare series evaluates to four times the actual
exterior quotient Hilbert series at one. -/
theorem poincare_at_one (f g : ⋀[K]^2 M) :
    evalAtOne (poincarePolynomial f g) = 4 * evalAtOne (exteriorQuotientHilbert f g) := by
  rw [poincare_eq_koszul, (exteriorKoszul_all_hilbert_formulas f g).2.2,
    exteriorKoszulH₂_hilbert]
  change evalAtOne
    (exteriorQuotientHilbert f g +
      (LaurentPolynomial.T (-1) *
        (exteriorQuotientHilbert f g +
          LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
            LaurentPolynomial.invert (exteriorQuotientHilbert f g) -
          (1 - LaurentPolynomial.T 2) ^ 2 *
            (1 + LaurentPolynomial.T 1) ^ Module.finrank K M) +
        LaurentPolynomial.T (-2) *
          (LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
            LaurentPolynomial.invert (exteriorQuotientHilbert f g)))) = _
  simp only [map_add, map_mul, map_sub, map_pow, map_one, evalAtOne_T, evalAtOne_invert]
  ring

/-- The paper's total Lie-cohomology dimension formula, with every summand
the actual categorical cohomology of the original CE complex. -/
theorem total_dimension_four (f g : ⋀[K]^2 M) :
    totalCohomologyDimension f g = 4 * evalAtOne (exteriorQuotientHilbert f g) := by
  rw [totalDimension_eq_eval, poincare_at_one]

end PaperVerification.TwoStepLieCohomology
