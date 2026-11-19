module

public import PaperVerification.TwoStepLieCohomologyBetti
public import PaperVerification.TwoStepOriginalLie
public import PaperVerification.ChevalleyEilenbergTransport

/-!
# Cohomology of the paper's literal Lie algebra on `V × K²`

The two original forms belong to `Λ²(V*)`.  The bracket is defined directly
on `V × K²`, and the differential below is the uniquely characterized
Chevalley--Eilenberg differential on its actual exterior cochains.  The
canonical evaluation Lie equivalence transports the already computed
cohomology, with the comparison proved on actual homogeneous cycle classes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace PaperVerification.TwoStepOriginalLieCohomology

open AlternatingForms

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

instance lie_finite (f g : ⋀[K]^2 (Module.Dual K V)) :
    FiniteDimensional K (TwoStepOriginalLie.L f g) :=
  inferInstanceAs (FiniteDimensional K (V × (Fin 2 → K)))

/-- The cochains are exterior powers of the dual of the original `V × K²`. -/
abbrev Cochains (f g : ⋀[K]^2 (Module.Dual K V)) :=
  ExteriorAlgebra K (Module.Dual K (TwoStepOriginalLie.L f g))

instance cochains_finite (f g : ⋀[K]^2 (Module.Dual K V)) :
    FiniteDimensional K (Cochains f g) := by
  change FiniteDimensional K
    (ExteriorAlgebra K (Module.Dual K (TwoStepOriginalLie.L f g)))
  infer_instance

/-- Pullback is the actual exterior-algebra map induced by the dual of
the canonical evaluation Lie equivalence. -/
def cochainPullback (f g : ⋀[K]^2 (Module.Dual K V)) :
    TwoStepLieCohomology.Cochains f g ≃ₐ[K] Cochains f g :=
  ExteriorDerivationTransport.mapEquiv
    (TwoStepOriginalLie.evalLieEquiv f g).toLinearEquiv.dualMap

/-- The actual CE differential on the original Lie algebra. -/
def differential (f g : ⋀[K]^2 (Module.Dual K V)) : Module.End K (Cochains f g) :=
  ChevalleyEilenbergTransport.pullback (TwoStepOriginalLie.evalLieEquiv f g)
    (TwoStepChevalleyEilenberg.differential f g)

/-- Its intrinsic characterization uses the original bracket and the
usual negative bracket-dual sign. -/
theorem differential_isChevalleyEilenberg (f g : ⋀[K]^2 (Module.Dual K V)) :
    ChevalleyEilenbergExterior.IsDifferential (differential f g) :=
  ChevalleyEilenbergTransport.pullback_isDifferential _ _
    (TwoStepChevalleyEilenberg.differential_isChevalleyEilenberg f g)

theorem differential_unique (f g : ⋀[K]^2 (Module.Dual K V))
    (D : Module.End K (Cochains f g))
    (hD : ChevalleyEilenbergExterior.IsDifferential D) : D = differential f g :=
  ChevalleyEilenbergExterior.differential_unique hD (differential_isChevalleyEilenberg f g)

theorem differential_square (f g : ⋀[K]^2 (Module.Dual K V)) :
    (differential f g).comp (differential f g) = 0 := by
  apply LinearMap.ext
  exact ChevalleyEilenbergTransport.pullback_square_zero _ _
    (TwoStepChevalleyEilenberg.differential_square_zero f g)

/-- Original exterior degrees, with the negative integer pieces zero. -/
def cochainGrading (f g : ⋀[K]^2 (Module.Dual K V)) :
    TauCeti.InternalGrading K (Cochains f g) := exteriorIntegerGrading

theorem differential_homogeneous (f g : ⋀[K]^2 (Module.Dual K V)) :
    TauCeti.LinearMap.IsHomogeneous (differential f g)
      (cochainGrading f g).piece (cochainGrading f g).piece 1 :=
  TwoCentralExteriorGrading.homogeneous_of_exterior_degree_one _
    (ChevalleyEilenbergTransport.pullback_degree _ _
      (fun _ _ hx ↦ TwoStepChevalleyEilenberg.differential_mem_exteriorPower f g hx))

/-- Pullback commutes with the actual differentials, on every cochain. -/
theorem cochainPullback_differential (f g : ⋀[K]^2 (Module.Dual K V))
    (x : TwoStepLieCohomology.Cochains f g) :
    cochainPullback f g (TwoStepChevalleyEilenberg.differential f g x) =
      differential f g (cochainPullback f g x) :=
  (ChevalleyEilenbergTransport.pullback_map _ _ x).symm

theorem cochainPullback_homogeneous (f g : ⋀[K]^2 (Module.Dual K V)) :
    TauCeti.LinearMap.IsHomogeneous (cochainPullback f g).toLinearMap
      (TwoStepLieCohomology.cochainGrading f g).piece (cochainGrading f g).piece 0 :=
  TwoCentralExteriorGrading.exteriorMap_homogeneous
    (TwoStepOriginalLie.evalLieEquiv f g).toLinearEquiv.dualMap.toLinearMap

/-- The genuine integer-indexed CE complex of the original Lie algebra. -/
def cochainComplex (f g : ⋀[K]^2 (Module.Dual K V)) : CochainComplex (ModuleCat K) ℤ :=
  GradedDifferentialCochainComplex.cochainComplex (cochainGrading f g)
    (differential f g) (differential_square f g) (differential_homogeneous f g)

/-- Its actual categorical cohomology in every integer degree. -/
def cohomology (f g : ⋀[K]^2 (Module.Dual K V)) (q : ℤ) : ModuleCat K :=
  (cochainComplex f g).homology q

/-- Canonical evaluation induces a linear equivalence on the actual
categorical cohomology groups, through explicit homogeneous cycle classes. -/
def cohomologyEquiv (f g : ⋀[K]^2 (Module.Dual K V)) (q : ℤ) :
    cohomology f g q ≃ₗ[K] TwoStepLieCohomology.cohomology f g q :=
  (GradedDifferentialCochainComplex.cochainHomologyEquiv
    (cochainGrading f g) (differential f g) (differential_square f g)
    (differential_homogeneous f g) q).trans
      ((SquareZeroHomologyGrading.homogeneousPieceEquiv
        (TwoStepLieCohomology.cochainGrading f g)
        (TwoStepChevalleyEilenberg.differential f g)
        (TwoStepLieCohomology.differential_square f g)
        (TwoStepLieCohomology.differential_homogeneous f g)
        (cochainGrading f g) (differential f g) (differential_square f g)
        (differential_homogeneous f g) (cochainPullback f g).toLinearEquiv
        (cochainPullback_differential f g) (cochainPullback_homogeneous f g) q).symm.trans
          (TwoStepLieCohomology.cohomologyEquiv f g q).symm)

instance cohomology_finite (f g : ⋀[K]^2 (Module.Dual K V)) (q : ℤ) :
    FiniteDimensional K (cohomology f g q) :=
  Module.Finite.equiv (cohomologyEquiv f g q).symm

/-- The Poincare polynomial transported along the proved degreewise
equivalence; the next theorem identifies its coefficients intrinsically. -/
def poincarePolynomial (f g : ⋀[K]^2 (Module.Dual K V)) : LaurentPolynomial ℤ :=
  TwoStepLieCohomology.poincarePolynomial f g

theorem poincarePolynomial_coeff (f g : ⋀[K]^2 (Module.Dual K V)) (q : ℤ) :
    (poincarePolynomial f g).coeff q = (Module.finrank K (cohomology f g q) : ℤ) := by
  rw [poincarePolynomial, TwoStepLieCohomology.poincarePolynomial_coeff]
  exact congrArg (fun n : ℕ ↦ (n : ℤ)) (cohomologyEquiv f g q).finrank_eq.symm

/-- The paper's full formula on the literal original Lie space, with
ordinary Tor in `B₁` and the dimension of the original vector space `V`. -/
theorem paper_lie_cohomology_poincare (f g : ⋀[K]^2 (Module.Dual K V)) :
    poincarePolynomial f g = exteriorQuotientHilbert f g +
      (LaurentPolynomial.T (-1) * exteriorOriginBettiPolynomial f g 1 +
        LaurentPolynomial.T ((Module.finrank K V : ℤ) + 2) *
          LaurentPolynomial.invert (exteriorQuotientHilbert f g)) := by
  simpa only [poincarePolynomial, Subspace.dual_finrank_eq] using
    TwoStepLieCohomology.paper_lie_cohomology_poincare f g

theorem paper_lie_cohomology_degree (f g : ⋀[K]^2 (Module.Dual K V)) (q : ℤ) :
    (Module.finrank K (cohomology f g q) : ℤ) =
      (exteriorQuotientHilbert f g +
        (LaurentPolynomial.T (-1) * exteriorOriginBettiPolynomial f g 1 +
          LaurentPolynomial.T ((Module.finrank K V : ℤ) + 2) *
            LaurentPolynomial.invert (exteriorQuotientHilbert f g))).coeff q := by
  rw [← poincarePolynomial_coeff, paper_lie_cohomology_poincare]

/-- There is no categorical cohomology in negative degrees. -/
theorem cohomology_subsingleton_negative (f g : ⋀[K]^2 (Module.Dual K V))
    {q : ℤ} (hq : q < 0) : Subsingleton (cohomology f g q) := by
  haveI := TwoStepLieCohomology.cohomology_subsingleton_negative f g hq
  constructor
  intro x y
  apply (cohomologyEquiv f g q).injective
  exact Subsingleton.elim _ _

theorem poincarePolynomial_is_ordinary (f g : ⋀[K]^2 (Module.Dual K V)) :
    ∃! P : Polynomial ℤ, P.toLaurent = poincarePolynomial f g :=
  TwoStepLieCohomology.poincarePolynomial_is_ordinary f g

/-- The finite sum of the dimensions of the actual original cohomology. -/
def totalCohomologyDimension (f g : ⋀[K]^2 (Module.Dual K V)) : ℤ :=
  ∑ q ∈ (poincarePolynomial f g).coeff.support, (Module.finrank K (cohomology f g q) : ℤ)

theorem cohomology_finrank_zero_of_not_support (f g : ⋀[K]^2 (Module.Dual K V)) {q : ℤ}
    (hq : q ∉ (poincarePolynomial f g).coeff.support) :
    Module.finrank K (cohomology f g q) = 0 := by
  rw [(cohomologyEquiv f g q).finrank_eq]
  exact TwoStepLieCohomology.cohomology_finrank_zero_of_not_support f g hq

/-- The total dimension is four times the actual exterior-quotient
Hilbert polynomial at one, with no genericity assumption on the forms. -/
theorem total_dimension_four (f g : ⋀[K]^2 (Module.Dual K V)) :
    totalCohomologyDimension f g =
      4 * TwoStepLieCohomology.evalAtOne (exteriorQuotientHilbert f g) := by
  have h : totalCohomologyDimension f g = TwoStepLieCohomology.totalCohomologyDimension f g := by
    apply Finset.sum_congr rfl
    intro q _
    exact congrArg (fun n : ℕ ↦ (n : ℤ)) (cohomologyEquiv f g q).finrank_eq
  rw [h, TwoStepLieCohomology.total_dimension_four]

end PaperVerification.TwoStepOriginalLieCohomology
