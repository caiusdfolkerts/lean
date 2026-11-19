module

public import higher_specht.verified.final

@[expose] public section
noncomputable section
open Module

namespace HigherSpecht

/-- The actual staircase monomials from the enlarged special-fiber diagram
give a basis over the elementary parameters for every coefficient ring. -/
theorem untruncated_parameter_staircase_basis (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsSpecifiedBasis (R := ElementaryParameterRing R n lam)
      (fun a : SpecialFiberMonomialIndex n lam => parameterMonomialClass R n lam a.val) :=
  ⟨untruncatedMonomialParameterBasis R n lam hk,
    untruncatedMonomialParameterBasis_apply R n lam hk⟩

/-- Every coefficient field gives the stated dimension and local
Cohen–Macaulayness at all primes. -/
theorem parameter_family_dimension_and_cohenMacaulay (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    ringKrullDim (UntruncatedRing K n lam) = (n - lam.card : ℕ) ∧
      IsNoetherianRing (UntruncatedRing K n lam) ∧
      ∀ (P : Ideal (UntruncatedRing K n lam)) [P.IsPrime],
        Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by
  letI := untruncated_parameter_finite_allCoefficients K n lam hk
  exact ⟨untruncated_krullDimension_allFields K n lam hk,
    IsNoetherianRing.of_finite (ElementaryParameterRing K n lam) _,
    fun P _ => untruncated_isCohenMacaulay_atPrime_allFields K n lam hk P⟩

/-- The two ordinary ring-theoretic classifications, over every field. -/
theorem untruncated_gorenstein_and_ci_cases (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (IsGorensteinRing (UntruncatedRing K n lam) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1) ∧
    (IsRegularSequencePresentation (untruncatedIdeal K n lam) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1) :=
  ⟨corollary_7_6_gorenstein_iff K n lam hk,
    corollary_7_6_completeIntersection_iff K n lam hk⟩

/-- The exact regularity value as the sharp support bound of the genuine
coordinate Koszul homology. -/
theorem untruncated_koszul_regularity_exact (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    let r : ℤ := (springerTopDegree lam : ℤ) +
      (n - lam.card : ℕ) * (lam.colLen 0 : ℤ)
    (∀ i a, r < a → Subsingleton (CoordinateKoszulHomology (untruncatedIdeal K n lam) i a)) ∧
      ∃ i, ¬ Subsingleton (CoordinateKoszulHomology (untruncatedIdeal K n lam) i r) := by
  exact (hasKoszulRegularity_iff_homology_support _ _).mp
    (corollary_7_5_regularity K n lam hk)

/-- The actual canonical module, with homogeneous generators described
by their degree shift on every homogeneous input. -/
theorem untruncated_canonical_intrinsic_degree_and_type (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    let d : ℤ := ((n - lam.card + 1).choose 2 : ℤ) -
      springerTopDegree (adjoinOnes lam (n - lam.card))
    let t := Nat.card (TauCeti.StandardYoungTableau (adjoinOnes lam (n - lam.card)))
    IsDualizingModule (UntruncatedRing K n lam) (UntruncatedRelativeDual K n lam) ∧
    (∃ v : Fin t → UntruncatedRelativeDual K n lam,
      (∀ i q (x : UntruncatedRing K n lam),
        x ∈ quotientIntegerPiece (untruncatedIdeal K n lam) q →
        v i x ∈ elementaryWeightedPiece K (n - lam.card)
          (q + d - elementaryCanonicalShift (n - lam.card))) ∧
      Submodule.span (UntruncatedRing K n lam) (Set.range v) = ⊤) ∧
    (∀ r (v : Fin r → UntruncatedRelativeDual K n lam),
      Submodule.span (UntruncatedRing K n lam) (Set.range v) = ⊤ → t ≤ r) := by
  dsimp only
  rw [Nat.card_eq_fintype_card]
  obtain ⟨hD, ⟨v, hv, hspan⟩, hmin⟩ := corollary_7_6_canonical_module K n lam hk
  refine ⟨hD, ⟨v, ?_, hspan⟩, hmin⟩
  intro i q x hx
  exact (mem_untruncatedRelativeDualGrading_iff K n lam hk _ (v i)).mp (hv i) q x hx

end HigherSpecht
