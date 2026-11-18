module
public import PaperVerification.PowerTheoremOneOne
public import PaperVerification.EulerParameters
public import PaperVerification.HypersurfaceTheoremSixThree
public import PaperVerification.CompleteIntersectionCodimensionFull

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module Representation
open scoped BigOperators Classical

namespace PalomarDeformed
open PaperVerification PaperVerification.PowerOperators
variable {K : Type*} [Field K] {n : ℕ}

/-- Hilbert series of the actual reversed quotient degree subspaces. -/
def tailHilbertSeries (c : Fin n → K) (lam : K) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d => (Module.finrank K (tailQuotientDegree c lam m d) : ℤ)

/-- Hilbert series of the actual original quotient degree subspaces. -/
def originalHilbertSeries (c : Fin n → K) (lam : K) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d => (Module.finrank K (originalTailQuotientDegree c lam m d) : ℤ)

/-- The finite q-integer 1+q+...+q^(j-1). -/
def qIntegerPolynomial (j : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range j, Polynomial.X ^ i

private theorem tailHilbertSeries_eq_source (c : Fin n → K) (lam : K) (m : ℕ) :
    tailHilbertSeries c lam m = GradedHilbert.series (tailQuotientGrading c lam m) := by
  ext d
  simp only [tailHilbertSeries, PowerSeries.coeff_mk, GradedHilbert.coeff_series]
  rw [tailQuotientGrading_piece c lam m d]

private theorem originalHilbertSeries_eq_source
    (c : Fin n → K) (lam : K) (m : ℕ)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0) :
    originalHilbertSeries c lam m =
      GradedHilbert.series (originalTailQuotientGrading c lam m h) := by
  ext d
  simp only [originalHilbertSeries, PowerSeries.coeff_mk, GradedHilbert.coeff_series]
  rw [originalTailQuotientGrading_piece c lam m h d]

/-- Every clause of the original weighted-tail theorem, transported only along
proved equality of the actual homogeneous-subspace Hilbert series. -/
theorem weighted_tail_theorem
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m) :
    (∃ B : Basis (ArtinIndex n m) K (MvPolynomial (Fin n) K ⧸ tailHit c lam m),
      ∀ a, B a = (tailHit c lam m).mkQ (monomial a.val 1)) ∧
    (tailHilbertSeries c lam m =
      ((∏ j ∈ Finset.Ico m (m+n), qIntegerPolynomial j : Polynomial ℤ) : PowerSeries ℤ)) ∧
    (∀ (G : Subgroup (Equiv.Perm (Fin n)))
      (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i),
      GradedRepresentationEquivalent (tailQuotientAction G c lam m hfix)
        (completeHomogeneousAction G m) (tailQuotientDegree c lam m)
        (ordinaryQuotientDegree (completeHomogeneousFamily K n m))) ∧
    (∀ a : K, (∀ i, c i = a) → ∀ G : Subgroup (Equiv.Perm (Fin n)),
      GradedRepresentationEquivalent
        (tailQuotientAction G (fun _ : Fin n => a) lam m (fun _ _ => rfl))
        (powerSumAction G m) (tailQuotientDegree (fun _ : Fin n => a) lam m)
        (ordinaryQuotientDegree (powerSumFamily K n m))) ∧
    (∀ hlow : ∀ i, ∀ a : ℕ, a < m → c i + lam * (a : K) ≠ 0,
      (∃ B : Basis (ArtinIndex n m) K
          (MvPolynomial (Fin n) K ⧸ originalTailHit c lam m),
        ∀ a, B a = (originalTailHit c lam m).mkQ (monomial a.val 1)) ∧
      (originalHilbertSeries c lam m =
        ((∏ j ∈ Finset.Ico m (m+n), qIntegerPolynomial j : Polynomial ℤ) : PowerSeries ℤ)) ∧
      (∀ (G : Subgroup (Equiv.Perm (Fin n)))
        (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i),
        GradedRepresentationEquivalent (originalTailQuotientAction G c lam m hfix)
          (completeHomogeneousAction G m) (originalTailQuotientDegree c lam m)
          (ordinaryQuotientDegree (completeHomogeneousFamily K n m))) ∧
      (∀ a : K, (∀ i, c i = a) → ∀ G : Subgroup (Equiv.Perm (Fin n)),
        GradedRepresentationEquivalent
          (originalTailQuotientAction G (fun _ : Fin n => a) lam m (fun _ _ => rfl))
          (powerSumAction G m) (originalTailQuotientDegree (fun _ : Fin n => a) lam m)
          (ordinaryQuotientDegree (powerSumFamily K n m)))) := by
  obtain ⟨hb, hh, hr, hp, ho⟩ := PaperVerification.PowerOperators.paper_theorem_2_2 c lam m hm hnr
  refine ⟨hb, ?_, hr, hp, ?_⟩
  · rw [tailHilbertSeries_eq_source]
    exact hh
  · intro hlow
    obtain ⟨hb, hh, hr, hp⟩ := ho hlow
    refine ⟨hb, ?_, hr, hp⟩
    rw [originalHilbertSeries_eq_source c lam m (coordinate_factor_ne_zero hnr hlow)]
    exact hh

end PalomarDeformed
