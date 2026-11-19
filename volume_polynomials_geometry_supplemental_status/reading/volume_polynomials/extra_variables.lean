module

public import VolumePolynomials.PolynomialCoordinates
public import VolumePolynomials.BodyOperations
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Adding point bodies and retaining all ordinary coefficients

Renaming a homogeneous polynomial into the first coordinates is a polynomial
map of coefficient spaces. Its preimage of the larger realization locus is
exactly the original locus. This transfers nonsemialgebraicity to every
larger number of bodies without assuming an image theorem.
-/

open MvPolynomial Set
open scoped BigOperators Pointwise

namespace VolumePolynomials

def extraVariables {m d : ℕ} (k : ℕ) (c : Coefficients m d) : Coefficients (m + k) d :=
  coefficientsOfPolynomial (MvPolynomial.rename (Fin.castAdd k) (coefficientPolynomial c))

theorem extraVariables_homogeneous {m d : ℕ} (k : ℕ) (c : Coefficients m d) :
    (MvPolynomial.rename (Fin.castAdd k) (coefficientPolynomial c)).IsHomogeneous d :=
  (coefficientPolynomial_homogeneous c).rename_isHomogeneous

theorem evaluate_extraVariables {m d : ℕ} (k : ℕ) (c : Coefficients m d)
    (t : Fin (m + k) → ℝ) :
    evaluate (extraVariables k c) t = evaluate c (fun i => t (Fin.castAdd k i)) := by
  first
  | rw [evaluate_eq_polynomial_eval, extraVariables,
      coefficientPolynomial_coefficientsOfPolynomial _ (extraVariables_homogeneous k c),
      MvPolynomial.eval_rename, ← evaluate_eq_polynomial_eval]
    rfl

def extraPointBodies {m d : ℕ} (k : ℕ) (K : Fin m → Body d) : Fin (m + k) → Body d :=
  Fin.addCases K (fun _ => 0)

theorem weightedSum_extraPointBodies {m d : ℕ} (k : ℕ) (K : Fin m → Body d)
    (t : Fin (m + k) → ℝ) :
    weightedSum (extraPointBodies k K) t = weightedSum K (fun i => t (Fin.castAdd k i)) := by
  first
  | have hzero (r : ℝ) : r • (0 : Body d) = 0 := by
      apply ConvexBody.ext
      change r • ({0} : Set (Space d)) = {0}
      simp
    simp only [weightedSum, Fin.sum_univ_add, extraPointBodies,
      Fin.addCases_left, Fin.addCases_right, hzero, Finset.sum_const_zero, add_zero]

theorem weightedSum_zero_extraWeights {m k d : ℕ} (K : Fin (m + k) → Body d)
    (t : Fin m → ℝ) :
    weightedSum K (Fin.addCases t (fun _ : Fin k => 0)) =
      weightedSum (fun i => K (Fin.castAdd k i)) t := by
  first
  | simp only [weightedSum, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      body_zero_smul, Finset.sum_const_zero, add_zero]

theorem Realizes.extraPointBodies {m d : ℕ} {K : Fin m → Body d} {c : Coefficients m d}
    (h : Realizes K c) (k : ℕ) : Realizes (extraPointBodies k K) (extraVariables k c) := by
  first
  | intro t ht
    rw [evaluate_extraVariables, volumeFunction, weightedSum_extraPointBodies]
    exact h (fun i => t (Fin.castAdd k i)) (fun i => ht _)

theorem Realizes.discard_extra {m k d : ℕ} {K : Fin (m + k) → Body d}
    {c : Coefficients m d} (h : Realizes K (extraVariables k c)) :
    Realizes (fun i => K (Fin.castAdd k i)) c := by
  first
  | intro t ht
    have ht' : ∀ i, (0 : ℝ) ≤ Fin.addCases t (fun _ : Fin k => (0 : ℝ)) i := by
      first
      | intro i
        refine Fin.addCases ?_ ?_ i
        · intro j
          simpa only [Fin.addCases_left] using ht j
        · intro j
          simp only [Fin.addCases_right, le_refl]
    have he := h (Fin.addCases t (fun _ : Fin k => 0)) ht'
    simpa only [evaluate_extraVariables, Fin.addCases_left, volumeFunction,
      weightedSum_zero_extraWeights] using he

theorem extraVariables_mem_iff {m k d : ℕ} (c : Coefficients m d) :
    extraVariables k c ∈ VolumeLocus (m + k) d ↔ c ∈ VolumeLocus m d := by
  first
  | constructor
    · rintro ⟨K, hK⟩
      exact ⟨_, hK.discard_extra⟩
    · rintro ⟨K, hK⟩
      exact ⟨_, hK.extraPointBodies k⟩

def extraVariableCoordinate {m d : ℕ} (k : ℕ) (β : MultiIndex (m + k) d) :
    MvPolynomial (MultiIndex m d) ℝ :=
  ∑ α : MultiIndex m d,
    if Finsupp.mapDomain (Fin.castAdd k) (exponent α) = exponent β then X α else 0

theorem extraVariableCoordinate_eval {m d : ℕ} (k : ℕ) (c : Coefficients m d)
    (β : MultiIndex (m + k) d) :
    MvPolynomial.eval c (extraVariableCoordinate k β) = extraVariables k c β := by
  first
  | classical
    simp only [extraVariableCoordinate, MvPolynomial.eval_sum, eval_X, map_zero,
      extraVariables, coefficientsOfPolynomial, coefficientPolynomial, map_sum,
      MvPolynomial.coeff_sum, rename_monomial, coeff_monomial]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs <;> simp

theorem not_semialgebraic_extraVariables {m k d : ℕ}
    (h : ¬ TauCeti.IsSemialgebraic (VolumeLocus m d)) :
    ¬ TauCeti.IsSemialgebraic (VolumeLocus (m + k) d) := by
  first
  | intro hlarge
    apply h
    have hs := hlarge.preimage_eval (extraVariableCoordinate (m := m) (d := d) k)
    have heq : (fun c β => MvPolynomial.eval c (extraVariableCoordinate k β)) ⁻¹'
        VolumeLocus (m + k) d = VolumeLocus m d := by
      first
      | ext c
        simpa only [Set.mem_preimage, funext (extraVariableCoordinate_eval k c)] using
          extraVariables_mem_iff (k := k) c
    rwa [heq] at hs

theorem not_semialgebraic_volumeLocus_of_three {n d : ℕ} (hn : 3 ≤ n)
    (h3 : ¬ TauCeti.IsSemialgebraic (VolumeLocus 3 d)) :
    ¬ TauCeti.IsSemialgebraic (VolumeLocus n d) := by
  first
  | have heq : 3 + (n - 3) = n := by omega
    rw [← heq]
    exact not_semialgebraic_extraVariables (k := n - 3) h3

end VolumePolynomials
