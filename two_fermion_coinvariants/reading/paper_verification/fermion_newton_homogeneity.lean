module

public import PaperVerification.FermionNewtonMembership
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Homogeneity of the common-numerator Newton columns

Clearing a homogeneous denominator is handled inside the polynomial ring:
the defining multiplication relation shows that the polynomial quotient is
homogeneous of the difference of the actual degrees. This includes zero
numerators and every allowed signed height.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators Matrix

variable {F : Type*} [Field F] {n : ℕ}

def signedEdges (σ : Fin n → ℤ) (a : ℤ) : Finset (Edge n) :=
  Finset.univ.filter (fun e ↦ σ e.1.1 = a)

def negativeEdgeCount (σ : Fin n → ℤ) : ℕ := (signedEdges σ (-1)).card

def positiveEdgeCount (σ : Fin n → ℤ) : ℕ := (signedEdges σ 1).card

def columnNumeratorDegree (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i : Fin n) : ℕ :=
  negativeEdgeCount σ + δ i + (earlierPositive σ i).card - (earlierNegative σ i).card

theorem starDenominator_homogeneous (k : Fin n) (T : Finset (Fin n)) :
    (starDenominator (F := F) k T).IsHomogeneous T.card := by
  have h := IsHomogeneous.prod T (fun j ↦ (X k - X j : P (F := F) (n := n))) (fun _ ↦ 1)
    (fun j hj ↦ (isHomogeneous_X F k).sub (isHomogeneous_X F j))
  simpa only [starDenominator, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id] using h

theorem negativeDenominator_homogeneous (σ : Fin n → ℤ) :
    (negativeDenominator (F := F) σ).IsHomogeneous (negativeEdgeCount σ) := by
  have h := IsHomogeneous.prod (signedEdges σ (-1)) (edgeLinear (F := F)) (fun _ ↦ 1)
    (fun e he ↦ (isHomogeneous_X F e.1.1).sub (isHomogeneous_X F e.1.2))
  simpa only [negativeDenominator, negativeEdgeCount, signedEdges,
    Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id] using h

theorem evaluated_columnNumerator_homogeneous
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i k : Fin n) :
    ((columnNumerator (F := F) δ σ i).eval (X k)).IsHomogeneous
      (δ i + (earlierPositive σ i).card) := by
  rw [columnNumerator, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact (isHomogeneous_X_pow k (δ i)).mul (starDenominator_homogeneous k _)

theorem clearedFractionNumerator_homogeneous
    (Q N D : P (F := F) (n := n)) (q r d : ℕ) (hdiv : D ∣ Q)
    (hQ : Q.IsHomogeneous q) (hN : N.IsHomogeneous r) (hD : D.IsHomogeneous d)
    (hQ0 : Q ≠ 0) :
    (clearedFractionNumerator Q N D hdiv).IsHomogeneous (q + r - d) := by
  let A := clearedFractionNumerator Q N D hdiv
  have he : D * A = Q * N := clearedFractionNumerator_relation Q N D hdiv
  have hD0 : D ≠ 0 := fun hz ↦ hQ0 (by obtain ⟨a,ha⟩ := hdiv; simpa only [hz, zero_mul] using ha)
  by_cases hN0 : N = 0
  · have hA0 : A = 0 := by
      rw [hN0, mul_zero] at he
      exact (mul_eq_zero.mp he).resolve_left hD0
    rw [show clearedFractionNumerator Q N D hdiv = 0 from hA0]
    exact isHomogeneous_zero (Fin n) F _
  · have hprod : (D * A).IsHomogeneous (q + r) := he.symm ▸ hQ.mul hN
    have hprod0 : D * A ≠ 0 := he.symm ▸ mul_ne_zero hQ0 hN0
    have hA := hprod.of_mul_right hprod0
    have hA0 : A ≠ 0 := right_ne_zero_of_mul hprod0
    have hdeg := hprod.totalDegree hprod0
    rw [totalDegree_mul_of_isDomain hD0 hA0, hD.totalDegree hD0] at hdeg
    have hdegree : A.totalDegree = q + r - d := by omega
    simpa only [A, hdegree] using hA

theorem activeNumerator_homogeneous
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i k : Fin n)
    (hk : k ∈ activeInterval δ i) :
    (activeNumerator (F := F) δ σ i k hk).IsHomogeneous (columnNumeratorDegree δ σ i) := by
  have h := clearedFractionNumerator_homogeneous (negativeDenominator (F := F) σ)
    ((columnNumerator δ σ i).eval (X k)) (starDenominator k (earlierNegative σ i))
    (negativeEdgeCount σ) (δ i + (earlierPositive σ i).card) (earlierNegative σ i).card
    (active_denominator_dvd δ σ i k hk) (negativeDenominator_homogeneous σ)
    (evaluated_columnNumerator_homogeneous δ σ i k) (starDenominator_homogeneous k _)
    (negativeDenominator_ne_zero σ)
  simpa only [activeNumerator, columnNumeratorDegree, Nat.add_assoc] using h

theorem residueNumerator_homogeneous
    (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i k l : Fin n)
    (hk : k ∈ earlierNegative σ i) (hl : l ∈ activeInterval δ i) :
    (residueNumerator (F := F) δ σ i k l hk hl).IsHomogeneous
      (columnNumeratorDegree δ σ i) := by
  have hD : (starDenominator (F := F) k ((earlierNegative σ i).erase k) *
      (X k - X l)).IsHomogeneous (earlierNegative σ i).card := by
    have h := (starDenominator_homogeneous (F := F) k ((earlierNegative σ i).erase k)).mul
      ((isHomogeneous_X F k).sub (isHomogeneous_X F l))
    have he : ((earlierNegative σ i).erase k).card + 1 = (earlierNegative σ i).card := by
      rw [Finset.card_erase_of_mem hk]
      have hc := Finset.card_pos.mpr ⟨k,hk⟩
      omega
    simpa only [he] using h
  have h := clearedFractionNumerator_homogeneous (negativeDenominator (F := F) σ)
    ((columnNumerator δ σ i).eval (X k))
    (starDenominator k ((earlierNegative σ i).erase k) * (X k - X l))
    (negativeEdgeCount σ) (δ i + (earlierPositive σ i).card) (earlierNegative σ i).card
    (residue_denominator_dvd δ σ i k l hk hl) (negativeDenominator_homogeneous σ)
    (evaluated_columnNumerator_homogeneous δ σ i k) hD (negativeDenominator_ne_zero σ)
  simpa only [residueNumerator, columnNumeratorDegree, Nat.add_assoc] using h

theorem columnCommonNumerator_homogeneous
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i k : Fin n) :
    (columnCommonNumerator β δ σ hc i k).IsHomogeneous (columnNumeratorDegree δ σ i) := by
  by_cases ha : k ∈ activeInterval δ i
  · rw [columnCommonNumerator_eq_active β δ σ hc i k ha]
    exact activeNumerator_homogeneous δ σ i k ha
  · by_cases hn : k ∈ earlierNegative σ i
    · rw [columnCommonNumerator_eq_residue_sum β δ σ hc i k hn]
      apply IsHomogeneous.sum
      intro l hl
      exact (residueNumerator_homogeneous δ σ i k l.val hn l.property).C_mul _
    · rw [columnCommonNumerator_eq_zero_of_outside β δ σ hc i k ha hn]
      exact isHomogeneous_zero (Fin n) F _

theorem commonNumeratorMatrix_det_homogeneous
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ) :
    (commonNumeratorMatrix β δ σ hc).det.IsHomogeneous (∑ i, columnNumeratorDegree δ σ i) := by
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro π hπ
  have h := IsHomogeneous.prod Finset.univ _ (columnNumeratorDegree δ σ)
    (fun i hi ↦ columnCommonNumerator_homogeneous β δ σ hc i (π i))
  simpa only [map_intCast, commonNumeratorMatrix] using h.C_mul (((Equiv.Perm.sign π : ℤ) : F))

end PaperVerification.Fermion.Newton
