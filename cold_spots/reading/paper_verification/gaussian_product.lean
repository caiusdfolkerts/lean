module
public import PaperVerification.Gaussian
public import PaperVerification.LatticeDefs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

/-- Absolute convergence justifies products of finitely many one-dimensional sums. -/
theorem hasSum_fin_product (n : ℕ) {κ : Type*} (f : Fin n → κ → ℝ)
    (hf : ∀ i, Summable (f i)) :
    HasSum (fun z : Fin n → κ ↦ ∏ i, f i (z i)) (∏ i, ∑' k, f i k) := by
  induction n with
  | zero =>
      simpa using hasSum_fintype (fun z : Fin 0 → κ ↦ ∏ i, f i (z i))
  | succ n ih =>
      let g : (Fin n → κ) → ℝ := fun z ↦ ∏ i : Fin n, f i.succ (z i)
      have htail : HasSum g
          (∏ i : Fin n, ∑' k, f i.succ k) :=
        ih (fun i ↦ f i.succ) (fun i ↦ hf i.succ)
      have hfabs : Summable (fun k : κ ↦ |f 0 k|) := (hf 0).abs
      have hgabs : Summable (fun z : Fin n → κ ↦ |g z|) :=
        htail.summable.abs
      have habsprod : Summable (fun p : κ × (Fin n → κ) ↦
          |f 0 p.1| * |g p.2|) :=
        Summable.mul_of_nonneg (f := fun k : κ ↦ |f 0 k|)
          (g := fun z : Fin n → κ ↦ |g z|)
          hfabs hgabs (fun _ ↦ abs_nonneg _) (fun _ ↦ abs_nonneg _)
      have habs : Summable (fun p : κ × (Fin n → κ) ↦
          f 0 p.1 * g p.2) := by
        apply Summable.of_abs
        simpa only [abs_mul] using habsprod
      have hprod : HasSum (fun p : κ × (Fin n → κ) ↦
          f 0 p.1 * g p.2)
          ((∑' k, f 0 k) * ∏ i : Fin n, ∑' k, f i.succ k) :=
        (hf 0).hasSum.mul htail habs
      apply ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ κ)).hasSum_iff
        (f := fun z : Fin (n + 1) → κ ↦ ∏ i, f i (z i))).mp
      simpa [g, Function.comp_def, Fin.consEquiv, Fin.prod_univ_succ] using hprod

theorem summable_fin_product (n : ℕ) {κ : Type*} (f : Fin n → κ → ℝ)
    (hf : ∀ i, Summable (f i)) :
    Summable (fun z : Fin n → κ ↦ ∏ i, f i (z i)) :=
  (hasSum_fin_product n f hf).summable

theorem tsum_fin_product (n : ℕ) {κ : Type*} (f : Fin n → κ → ℝ)
    (hf : ∀ i, Summable (f i)) :
    (∑' z : Fin n → κ, ∏ i, f i (z i)) = ∏ i, ∑' k, f i k :=
  (hasSum_fin_product n f hf).tsum_eq

/-- The Gaussian lattice sum on the ordinary integer lattice in dimension `n`. -/
def integerGaussian {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑' z : Fin n → ℤ, Real.exp (-α * sqDist (intVec z) x)

lemma exp_neg_sqDist {n : ℕ} (α : ℝ) (z : Fin n → ℤ) (x : Fin n → ℝ) :
    Real.exp (-α * sqDist (intVec z) x) =
      ∏ i, Real.exp (-α * ((z i : ℝ) - x i) ^ 2) := by
  change Real.exp (-α * ∑ i : Fin n, ((z i : ℝ) - x i) ^ 2) = _
  rw [Finset.mul_sum, Real.exp_sum]

lemma summable_integerGaussian {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    Summable (fun z : Fin n → ℤ ↦ Real.exp (-α * sqDist (intVec z) x)) := by
  simp only [exp_neg_sqDist]
  exact summable_fin_product n (fun i (z : ℤ) ↦ Real.exp (-α * ((z : ℝ) - x i) ^ 2))
    (fun i ↦ summable_gaussian hα (x i))

theorem integerGaussian_eq_product {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    integerGaussian α x = ∏ i, gaussian α (x i) := by
  unfold integerGaussian gaussian
  simp only [exp_neg_sqDist]
  exact tsum_fin_product n (fun i (z : ℤ) ↦ Real.exp (-α * ((z : ℝ) - x i) ^ 2))
    (fun i ↦ summable_gaussian hα (x i))

end PaperVerification.ColdSpots
