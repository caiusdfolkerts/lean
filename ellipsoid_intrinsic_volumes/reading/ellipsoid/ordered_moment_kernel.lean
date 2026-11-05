module

public import Ellipsoid.TailMoments
public import Mathlib.Data.Finset.Sort

@[expose] public section

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators

namespace EllipsoidVerification

theorem orderedMomentKernel_gram_identity
    {μ : Measure PositiveLine} (hμ : μ ≠ 0) {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hp0 : ∀ i, 0 < p i)
    (h3 : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (3 * p i)) μ) :
    orderedMomentKernel μ p =
      Matrix.diagonal (fun i => p i * positiveMoment μ (3 * p i)) *
        (orderedMomentGram μ p + orderedMomentGram μ p ⊙ minRatioKernel p) *
      Matrix.diagonal (fun i => p i * positiveMoment μ (3 * p i)) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.hadamard_apply, orderedMomentKernel, orderedMomentGram, minRatioKernel]
  have hi := positiveMoment_pos hμ (h3 i)
  have hj := positiveMoment_pos hμ (h3 j)
  have hsum := add_pos (hp0 i) (hp0 j)
  rcases le_total i j with hij | hji
  · rw [min_eq_left (hp.monotone hij), max_eq_right (hp.monotone hij)]
    field_simp [(hp0 j).ne', hj.ne', hsum.ne'] <;> ring
  · rw [min_eq_right (hp.monotone hji), max_eq_left (hp.monotone hji)]
    field_simp [(hp0 i).ne', hi.ne', hsum.ne'] <;> ring

/-- Lemma 3.1 in its full measure-theoretic generality. The measure need not
have finite mass; the assumed moments are precisely those in the paper.
The subtype is the positive real half-line with its inherited Borel space. -/
theorem orderedMomentKernel_posDef
    {μ : Measure PositiveLine} [SigmaFinite μ] (hμ : μ ≠ 0)
    {m : ℕ} {p : Fin m → ℝ} (hp : StrictMono p) (hp0 : ∀ i, 0 < p i)
    (h3 : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (3 * p i)) μ)
    (hm : ∀ i j, i ≤ j → Integrable
      (fun t : PositiveLine => (t.val : ℝ) ^ (2 * p j - p i)) μ) :
    (orderedMomentKernel μ p).PosDef := by
  have hG := orderedMomentGram_posSemidef hμ hp hp0 h3 hm
  have hdiag : ∀ i, 0 < orderedMomentGram μ p i i :=
    orderedMomentGram_diagonal_pos hμ hp0 h3 (fun i => by
      simpa only [show 2 * p i - p i = p i by ring] using hm i i le_rfl)
  have hR := minRatioKernel_posDef hp hp0
  have hstrict := posDef_hadamard_of_posSemidef_positive_diagonal hG hdiag hR
  have hsum : (orderedMomentGram μ p + orderedMomentGram μ p ⊙ minRatioKernel p).PosDef :=
    Matrix.PosDef.posSemidef_add hG hstrict
  let D : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.diagonal (fun i => p i * positiveMoment μ (3 * p i))
  have hD : D.PosDef := Matrix.PosDef.diagonal
    (fun i => mul_pos (hp0 i) (positiveMoment_pos hμ (h3 i)))
  have hconj := hsum.mul_mul_conjTranspose_same (B := D)
    (Matrix.vecMul_injective_iff_isUnit.mpr hD.isUnit)
  rw [orderedMomentKernel_gram_identity hμ hp hp0 h3]
  simpa only [D, Matrix.diagonal_conjTranspose, star_trivial] using hconj

theorem orderedMomentKernel_posDef_of_injective
    {μ : Measure PositiveLine} [SigmaFinite μ] (hμ : μ ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (hp : Function.Injective p) (hp0 : ∀ i, 0 < p i)
    (h3 : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (3 * p i)) μ)
    (hm : ∀ i j, p i ≤ p j → Integrable
      (fun t : PositiveLine => (t.val : ℝ) ^ (2 * p j - p i)) μ) :
    (orderedMomentKernel μ p).PosDef := by
  letI : LinearOrder ι := LinearOrder.lift' p hp
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  have hmono : StrictMono (fun i => p (e i)) := by
    intro i j hij
    exact e.strictMono hij
  have h := orderedMomentKernel_posDef hμ hmono (fun i => hp0 (e i))
    (fun i => h3 (e i)) (fun i j hij => hm (e i) (e j) (hmono.monotone hij))
  have hsub := h.submatrix e.symm.injective
  have hmat : (orderedMomentKernel μ (fun i => p (e i))).submatrix e.symm e.symm =
      orderedMomentKernel μ p := by
    ext i j
    simp only [Matrix.submatrix_apply, orderedMomentKernel, OrderIso.apply_symm_apply]
  rw [hmat] at hsub
  exact hsub

end EllipsoidVerification
