module

public import sunlet.class_dimension
public import sunlet.height_obstructions
public import Mathlib.Tactic.Push

/-! Opposite signs eliminate both actual height kernels for a good class order. -/

@[expose] public section
noncomputable section

namespace Sunlet.OrbitHeight.InverseStablePartition

variable {G C : Type*} [AddCommGroup G] [Fintype G] [Fintype C] [LinearOrder C]
  (P : InverseStablePartition G C)

/-- Evaluation at a nonzero coordinate of one height vector is injective on
the entire height space. This proves the needed one-dimensional consequence
without assuming a choice of a generator. -/
theorem height_eq_zero_of_coordinate_zero {x y : C → ℚ}
    (hx : x ∈ P.heightSpace) (hy : y ∈ P.heightSpace) (i : C)
    (hxi : x i ≠ 0) (hyi : y i = 0) : y = 0 := by
  funext j
  by_contra hyj
  have hyj' : y j ≠ 0 := by simpa using hyj
  let t : ℚ := (-x i - x j) / y j
  have hz : x + t • y ∈ P.heightSpace := P.heightSpace.add_mem hx (P.heightSpace.smul_mem t hy)
  have hzi : (x + t • y) i = x i := by simp [hyi]
  have hzj : (x + t • y) j = -x i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, t]
    field_simp [hyj']
    ring
  rcases P.one_sign hz with hp | hn
  · have hi := hp i
    have hj := hp j
    rw [hzi] at hi
    rw [hzj] at hj
    exact hxi (by linarith)
  · have hi := hn i
    have hj := hn j
    rw [hzi] at hi
    rw [hzj] at hj
    exact hxi (by linarith)

/-- The paper calls an order good after the nonzero height vector has been
rescaled to be nonnegative. That sign convention is explicit here. -/
def GoodHeightOrder : Prop :=
  ∀ x ∈ P.heightSpace, (∀ i, 0 ≤ x i) → x ≠ 0 → ¬ P.BadHeight x

/-- A good order supplies actual choices of the same-class monomials, and
those choices kill both residual kernels. -/
theorem exists_signs_killing_heights (hgood : P.GoodHeightOrder) :
    ∃ σ : Set C, P.zeroClass ∉ σ ∧ ClassKernel.KillsHeights P σ := by
  classical
  by_cases hz : ∀ x ∈ P.heightSpace, x = 0
  · exact ⟨∅, Set.notMem_empty _, ⟨fun x hx _ => hz x hx, fun x hx _ => hz x hx⟩⟩
  push_neg at hz
  obtain ⟨x, hx, hx0⟩ := hz
  obtain ⟨r, hr, hy, _, hvalues, _, _⟩ := P.normalized_height hx hx0
  let y : C → ℚ := r • x
  have hy0 : y ≠ 0 := smul_ne_zero hr hx0
  have hyn : ∀ i, 0 ≤ y i := by
    intro i
    rcases hvalues i with h | h | h <;> change 0 ≤ (r • x) i <;> rw [h] <;> norm_num
  have hnot := hgood y hy hyn hy0
  unfold BadHeight at hnot
  push_neg at hnot
  obtain ⟨i, j, hRi, hRj, hi, hj, hij⟩ := hnot
  refine ⟨{i}, ?_, ?_, ?_⟩
  · simpa only [Set.mem_singleton_iff] using Ne.symm hRi.1
  · intro z hz hzi
    exact P.height_eq_zero_of_coordinate_zero hy hz i (ne_of_gt hi)
      (hzi i hRi (Set.mem_singleton i))
  · intro z hz hzj
    exact P.height_eq_zero_of_coordinate_zero hy hz j (ne_of_gt hj)
      (hzj j hRj (by simpa only [Set.mem_singleton_iff] using Ne.symm hij))

/-- The entire dimension calculation now follows from the combinatorial
good-order conclusion; no rank, Jacobian, or dimension assumption is hidden
in the definition of the identified model. -/
theorem imageClosure_dimension_of_good_order {K : Type*} [Field K] [Infinite K]
    (hmin : ∀ i, P.zeroClass ≤ i) (hgood : P.GoodHeightOrder) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Sunlet.Identified.coordinatePolynomial (K := K) P.classOf))) =
        (5 * Fintype.card C - 4 : ℕ) := by
  classical
  obtain ⟨σ, hσ0, hkill⟩ := P.exists_signs_killing_heights hgood
  exact ClassKernel.imageClosure_dimension_eq P σ hmin hσ0 hkill

end Sunlet.OrbitHeight.InverseStablePartition
