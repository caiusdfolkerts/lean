module
public import PaperVerification.ToricBasisCovering
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Abel
@[expose] public section
/-!
# Matched box averages and lattice decompositions

This is equation (7) of the toric manuscript, with the centered zonotope and
all convex-combination hypotheses made explicit. Different boxes may use
unrelated bases of the common ambient real vector space.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators

variable {J ι E : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The centered unit box in a selected subset of the vector configuration. -/
def SubsetBox (v : ι → E) (s : Finset ι) : Set E :=
  CenteredZonotope v (fun j => if j ∈ s then 1 else 0)

/-- Total occurrence weight of each vector in a family of selected subsets. -/
def averagedWidths (s : J → Finset ι) (p : J → ℝ) (j : ι) : ℝ :=
  ∑ B, if j ∈ s B then p B else 0

lemma averagedWidths_nonneg (s : J → Finset ι) (p : J → ℝ) (hp : ∀ B, 0 ≤ p B)
    (j : ι) : 0 ≤ averagedWidths s p j := by
  apply Finset.sum_nonneg
  intro B _
  split_ifs <;> simp [hp B]

lemma neg_mem_centeredZonotope (v : ι → E) (c : ι → ℝ) {z : E}
    (hz : z ∈ CenteredZonotope v c) : -z ∈ CenteredZonotope v c := by
  obtain ⟨t, ht, hsum⟩ := hz
  refine ⟨fun j => -t j, ?_, ?_⟩
  · intro j
    simpa using ht j
  · simpa only [neg_smul, Finset.sum_neg_distrib, hsum]

/-- A point of the averaged-width zonotope is an actual convex Minkowski
average of points of the individual unit boxes. Zero width coordinates and
zero probability weights are included. -/
theorem zonotope_exists_box_average (v : ι → E) (s : J → Finset ι)
    (p : J → ℝ) (hp : ∀ B, 0 ≤ p B) {z : E}
    (hz : z ∈ CenteredZonotope v (averagedWidths s p)) :
    ∃ q : J → E, (∀ B, q B ∈ SubsetBox v (s B)) ∧ ∑ B, p B • q B = z := by
  classical
  obtain ⟨t, ht, hsum⟩ := hz
  let c : ι → ℝ := averagedWidths s p
  let u : J → ι → ℝ := fun B j => if j ∈ s B then t j / c j else 0
  have hc (j : ι) : 0 ≤ c j := averagedWidths_nonneg s p hp j
  have htzero (j : ι) (hj : c j = 0) : t j = 0 := by
    have h := ht j
    change |t j| ≤ c j / 2 at h
    rw [hj, zero_div] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hu (B : J) (j : ι) : |u B j| ≤ (if j ∈ s B then 1 else 0) / 2 := by
    by_cases hmem : j ∈ s B
    · simp only [u, hmem, if_true]
      by_cases hj : c j = 0
      · simp [hj]
      · have hcpos : 0 < c j := lt_of_le_of_ne (hc j) (Ne.symm hj)
        rw [abs_div, abs_of_pos hcpos]
        apply (div_le_iff₀ hcpos).mpr
        have h := ht j
        change |t j| ≤ c j / 2 at h
        linarith
    · simp [u, hmem]
  have hcoeff (j : ι) : ∑ B, p B * u B j = t j := by
    calc
      (∑ B, p B * u B j) =
          (∑ B, if j ∈ s B then p B else 0) * (t j / c j) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro B _
        by_cases hj : j ∈ s B <;> simp [u, hj]
      _ = t j := by
        change c j * (t j / c j) = t j
        by_cases hj : c j = 0
        · simp [hj, htzero j hj]
        · field_simp [hj]
  refine ⟨fun B => ∑ j, u B j • v j, ?_, ?_⟩
  · intro B
    exact ⟨u B, hu B, rfl⟩
  · calc
      (∑ B, p B • ∑ j, u B j • v j) = ∑ j, ∑ B, (p B * u B j) • v j := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
      _ = ∑ j, t j • v j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_smul, hcoeff]
      _ = z := hsum

/-- Equation (7): matched box centers and the common average zonotope give
points simultaneously in the first polytope and in the reflected second one. -/
theorem matched_boxes_average (A B : Set E) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (v : ι → E) (s : J → Finset ι) (p : J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (a b : J → E)
    (hboxA : ∀ i z, z ∈ SubsetBox v (s i) → a i + z ∈ A)
    (hboxB : ∀ i z, z ∈ SubsetBox v (s i) → b i + z ∈ B)
    (m : E) (hm : m = ∑ i, p i • (a i + b i))
    {z : E} (hz : z ∈ CenteredZonotope v (averagedWidths s p)) :
    (∑ i, p i • a i) + z ∈ A ∧ m - ((∑ i, p i • a i) + z) ∈ B := by
  obtain ⟨q, hq, hqsum⟩ := zonotope_exists_box_average v s p hp hz
  have hfirst := hA.sum_mem (t := Finset.univ) (fun i _ => hp i) hpsum
    (fun i _ => hboxA i (q i) (hq i))
  have hsecond := hB.sum_mem (t := Finset.univ) (fun i _ => hp i) hpsum
    (fun i _ => hboxB i (-q i) (neg_mem_centeredZonotope v _ (hq i)))
  constructor
  · simpa only [smul_add, Finset.sum_add_distrib, hqsum] using hfirst
  · have hsum : (∑ i, p i • (b i + -q i)) =
        m - ((∑ i, p i • a i) + z) := by
      rw [hm]
      simp only [smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, hqsum]
      abel
    rw [← hsum]
    exact hsecond

/-- Lattice decomposition supplied by matched integral basis boxes. This is
the common geometric consequence of Lemma 4.1 and equation (7). -/
theorem matched_boxes_lattice_decomposition {d n : ℕ}
    (V : Matrix (Fin d) (Fin n) ℝ)
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hv : ∀ j, matrixColumn V j ∈ Γ)
    (A B : Set (EuclideanSpace ℝ (Fin d))) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (s : J → Finset (Fin n)) (hs : ∀ i, 0 < squaredMinor V (s i))
    (p : J → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (a b : J → EuclideanSpace ℝ (Fin d))
    (hboxA : ∀ i z, z ∈ SubsetBox (matrixColumn V) (s i) → a i + z ∈ A)
    (hboxB : ∀ i z, z ∈ SubsetBox (matrixColumn V) (s i) → b i + z ∈ B)
    (m : EuclideanSpace ℝ (Fin d)) (hmΓ : m ∈ Γ)
    (hm : m = ∑ i, p i • (a i + b i)) :
    ∃ x ∈ A, ∃ y ∈ B, x ∈ Γ ∧ y ∈ Γ ∧ x + y = m := by
  let C : EuclideanSpace ℝ (Fin n) :=
    ∑ i, p i • basisIncidence V ⟨s i, hs i⟩
  have hC : C ∈ convexHull ℝ (Set.range (basisIncidence V)) :=
    mem_convexHull_of_exists_fintype p (fun i => basisIncidence V ⟨s i, hs i⟩)
      hp hpsum (fun i => Set.mem_range_self _) rfl
  have hwidth : (C : Fin n → ℝ) = averagedWidths s p := by
    funext j
    dsimp only [C]
    rw [euclidean_sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp [basisIncidence]
  let ac : EuclideanSpace ℝ (Fin d) := ∑ i, p i • a i
  obtain ⟨x, hxΓ, hxerror⟩ := matroid_basis_polytope_covering V Γ hclosed hv C hC ac
  have hxbox : x - ac ∈ CenteredZonotope (matrixColumn V) (averagedWidths s p) := by
    have hn := neg_mem_centeredZonotope (matrixColumn V) C hxerror
    simpa only [neg_sub, hwidth] using hn
  have hboth := matched_boxes_average A B hA hB (matrixColumn V) s p hp hpsum
    a b hboxA hboxB m hm hxbox
  have hAx : x ∈ A := by
    simpa [ac, add_sub_cancel_left] using hboth.1
  have hBy : m - x ∈ B := by
    simpa [ac, add_sub_cancel_left] using hboth.2
  exact ⟨x, hAx, m - x, hBy, hxΓ, Γ.sub_mem hmΓ hxΓ, by abel⟩

end PaperVerification.Toric
