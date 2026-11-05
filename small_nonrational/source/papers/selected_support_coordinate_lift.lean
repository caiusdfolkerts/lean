module
public import Papers.PrescribedSupportCoordinateLift

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- The chosen normal basis is internal: any independent family of actual
supporting normals can be retained while lifting a reduced relation matrix.
Only the outside-column rank for each selected facet is assumed in the
matrix density input. -/
theorem rational_selected_support_coordinate_lift {c n r k : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (p : Matrix (Fin n) (Fin r) ℝ)
    (hCp : C * p = 0) (H : Fin k → Finset (Fin n))
    (a : Fin k → Fin r → ℝ) (ha : LinearIndependent ℝ a)
    (hH : ∀ b i, i ∈ H b → a b ⬝ᵥ p i = 0)
    (hC : C ∈ closure {D : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      ∀ b, subsetRank C.col (H b)ᶜ = subsetRank D.col (H b)ᶜ}) :
    (C, p) ∈ closure {z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin n) (Fin r) ℝ |
      RationalCoordinates z.1 ∧ RationalCoordinates z.2 ∧
      z.1.rank = C.rank ∧ PreservesZeroEntries C z.1 ∧ z.1 * z.2 = 0 ∧
      ∀ b, ∃ v : Fin r → ℝ, v ≠ 0 ∧ (∀ i, RatScalar (v i)) ∧
        ∀ i ∈ H b, v ⬝ᵥ z.2 i = 0} := by
  classical
  obtain ⟨B, hB, e, he, hBe⟩ := exists_invertible_matrix_containing_normals a ha
  let Z : Fin r → Finset (Fin n) := fun j =>
    if h : ∃ b, e b = j then H (Classical.choose h) else ∅
  have hZe (b : Fin k) : Z (e b) = H b := by
    have h : ∃ b', e b' = e b := ⟨b, rfl⟩
    have hb : Classical.choose h = b := he (Classical.choose_spec h)
    simp only [Z, dif_pos h, hb]
  have hZ : ∀ j i, i ∈ Z j → (p * B) i j = 0 := by
    intro j i hi
    by_cases h : ∃ b, e b = j
    · let b := Classical.choose h
      have hb : e b = j := Classical.choose_spec h
      have hiH : i ∈ H b := by simpa only [Z, dif_pos h] using hi
      have hcol : B.col j = a b := by rw [← hb]; exact hBe b
      have hz := hH b i hiH
      change p i ⬝ᵥ B.col j = 0
      rw [hcol, dotProduct_comm]
      exact hz
    · simp only [Z, dif_neg h, Finset.notMem_empty] at hi
  have hCZ : C ∈ closure {D : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      ∀ j, subsetRank C.col (Z j)ᶜ = subsetRank D.col (Z j)ᶜ} := by
    apply closure_mono ?_ hC
    intro D hD
    refine ⟨hD.1, hD.2.1, hD.2.2.1, ?_⟩
    intro j
    by_cases h : ∃ b, e b = j
    · simpa only [Z, dif_pos h] using hD.2.2.2 (Classical.choose h)
    · simp only [Z, dif_neg h, Finset.compl_empty, subsetRank_col_univ]
      exact hD.2.1.symm
  have hcl := rational_prescribed_support_coordinate_lift C p hCp B hB Z hZ hCZ
  apply closure_mono ?_ hcl
  intro z hz
  refine ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, ?_⟩
  intro b
  simpa only [hZe b] using hz.2.2.2.2.2 (e b)

#print axioms rational_selected_support_coordinate_lift

end Papers.RationalityTen.FixedCoordinateFlagDensity
