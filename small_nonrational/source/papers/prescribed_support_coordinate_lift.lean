module
public import Papers.PrescribedKernelDensity
public import Papers.ExtendedNormalBasis

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- Reconstruct homogeneous coordinates while retaining selected supporting
hyperplanes. The invertible matrix `B` includes their original normals among
its columns. Only ranks of complementary relation-matrix columns are needed;
no full subset-rank condition on the relation matrix is imposed. -/
theorem rational_prescribed_support_coordinate_lift {c n r : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (p : Matrix (Fin n) (Fin r) ℝ)
    (hCp : C * p = 0) (B : Matrix (Fin r) (Fin r) ℝ) (hB : B.det ≠ 0)
    (Z : Fin r → Finset (Fin n))
    (hZ : ∀ j i, i ∈ Z j → (p * B) i j = 0)
    (hC : C ∈ closure {D : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      ∀ j, subsetRank C.col (Z j)ᶜ = subsetRank D.col (Z j)ᶜ}) :
    (C, p) ∈ closure {z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin n) (Fin r) ℝ |
      RationalCoordinates z.1 ∧ RationalCoordinates z.2 ∧
      z.1.rank = C.rank ∧ PreservesZeroEntries C z.1 ∧ z.1 * z.2 = 0 ∧
      ∀ j, ∃ a : Fin r → ℝ, a ≠ 0 ∧ (∀ i, RatScalar (a i)) ∧
        ∀ i ∈ Z j, a ⬝ᵥ z.2 i = 0} := by
  classical
  let S : Set (Matrix (Fin c) (Fin n) ℝ) := {D |
    RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
    ∀ j, subsetRank C.col (Z j)ᶜ = subsetRank D.col (Z j)ᶜ}
  let X := p * B
  have hCX : C * X = 0 := by
    change C * (p * B) = 0
    rw [← Matrix.mul_assoc, hCp, Matrix.zero_mul]
  have hker : ∀ j, C.mulVec (X.col j) = 0 := by
    intro j
    ext i
    exact congrFun (congrFun hCX i) j
  have hcl := relative_prescribed_column_kernel_density
    (fun D : Matrix (Fin c) (Fin n) ℝ => fun _ : Fin r => D) C
    (fun _ => continuous_id.continuousAt) S hC
    (fun D hD _ => hD.1) Z (fun D hD j => hD.2.2.2 j) X hker hZ
  let T : Set (Matrix (Fin c) (Fin n) ℝ × Matrix (Fin n) (Fin r) ℝ) := {z |
    z.1 ∈ S ∧ RationalCoordinates z.2 ∧
    (∀ j, z.1.mulVec (z.2.col j) = 0) ∧ ∀ j i, i ∈ Z j → z.2 i j = 0}
  have hT : (C, X) ∈ closure T := hcl
  have hprod : ((C, X), B) ∈ closure
      (T ×ˢ {D : Matrix (Fin r) (Fin r) ℝ | RationalCoordinates D}) := by
    rw [closure_prod_eq]
    exact ⟨hT, rationalCoordinates_dense r r B⟩
  let F : (Matrix (Fin c) (Fin n) ℝ × Matrix (Fin n) (Fin r) ℝ) ×
      Matrix (Fin r) (Fin r) ℝ → Matrix (Fin c) (Fin n) ℝ ×
      Matrix (Fin n) (Fin r) ℝ := fun z => (z.1.1, z.1.2 * z.2⁻¹)
  have hi : ContinuousAt (Inv.inv : Matrix (Fin r) (Fin r) ℝ → _) B :=
    continuousAt_matrix_inv B (by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hB)
  have hF : ContinuousAt F ((C, X), B) :=
    (continuous_fst.comp continuous_fst).continuousAt.prodMk
      (matrix_mul_continuousAt
        (continuous_snd.comp continuous_fst).continuousAt
        (hi.comp_of_eq continuous_snd.continuousAt rfl))
  have hbase : F ((C, X), B) = (C, p) := by
    change (C, (p * B) * B⁻¹) = (C, p)
    exact congrArg (fun M => (C, M))
      (Matrix.mul_nonsing_inv_cancel_right B p (isUnit_iff_ne_zero.mpr hB))
  have hdet : ∀ᶠ z in 𝓝 ((C, X), B), z.2.det ≠ 0 := by
    exact continuous_snd.matrix_det.continuousAt.tendsto.eventually
      (isOpen_compl_singleton.mem_nhds hB)
  have hc := mem_closure_image hF (mem_closure_inter_of_eventually hprod hdet)
  rw [hbase] at hc
  apply closure_mono (s := F '' _) ?_ hc
  rintro _ ⟨⟨⟨D, Y⟩, E⟩, ⟨⟨hDY, hE⟩, hEdet⟩, rfl⟩
  have hDYzero : D * Y = 0 := by
    ext i j
    exact congrFun (hDY.2.2.1 j) i
  have hEY : (Y * E⁻¹) * E = Y :=
    Matrix.nonsing_inv_mul_cancel_right E Y (isUnit_iff_ne_zero.mpr hEdet)
  refine ⟨hDY.1.1, rationalCoordinates_mul hDY.2.1 (rationalCoordinates_inv hE),
    hDY.1.2.1, hDY.1.2.2.1, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, hDYzero, Matrix.zero_mul]
  · intro j
    refine ⟨E.col j, (Matrix.linearIndependent_cols_of_det_ne_zero hEdet).ne_zero j,
      fun i => hE i j, ?_⟩
    intro i hiZ
    have hz := congrFun (congrFun hEY i) j
    have hzero := hDY.2.2.2 j i hiZ
    change E.col j ⬝ᵥ (Y * E⁻¹) i = 0
    rw [dotProduct_comm]
    exact hz.trans hzero

#print axioms rational_prescribed_support_coordinate_lift

end Papers.RationalityTen.FixedCoordinateFlagDensity
