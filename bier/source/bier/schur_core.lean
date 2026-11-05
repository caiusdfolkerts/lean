import bier.schur_algebra
import bier.schur_rank

/-! # Restricting the geometric Schur complement to the core labels -/

noncomputable section

namespace Bier

open Classical Finset Matrix

variable {U C J : Type*} [Fintype U] [Fintype C] [Fintype J]
  [DecidableEq U] [DecidableEq C] [DecidableEq J]

theorem principalMatrix_map_eq (X : Matrix J J ℝ) (e : U ↪ J) (S : Finset U) :
    (principalMatrix X (S.map e)).submatrix (Finset.equivMap e S) (Finset.equivMap e S) =
      principalMatrix (X.submatrix e e) S := rfl

theorem principalMatrix_map_det (X : Matrix J J ℝ) (e : U ↪ J) (S : Finset U) :
    (principalMatrix (X.submatrix e e) S).det = (principalMatrix X (S.map e)).det := by
  rw [← principalMatrix_map_eq X e S, Matrix.det_submatrix_equiv_self]

theorem principalMatrix_map_isUnit (X : Matrix J J ℝ) (e : U ↪ J) (S : Finset U)
    (h : IsUnit (principalMatrix X (S.map e)).det) :
    IsUnit (principalMatrix (X.submatrix e e) S).det := by
  rwa [principalMatrix_map_det]

theorem principalMatrix_map_inverse (X : Matrix J J ℝ) (e : U ↪ J) (S : Finset U)
    (i j : S) :
    (principalMatrix X (S.map e))⁻¹ (Finset.equivMap e S i) (Finset.equivMap e S j) =
      (principalMatrix (X.submatrix e e) S)⁻¹ i j := by
  have he := Matrix.inv_submatrix_equiv (principalMatrix X (S.map e))
    (Finset.equivMap e S) (Finset.equivMap e S)
  rw [principalMatrix_map_eq] at he
  exact (congrFun (congrFun he i) j).symm

theorem quadraticEvaluation_padded (G : Matrix U U ℝ) (S : Finset U) (u v : U → ℝ) :
    quadraticEvaluation u v (paddedPrincipalInverse G S) =
      ∑ i : S, ∑ j : S, u i.val * (principalMatrix G S)⁻¹ i j * v j.val := by
  change (∑ i, ∑ j, u i * paddedPrincipalInverse G S i j * v j) = _
  calc
    _ = ∑ i ∈ S, ∑ j, u i * paddedPrincipalInverse G S i j * v j := by
      apply (Finset.sum_subset S.subset_univ _).symm
      intro i hi hni
      simp [paddedPrincipalInverse, hni]
    _ = ∑ i : S, ∑ j, u i.val * paddedPrincipalInverse G S i.val j * v j := by
      rw [Finset.sum_subtype (p := fun i => i ∈ S) (F := inferInstance) S (fun _ => Iff.rfl)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = ∑ j ∈ S, u i.val * paddedPrincipalInverse G S i.val j * v j := by
          apply (Finset.sum_subset S.subset_univ _).symm
          intro j hj hnj
          simp [paddedPrincipalInverse, hnj]
        _ = _ := by
          rw [Finset.sum_subtype (p := fun j => j ∈ S) (F := inferInstance) S (fun _ => Iff.rfl)]
          simp [paddedPrincipalInverse, i.property]

theorem schurValue_map (X : Matrix J J ℝ) (e : U ↪ J) (S : Finset U) (a : J) :
    schurValue X (S.map e) a =
      X a a - ∑ i : S, ∑ j : S,
        X a (e i.val) * (principalMatrix (X.submatrix e e) S)⁻¹ i j * X (e j.val) a := by
  unfold schurValue
  congr 1
  rw [← (Finset.equivMap e S).sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (Finset.equivMap e S).sum_comp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [principalMatrix_map_inverse]
  rfl

/-- The sign convention `X = -N` in the coordinate normalization gives
exactly the paper's `d - u W v` feature formula. -/
theorem neg_schurValue_core (X : Matrix (U ⊕ C) (U ⊕ C) ℝ)
    (S : Finset U) (c : C) :
    -schurValue X (S.map Function.Embedding.inl) (Sum.inr c) =
      -X (Sum.inr c) (Sum.inr c) -
        quadraticEvaluation (fun i => -X (Sum.inr c) (Sum.inl i))
          (fun i => X (Sum.inl i) (Sum.inr c))
          (paddedPrincipalInverse (X.submatrix Sum.inl Sum.inl) S) := by
  rw [schurValue_map, quadraticEvaluation_padded]
  simp only [Function.Embedding.inl_apply, neg_mul, Finset.sum_neg_distrib]
  ring_nf
  rfl

end Bier
