import bier.padded_inverse_span
import bier.sign_rank

/-! # The rank of the Schur-sign matrix

Fixed positive face cardinality lets the constant feature be replaced by
the trace of the padded principal inverse. Arbitrary cardinalities use one
additional scalar coordinate.
-/

noncomputable section

namespace Bier

open Classical Finset Matrix Module

variable {R C I : Type*} [Fintype R] [Fintype C] [Fintype I] [DecidableEq I]

def quadraticEvaluation (u v : I → ℝ) : Matrix I I ℝ →ₗ[ℝ] ℝ where
  toFun W := ∑ i, ∑ j, u i * W i j * v j
  map_add' W Z := by
    simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c W := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ i j, u i * (c * W i j) * v j = c * (u i * W i j * v j) by
      intros; ring]
    simp only [Finset.mul_sum]

theorem linearEvaluation_rank_le {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (w : R → M) (f : C → Module.Dual ℝ M) :
    Matrix.rank (Matrix.of fun r c => f c (w r)) ≤ Module.finrank ℝ M := by
  let L : M →ₗ[ℝ] (C → ℝ) :=
    { toFun := fun x c => f c x
      map_add' := by intros; funext c; exact map_add _ _ _
      map_smul' := by intros; funext c; exact map_smul _ _ _ }
  rw [Matrix.rank_eq_finrank_span_row]
  have h : Submodule.span ℝ (Set.range (fun r c => f c (w r))) ≤ LinearMap.range L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    exact ⟨w r, rfl⟩
  exact (Submodule.finrank_mono h).trans (LinearMap.finrank_range_le L)

def schurFeatureMatrix (G : Matrix I I ℝ) (S : R → Finset I)
    (d : C → ℝ) (u v : C → I → ℝ) : Matrix R C ℝ :=
  fun r c => d c - quadraticEvaluation (u c) (v c) (paddedPrincipalInverse G (S r))

theorem schurFeatureMatrix_rank_fixedCard (G : Matrix I I ℝ) (S : R → Finset I)
    (hS : ∀ r, IsUnit (principalMatrix G (S r)).det)
    (k : ℕ) (hk : 0 < k) (hcard : ∀ r, (S r).card = k)
    (d : C → ℝ) (u v : C → I → ℝ) :
    (schurFeatureMatrix G S d u v).rank ≤ Fintype.card I ^ 2 - Fintype.card I + 1 := by
  let P := Submodule.span ℝ (Set.range (fun r => paddedPrincipalInverse G (S r)))
  let w : R → P := fun r => ⟨paddedPrincipalInverse G (S r), Submodule.subset_span ⟨r, rfl⟩⟩
  let f : C → Module.Dual ℝ P := fun c =>
    (((d c / (k : ℝ)) • matrixTracePairing G) - quadraticEvaluation (u c) (v c)).comp P.subtype
  have he : Matrix.of (fun r c => f c (w r)) = schurFeatureMatrix G S d u v := by
    ext r c
    change (d c / (k : ℝ)) * (G * paddedPrincipalInverse G (S r)).trace -
      quadraticEvaluation (u c) (v c) (paddedPrincipalInverse G (S r)) = _
    rw [trace_mul_paddedPrincipalInverse G (S r) (hS r), hcard]
    have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp [schurFeatureMatrix, div_mul_cancel₀ _ hkn]
  rw [← he]
  exact (linearEvaluation_rank_le w f).trans (paddedPrincipalInverse_span_finrank G S hS)

theorem schurFeatureMatrix_rank_arbitrary (G : Matrix I I ℝ) (S : R → Finset I)
    (hS : ∀ r, IsUnit (principalMatrix G (S r)).det)
    (d : C → ℝ) (u v : C → I → ℝ) :
    (schurFeatureMatrix G S d u v).rank ≤ Fintype.card I ^ 2 - Fintype.card I + 2 := by
  let P := Submodule.span ℝ (Set.range (fun r => paddedPrincipalInverse G (S r)))
  let w : R → P × ℝ := fun r =>
    (⟨paddedPrincipalInverse G (S r), Submodule.subset_span ⟨r, rfl⟩⟩, 1)
  let f : C → Module.Dual ℝ (P × ℝ) := fun c =>
    (d c • LinearMap.snd ℝ P ℝ) -
      (quadraticEvaluation (u c) (v c)).comp (P.subtype.comp (LinearMap.fst ℝ P ℝ))
  have he : Matrix.of (fun r c => f c (w r)) = schurFeatureMatrix G S d u v := by
    ext r c
    change d c * 1 - _ = _
    simp [schurFeatureMatrix, w]
  rw [← he]
  have hle := linearEvaluation_rank_le w f
  have hb := paddedPrincipalInverse_span_finrank G S hS
  simp only [Module.finrank_prod, Module.finrank_self] at hle
  change Module.finrank ℝ P ≤ _ at hb
  omega

end Bier
