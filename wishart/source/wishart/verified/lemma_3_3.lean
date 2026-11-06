module

public import wishart.verified.core04

/-!
# Lemma 3.3: radial comparison for a principal partition

The proper-block case follows from the determinant-product generator bound.
The full single block is handled separately by the unrestricted Gaussian
determinant comparison.  This separation retains the entire range `N > m`,
including shapes between `m` and `m + 1`.
-/

@[expose] public section

noncomputable section

open Matrix MeasureTheory ProbabilityTheory TauCeti.Probability Set
open scoped Classical BigOperators

namespace WishartVerification

variable {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ} {N : ℝ}

theorem allFiniteMoments_offset_radial_entry
    (hC : C.PosDef) (hN : (m : ℝ) < N)
    (A : SymmetricMatrix m) (v : EuclideanSpace ℝ (Fin m)) (s : ℝ) (i j : Fin m) :
    HasAllFiniteMoments (fun Y : RadialInputSpace m =>
      (A + radialInput v s Y : Matrix (Fin m) (Fin m) ℝ) i j)
      ((nonsingularWishartMeasure (N - 1) C).prod (multivariateGaussian 0 C)) := by
  let := isProbabilityMeasure_nonsingularWishartMeasure hC
    (show (m : ℝ) - 1 < N - 1 by linarith)
  have hW : HasAllFiniteMoments (fun Y : RadialInputSpace m =>
      (Y.1 : Matrix (Fin m) (Fin m) ℝ) i j)
      ((nonsingularWishartMeasure (N - 1) C).prod (multivariateGaussian 0 C)) :=
    (allFiniteMoments_wishart_entry (α := N - 1) (Sigma := C) i j).comp_measurePreserving
      measurePreserving_fst
  have hz (a : Fin m) : HasAllFiniteMoments (fun Y : RadialInputSpace m => Y.2 a)
      ((nonsingularWishartMeasure (N - 1) C).prod (multivariateGaussian 0 C)) :=
    (allFiniteMoments_gaussian_coordinate 0 C a).comp_measurePreserving measurePreserving_snd
  have h := (HasAllFiniteMoments.const ((A : Matrix (Fin m) (Fin m) ℝ) i j)).add
    (hW.add (((hz i).add (HasAllFiniteMoments.const (s * v i))).mul
      ((hz j).add (HasAllFiniteMoments.const (s * v j)))))
  simpa only [radialInput, Submodule.coe_add, coe_rankOneSymmetric,
    Matrix.add_apply, Matrix.vecMulVec_apply, WithLp.ofLp_add, WithLp.ofLp_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h

theorem integrable_offset_radial_detPower
    (hC : C.PosDef) (hN : (m : ℝ) < N)
    (A : SymmetricMatrix m) (v : EuclideanSpace ℝ (Fin m)) (s : ℝ)
    {η : ℝ} (hη : 0 ≤ η) :
    Integrable (fun Y : RadialInputSpace m =>
      (A + radialInput v s Y : Matrix (Fin m) (Fin m) ℝ).det ^ η)
      ((nonsingularWishartMeasure (N - 1) C).prod (multivariateGaussian 0 C)) := by
  exact ((HasAllFiniteMoments.det _ (allFiniteMoments_offset_radial_entry hC hN A v s)).rpow hη).integrable

/-- The strict single-block assertion used in the proof of Lemma 3.3. -/
theorem strictMonoOn_radial_full_determinant
    (hC : C.PosDef) (hN : (m : ℝ) < N)
    (A : SymmetricMatrix m) (hA : (A : Matrix (Fin m) (Fin m) ℝ).PosSemidef)
    {v : EuclideanSpace ℝ (Fin m)} (hv : v ≠ 0) {η : ℝ} (hη : 0 < η) :
    StrictMonoOn (fun t : ℝ => ∫ Y : RadialInputSpace m,
      (A + radialInput v (Real.sqrt t) Y : Matrix (Fin m) (Fin m) ℝ).det ^ η
      ∂(nonsingularWishartMeasure (N - 1) C).prod (multivariateGaussian 0 C)) (Ici 0) := by
  let := isProbabilityMeasure_nonsingularWishartMeasure hC
    (show (m : ℝ) - 1 < N - 1 by linarith)
  have hint (t : ℝ) := integrable_offset_radial_detPower hC hN A v (Real.sqrt t) hη.le
  intro s hs t ht hst
  dsimp only
  rw [integral_prod _ (hint s), integral_prod _ (hint t)]
  have hlt : ∀ᵐ W : SymmetricMatrix m ∂nonsingularWishartMeasure (N - 1) C,
      (∫ z : EuclideanSpace ℝ (Fin m),
        (A + radialInput v (Real.sqrt s) (W, z) : Matrix (Fin m) (Fin m) ℝ).det ^ η
        ∂multivariateGaussian 0 C) <
      ∫ z : EuclideanSpace ℝ (Fin m),
        (A + radialInput v (Real.sqrt t) (W, z) : Matrix (Fin m) (Fin m) ℝ).det ^ η
        ∂multivariateGaussian 0 C := by
    filter_upwards [ae_posDef_nonsingularWishartMeasure (N - 1) C] with W hW
    have hB : ((A : Matrix (Fin m) (Fin m) ℝ) + W).PosDef := by
      simpa only [add_comm] using hW.add_posSemidef hA
    simpa only [rankOneDeterminant, radialInput, Submodule.coe_add,
      coe_rankOneSymmetric, add_assoc] using
      integral_gaussian_rankOneDeterminant_rpow_strictMono hB hC.posSemidef hv hη hs ht hst
  have hpos := integral_pos_of_pos_ae
    ((hint t).integral_prod_left.sub (hint s).integral_prod_left)
    (hlt.mono fun W hW => sub_pos.mpr hW)
  simp only [Pi.sub_apply] at hpos
  rw [integral_sub (hint t).integral_prod_left (hint s).integral_prod_left] at hpos
  exact sub_pos.mp hpos

theorem monotoneOn_radial_full_determinant
    (hC : C.PosDef) (hN : (m : ℝ) < N)
    (A : SymmetricMatrix m) (hA : (A : Matrix (Fin m) (Fin m) ℝ).PosSemidef)
    (v : EuclideanSpace ℝ (Fin m)) {η : ℝ} (hη : 0 ≤ η) :
    MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace m,
      (A + radialInput v (Real.sqrt t) Y : Matrix (Fin m) (Fin m) ℝ).det ^ η
      ∂(nonsingularWishartMeasure (N - 1) C).prod (multivariateGaussian 0 C)) (Ici 0) := by
  by_cases hv : v = 0
  · subst v
    intro s hs t ht hst
    simp only [radialInput, smul_zero, add_zero, le_refl]
  by_cases hη0 : η = 0
  · subst η
    intro s hs t ht hst
    simp only [Real.rpow_zero, le_refl]
  exact (strictMonoOn_radial_full_determinant hC hN A hA hv
    (lt_of_le_of_ne hη (Ne.symm hη0))).monotoneOn

variable {d : ℕ}

/-- Principal blocks as the fixed compressions used by the generator theorem. -/
def partitionRadialCompressionData (P : PrincipalPartition m d)
    (A : SymmetricMatrix m) (η : Fin d → ℝ) (i : Fin d) : CompressionData m where
  size := Fintype.card (P.block i)
  offset := (A : Matrix (Fin m) (Fin m) ℝ).submatrix
    (fun a => ((Fintype.equivFin (P.block i)).symm a : Fin m))
    (fun a => ((Fintype.equivFin (P.block i)).symm a : Fin m))
  linear := (1 : Matrix (Fin m) (Fin m) ℝ).submatrix id
    (fun a => ((Fintype.equivFin (P.block i)).symm a : Fin m))
  exponent := η i

theorem partitionRadialCompressionData_product (P : PrincipalPartition m d)
    (A X : SymmetricMatrix m) (η : Fin d → ℝ) :
    compressionProduct (partitionRadialCompressionData P A η) X =
      ∏ i, (principalMinor (P.block i) (A + X)) ^ η i := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [principalMinor_eq_det_enumeration (P.block i) (A + X)
    (Fintype.equivFin (P.block i)).symm]
  let e : Fin (Fintype.card (P.block i)) → Fin m :=
    fun a => ((Fintype.equivFin (P.block i)).symm a : Fin m)
  change (((A : Matrix (Fin m) (Fin m) ℝ).submatrix e e +
    ((1 : Matrix (Fin m) (Fin m) ℝ).submatrix id e)ᵀ *
      (X : Matrix (Fin m) (Fin m) ℝ) * (1 : Matrix (Fin m) (Fin m) ℝ).submatrix id e).det ^ η i) = _
  rw [Matrix.transpose_submatrix, Matrix.transpose_one,
    Matrix.submatrix_one_mul_mul_submatrix_one]
  rfl

theorem principalMinor_univ (X : SymmetricMatrix m) :
    principalMinor Finset.univ X = (X : Matrix (Fin m) (Fin m) ℝ).det := by
  let e : (Finset.univ : Finset (Fin m)) ≃ Fin m :=
    ⟨Subtype.val, (fun i => ⟨i, Finset.mem_univ i⟩), (fun _ => rfl), (fun _ => rfl)⟩
  exact Matrix.det_submatrix_equiv_self e
    (X : Matrix (Fin m) (Fin m) ℝ)

/-- The literal partition comparison of Lemma 3.3, with integrability
derived for every radial parameter.  No extra degree bound is imposed. -/
theorem lemma_3_3 (P : PrincipalPartition m d)
    (hC : C.PosDef) (hN : (m : ℝ) < N)
    (A : SymmetricMatrix m) (hA : (A : Matrix (Fin m) (Fin m) ℝ).PosSemidef)
    (η : Fin d → ℝ) (hη : ∀ i, 0 ≤ η i) (v : EuclideanSpace ℝ (Fin m)) :
    (∀ t : ℝ, Integrable (fun Y : RadialInputSpace m =>
      ∏ i, (principalMinor (P.block i) (A + radialInput v (Real.sqrt t) Y)) ^ η i)
      ((nonsingularWishartMeasure (N - 1) C).prod (multivariateGaussian 0 C))) ∧
    MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace m,
      ∏ i, (principalMinor (P.block i) (A + radialInput v (Real.sqrt t) Y)) ^ η i
      ∂(nonsingularWishartMeasure (N - 1) C).prod (multivariateGaussian 0 C)) (Ici 0) := by
  let := isProbabilityMeasure_nonsingularWishartMeasure hC
    (show (m : ℝ) - 1 < N - 1 by linarith)
  constructor
  · intro t
    apply HasAllFiniteMoments.integrable
    apply HasAllFiniteMoments.finset_prod Finset.univ
    intro i hi
    apply HasAllFiniteMoments.rpow _ (hη i)
    exact HasAllFiniteMoments.det _ (fun a b =>
      allFiniteMoments_offset_radial_entry hC hN A v (Real.sqrt t) (a : Fin m) (b : Fin m))
  · by_cases hfull : ∃ i, P.block i = Finset.univ
    · obtain ⟨i, hi⟩ := hfull
      have huniq (j : Fin d) : j = i := by
        by_contra hji
        obtain ⟨a, ha⟩ := P.nonempty j
        exact Finset.disjoint_left.mp (P.disjoint hji) ha (by rw [hi]; exact Finset.mem_univ a)
      have heq (X : SymmetricMatrix m) :
          (∏ j, (principalMinor (P.block j) X) ^ η j) =
          (X : Matrix (Fin m) (Fin m) ℝ).det ^ η i := by
        rw [Finset.prod_eq_single i]
        · rw [hi, principalMinor_univ]
        · intro j hj hji
          exact (hji (huniq j)).elim
        · simp
      simp_rw [heq]
      exact monotoneOn_radial_full_determinant hC hN A hA v (hη i)
    · let D := partitionRadialCompressionData P A η
      have hB (i : Fin d) : (D i).offset.PosSemidef :=
        hA.submatrix _
      have hsize (i : Fin d) : ((D i).size : ℝ) + 1 ≤ (N - 1) + 1 := by
        have hproper : P.block i ⊂ Finset.univ :=
          Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun h => hfull ⟨i, h⟩⟩
        have hcard : (P.block i).card + 1 ≤ m := by
          have h := Finset.card_lt_card hproper
          exact Nat.succ_le_of_lt (by simpa only [Finset.card_univ, Fintype.card_fin] using h)
        have hreal : ((P.block i).card : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hcard
        change (Fintype.card (P.block i) : ℝ) + 1 ≤ (N - 1) + 1
        simp only [Fintype.card_coe]
        linarith
      have hmono := monotoneOn_radial_compressionProduct hC
        (show (m : ℝ) - 1 < N - 1 by linarith) D hB hη hsize v
      simpa only [D, partitionRadialCompressionData_product] using hmono

end WishartVerification

end
