module

public import wishart.verified.field_residual05
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Logic.Equiv.Fintype

/- Recovered canonical proof stage; see verification/recovery-patches.json. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

section CanonicalSource50
/- Source: Wishart/FieldGramSchurAlgebra.lean -/




/-!
# Identification of Gaussian column elimination with the literal Schur map

The only reindexing is the canonical equality `1 + q = q + 1`.
The formulas include zero scalar input; positivity is needed later only for
the Gamma density and probability normalization.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage6_1 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


def castHermitian {p q : ℕ} (h : p = q) (X : Hermitian F p) : Hermitian F q :=
  ⟨(X : Matrix (Fin p) (Fin p) F).submatrix (finCongr h.symm) (finCongr h.symm),
    (WishartVerification.hermitian_matrix_coe X).submatrix _⟩

@[simp] theorem castHermitian_rfl {p : ℕ} (X : Hermitian F p) :
    castHermitian F rfl X = X := by rfl

theorem continuous_castHermitian {p q : ℕ} (h : p = q) :
    Continuous (castHermitian F h) := by
  cases h
  exact continuous_id

theorem castHermitian_map_gram {p q : ℕ} (h : p = q) (n : ℕ) :
    (gramWithFactor F n (1 : Matrix (Fin p) (Fin p) F)).map (castHermitian F h) =
      gramWithFactor F n (1 : Matrix (Fin q) (Fin q) F) := by
  cases h
  exact Measure.map_id

theorem headCast_zero (q : ℕ) :
    finCongr (Nat.add_comm q 1) (0 : Fin (q+1)) = (Fin.castAdd q (0 : Fin 1)) := by
  apply Fin.ext
  rfl

theorem headCast_succ (q : ℕ) (j : Fin q) :
    finCongr (Nat.add_comm q 1) j.succ = Fin.natAdd 1 j := by
  apply Fin.ext
  simp only [finCongr_apply,Fin.val_cast,Fin.val_succ,Fin.val_natAdd]
  omega

theorem cast_fromBlocks_zero_zero {q : ℕ} (S : Hermitian F 1)
    (B : Matrix (Fin 1) (Fin q) F) (W : Hermitian F q) :
    (castHermitian F (Nat.add_comm 1 q) (Wishart.FieldHermitian.fromBlocks F (S,B,W)) :
      Matrix (Fin (q+1)) (Fin (q+1)) F) 0 0 = S.val 0 0 := by
  simp only [castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
    headCast_zero,finSumFinEquiv_symm_apply_castAdd,Matrix.fromBlocks_apply₁₁]

theorem cast_fromBlocks_zero_succ {q : ℕ} (S : Hermitian F 1)
    (B : Matrix (Fin 1) (Fin q) F) (W : Hermitian F q) (j : Fin q) :
    (castHermitian F (Nat.add_comm 1 q) (Wishart.FieldHermitian.fromBlocks F (S,B,W)) :
      Matrix (Fin (q+1)) (Fin (q+1)) F) 0 j.succ = B 0 j := by
  simp only [castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
    headCast_zero,headCast_succ,finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd,Matrix.fromBlocks_apply₁₂]

theorem cast_fromBlocks_succ_zero {q : ℕ} (S : Hermitian F 1)
    (B : Matrix (Fin 1) (Fin q) F) (W : Hermitian F q) (i : Fin q) :
    (castHermitian F (Nat.add_comm 1 q) (Wishart.FieldHermitian.fromBlocks F (S,B,W)) :
      Matrix (Fin (q+1)) (Fin (q+1)) F) i.succ 0 = star (B 0 i) := by
  simp only [castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
    headCast_zero,headCast_succ,finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd,Matrix.fromBlocks_apply₂₁,Matrix.conjTranspose_apply]

theorem cast_fromBlocks_succ_succ {q : ℕ} (S : Hermitian F 1)
    (B : Matrix (Fin 1) (Fin q) F) (W : Hermitian F q) (i j : Fin q) :
    (castHermitian F (Nat.add_comm 1 q) (Wishart.FieldHermitian.fromBlocks F (S,B,W)) :
      Matrix (Fin (q+1)) (Fin (q+1)) F) i.succ j.succ = W.val i j := by
  simp only [castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
    headCast_succ,finSumFinEquiv_symm_apply_natAdd,Matrix.fromBlocks_apply₂₂]

theorem radialGramInput_entries {n q : ℕ} (t : ℝ) (ht : 0 ≤ t) (z : Row F q)
    (H : Matrix (Fin n) (Fin q) F) :
    let X := (radialGramInput F t z H : Matrix (Fin (q+1)) (Fin (q+1)) F)
    X 0 0 = algebraMap ℝ F t ∧
      (∀ j, X 0 j.succ = algebraMap ℝ F (Real.sqrt t) * z j) ∧
      (∀ i, X i.succ 0 = star (z i) * algebraMap ℝ F (Real.sqrt t)) ∧
      (∀ i j, X i.succ j.succ = star (z i) * z j + (Hᴴ * H) i j) := by
  dsimp only
  simp only [radialGramInput,Wishart.FieldGaussian.matrixGram,Matrix.mul_apply,Matrix.conjTranspose_apply,
    appendColumn,appendRow,firstColumn,Matrix.of_apply,Fin.cases_zero,Fin.cases_succ,
    Fin.sum_univ_succ,Pi.single_eq_same,Pi.single_eq_of_ne (Fin.succ_ne_zero _),
    star_zero,zero_mul,mul_zero,Finset.sum_const_zero,add_zero,← algebraMap_star_comm,
    star_trivial,← map_mul,← pow_two,Real.sq_sqrt ht]
  simp only [zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero, ← map_pow,
    Real.sq_sqrt ht, and_self, implies_true]

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open Wishart.FieldGaussian

theorem sqrt_scalarHermitian {t : ℝ} (ht : 0 ≤ t) :
    CFC.sqrt (scalarHermitian t : Matrix (Fin 1) (Fin 1) ℂ) = scalarHermitian (Real.sqrt t) := by
  apply CFC.sqrt_unique
  · simp only [scalarHermitian,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul,← pow_two,Real.sq_sqrt ht]
  · exact (Matrix.PosSemidef.diagonal
      (fun _ => RCLike.nonneg_iff.mpr ⟨Real.sqrt_nonneg t,by simp⟩)).nonneg

theorem radialGramInput_eq_schur {n q : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (z : Row ℂ q) (H : Matrix (Fin n) (Fin q) ℂ) :
    radialGramInput ℂ t z H = castHermitian ℂ (Nat.add_comm 1 q)
      (schurInput (scalarHermitian t) (Wishart.FieldGaussian.matrixGram ℂ H) (oneRowMatrix ℂ z)) := by
  obtain ⟨h00,h0j,hi0,hij⟩ := radialGramInput_entries ℂ t ht z H
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · rw [h00]
    simp only [schurInput,castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
      headCast_zero,headCast_succ,finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁]
    simp [scalarHermitian, Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one]
  · rw [h0j]
    simp only [schurInput,castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
      headCast_zero,headCast_succ,finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂]
    rw [sqrt_scalarHermitian ht]
    simp [scalarHermitian,oneRowMatrix,Matrix.mul_apply, Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one, mul_comm]
  · rw [hi0]
    simp only [schurInput,castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
      headCast_zero,headCast_succ,finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    rw [sqrt_scalarHermitian ht]
    simp [scalarHermitian,oneRowMatrix,Matrix.mul_apply, Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one, mul_comm]
  · rw [hij]
    simp only [schurInput,castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
      headCast_zero,headCast_succ,finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]
    simp [Wishart.FieldGaussian.matrixGram,oneRowMatrix,Matrix.mul_apply,add_comm]

theorem castHermitian_map_wishart {p q : ℕ} (h : p = q) (α : ℝ) :
    (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℂ)).map (castHermitian ℂ h) =
      wishartMeasure α (1 : Matrix (Fin q) (Fin q) ℂ) := by
  cases h
  exact Measure.map_id

theorem matrixGaussian_gram_eq_standardGram (n p : ℕ) :
    (matrixGaussian ℂ n p).map (Wishart.FieldGaussian.matrixGram ℂ) =
      gramMeasure n (1 : Matrix (Fin p) (Fin p) ℂ) := by
  rw [matrixGaussian_map_gram]
  simp only [gramMeasure,CFC.sqrt_one]

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian

theorem sqrt_scalarHermitian {t : ℝ} (ht : 0 ≤ t) :
    sqrt (scalarHermitian t : Matrix (Fin 1) (Fin 1) ℍ[ℝ]) = scalarHermitian (Real.sqrt t) := by
  apply complexRepresentation_injective
  have hp : PosSemidef (scalarHermitian t : Matrix (Fin 1) (Fin 1) ℍ[ℝ]) := by
    unfold PosSemidef scalarHermitian
    rw [complexRepresentation_diagonal]
    exact Matrix.PosSemidef.diagonal fun _ => RCLike.nonneg_iff.mpr ⟨ht,by simp⟩
  rw [complexRepresentation_sqrt hp]
  apply CFC.sqrt_unique
  · rw [← complexRepresentation_mul]
    congr 1
    simp only [scalarHermitian,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Quaternion.coe_mul,← pow_two,Real.sq_sqrt ht]
  · change 0 ≤ complexRepresentation (Matrix.diagonal (fun _ : Fin 1 =>
        (Real.sqrt t : ℍ[ℝ])))
    rw [complexRepresentation_diagonal]
    exact (Matrix.PosSemidef.diagonal
      (fun _ => RCLike.nonneg_iff.mpr ⟨Real.sqrt_nonneg t,by simp⟩)).nonneg

theorem radialGramInput_eq_schur {n q : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (z : Row ℍ[ℝ] q) (H : Matrix (Fin n) (Fin q) ℍ[ℝ]) :
    radialGramInput ℍ[ℝ] t z H = castHermitian ℍ[ℝ] (Nat.add_comm 1 q)
      (schurInput (scalarHermitian t) (Wishart.FieldGaussian.matrixGram ℍ[ℝ] H) (oneRowMatrix ℍ[ℝ] z)) := by
  obtain ⟨h00,h0j,hi0,hij⟩ := radialGramInput_entries ℍ[ℝ] t ht z H
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · rw [h00]
    simp only [schurInput,castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
      headCast_zero,headCast_succ,finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁]
    simp [scalarHermitian, Algebra.algebraMap_eq_smul_one, ← Quaternion.coe_mul_eq_smul, mul_one]
  · rw [h0j]
    simp only [schurInput,castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
      headCast_zero,headCast_succ,finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂]
    rw [sqrt_scalarHermitian ht]
    simp [scalarHermitian,oneRowMatrix,Matrix.mul_apply, Algebra.algebraMap_eq_smul_one, ← Quaternion.coe_mul_eq_smul, mul_one]
  · rw [hi0]
    simp only [schurInput,castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
      headCast_zero,headCast_succ,finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    rw [sqrt_scalarHermitian ht]
    simp [scalarHermitian,oneRowMatrix,Matrix.mul_apply, Algebra.algebraMap_eq_smul_one, ← Quaternion.coe_mul_eq_smul, mul_one]
  · rw [hij]
    simp only [schurInput,castHermitian,Wishart.FieldHermitian.fromBlocks,Matrix.submatrix_apply,
      headCast_zero,headCast_succ,finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]
    simp [Wishart.FieldGaussian.matrixGram,oneRowMatrix,Matrix.mul_apply,add_comm]

theorem castHermitian_map_wishart {p q : ℕ} (h : p = q) (α : ℝ) :
    (wishartMeasure α (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])).map (castHermitian ℍ[ℝ] h) =
      wishartMeasure α (1 : Matrix (Fin q) (Fin q) ℍ[ℝ]) := by
  cases h
  exact Measure.map_id

theorem matrixGaussian_gram_eq_standardGram (n p : ℕ) :
    (matrixGaussian ℍ[ℝ] n p).map (Wishart.FieldGaussian.matrixGram ℍ[ℝ]) =
      gramMeasure n (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  rw [matrixGaussian_map_gram]
  simp only [gramMeasure,sqrt_one_matrix]

end Wishart.QuaternionMatrix
end
end CanonicalSource50

section CanonicalSource51
/- Source: Wishart/FieldGramAgreement.lean -/



/-!
# Agreement of the two independently defined field laws

For every integer sample count at least the ambient dimension, the actual
Gaussian Gram image equals the independently normalized literal Hermitian
density. The induction uses the exact Gaussian column-elimination identity
and the real-shape Schur identity, with identical scalar Gamma seeds.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius

theorem probability_eq_of_subsingleton {E : Type*} [MeasurableSpace E] [Subsingleton E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  apply Measure.ext
  intro s hs
  by_cases h : s.Nonempty
  · have heq : s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y,hy⟩ := h
      simpa only [Subsingleton.elim x y] using hy
    simp only [heq,measure_univ]
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    simp

theorem map_product_three {A B C A' B' C' D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace A'] [MeasurableSpace B'] [MeasurableSpace C'] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite ν] [SFinite ρ]
    (a : A → A') (b : B → B') (c : C → C')
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (T : A' × B' × C' → D) (hT : Measurable T) :
    ((μ.map a).prod ((ν.map b).prod (ρ.map c))).map T =
      (μ.prod (ν.prod ρ)).map (fun z => T (a z.1,b z.2.1,c z.2.2)) := by
  rw [Measure.map_prod_map ν ρ hb hc,
    Measure.map_prod_map μ (ν.prod ρ) ha (hb.prodMap hc),
    Measure.map_map hT (ha.prodMap (hb.prodMap hc))]
  rfl

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open Wishart.FieldGaussian

theorem matrixGaussian_gram_schur_law (n q : ℕ) :
    (matrixGaussian ℂ (n+1) (q+1)).map (Wishart.FieldGaussian.matrixGram ℂ) =
      ((wishartMeasure (n+1 : ℝ) (1 : Matrix (Fin 1) (Fin 1) ℂ)).prod
        ((matrixGaussian ℂ 1 q).prod
          ((matrixGaussian ℂ n q).map (Wishart.FieldGaussian.matrixGram ℂ)))).map
        (fun z => castHermitian ℂ (Nat.add_comm 1 q) (schurInput z.1 z.2.2 z.2.1)) := by
  have hrec := matrixGram_recursive_law (n := n) (q := q) ℂ
    (by simp [Complex.finrank_real_complex]) Complex.reLm complex_re_star_mul (by
      intro v
      simpa only [Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one] using exists_rotate_column v)
  norm_num [Complex.finrank_real_complex] at hrec
  rw [hrec,wishartMeasure_one_eq_gamma (by positivity),
    ← gaussianRow_map_oneRowMatrix ℂ q]
  have hmap := map_product_three (gammaMeasure (n+1 : ℝ) 1)
    (gaussianRowWithFactor ℂ (1 : Matrix (Fin q) (Fin q) ℂ)) (matrixGaussian ℂ n q)
    scalarHermitian (oneRowMatrix ℂ) (Wishart.FieldGaussian.matrixGram ℂ)
    scalarHermitianCL.continuous.measurable (continuous_oneRowMatrix ℂ q).measurable
    (Wishart.FieldGaussian.continuous_matrixGram ℂ n q).measurable
    (fun z => castHermitian ℂ (Nat.add_comm 1 q) (schurInput z.1 z.2.2 z.2.1))
    ((continuous_castHermitian ℂ _).measurable.comp measurable_schurInput)
  rw [hmap]
  apply Measure.map_congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (TauCeti.Probability.ae_pos_gammaMeasure (n+1 : ℝ) 1)] with z hz
  exact radialGramInput_eq_schur z.1 hz.le z.2.1 z.2.2

theorem gramMeasure_eq_wishartMeasure {n p : ℕ} (hp : p ≤ n) :
    gramMeasure n (1 : Matrix (Fin p) (Fin p) ℂ) =
      wishartMeasure (n : ℝ) (1 : Matrix (Fin p) (Fin p) ℂ) := by
  induction p generalizing n with
  | zero =>
      letI := wishart_standard_probability 0 (α := (n : ℝ)) (by
        simpa only [Nat.cast_zero, zero_sub] using
          (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)))
      exact probability_eq_of_subsingleton _ _
  | succ q ih =>
      cases n with
      | zero => omega
      | succ n =>
          have hqn : q ≤ n := Nat.succ_le_succ_iff.mp hp
          have hn : (q : ℝ) - 1 < (n : ℝ) := by exact_mod_cast (show (q : ℤ)-1 < n by omega)
          have hsmall := ih hqn
          have hschur := (finiteDensity_and_schur_law (p := 1) (q := q) (n+1 : ℝ)
            (finiteDensity_wishart_one (by positivity))
            (by simpa using finiteDensity_wishart_standard q hn)).2
          have hcast := congrArg (fun μ => μ.map (castHermitian ℂ (Nat.add_comm 1 q))) hschur
          rw [castHermitian_map_wishart,
            Measure.map_map (continuous_castHermitian ℂ _).measurable measurable_schurInput] at hcast
          rw [← matrixGaussian_gram_eq_standardGram,matrixGaussian_gram_schur_law]
          rw [matrixGaussian_gram_eq_standardGram,hsmall]
          simpa only [Nat.cast_succ,Nat.cast_one,Nat.cast_zero,zero_add,add_sub_cancel_right,Function.comp_def] using hcast.symm

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian

theorem matrixGaussian_gram_schur_law (n q : ℕ) :
    (matrixGaussian ℍ[ℝ] (n+1) (q+1)).map (Wishart.FieldGaussian.matrixGram ℍ[ℝ]) =
      ((wishartMeasure (n+1 : ℝ) (1 : Matrix (Fin 1) (Fin 1) ℍ[ℝ])).prod
        ((matrixGaussian ℍ[ℝ] 1 q).prod
          ((matrixGaussian ℍ[ℝ] n q).map (Wishart.FieldGaussian.matrixGram ℍ[ℝ])))).map
        (fun z => castHermitian ℍ[ℝ] (Nat.add_comm 1 q) (schurInput z.1 z.2.2 z.2.1)) := by
  have hrec := matrixGram_recursive_law (n := n) (q := q) ℍ[ℝ]
    (by simp [Quaternion.finrank_eq_four]) (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) quaternion_re_star_mul (by
      intro v
      simpa only [Algebra.algebraMap_eq_smul_one, ← Quaternion.coe_mul_eq_smul, mul_one] using exists_rotate_column v)
  norm_num [Quaternion.finrank_eq_four] at hrec
  rw [show 4 * (n + 1 : ℝ) / 2 = 2 * (n + 1) by ring] at hrec
  rw [hrec,wishartMeasure_one_eq_gamma (by positivity),
    ← gaussianRow_map_oneRowMatrix ℍ[ℝ] q]
  have hmap := map_product_three (gammaMeasure (2*(n+1 : ℝ)) 2)
    (gaussianRowWithFactor ℍ[ℝ] (1 : Matrix (Fin q) (Fin q) ℍ[ℝ])) (matrixGaussian ℍ[ℝ] n q)
    scalarHermitian (oneRowMatrix ℍ[ℝ]) (Wishart.FieldGaussian.matrixGram ℍ[ℝ])
    scalarHermitianCL.continuous.measurable (continuous_oneRowMatrix ℍ[ℝ] q).measurable
    (Wishart.FieldGaussian.continuous_matrixGram ℍ[ℝ] n q).measurable
    (fun z => castHermitian ℍ[ℝ] (Nat.add_comm 1 q) (schurInput z.1 z.2.2 z.2.1))
    ((continuous_castHermitian ℍ[ℝ] _).measurable.comp measurable_schurInput)
  rw [hmap]
  apply Measure.map_congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (TauCeti.Probability.ae_pos_gammaMeasure (2*(n+1 : ℝ)) 2)] with z hz
  exact radialGramInput_eq_schur z.1 hz.le z.2.1 z.2.2

theorem gramMeasure_eq_wishartMeasure {n p : ℕ} (hp : p ≤ n) :
    gramMeasure n (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) =
      wishartMeasure (n : ℝ) (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  induction p generalizing n with
  | zero =>
      letI := wishart_standard_probability 0 (α := (n : ℝ)) (by
        simpa only [Nat.cast_zero, zero_sub] using
          (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)))
      exact probability_eq_of_subsingleton _ _
  | succ q ih =>
      cases n with
      | zero => omega
      | succ n =>
          have hqn : q ≤ n := Nat.succ_le_succ_iff.mp hp
          have hn : (q : ℝ) - 1 < (n : ℝ) := by exact_mod_cast (show (q : ℤ)-1 < n by omega)
          have hsmall := ih hqn
          have hschur := (finiteDensity_and_schur_law (p := 1) (q := q) (n+1 : ℝ)
            (finiteDensity_wishart_one (by positivity))
            (by simpa using finiteDensity_wishart_standard q hn)).2
          have hcast := congrArg (fun μ => μ.map (castHermitian ℍ[ℝ] (Nat.add_comm 1 q))) hschur
          rw [castHermitian_map_wishart,
            Measure.map_map (continuous_castHermitian ℍ[ℝ] _).measurable measurable_schurInput] at hcast
          rw [← matrixGaussian_gram_eq_standardGram,matrixGaussian_gram_schur_law]
          rw [matrixGaussian_gram_eq_standardGram,hsmall]
          simpa only [Nat.cast_succ,Nat.cast_one,Nat.cast_zero,zero_add,add_sub_cancel_right,Function.comp_def] using hcast.symm

end Wishart.QuaternionMatrix
end
end CanonicalSource51

section CanonicalSource52
/- Source: Wishart/FieldRectangularSpectrum.lean -/




/-!
# The actual spectrum of a rectangular field Gaussian Gram matrix

For a full-row-rank rectangular matrix, a dual eigenframe gives an explicit
orthonormal frame in the ambient column space. Completing that frame proves
the padded-spectrum orbit identity. This is a pointwise algebraic proof; no
measurable singular-value decomposition is assumed.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage6_2 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


def coordinateColumns {n p : ℕ} (e : Fin n ↪ Fin p) : Matrix (Fin p) (Fin n) F :=
  (1 : Matrix (Fin p) (Fin p) F).submatrix id e

theorem mul_coordinateColumns {n p : ℕ} (e : Fin n ↪ Fin p)
    (A : Matrix (Fin p) (Fin p) F) :
    A * coordinateColumns F e = A.submatrix id e := by
  have h := Matrix.mul_submatrix_one (Equiv.refl (Fin p)) e (M := A)
  simpa only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp, coordinateColumns] using h

def paddedDiagonal {n p : ℕ} (hnp : n ≤ p) (lam : Fin n → ℝ) : Hermitian F p :=
  let E := coordinateColumns F ⟨Fin.castLE hnp,Fin.castLE_injective hnp⟩
  ⟨E * realDiagonal F lam * Eᴴ,
    Matrix.isHermitian_mul_mul_conjTranspose E
      (WishartVerification.hermitian_matrix_coe (diagonalHermitian F lam))⟩

theorem continuous_paddedDiagonal {n p : ℕ} (hnp : n ≤ p) :
    Continuous (paddedDiagonal F hnp) := by
  apply Continuous.subtype_mk
  change Continuous (fun lam => _ * realDiagonal F lam * _)
  unfold realDiagonal
  fun_prop

theorem realDiagonal_inv_sqrt_cancel {n : ℕ} (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i) :
    realDiagonal F (fun i => (Real.sqrt (lam i))⁻¹) * realDiagonal F lam *
      realDiagonal F (fun i => (Real.sqrt (lam i))⁻¹) = 1 := by
  simp only [realDiagonal,Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← map_mul,← map_mul]
  have hs : Real.sqrt (lam i) ≠ 0 := (Real.sqrt_pos.mpr (hlam i)).ne'
  have heq : (Real.sqrt (lam i))⁻¹ * lam i * (Real.sqrt (lam i))⁻¹ = 1 := by
    field_simp
    exact (Real.sq_sqrt (hlam i).le).symm
  rw [heq,map_one]

theorem unitary_val_star_mul_self {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) F)) : U.valᴴ * U.val = 1 := by
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U

theorem unitary_val_mul_star_self {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) F)) : U.val * U.valᴴ = 1 := by
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U

def dualEigenFrame {n p : ℕ} (Z : Matrix (Fin n) (Fin p) F)
    (U : unitary (Matrix (Fin n) (Fin n) F)) (lam : Fin n → ℝ) :
    Matrix (Fin p) (Fin n) F :=
  Zᴴ * U.val * realDiagonal F (fun i => (Real.sqrt (lam i))⁻¹)

theorem dualEigenFrame_orthonormal {n p : ℕ} (Z : Matrix (Fin n) (Fin p) F)
    (U : unitary (Matrix (Fin n) (Fin n) F)) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i)
    (hZ : Z * Zᴴ = U.val * realDiagonal F lam * U.valᴴ) :
    (dualEigenFrame F Z U lam)ᴴ * dualEigenFrame F Z U lam = 1 := by
  let D := realDiagonal F (fun i => (Real.sqrt (lam i))⁻¹)
  have hD : Dᴴ = D :=
    WishartVerification.hermitian_matrix_coe (diagonalHermitian F _)
  change (Zᴴ * U.val * D)ᴴ * (Zᴴ * U.val * D) = 1
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hD]
  calc
    _ = D * U.valᴴ * (Z * Zᴴ) * U.val * D := by
      simp only [Matrix.mul_assoc]
    _ = D * realDiagonal F lam * D := by
      rw [hZ]
      calc
        _ = D * (U.valᴴ * U.val) * realDiagonal F lam * (U.valᴴ * U.val) * D := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [unitary_val_star_mul_self]; simp only [Matrix.mul_one, Matrix.one_mul]
    _ = 1 := realDiagonal_inv_sqrt_cancel F lam hlam

theorem dualEigenFrame_weighted_gram {n p : ℕ} (Z : Matrix (Fin n) (Fin p) F)
    (U : unitary (Matrix (Fin n) (Fin n) F)) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) :
    dualEigenFrame F Z U lam * realDiagonal F lam * (dualEigenFrame F Z U lam)ᴴ = Zᴴ * Z := by
  let D := realDiagonal F (fun i => (Real.sqrt (lam i))⁻¹)
  have hD : Dᴴ = D :=
    WishartVerification.hermitian_matrix_coe (diagonalHermitian F _)
  change (Zᴴ * U.val * D) * realDiagonal F lam * (Zᴴ * U.val * D)ᴴ = Zᴴ * Z
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hD]
  calc
    _ = Zᴴ * U.val * (D * realDiagonal F lam * D) * U.valᴴ * Z := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [realDiagonal_inv_sqrt_cancel F lam hlam,Matrix.mul_one]
      calc
        _ = Zᴴ * (U.val * U.valᴴ) * Z := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [unitary_val_mul_star_self, Matrix.mul_one]

theorem paddedDiagonal_orbit_of_dual {n p : ℕ} (hnp : n ≤ p)
    (hcomplete : ∀ B : Matrix (Fin p) (Fin n) F, Bᴴ * B = 1 →
      ∃ O : unitary (Matrix (Fin p) (Fin p) F),
        O.val.submatrix id (Fin.castLE hnp) = B)
    (Z : Matrix (Fin n) (Fin p) F)
    (U : unitary (Matrix (Fin n) (Fin n) F)) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i)
    (hZ : Z * Zᴴ = U.val * realDiagonal F lam * U.valᴴ) :
    ∃ O : unitary (Matrix (Fin p) (Fin p) F),
      unitaryConjugate F O (paddedDiagonal F hnp lam) = Wishart.FieldGaussian.matrixGram F Z := by
  obtain ⟨O,hO⟩ := hcomplete (dualEigenFrame F Z U lam)
    (dualEigenFrame_orthonormal F Z U lam hlam hZ)
  let E := coordinateColumns F ⟨Fin.castLE hnp,Fin.castLE_injective hnp⟩
  have hOE : O.val * E = dualEigenFrame F Z U lam := by
    rw [mul_coordinateColumns]
    exact hO
  refine ⟨O,?_⟩
  apply Subtype.ext
  change O.val * (E * realDiagonal F lam * Eᴴ) * O.valᴴ = Zᴴ * Z
  calc
    _ = (O.val * E) * realDiagonal F lam *
        (O.val * E)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hOE,dualEigenFrame_weighted_gram F Z U lam hlam]

theorem matrixGaussian_map_unitary_right {n p : ℕ} (hF : 0 < Module.finrank ℝ F)
    (re : F →ₗ[ℝ] ℝ) (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (U : unitary (Matrix (Fin p) (Fin p) F)) :
    (matrixGaussian F n p).map (fun Z => Z * U.valᴴ) = matrixGaussian F n p := by
  calc
    _ = (((matrixGaussian F n p).map Matrix.conjTranspose).map
        (fun Z => U.val * Z)).map Matrix.conjTranspose := by
      rw [Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext Z
      simp only [Function.comp_def,Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    _ = ((matrixGaussian F p n).map
        (fun Z => U.val * Z)).map Matrix.conjTranspose := by
      rw [matrixGaussian_map_conjTranspose F n p hF]
    _ = (matrixGaussian F p n).map Matrix.conjTranspose := by
      rw [matrixGaussian_map_unitary_left F hF re hstar U]
    _ = _ := matrixGaussian_map_conjTranspose F p n hF

theorem matrixGram_unitary_right {n p : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) F)) (Z : Matrix (Fin n) (Fin p) F) :
    Wishart.FieldGaussian.matrixGram F (Z * U.valᴴ) = unitaryConjugate F U (Wishart.FieldGaussian.matrixGram F Z) := by
  apply Subtype.ext
  change (Z * U.valᴴ)ᴴ * (Z * U.valᴴ) = U.val * (Zᴴ * Z) * U.valᴴ
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

theorem gram_map_unitaryConjugate {n p : ℕ} (hF : 0 < Module.finrank ℝ F)
    (re : F →ₗ[ℝ] ℝ) (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (U : unitary (Matrix (Fin p) (Fin p) F)) :
    ((matrixGaussian F n p).map (Wishart.FieldGaussian.matrixGram F)).map (unitaryConjugate F U) =
      (matrixGaussian F n p).map (Wishart.FieldGaussian.matrixGram F) := by
  have hc : Continuous (unitaryConjugate F U) := by
    apply Continuous.subtype_mk
    change Continuous (fun X : Hermitian F p => U.val * X.val * U.valᴴ)
    fun_prop
  rw [Measure.map_map hc.measurable (Wishart.FieldGaussian.continuous_matrixGram F n p).measurable]
  have h := congrArg (fun μ => μ.map (Wishart.FieldGaussian.matrixGram F))
    (matrixGaussian_map_unitary_right F hF re hstar U (n := n))
  rw [Measure.map_map (Wishart.FieldGaussian.continuous_matrixGram F n p).measurable (by fun_prop)] at h
  simpa only [Function.comp_def,matrixGram_unitary_right] using h

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.FieldCharts

theorem matrixGaussian_dual_gram_law {n p : ℕ} (hnp : n ≤ p) :
    (matrixGaussian ℂ n p).map (fun Z => Wishart.FieldGaussian.matrixGram ℂ Zᴴ) =
      wishartMeasure (p : ℝ) (1 : Matrix (Fin n) (Fin n) ℂ) := by
  change (matrixGaussian ℂ n p).map (Wishart.FieldGaussian.matrixGram ℂ ∘ Matrix.conjTranspose) = _
  rw [← Measure.map_map (Wishart.FieldGaussian.continuous_matrixGram ℂ p n).measurable (by fun_prop),
    matrixGaussian_map_conjTranspose ℂ n p (by simp [Complex.finrank_real_complex]),
    matrixGaussian_gram_eq_standardGram,gramMeasure_eq_wishartMeasure hnp]

theorem gram_padded_orbit {n p : ℕ} (hnp : n ≤ p)
    (Z : Matrix (Fin n) (Fin p) ℂ) (hZ : (Z * Zᴴ).PosDef) :
    ∃ O : unitary (Matrix (Fin p) (Fin p) ℂ),
      unitaryConjugate ℂ O (paddedDiagonal ℂ hnp (ascendingValues (Wishart.FieldGaussian.matrixGram ℂ Zᴴ))) =
        Wishart.FieldGaussian.matrixGram ℂ Z := by
  obtain ⟨U,hU⟩ := exists_conjugate_ascending (Wishart.FieldGaussian.matrixGram ℂ Zᴴ)
  apply paddedDiagonal_orbit_of_dual ℂ hnp
    (fun B hB => Wishart.FieldSpectral.exists_unitary_extension hnp B hB) Z U
  · intro i
    exact ascendingValues_pos _ (by simpa [Wishart.FieldGaussian.matrixGram] using hZ) i
  · have h := congrArg Subtype.val hU
    simpa only [Wishart.FieldGaussian.matrixGram,Matrix.conjTranspose_conjTranspose,unitaryConjugate,
      diagonalHermitian, realDiagonal, Algebra.algebraMap_eq_smul_one,
      Matrix.star_eq_conjTranspose] using h.symm

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.FieldCharts

theorem matrixGaussian_dual_gram_law {n p : ℕ} (hnp : n ≤ p) :
    (matrixGaussian ℍ[ℝ] n p).map (fun Z => Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ) =
      wishartMeasure (p : ℝ) (1 : Matrix (Fin n) (Fin n) ℍ[ℝ]) := by
  change (matrixGaussian ℍ[ℝ] n p).map (Wishart.FieldGaussian.matrixGram ℍ[ℝ] ∘ Matrix.conjTranspose) = _
  rw [← Measure.map_map (Wishart.FieldGaussian.continuous_matrixGram ℍ[ℝ] p n).measurable (by fun_prop),
    matrixGaussian_map_conjTranspose ℍ[ℝ] n p (by simp [Quaternion.finrank_eq_four]),
    matrixGaussian_gram_eq_standardGram,gramMeasure_eq_wishartMeasure hnp]

theorem gram_padded_orbit {n p : ℕ} (hnp : n ≤ p)
    (Z : Matrix (Fin n) (Fin p) ℍ[ℝ]) (hZ : PosDef (Z * Zᴴ)) :
    ∃ O : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]),
      unitaryConjugate ℍ[ℝ] O (paddedDiagonal ℍ[ℝ] hnp (ascendingValues (Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ))) =
        Wishart.FieldGaussian.matrixGram ℍ[ℝ] Z := by
  obtain ⟨U,hU⟩ := exists_conjugate_ascending (Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ)
  apply paddedDiagonal_orbit_of_dual ℍ[ℝ] hnp
    (fun B hB => exists_unitary_extension p n hnp B hB) Z U
  · intro i
    exact ascendingValues_pos _ (by simpa [Wishart.FieldGaussian.matrixGram] using hZ) i
  · have h := congrArg Subtype.val hU
    simpa only [Wishart.FieldGaussian.matrixGram,Matrix.conjTranspose_conjTranspose,unitaryConjugate,
      Wishart.FieldCharts.diagonalHermitian, realDiagonal, Algebra.algebraMap_eq_smul_one,
      Matrix.star_eq_conjTranspose] using h.symm

end Wishart.QuaternionMatrix
end
end CanonicalSource52

section CanonicalSource53
/- Source: Wishart/FieldGaussianSVD.lean -/




/-!
# Actual independent Haar singular-value representations over C and H

The scalar spectrum is the positive Laguerre law of dimension `min(n,p)`
and shape `max(n,p)`. Both unitary factors are independent Haar variables.
The proof uses pointwise factorizations and invariant integration, so no
measurable singular-vector selection is required.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Classical Quaternion ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage6_3 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


def rectangularUnitaryAction {n p : ℕ}
    (g : unitary (Matrix (Fin n) (Fin n) F) × unitary (Matrix (Fin p) (Fin p) F))
    (Z : Matrix (Fin n) (Fin p) F) : Matrix (Fin n) (Fin p) F :=
  g.1.val * Z * g.2.valᴴ

theorem measurable_rectangularUnitaryAction (n p : ℕ) :
    Measurable (Function.uncurry (rectangularUnitaryAction F (n := n) (p := p))) := by
  unfold rectangularUnitaryAction
  fun_prop

theorem rectangularUnitaryAction_mul {n p : ℕ}
    (g h : unitary (Matrix (Fin n) (Fin n) F) × unitary (Matrix (Fin p) (Fin p) F))
    (Z : Matrix (Fin n) (Fin p) F) :
    rectangularUnitaryAction F (g*h) Z =
      rectangularUnitaryAction F g (rectangularUnitaryAction F h Z) := by
  simp only [rectangularUnitaryAction,Prod.fst_mul,Prod.snd_mul,
    Submonoid.coe_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem matrixGaussian_map_rectangularUnitaryAction {n p : ℕ}
    (hF : 0 < Module.finrank ℝ F) (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (g : unitary (Matrix (Fin n) (Fin n) F) × unitary (Matrix (Fin p) (Fin p) F)) :
    (matrixGaussian F n p).map (rectangularUnitaryAction F g) = matrixGaussian F n p := by
  have h := congrArg (fun μ => μ.map (fun Z => Z * g.2.valᴴ))
    (matrixGaussian_map_unitary_left F hF re hstar g.1 (q := p))
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    matrixGaussian_map_unitary_right F hF re hstar g.2] at h
  exact h

def wideDiagonalFactor {n p : ℕ} (hnp : n ≤ p) (lam : Fin n → ℝ) :
    Matrix (Fin n) (Fin p) F :=
  realDiagonal F (fun i => Real.sqrt (lam i)) *
    (coordinateColumns F ⟨Fin.castLE hnp,Fin.castLE_injective hnp⟩)ᴴ

theorem continuous_wideDiagonalFactor {n p : ℕ} (hnp : n ≤ p) :
    Continuous (wideDiagonalFactor F hnp) := by
  unfold wideDiagonalFactor realDiagonal
  fun_prop

theorem realDiagonal_sqrt_inv_cancel {n : ℕ} (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i) :
    realDiagonal F (fun i => Real.sqrt (lam i)) *
      realDiagonal F (fun i => (Real.sqrt (lam i))⁻¹) = 1 := by
  simp only [realDiagonal,Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← map_mul,mul_inv_cancel₀ (Real.sqrt_pos.mpr (hlam i)).ne',map_one]

theorem dualEigenFrame_reconstruction {n p : ℕ} (Z : Matrix (Fin n) (Fin p) F)
    (U : unitary (Matrix (Fin n) (Fin n) F)) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) :
    U.val * realDiagonal F (fun i => Real.sqrt (lam i)) *
      (dualEigenFrame F Z U lam)ᴴ = Z := by
  have hD : (realDiagonal F (fun i => (Real.sqrt (lam i))⁻¹))ᴴ =
      realDiagonal F (fun i => (Real.sqrt (lam i))⁻¹) :=
    WishartVerification.hermitian_matrix_coe (diagonalHermitian F _)
  rw [dualEigenFrame,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,hD]
  calc
    _ = U.val *
        (realDiagonal F (fun i => Real.sqrt (lam i)) *
          realDiagonal F (fun i => (Real.sqrt (lam i))⁻¹)) * U.valᴴ * Z := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [realDiagonal_sqrt_inv_cancel F lam hlam,
      Matrix.mul_one,unitary_val_mul_star_self,Matrix.one_mul]

theorem wideSVD_of_dual {n p : ℕ} (hnp : n ≤ p)
    (hcomplete : ∀ B : Matrix (Fin p) (Fin n) F, Bᴴ * B = 1 →
      ∃ O : unitary (Matrix (Fin p) (Fin p) F),
        O.val.submatrix id (Fin.castLE hnp) = B)
    (Z : Matrix (Fin n) (Fin p) F)
    (U : unitary (Matrix (Fin n) (Fin n) F)) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i)
    (hZ : Z * Zᴴ = U.val * realDiagonal F lam * U.valᴴ) :
    ∃ g : unitary (Matrix (Fin n) (Fin n) F) × unitary (Matrix (Fin p) (Fin p) F),
      rectangularUnitaryAction F g (wideDiagonalFactor F hnp lam) = Z := by
  obtain ⟨O,hO⟩ := hcomplete (dualEigenFrame F Z U lam)
    (dualEigenFrame_orthonormal F Z U lam hlam hZ)
  let E := coordinateColumns F ⟨Fin.castLE hnp,Fin.castLE_injective hnp⟩
  have hOE : O.val * E = dualEigenFrame F Z U lam := by
    rw [mul_coordinateColumns]
    exact hO
  refine ⟨(U,O),?_⟩
  change U.val * (realDiagonal F (fun i => Real.sqrt (lam i)) * Eᴴ) *
    O.valᴴ = Z
  calc
    _ = U.val * realDiagonal F (fun i => Real.sqrt (lam i)) *
        (O.val * E)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hOE,dualEigenFrame_reconstruction F Z U lam hlam]

theorem transpose_svd_law {n p : ℕ} (hpn : p ≤ n)
    (hF : 0 < Module.finrank ℝ F)
    [CompactSpace (unitary (Matrix (Fin n) (Fin n) F))]
    [CompactSpace (unitary (Matrix (Fin p) (Fin p) F))]
    (κ : Measure (Fin p → ℝ)) [SFinite κ]
    (hwide : (((TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) F)))).prod κ).map
      (fun z => rectangularUnitaryAction F z.1 (wideDiagonalFactor F hpn z.2)) =
        matrixGaussian F p n) :
    (((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) F))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F)))).prod κ).map
      (fun z => rectangularUnitaryAction F z.1 ((wideDiagonalFactor F hpn z.2)ᴴ)) =
        matrixGaussian F n p := by
  let μ := TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) F))
  let ν := TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) F))
  have hswap : (ν.prod μ).prod κ = ((μ.prod ν).prod κ).map (Prod.map Prod.swap id) := by
    rw [← Measure.prod_swap (μ := μ) (ν := ν)]
    simpa only [Measure.map_id] using Measure.map_prod_map (μ.prod ν) κ measurable_swap measurable_id
  have h := congrArg (fun ρ => ρ.map Matrix.conjTranspose) hwide
  have hm : Measurable (fun z :
      (unitary (Matrix (Fin p) (Fin p) F) × unitary (Matrix (Fin n) (Fin n) F)) ×
        (Fin p → ℝ) => rectangularUnitaryAction F z.1 (wideDiagonalFactor F hpn z.2)) :=
    (by
      apply Continuous.measurable
      unfold rectangularUnitaryAction wideDiagonalFactor realDiagonal
      fun_prop)
  rw [Measure.map_map (by fun_prop) hm,
    matrixGaussian_map_conjTranspose F p n hF,hswap,
    Measure.map_map (by fun_prop) (measurable_swap.prodMap measurable_id)] at h
  simpa only [Function.comp_def,Prod.map_def,Prod.fst_swap,Prod.snd_swap,id_eq,μ,ν,rectangularUnitaryAction,
    Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc] using h

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.FieldCharts

theorem exists_wideSVD {n p : ℕ} (hnp : n ≤ p)
    (Z : Matrix (Fin n) (Fin p) ℂ) (hZ : (Z * Zᴴ).PosDef) :
    ∃ g : unitary (Matrix (Fin n) (Fin n) ℂ) × unitary (Matrix (Fin p) (Fin p) ℂ),
      rectangularUnitaryAction ℂ g
        (wideDiagonalFactor ℂ hnp (ascendingValues (Wishart.FieldGaussian.matrixGram ℂ Zᴴ))) = Z := by
  obtain ⟨U,hU⟩ := exists_conjugate_ascending (Wishart.FieldGaussian.matrixGram ℂ Zᴴ)
  apply wideSVD_of_dual ℂ hnp
    (fun B hB => Wishart.FieldSpectral.exists_unitary_extension hnp B hB) Z U
  · exact fun i => ascendingValues_pos _ (by simpa [Wishart.FieldGaussian.matrixGram] using hZ) i
  · simpa only [Wishart.FieldGaussian.matrixGram,Matrix.conjTranspose_conjTranspose,unitaryConjugate,
      diagonalHermitian, realDiagonal, Algebra.algebraMap_eq_smul_one,
      Matrix.star_eq_conjTranspose] using (congrArg Subtype.val hU).symm

theorem matrixGaussian_svd_law_of_le {n p : ℕ} (hnp : n ≤ p) :
    (((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℂ))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ)))).prod
        (identityEigenLaw n (p : ℝ))).map
          (fun z => rectangularUnitaryAction ℂ z.1 (wideDiagonalFactor ℂ hnp z.2)) =
      matrixGaussian ℂ n p := by
  have hmap : Measurable (fun Z : Matrix (Fin n) (Fin p) ℂ => Wishart.FieldGaussian.matrixGram ℂ Zᴴ) :=
    (Wishart.FieldGaussian.continuous_matrixGram ℂ p n).measurable.comp (by fun_prop)
  have hsel : Measurable (fun Z : Matrix (Fin n) (Fin p) ℂ =>
      ascendingValues (Wishart.FieldGaussian.matrixGram ℂ Zᴴ)) := (continuous_ascendingValues n).measurable.comp hmap
  have hlabel : (matrixGaussian ℂ n p).map
      (fun Z => ascendingValues (Wishart.FieldGaussian.matrixGram ℂ Zᴴ)) = identityEigenLaw n (p : ℝ) := by
    change (matrixGaussian ℂ n p).map
      (ascendingValues ∘ fun Z => Wishart.FieldGaussian.matrixGram ℂ Zᴴ) = _
    rw [← Measure.map_map (continuous_ascendingValues n).measurable hmap,
      matrixGaussian_dual_gram_law hnp]
    rfl
  have hpos : ∀ᵐ Z ∂matrixGaussian ℂ n p, (Z * Zᴴ).PosDef := by
    have h := wishart_ae_posDef (p : ℝ) (1 : Matrix (Fin n) (Fin n) ℂ)
    rw [← matrixGaussian_dual_gram_law hnp] at h
    simpa only [Wishart.FieldGaussian.matrixGram,Matrix.conjTranspose_conjTranspose] using
      ae_of_ae_map hmap.aemeasurable h
  have h := Wishart.map_prod_orbit_representative_ae
    ((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℂ))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ))))
    (matrixGaussian ℂ n p) (rectangularUnitaryAction ℂ)
    (fun Z => ascendingValues (Wishart.FieldGaussian.matrixGram ℂ Zᴴ)) (wideDiagonalFactor ℂ hnp)
    (measurable_rectangularUnitaryAction ℂ n p) hsel
    (continuous_wideDiagonalFactor ℂ hnp).measurable
    (rectangularUnitaryAction_mul ℂ)
    (matrixGaussian_map_rectangularUnitaryAction ℂ (by simp [Complex.finrank_real_complex])
      Complex.reLm complex_re_star_mul) (hpos.mono fun Z hZ => exists_wideSVD hnp Z hZ)
  rw [hlabel] at h
  exact h

theorem matrixGaussian_svd_laguerre_of_le {n p : ℕ} (hnp : n ≤ p) :
    (((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℂ))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ)))).prod
        (WishartVerification.normalizedWeight volume (Wishart.FieldSpectral.fieldEigenDensity 2 n p))).map
          (fun z => rectangularUnitaryAction ℂ z.1 (wideDiagonalFactor ℂ hnp z.2)) =
      matrixGaussian ℂ n p := by
  have hp : (n : ℝ)-1 < p := by exact_mod_cast (show (n : ℤ)-1 < p by omega)
  rw [← (identityEigenLaw_normalized_density hp).2.2]
  exact matrixGaussian_svd_law_of_le hnp

theorem matrixGaussian_svd_law_of_ge {n p : ℕ} (hpn : p ≤ n) :
    (((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℂ))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ)))).prod
        (identityEigenLaw p (n : ℝ))).map
          (fun z => rectangularUnitaryAction ℂ z.1 ((wideDiagonalFactor ℂ hpn z.2)ᴴ)) =
      matrixGaussian ℂ n p := by
  have hn : (p : ℝ)-1 < n := by exact_mod_cast (show (p : ℤ)-1 < n by omega)
  letI := identityEigenLaw_isProbability hn
  exact transpose_svd_law ℂ hpn (by simp [Complex.finrank_real_complex])
    (identityEigenLaw p (n : ℝ)) (matrixGaussian_svd_law_of_le hpn)

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.FieldCharts

theorem exists_wideSVD {n p : ℕ} (hnp : n ≤ p)
    (Z : Matrix (Fin n) (Fin p) ℍ[ℝ]) (hZ : PosDef (Z * Zᴴ)) :
    ∃ g : unitary (Matrix (Fin n) (Fin n) ℍ[ℝ]) × unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]),
      rectangularUnitaryAction ℍ[ℝ] g
        (wideDiagonalFactor ℍ[ℝ] hnp (ascendingValues (Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ))) = Z := by
  obtain ⟨U,hU⟩ := exists_conjugate_ascending (Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ)
  apply wideSVD_of_dual ℍ[ℝ] hnp
    (fun B hB => exists_unitary_extension p n hnp B hB) Z U
  · exact fun i => ascendingValues_pos _ (by simpa [Wishart.FieldGaussian.matrixGram] using hZ) i
  · simpa only [Wishart.FieldGaussian.matrixGram,Matrix.conjTranspose_conjTranspose,unitaryConjugate,
      Wishart.FieldCharts.diagonalHermitian, realDiagonal, Algebra.algebraMap_eq_smul_one,
      Matrix.star_eq_conjTranspose] using (congrArg Subtype.val hU).symm

theorem matrixGaussian_svd_law_of_le {n p : ℕ} (hnp : n ≤ p) :
    (((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℍ[ℝ]))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])))).prod
        (identityEigenLaw n (p : ℝ))).map
          (fun z => rectangularUnitaryAction ℍ[ℝ] z.1 (wideDiagonalFactor ℍ[ℝ] hnp z.2)) =
      matrixGaussian ℍ[ℝ] n p := by
  have hmap : Measurable (fun Z : Matrix (Fin n) (Fin p) ℍ[ℝ] => Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ) :=
    (Wishart.FieldGaussian.continuous_matrixGram ℍ[ℝ] p n).measurable.comp (by fun_prop)
  have hsel : Measurable (fun Z : Matrix (Fin n) (Fin p) ℍ[ℝ] =>
      ascendingValues (Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ)) := (continuous_ascendingValues n).measurable.comp hmap
  have hlabel : (matrixGaussian ℍ[ℝ] n p).map
      (fun Z => ascendingValues (Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ)) = identityEigenLaw n (p : ℝ) := by
    change (matrixGaussian ℍ[ℝ] n p).map
      (ascendingValues ∘ fun Z => Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ) = _
    rw [← Measure.map_map (continuous_ascendingValues n).measurable hmap,
      matrixGaussian_dual_gram_law hnp]
    rfl
  have hpos : ∀ᵐ Z ∂matrixGaussian ℍ[ℝ] n p, PosDef (Z * Zᴴ) := by
    have h := wishart_ae_posDef (p : ℝ) (1 : Matrix (Fin n) (Fin n) ℍ[ℝ])
    rw [← matrixGaussian_dual_gram_law hnp] at h
    simpa only [Wishart.FieldGaussian.matrixGram,Matrix.conjTranspose_conjTranspose] using
      ae_of_ae_map hmap.aemeasurable h
  have h := Wishart.map_prod_orbit_representative_ae
    ((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℍ[ℝ]))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))))
    (matrixGaussian ℍ[ℝ] n p) (rectangularUnitaryAction ℍ[ℝ])
    (fun Z => ascendingValues (Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ)) (wideDiagonalFactor ℍ[ℝ] hnp)
    (measurable_rectangularUnitaryAction ℍ[ℝ] n p) hsel
    (continuous_wideDiagonalFactor ℍ[ℝ] hnp).measurable
    (rectangularUnitaryAction_mul ℍ[ℝ])
    (matrixGaussian_map_rectangularUnitaryAction ℍ[ℝ] (by simp [Quaternion.finrank_eq_four])
      (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) quaternion_re_star_mul)
    (hpos.mono fun Z hZ => exists_wideSVD hnp Z hZ)
  rw [hlabel] at h
  exact h

theorem matrixGaussian_svd_laguerre_of_le {n p : ℕ} (hnp : n ≤ p) :
    (((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℍ[ℝ]))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])))).prod
        (WishartVerification.normalizedWeight volume (Wishart.FieldSpectral.fieldEigenDensity 4 n p))).map
          (fun z => rectangularUnitaryAction ℍ[ℝ] z.1 (wideDiagonalFactor ℍ[ℝ] hnp z.2)) =
      matrixGaussian ℍ[ℝ] n p := by
  have hp : (n : ℝ)-1 < p := by exact_mod_cast (show (n : ℤ)-1 < p by omega)
  rw [← (identityEigenLaw_normalized_density hp).2.2]
  exact matrixGaussian_svd_law_of_le hnp

theorem matrixGaussian_svd_law_of_ge {n p : ℕ} (hpn : p ≤ n) :
    (((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℍ[ℝ]))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])))).prod
        (identityEigenLaw p (n : ℝ))).map
          (fun z => rectangularUnitaryAction ℍ[ℝ] z.1 ((wideDiagonalFactor ℍ[ℝ] hpn z.2)ᴴ)) =
      matrixGaussian ℍ[ℝ] n p := by
  have hn : (p : ℝ)-1 < n := by exact_mod_cast (show (p : ℤ)-1 < n by omega)
  letI := identityEigenLaw_isProbability hn
  exact transpose_svd_law ℍ[ℝ] hpn (by simp [Quaternion.finrank_eq_four])
    (identityEigenLaw p (n : ℝ)) (matrixGaussian_svd_law_of_le hpn)

end Wishart.QuaternionMatrix
end
end CanonicalSource53

section CanonicalSource54
/- Source: Wishart/FieldGaussianSlots.lean -/



/-!
# Haar singular-value representations with prescribed positive slots

Any injection of the positive singular values into the ambient coordinates
is permitted. The extension of the corresponding orthonormal columns is
proved by an actual finite permutation, so the zero-first convention used
for ascending spectra is an exact representation of the same Gaussian law.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage6_4 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


theorem exists_unitary_extension_at {n p : ℕ} (hnp : n ≤ p)
    (hcomplete : ∀ B : Matrix (Fin p) (Fin n) F, Bᴴ * B = 1 →
      ∃ O : unitary (Matrix (Fin p) (Fin p) F),
        O.val.submatrix id (Fin.castLE hnp) = B)
    (e : Fin n ↪ Fin p) (B : Matrix (Fin p) (Fin n) F) (hB : Bᴴ * B = 1) :
    ∃ O : unitary (Matrix (Fin p) (Fin p) F),
      O.val.submatrix id e = B := by
  obtain ⟨O,hO⟩ := hcomplete B hB
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hnp) e
    (Fin.castLE_injective hnp) e.injective
  refine ⟨O * permutationUnitary F σ,?_⟩
  ext i j
  change (O.val * σ.permMatrix F) i (e j) = B i j
  rw [PEquiv.mul_toMatrix_toPEquiv]
  change O.val i (σ.symm (e j)) = B i j
  rw [← hσ j,σ.symm_apply_apply]
  exact congrArg (fun A => A i j) hO

def wideDiagonalAt {n p : ℕ} (e : Fin n ↪ Fin p) (lam : Fin n → ℝ) :
    Matrix (Fin n) (Fin p) F :=
  realDiagonal F (fun i => Real.sqrt (lam i)) * (coordinateColumns F e)ᴴ

theorem continuous_wideDiagonalAt {n p : ℕ} (e : Fin n ↪ Fin p) :
    Continuous (wideDiagonalAt F e) := by
  unfold wideDiagonalAt realDiagonal
  fun_prop

theorem wideDiagonalAt_mul_star {n p : ℕ} (e : Fin n ↪ Fin p) (lam : Fin n → ℝ)
    (O : unitary (Matrix (Fin p) (Fin p) F)) :
    wideDiagonalAt F e lam * O.valᴴ =
      realDiagonal F (fun i => Real.sqrt (lam i)) *
        (O.valᴴ).submatrix e id := by
  rw [wideDiagonalAt,Matrix.mul_assoc,coordinateColumns,Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_one]
  have h := Matrix.one_submatrix_mul e (Equiv.refl (Fin p)) (M := O.valᴴ)
  simp only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] at h
  rw [h]

theorem wideSVD_at_of_dual {n p : ℕ} (hnp : n ≤ p)
    (hcomplete : ∀ B : Matrix (Fin p) (Fin n) F, Bᴴ * B = 1 →
      ∃ O : unitary (Matrix (Fin p) (Fin p) F),
        O.val.submatrix id (Fin.castLE hnp) = B)
    (e : Fin n ↪ Fin p) (Z : Matrix (Fin n) (Fin p) F)
    (U : unitary (Matrix (Fin n) (Fin n) F)) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i)
    (hZ : Z * Zᴴ = U.val * realDiagonal F lam * U.valᴴ) :
    ∃ g : unitary (Matrix (Fin n) (Fin n) F) × unitary (Matrix (Fin p) (Fin p) F),
      rectangularUnitaryAction F g (wideDiagonalAt F e lam) = Z := by
  obtain ⟨O,hO⟩ := exists_unitary_extension_at F hnp hcomplete e (dualEigenFrame F Z U lam)
    (dualEigenFrame_orthonormal F Z U lam hlam hZ)
  have hOE : O.val * coordinateColumns F e =
      dualEigenFrame F Z U lam := by
    rw [mul_coordinateColumns]
    exact hO
  refine ⟨(U,O),?_⟩
  change U.val *
    (realDiagonal F (fun i => Real.sqrt (lam i)) * (coordinateColumns F e)ᴴ) * O.valᴴ = Z
  calc
    _ = U.val * realDiagonal F (fun i => Real.sqrt (lam i)) *
        (O.val * coordinateColumns F e)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hOE,dualEigenFrame_reconstruction F Z U lam hlam]

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.FieldCharts

theorem matrixGaussian_svd_law_at {n p : ℕ} (hnp : n ≤ p) (e : Fin n ↪ Fin p) :
    (((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℂ))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ)))).prod
        (identityEigenLaw n (p : ℝ))).map
          (fun z => rectangularUnitaryAction ℂ z.1 (wideDiagonalAt ℂ e z.2)) =
      matrixGaussian ℂ n p := by
  have hmap : Measurable (fun Z : Matrix (Fin n) (Fin p) ℂ => Wishart.FieldGaussian.matrixGram ℂ Zᴴ) :=
    (Wishart.FieldGaussian.continuous_matrixGram ℂ p n).measurable.comp (by fun_prop)
  have hsel : Measurable (fun Z : Matrix (Fin n) (Fin p) ℂ =>
      ascendingValues (Wishart.FieldGaussian.matrixGram ℂ Zᴴ)) := (continuous_ascendingValues n).measurable.comp hmap
  have hlabel : (matrixGaussian ℂ n p).map
      (fun Z => ascendingValues (Wishart.FieldGaussian.matrixGram ℂ Zᴴ)) = identityEigenLaw n (p : ℝ) := by
    change (matrixGaussian ℂ n p).map
      (ascendingValues ∘ fun Z => Wishart.FieldGaussian.matrixGram ℂ Zᴴ) = _
    rw [← Measure.map_map (continuous_ascendingValues n).measurable hmap,
      matrixGaussian_dual_gram_law hnp]
    rfl
  have hpos : ∀ᵐ Z ∂matrixGaussian ℂ n p, (Z * Zᴴ).PosDef := by
    have h := wishart_ae_posDef (p : ℝ) (1 : Matrix (Fin n) (Fin n) ℂ)
    rw [← matrixGaussian_dual_gram_law hnp] at h
    simpa only [Wishart.FieldGaussian.matrixGram,Matrix.conjTranspose_conjTranspose] using
      ae_of_ae_map hmap.aemeasurable h
  have h := Wishart.map_prod_orbit_representative_ae
    ((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℂ))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ))))
    (matrixGaussian ℂ n p) (rectangularUnitaryAction ℂ)
    (fun Z => ascendingValues (Wishart.FieldGaussian.matrixGram ℂ Zᴴ)) (wideDiagonalAt ℂ e)
    (measurable_rectangularUnitaryAction ℂ n p) hsel
    (continuous_wideDiagonalAt ℂ e).measurable
    (rectangularUnitaryAction_mul ℂ)
    (matrixGaussian_map_rectangularUnitaryAction ℂ (by simp [Complex.finrank_real_complex])
      Complex.reLm complex_re_star_mul) (by
        filter_upwards [hpos] with Z hZ
        obtain ⟨U,hU⟩ := exists_conjugate_ascending (Wishart.FieldGaussian.matrixGram ℂ Zᴴ)
        apply wideSVD_at_of_dual ℂ hnp
          (fun B hB => Wishart.FieldSpectral.exists_unitary_extension hnp B hB) e Z U
        · exact fun i => ascendingValues_pos _ (by simpa [Wishart.FieldGaussian.matrixGram] using hZ) i
        · simpa only [Wishart.FieldGaussian.matrixGram,Matrix.conjTranspose_conjTranspose,unitaryConjugate,
            diagonalHermitian, realDiagonal, Algebra.algebraMap_eq_smul_one,
      Matrix.star_eq_conjTranspose] using (congrArg Subtype.val hU).symm)
  rw [hlabel] at h
  exact h

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.FieldCharts

theorem matrixGaussian_svd_law_at {n p : ℕ} (hnp : n ≤ p) (e : Fin n ↪ Fin p) :
    (((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℍ[ℝ]))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])))).prod
        (identityEigenLaw n (p : ℝ))).map
          (fun z => rectangularUnitaryAction ℍ[ℝ] z.1 (wideDiagonalAt ℍ[ℝ] e z.2)) =
      matrixGaussian ℍ[ℝ] n p := by
  have hmap : Measurable (fun Z : Matrix (Fin n) (Fin p) ℍ[ℝ] => Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ) :=
    (Wishart.FieldGaussian.continuous_matrixGram ℍ[ℝ] p n).measurable.comp (by fun_prop)
  have hsel : Measurable (fun Z : Matrix (Fin n) (Fin p) ℍ[ℝ] =>
      ascendingValues (Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ)) := (continuous_ascendingValues n).measurable.comp hmap
  have hlabel : (matrixGaussian ℍ[ℝ] n p).map
      (fun Z => ascendingValues (Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ)) = identityEigenLaw n (p : ℝ) := by
    change (matrixGaussian ℍ[ℝ] n p).map
      (ascendingValues ∘ fun Z => Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ) = _
    rw [← Measure.map_map (continuous_ascendingValues n).measurable hmap,
      matrixGaussian_dual_gram_law hnp]
    rfl
  have hpos : ∀ᵐ Z ∂matrixGaussian ℍ[ℝ] n p, PosDef (Z * Zᴴ) := by
    have h := wishart_ae_posDef (p : ℝ) (1 : Matrix (Fin n) (Fin n) ℍ[ℝ])
    rw [← matrixGaussian_dual_gram_law hnp] at h
    simpa only [Wishart.FieldGaussian.matrixGram,Matrix.conjTranspose_conjTranspose] using
      ae_of_ae_map hmap.aemeasurable h
  have h := Wishart.map_prod_orbit_representative_ae
    ((TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℍ[ℝ]))).prod
      (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))))
    (matrixGaussian ℍ[ℝ] n p) (rectangularUnitaryAction ℍ[ℝ])
    (fun Z => ascendingValues (Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ)) (wideDiagonalAt ℍ[ℝ] e)
    (measurable_rectangularUnitaryAction ℍ[ℝ] n p) hsel
    (continuous_wideDiagonalAt ℍ[ℝ] e).measurable
    (rectangularUnitaryAction_mul ℍ[ℝ])
    (matrixGaussian_map_rectangularUnitaryAction ℍ[ℝ] (by simp [Quaternion.finrank_eq_four])
      (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) quaternion_re_star_mul) (by
        filter_upwards [hpos] with Z hZ
        obtain ⟨U,hU⟩ := exists_conjugate_ascending (Wishart.FieldGaussian.matrixGram ℍ[ℝ] Zᴴ)
        apply wideSVD_at_of_dual ℍ[ℝ] hnp
          (fun B hB => exists_unitary_extension p n hnp B hB) e Z U
        · exact fun i => ascendingValues_pos _ (by simpa [Wishart.FieldGaussian.matrixGram] using hZ) i
        · simpa only [Wishart.FieldGaussian.matrixGram,Matrix.conjTranspose_conjTranspose,unitaryConjugate,
            Wishart.FieldCharts.diagonalHermitian, realDiagonal, Algebra.algebraMap_eq_smul_one,
      Matrix.star_eq_conjTranspose] using (congrArg Subtype.val hU).symm)
  rw [hlabel] at h
  exact h

end Wishart.QuaternionMatrix
end
end CanonicalSource54

section CanonicalSource55
/- Source: Wishart/FieldGaussianBlocks.lean -/



/-!
# Independent Gaussian column blocks and elimination of a left Haar frame

The block split follows from the literal rectangular Gaussian density. A
common left unitary on the selected block can be absorbed into the independent
noise when taking the full Gram matrix, including after an arbitrary fixed
rectangular right factor. These are exact pushforward identities.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ENNReal

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldDensity WishartVerification.FieldDensity

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage6_5 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


def splitColumnsLinearEquiv (n p q : ℕ) :
    (Matrix (Fin n) (Fin p) F × Matrix (Fin n) (Fin q) F) ≃ₗ[ℝ]
      Matrix (Fin n) (Fin (p+q)) F where
  toFun z := horizontalJoin F z.1 z.2
  invFun Z := (Z.submatrix id (Fin.castAdd q),Z.submatrix id (Fin.natAdd p))
  left_inv z := by
    apply Prod.ext <;> apply Matrix.ext <;> intro i j <;>
      simp [horizontalJoin, Matrix.submatrix_apply]
  right_inv Z := by
    ext i j
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    cases j <;> simp [horizontalJoin, Matrix.submatrix_apply]
  map_add' A B := by
    ext i j
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    cases j <;> simp [horizontalJoin, Matrix.submatrix_apply]
  map_smul' r A := by
    ext i j
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    cases j <;> simp [horizontalJoin, Matrix.submatrix_apply]

theorem continuous_horizontalJoin (n p q : ℕ) :
    Continuous (fun z : Matrix (Fin n) (Fin p) F × Matrix (Fin n) (Fin q) F =>
      horizontalJoin F z.1 z.2) :=
  (splitColumnsLinearEquiv F n p q).toContinuousLinearEquiv.continuous

theorem matrixKernel_horizontalJoin {n p q : ℕ}
    (A : Matrix (Fin n) (Fin p) F) (B : Matrix (Fin n) (Fin q) F) :
    matrixKernel F (horizontalJoin F A B) = matrixKernel F A * matrixKernel F B := by
  have hn : rectangularNormSquare (horizontalJoin F A B) =
      rectangularNormSquare A + rectangularNormSquare B := by
    unfold rectangularNormSquare
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← finSumFinEquiv.sum_comp (fun j => ‖horizontalJoin F A B i j‖ ^ 2),
      Fintype.sum_sum_type]
    simp [horizontalJoin]
  rw [matrixKernel,hn,mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

theorem matrixGaussian_split_columns (n p q : ℕ) (hF : 0 < Module.finrank ℝ F) :
    ((matrixGaussian F n p).prod (matrixGaussian F n q)).map
      (fun z => horizontalJoin F z.1 z.2) = matrixGaussian F n (p+q) := by
  have hA := finiteDensity_matrixKernel_and_law F n p hF
  have hB := finiteDensity_matrixKernel_and_law F n q hF
  have hp := finiteDensity_product
    (Wishart.FieldHermitian.rectangularLebesgue F n p)
    (Wishart.FieldHermitian.rectangularLebesgue F n q)
    (matrixKernel F) (matrixKernel F) (measurable_matrixKernel F n p)
    (measurable_matrixKernel F n q) hA.1 hB.1
  have h := normalized_transport_haar (splitColumnsLinearEquiv F n p q).toContinuousLinearEquiv
    ((Wishart.FieldHermitian.rectangularLebesgue F n p).prod
      (Wishart.FieldHermitian.rectangularLebesgue F n q))
    (Wishart.FieldHermitian.rectangularLebesgue F n (p+q))
    (fun z => matrixKernel F z.1 * matrixKernel F z.2) (matrixKernel F) hp.1
    (fun z => matrixKernel_horizontalJoin F z.1 z.2)
  rw [hp.2,hA.2,hB.2,(finiteDensity_matrixKernel_and_law F n (p+q) hF).2] at h
  exact h.2.symm

theorem horizontalJoin_mul_left {n p q : ℕ}
    (U : Matrix (Fin n) (Fin n) F) (A : Matrix (Fin n) (Fin p) F)
    (B : Matrix (Fin n) (Fin q) F) :
    horizontalJoin F (U*A) (U*B) = U * horizontalJoin F A B := by
  ext i j
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases j <;> simp [horizontalJoin, Matrix.mul_apply]

def blockGramWithFactor {n p q m : ℕ} (T : Matrix (Fin (p+q)) (Fin m) F)
    (A : Matrix (Fin n) (Fin p) F) (G : Matrix (Fin n) (Fin q) F) : Hermitian F m :=
  Wishart.FieldGaussian.matrixGram F (horizontalJoin F A G * T)

theorem measurable_blockGramWithFactor {n p q m : ℕ}
    (T : Matrix (Fin (p+q)) (Fin m) F) :
    Measurable (fun z : Matrix (Fin n) (Fin p) F × Matrix (Fin n) (Fin q) F =>
      blockGramWithFactor F T z.1 z.2) :=
  (Wishart.FieldGaussian.continuous_matrixGram F n m).measurable.comp
    ((continuous_horizontalJoin F n p q).matrix_mul continuous_const).measurable

theorem blockGramWithFactor_drop_left {n p q m : ℕ}
    (T : Matrix (Fin (p+q)) (Fin m) F)
    (U : unitary (Matrix (Fin n) (Fin n) F))
    (A : Matrix (Fin n) (Fin p) F) (G : Matrix (Fin n) (Fin q) F) :
    blockGramWithFactor F T (U.val*A) G = blockGramWithFactor F T A (U.valᴴ * G) := by
  have hG : U.val * (U.valᴴ * G) = G := by
    rw [← Matrix.mul_assoc,unitary_val_mul_star_self,Matrix.one_mul]
  conv_lhs => rw [← hG]
  rw [blockGramWithFactor,horizontalJoin_mul_left,Matrix.mul_assoc,matrixGram_unitary_left]
  rfl

theorem blockGram_noise_fibre_drop_left {n p q m : ℕ}
    (hF : 0 < Module.finrank ℝ F) (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (T : Matrix (Fin (p+q)) (Fin m) F)
    (U : unitary (Matrix (Fin n) (Fin n) F)) (A : Matrix (Fin n) (Fin p) F) :
    (matrixGaussian F n q).map (fun G => blockGramWithFactor F T (U.val*A) G) =
      (matrixGaussian F n q).map (fun G => blockGramWithFactor F T A G) := by
  have hpair : Measurable (fun G : Matrix (Fin n) (Fin q) F => (A, G)) :=
    measurable_const.prodMk measurable_id
  have hmap : Measurable (fun G : Matrix (Fin n) (Fin q) F =>
      blockGramWithFactor F T A G) := by
    simpa only [Function.comp_def] using (measurable_blockGramWithFactor F T).comp hpair
  calc
    _ = (matrixGaussian F n q).map
        ((fun G => blockGramWithFactor F T A G) ∘ (fun G => U.valᴴ * G)) := by
      congr 1
      exact funext (blockGramWithFactor_drop_left F T U A)
    _ = ((matrixGaussian F n q).map (fun G => U.valᴴ * G)).map
        (fun G => blockGramWithFactor F T A G) :=
      (Measure.map_map hmap (by fun_prop)).symm
    _ = _ := by
      have hrot := matrixGaussian_map_unitary_left F hF re hstar (star U) (q := q)
      simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose] at hrot
      rw [hrot]

set_option backward.isDefEq.respectTransparency true in
theorem discard_left_unitary_noise {n p q m : ℕ} {L : Type*} [MeasurableSpace L]
    (hF : 0 < Module.finrank ℝ F) (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (ξ : Measure L) [SFinite ξ]
    (ρ : Measure (unitary (Matrix (Fin n) (Fin n) F))) [IsProbabilityMeasure ρ]
    (B : L → Matrix (Fin n) (Fin p) F) (hB : Measurable B)
    (T : Matrix (Fin (p+q)) (Fin m) F) :
    ((ρ.prod ξ).prod (matrixGaussian F n q)).map
      (fun z : (unitary (Matrix (Fin n) (Fin n) F) × L) × Matrix (Fin n) (Fin q) F => blockGramWithFactor F (n := n) (p := p) (q := q) (m := m) T (z.1.1.val * B z.1.2) z.2) =
      (ξ.prod (matrixGaussian F n q)).map
        (fun z : L × Matrix (Fin n) (Fin q) F => blockGramWithFactor F (n := n) (p := p) (q := q) (m := m) T (B z.1) z.2) := by
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  letI : SecondCountableTopology F := e.toHomeomorph.secondCountableTopology
  have hleft : Measurable (fun z :
      (unitary (Matrix (Fin n) (Fin n) F) × L) × Matrix (Fin n) (Fin q) F =>
      blockGramWithFactor F (n := n) (p := p) (q := q) (m := m) T (z.1.1.val * B z.1.2) z.2) := by
    have hmul : Measurable (fun z :
        Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin p) F => z.1 * z.2) := by
      apply measurable_pi_iff.mpr
      intro i
      apply measurable_pi_iff.mpr
      intro j
      change Measurable (fun z : Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin p) F =>
        ∑ k, z.1 i k * z.2 k j)
      fun_prop
    have harg : Measurable (fun z :
        (unitary (Matrix (Fin n) (Fin n) F) × L) × Matrix (Fin n) (Fin q) F =>
          (z.1.1.val, B z.1.2)) :=
      (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).prodMk
        (hB.comp (measurable_snd.comp measurable_fst))
    have h := (measurable_blockGramWithFactor F (n := n) (p := p) (q := q) (m := m) T).comp
      ((hmul.comp harg).prodMk measurable_snd)
    simpa only [Function.comp_def] using h
  have harg : Measurable (fun z : L × Matrix (Fin n) (Fin q) F => (B z.1, z.2)) :=
    (hB.comp measurable_fst).prodMk measurable_snd
  have hright : Measurable (fun z : L × Matrix (Fin n) (Fin q) F =>
      blockGramWithFactor F (n := n) (p := p) (q := q) (m := m) T (B z.1) z.2) := by
    simpa only [Function.comp_def] using (measurable_blockGramWithFactor F (n := n) (p := p) (q := q) (m := m) T).comp harg
  have h := Wishart.map_prod_eq_of_map_fibres (ρ.prod ξ) (matrixGaussian F n q)
    Prod.snd measurable_snd _ hleft _ hright (by
      filter_upwards [] with z
      exact blockGram_noise_fibre_drop_left F hF re hstar T z.1 (B z.2))
  rw [(measurePreserving_snd (μ := ρ) (ν := ξ)).map_eq] at h
  exact h

end Wishart.FieldGaussian
end
end CanonicalSource55

section CanonicalSource56
/- Source: Wishart/FieldSingularRowComparison.lean -/




/-!
# Actual shifted-row comparison below the selected rank

For `n ≤ k`, the leading `k × k` Gram matrix has `k-n` zero eigenvalues
followed by its `n` nonnegative ascending eigenvalues.  The model retains the
literal last-slot embedding and all `n` Gaussian trailing rows.  There is no
residual matrix, and no positive-definiteness assumption on the compressed
row covariance.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical Quaternion ComplexOrder ENNReal BigOperators

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.Spectral

def singularPositiveSlot {n k : ℕ} (hnk : n ≤ k) (i : Fin n) : Fin k :=
  ⟨k - n + i.val, by omega⟩

theorem singularPositiveSlot_injective {n k : ℕ} (hnk : n ≤ k) :
    Function.Injective (singularPositiveSlot hnk) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  dsimp [singularPositiveSlot] at h
  omega

def singularPaddedSpectrum {n k : ℕ} (hnk : n ≤ k) (lam : Fin n → ℝ) : Fin k → ℝ :=
  fun j => if h : j.val < k - n then 0 else lam ⟨j.val - (k - n), by omega⟩

@[simp] theorem singularPaddedSpectrum_positiveSlot {n k : ℕ} (hnk : n ≤ k)
    (lam : Fin n → ℝ) (i : Fin n) :
    singularPaddedSpectrum hnk lam (singularPositiveSlot hnk i) = lam i := by
  simp only [singularPaddedSpectrum, singularPositiveSlot]
  rw [dif_neg (by omega)]
  congr 1
  apply Fin.ext
  change k - n + i.val - (k - n) = i.val
  omega

theorem singularPaddedSpectrum_nonneg {n k : ℕ} (hnk : n ≤ k)
    {lam : Fin n → ℝ} (hlam : ∀ i, 0 ≤ lam i) (j : Fin k) :
    0 ≤ singularPaddedSpectrum hnk lam j := by
  unfold singularPaddedSpectrum
  split_ifs
  · exact le_rfl
  · exact hlam _

theorem singularPaddedSpectrum_mono_parameter {n k : ℕ} (hnk : n ≤ k) :
    Monotone (singularPaddedSpectrum hnk) := by
  intro x y hxy j
  unfold singularPaddedSpectrum
  split_ifs
  · exact le_rfl
  · exact hxy _

theorem singularPaddedSpectrum_monotone {n k : ℕ} (hnk : n ≤ k)
    {lam : Fin n → ℝ} (hlam : Monotone lam) (hzero : ∀ i, 0 ≤ lam i) :
    Monotone (singularPaddedSpectrum hnk lam) := by
  intro i j hij
  unfold singularPaddedSpectrum
  split_ifs with hi hj hj
  · exact le_rfl
  · exact hzero _
  · have hval : i.val ≤ j.val := hij
    omega
  · exact hlam (by change i.val - (k - n) ≤ j.val - (k - n); omega)

@[fun_prop] theorem continuous_singularPaddedSpectrum {n k : ℕ} (hnk : n ≤ k) :
    Continuous (singularPaddedSpectrum hnk) := by
  apply continuous_pi
  intro j
  unfold singularPaddedSpectrum
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

variable (F : Type*) [NormedDivisionRing F]
  [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage6_6 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


def singularDiagonalFactor {n k : ℕ} (hnk : n ≤ k) (lam : Fin n → ℝ) :
    Matrix (Fin n) (Fin k) F :=
  fun i j => if singularPositiveSlot hnk i = j then algebraMap ℝ F (Real.sqrt (lam i)) else 0

def singularLeadingFactor {n k : ℕ} (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) F)) (lam : Fin n → ℝ) :
    Matrix (Fin n) (Fin k) F :=
  realDiagonal F (fun i => Real.sqrt (lam i)) *
    (U.valᴴ).submatrix (singularPositiveSlot hnk) id

theorem singularDiagonalFactor_mul_star {n k : ℕ} (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) F)) (lam : Fin n → ℝ) :
    singularDiagonalFactor F hnk lam * (U.valᴴ) =
      singularLeadingFactor F hnk U lam := by
  ext i j
  simp only [singularLeadingFactor, realDiagonal, Matrix.diagonal_mul, Matrix.submatrix_apply]
  simp [singularDiagonalFactor, Matrix.mul_apply, ite_mul]

theorem singularDiagonalFactor_gram {n k : ℕ} (hnk : n ≤ k)
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    (singularDiagonalFactor F hnk lam)ᴴ * singularDiagonalFactor F hnk lam =
      realDiagonal F (singularPaddedSpectrum hnk lam) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < k - n
    · have hslot (a : Fin n) : singularPositiveSlot hnk a ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [singularPositiveSlot] at hv
        omega
      simp [singularDiagonalFactor, Matrix.mul_apply, Matrix.conjTranspose_apply,
        hslot, realDiagonal, singularPaddedSpectrum, hi]
    · let a : Fin n := ⟨i.val - (k - n), by omega⟩
      have ha : singularPositiveSlot hnk a = i := by
        apply Fin.ext
        dsimp [singularPositiveSlot, a]
        omega
      have hsum : ∑ b : Fin n,
          star (singularDiagonalFactor F hnk lam b i) *
            singularDiagonalFactor F hnk lam b i = algebraMap ℝ F (lam a) := by
        rw [Finset.sum_eq_single a]
        · simp only [singularDiagonalFactor, ha, if_true, ← algebraMap_star_comm,
            star_trivial, ← map_mul, ← pow_two, ← map_pow, Real.sq_sqrt (hlam a)]
        · intro b hb hba
          have hslot : singularPositiveSlot hnk b ≠ i := by
            intro h
            exact hba (singularPositiveSlot_injective hnk (h.trans ha.symm))
          simp [singularDiagonalFactor, hslot]
        · simp
      simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, realDiagonal,
        Matrix.diagonal_apply_eq, singularPaddedSpectrum, dif_neg hi, a] using hsum
  · have hz (a : Fin n) : star (singularDiagonalFactor F hnk lam a i) *
        singularDiagonalFactor F hnk lam a j = 0 := by
      by_cases hai : singularPositiveSlot hnk a = i
      · have haj : singularPositiveSlot hnk a ≠ j := by
          intro haj
          exact hij (hai.symm.trans haj)
        simp [singularDiagonalFactor, hai, haj, hij]
      · simp [singularDiagonalFactor, hai]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hz, Finset.sum_const_zero,
      realDiagonal, Matrix.diagonal_apply_ne _ hij]

theorem singularLeadingFactor_gram {n k : ℕ} (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) F)) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) :
    (singularLeadingFactor F hnk U lam)ᴴ * singularLeadingFactor F hnk U lam =
      (unitaryConjugate F U (diagonalHermitian F (singularPaddedSpectrum hnk lam)) :
        Matrix (Fin k) (Fin k) F) := by
  simp only [← singularDiagonalFactor_mul_star F hnk U lam, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc
    _ = U.val *
      ((singularDiagonalFactor F hnk lam)ᴴ * singularDiagonalFactor F hnk lam) * U.valᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [singularDiagonalFactor_gram F hnk lam hlam]; rfl

def singularLeadingRows {n k q : ℕ} (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) F)) : Fin n → Row F (k + q) :=
  fun a => leadingRows F U (singularPositiveSlot hnk a)

def singularSchurGram {n k q : ℕ} (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) F)) (lam : Fin n → ℝ)
    (Z : Matrix (Fin n) (Fin q) F) : Hermitian F (k + q) :=
  let A := horizontalJoin F (singularLeadingFactor F hnk U lam) Z
  ⟨Aᴴ * A, Matrix.isHermitian_conjTranspose_mul_self A⟩

@[fun_prop] theorem continuous_singularSchurGram {n k q : ℕ} (hnk : n ≤ k) :
    Continuous (fun z : (Fin n → ℝ) ×
      (unitary (Matrix (Fin k) (Fin k) F) × Matrix (Fin n) (Fin q) F) =>
        singularSchurGram F hnk z.2.1 z.1 z.2.2) := by
  apply Continuous.subtype_mk
  have hfirst : Continuous (fun z : (Fin n → ℝ) ×
      (unitary (Matrix (Fin k) (Fin k) F) × Matrix (Fin n) (Fin q) F) =>
        singularLeadingFactor F hnk z.2.1 z.1) := by
    unfold singularLeadingFactor realDiagonal
    fun_prop
  have hj : Continuous (fun z : (Fin n → ℝ) ×
      (unitary (Matrix (Fin k) (Fin k) F) × Matrix (Fin n) (Fin q) F) =>
        horizontalJoin F (singularLeadingFactor F hnk z.2.1 z.1) z.2.2) := by
    simpa only [Function.comp_def] using (continuous_horizontalJoin F n k q).comp
      (hfirst.prodMk (continuous_snd.comp continuous_snd))
  exact hj.matrix_conjTranspose.matrix_mul hj

theorem leadingBlock_singularSchurGram {n k q : ℕ} (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) F)) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (Z : Matrix (Fin n) (Fin q) F) :
    Wishart.FieldHermitian.leadingBlock F (singularSchurGram F hnk U lam Z) =
      unitaryConjugate F U (diagonalHermitian F (singularPaddedSpectrum hnk lam)) := by
  apply Subtype.ext
  have h := singularLeadingFactor_gram F hnk U lam hlam
  change ((horizontalJoin F (singularLeadingFactor F hnk U lam) Z)ᴴ *
    horizontalJoin F (singularLeadingFactor F hnk U lam) Z).submatrix
      (Fin.castAdd q) (Fin.castAdd q) = _
  rw [horizontalJoin_gram]
  apply Matrix.ext
  intro i j
  simpa only [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    Matrix.fromBlocks_apply₁₁] using congrArg (fun A => A i j) h

theorem shiftedRows_singular_horizontalJoin {n k q : ℕ} (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) F)) (lam : Fin n → ℝ)
    (z : Fin n → Row F q) :
    rowsMatrix F (fun a => rowFactorCLM F (trailingSelector F k q) (z a) +
      Real.sqrt (lam a) • singularLeadingRows F hnk U a) =
        horizontalJoin F (singularLeadingFactor F hnk U lam) (rowsMatrix F z) := by
  ext a j
  change (rowFactorCLM F (trailingSelector F k q) (z a)) j +
    Real.sqrt (lam a) • (singularLeadingRows F hnk U a) j = _
  generalize hj : (finSumFinEquiv.symm j : Fin k ⊕ Fin q) = b
  cases b with
  | inl i =>
    simp [rowFactorCLM_apply, trailingSelector, singularLeadingRows, leadingRows,
      singularLeadingFactor, horizontalJoin, hj, rowsMatrix, realDiagonal,
      Matrix.diagonal_mul, Matrix.submatrix_apply, Algebra.smul_def]
  | inr i =>
    simp [rowFactorCLM_apply, trailingSelector, singularLeadingRows, leadingRows,
      horizontalJoin, hj, rowsMatrix, Matrix.one_apply]

theorem compress_singularSchurGram {n k q j : ℕ} (hnk : n ≤ k)
    (B : Matrix (Fin (k + q)) (Fin j) F)
    (U : unitary (Matrix (Fin k) (Fin k) F)) (lam : Fin n → ℝ)
    (z : Fin n → Row F q) :
    compress F B (singularSchurGram F hnk U lam (rowsMatrix F z)) =
      ∑ a, compressedRowContribution F B
        (rowFactorCLM F (trailingSelector F k q) (z a) +
          Real.sqrt (lam a) • singularLeadingRows F hnk U a) := by
  rw [← compress_rowsGram]
  apply congrArg (compress F B)
  apply Subtype.ext
  exact congrArg (fun A : Matrix (Fin n) (Fin (k + q)) F => Aᴴ * A)
    (shiftedRows_singular_horizontalJoin F hnk U lam z).symm

theorem lintegral_rectangular_matrixGaussian_eq_padded_rows {n k q : ℕ}
    (f : Matrix (Fin n) (Fin q) F → ℝ≥0∞) (g : (Fin n → Row F (k + q)) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (heq : ∀ z : Fin n → Row F q, f (rowsMatrix F z) =
      g (fun a => rowFactorCLM F (trailingSelector F k q) (z a))) :
    (∫⁻ Z, f Z ∂matrixGaussian F n q) =
      ∫⁻ z, g z ∂Measure.pi (fun _ : Fin n => gaussianRowWithFactor F (trailingSelector F k q)) := by
  rw [matrixGaussian, lintegral_map hf (continuous_rowsMatrix F n q).measurable,
    ← gaussianRowsWithFactor_one_map_factor F (trailingSelector F k q)]
  have hmap : Measurable (fun z : Fin n → Row F q =>
      fun a => rowFactorCLM F (trailingSelector F k q) (z a)) :=
    measurable_pi_iff.mpr fun a =>
      (rowFactorCLM F (trailingSelector F k q)).continuous.measurable.comp (measurable_pi_apply a)
  rw [lintegral_map hg hmap]
  exact lintegral_congr heq

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral

variable {n k q : ℕ}

abbrev SingularSchurNoise (n k q : ℕ) :=
  unitary (Matrix (Fin k) (Fin k) ℂ) × Matrix (Fin n) (Fin q) ℂ

def singularSchurNoiseLaw (n k q : ℕ) : Measure (SingularSchurNoise n k q) :=
  (TauCeti.haarProb (unitary (Matrix (Fin k) (Fin k) ℂ))).prod (matrixGaussian ℂ n q)

def singularSchurBuild (hnk : n ≤ k)
    (z : (Fin n → ℝ) × SingularSchurNoise n k q) : Hermitian (k + q) :=
  singularSchurGram ℂ hnk z.2.1 z.1 z.2.2

theorem measurable_singularSchurBuild (hnk : n ≤ k) :
    Measurable (@singularSchurBuild n k q hnk) :=
  (continuous_singularSchurGram ℂ hnk).measurable

theorem singularSchurNoiseLaw_probability (n k q : ℕ) :
    IsProbabilityMeasure (singularSchurNoiseLaw n k q) := by
  unfold singularSchurNoiseLaw
  infer_instance

theorem ascendingValues_leading_singularSchurGram (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) (lam : Fin n → ℝ)
    (hlam : Monotone lam) (hzero : ∀ i, 0 ≤ lam i) (Z : Matrix (Fin n) (Fin q) ℂ) :
    ascendingValues (Wishart.FieldHermitian.leadingBlock ℂ
      (singularSchurGram ℂ hnk U lam Z)) = singularPaddedSpectrum hnk lam := by
  have hlead : Wishart.FieldHermitian.leadingBlock ℂ
      (singularSchurGram ℂ hnk U lam Z) =
        unitaryConjugate ℂ U (Wishart.FieldCharts.diagonalHermitian ℂ (singularPaddedSpectrum hnk lam)) := by
    apply Subtype.ext
    simpa only [Wishart.FieldHermitian.leadingBlock, unitaryConjugate,
      singularSchurGram, singularLeadingFactor, Wishart.FieldCharts.diagonalHermitian,
      realDiagonal, horizontalJoin, Algebra.algebraMap_eq_smul_one] using
        (congrArg Subtype.val (leadingBlock_singularSchurGram ℂ hnk U lam hzero Z))
  rw [hlead, ascendingValues_conjugate, ascendingValues_diagonal _
      (singularPaddedSpectrum_monotone hnk hlam hzero)]

theorem orderedValues_leading_singularSchurGram (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) (lam : Fin n → ℝ)
    (hlam : Monotone lam) (hzero : ∀ i, 0 ≤ lam i) (Z : Matrix (Fin n) (Fin q) ℂ) :
    Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe
      (Wishart.FieldHermitian.leadingBlock ℂ (singularSchurGram ℂ hnk U lam Z))) =
      singularPaddedSpectrum hnk lam ∘ Fin.rev := by
  rw [← ascendingValues_reversal, ascendingValues_leading_singularSchurGram hnk U lam hlam hzero]

set_option backward.isDefEq.respectTransparency true in
theorem monotone_singularSchur_average (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) {ι : Type*} [Fintype ι]
    (j : ι → ℕ) (B : ∀ i, Matrix (Fin (k + q)) (Fin (j i)) ℂ)
    (Q : ∀ i, Hermitian (j i))
    (hQ : ∀ i, (Q i : Matrix (Fin (j i)) (Fin (j i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (j i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin n → ℝ => ∫⁻ Z,
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℂ (B i) (singularSchurGram ℂ hnk U lam Z)))
      ∂matrixGaussian ℂ n q) (Ici 0) := by
  have hmono := complex_multiple_rows_spectral_comparison
    (trailingSelector ℂ k q) (singularLeadingRows ℂ hnk U) j B Q hQ h hc hm L
  have heq (lam : Fin n → ℝ) :
      (∫⁻ Z, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℂ (B i) (singularSchurGram ℂ hnk U lam Z)))
        ∂matrixGaussian ℂ n q) =
      ∫⁻ z, ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + ∑ a, compressedRowContribution ℂ (B i)
          (z a + Real.sqrt (lam a) • singularLeadingRows ℂ hnk U a)))
        ∂Measure.pi (fun _ : Fin n => gaussianRowWithFactor ℂ (trailingSelector ℂ k q)) := by
    apply lintegral_rectangular_matrixGaussian_eq_padded_rows ℂ
    · apply Measurable.ennreal_ofReal
      apply Finset.measurable_prod
      intro i hi
      apply (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      apply Continuous.measurable
      apply Continuous.add continuous_const
      apply (continuous_compress ℂ (B i)).comp
      have harg : Continuous (fun Z : Matrix (Fin n) (Fin q) ℂ => (lam, (U, Z))) :=
        continuous_const.prodMk (continuous_const.prodMk continuous_id)
      simpa only [Function.comp_def] using (continuous_singularSchurGram ℂ hnk).comp harg
    · apply Measurable.ennreal_ofReal
      apply Finset.measurable_prod
      intro i hi
      apply (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      apply Continuous.measurable
      apply Continuous.add continuous_const
      apply continuous_finsetSum
      intro a ha
      exact (continuous_compressedRowContribution ℂ (B i)).comp
        ((continuous_apply a).add continuous_const)
    · intro z
      apply congrArg ENNReal.ofReal
      apply Finset.prod_congr rfl
      intro i hi
      apply congrArg (complexFaceApprox (hc i) (hm i) (L i))
      apply congrArg (fun X : Hermitian (j i) => Q i + X)
      simpa only [singularSchurGram, singularLeadingFactor, realDiagonal,
        Algebra.algebraMap_eq_smul_one] using
          (compress_singularSchurGram ℂ hnk (B i) U lam z)
  simpa only [heq] using hmono

set_option backward.isDefEq.respectTransparency true in
theorem monotone_singularSchur_conditional_product (hnk : n ≤ k)
    {ι : Type*} [Fintype ι]
    (j : ι → ℕ) (B : ∀ i, Matrix (Fin (k + q)) (Fin (j i)) ℂ)
    (Q : ∀ i, Hermitian (j i))
    (hQ : ∀ i, (Q i : Matrix (Fin (j i)) (Fin (j i)) ℂ).PosSemidef)
    (h : ∀ i, (Fin (j i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin n → ℝ => ∫⁻ z,
      ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℂ (B i) (singularSchurBuild hnk (lam,z))))
      ∂singularSchurNoiseLaw n k q) (Ici 0) := by
  let f : Hermitian (k + q) → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (∏ i, complexFaceApprox (hc i) (hm i) (L i) (Q i + compress ℂ (B i) X))
  have hf : Measurable f := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_complexFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (continuous_compress ℂ (B i))).measurable
  have hprod (lam : Fin n → ℝ) :
      (∫⁻ z, f (singularSchurBuild hnk (lam,z)) ∂singularSchurNoiseLaw n k q) =
      ∫⁻ U, ∫⁻ Z, f (singularSchurGram ℂ hnk U lam Z) ∂matrixGaussian ℂ n q
        ∂TauCeti.haarProb (unitary (Matrix (Fin k) (Fin k) ℂ)) := by
    exact lintegral_prod _
      (hf.comp ((measurable_singularSchurBuild hnk).comp
        (measurable_const.prodMk measurable_id))).aemeasurable
  intro x hx y hy hxy
  change (∫⁻ z, f (singularSchurBuild hnk (x,z)) ∂singularSchurNoiseLaw n k q) ≤
    ∫⁻ z, f (singularSchurBuild hnk (y,z)) ∂singularSchurNoiseLaw n k q
  rw [hprod, hprod]
  exact lintegral_mono fun U =>
    monotone_singularSchur_average hnk U j B Q hQ h hc hm L hx hy hxy

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts Wishart.FieldGaussian Wishart.Spectral

variable {n k q : ℕ}

abbrev SingularSchurNoise (n k q : ℕ) :=
  unitary (Matrix (Fin k) (Fin k) ℍ[ℝ]) × Matrix (Fin n) (Fin q) ℍ[ℝ]

def singularSchurNoiseLaw (n k q : ℕ) : Measure (SingularSchurNoise n k q) :=
  (TauCeti.haarProb (unitary (Matrix (Fin k) (Fin k) ℍ[ℝ]))).prod (matrixGaussian ℍ[ℝ] n q)

def singularSchurBuild (hnk : n ≤ k)
    (z : (Fin n → ℝ) × SingularSchurNoise n k q) : Hermitian (k + q) :=
  singularSchurGram ℍ[ℝ] hnk z.2.1 z.1 z.2.2

theorem measurable_singularSchurBuild (hnk : n ≤ k) :
    Measurable (@singularSchurBuild n k q hnk) :=
  (continuous_singularSchurGram ℍ[ℝ] hnk).measurable

theorem singularSchurNoiseLaw_probability (n k q : ℕ) :
    IsProbabilityMeasure (singularSchurNoiseLaw n k q) := by
  unfold singularSchurNoiseLaw
  infer_instance

theorem ascendingValues_leading_singularSchurGram (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℍ[ℝ])) (lam : Fin n → ℝ)
    (hlam : Monotone lam) (hzero : ∀ i, 0 ≤ lam i) (Z : Matrix (Fin n) (Fin q) ℍ[ℝ]) :
    ascendingValues (Wishart.FieldHermitian.leadingBlock ℍ[ℝ]
      (singularSchurGram ℍ[ℝ] hnk U lam Z)) = singularPaddedSpectrum hnk lam := by
  have hlead : Wishart.FieldHermitian.leadingBlock ℍ[ℝ]
      (singularSchurGram ℍ[ℝ] hnk U lam Z) =
        unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] (singularPaddedSpectrum hnk lam)) := by
    apply Subtype.ext
    simpa only [Wishart.FieldHermitian.leadingBlock, unitaryConjugate,
      singularSchurGram, singularLeadingFactor, Wishart.FieldCharts.diagonalHermitian,
      realDiagonal, horizontalJoin, Algebra.algebraMap_eq_smul_one] using
        (congrArg Subtype.val (leadingBlock_singularSchurGram ℍ[ℝ] hnk U lam hzero Z))
  rw [hlead, ascendingValues_conjugate, ascendingValues_diagonal _
      (singularPaddedSpectrum_monotone hnk hlam hzero)]

theorem orderedValues_leading_singularSchurGram (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℍ[ℝ])) (lam : Fin n → ℝ)
    (hlam : Monotone lam) (hzero : ∀ i, 0 ≤ lam i) (Z : Matrix (Fin n) (Fin q) ℍ[ℝ]) :
    orderedValues (Wishart.FieldHermitian.leadingBlock ℍ[ℝ]
      (singularSchurGram ℍ[ℝ] hnk U lam Z)) =
      singularPaddedSpectrum hnk lam ∘ Fin.rev := by
  rw [← ascendingValues_reversal, ascendingValues_leading_singularSchurGram hnk U lam hlam hzero]

set_option backward.isDefEq.respectTransparency true in
theorem monotone_singularSchur_average (hnk : n ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℍ[ℝ])) {ι : Type*} [Fintype ι]
    (j : ι → ℕ) (B : ∀ i, Matrix (Fin (k + q)) (Fin (j i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (j i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (j i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin n → ℝ => ∫⁻ Z,
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℍ[ℝ] (B i) (singularSchurGram ℍ[ℝ] hnk U lam Z)))
      ∂matrixGaussian ℍ[ℝ] n q) (Ici 0) := by
  have hmono := quaternion_multiple_rows_spectral_comparison
    (trailingSelector ℍ[ℝ] k q) (singularLeadingRows ℍ[ℝ] hnk U) j B Q hQ h hc hm L
  have heq (lam : Fin n → ℝ) :
      (∫⁻ Z, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℍ[ℝ] (B i) (singularSchurGram ℍ[ℝ] hnk U lam Z)))
        ∂matrixGaussian ℍ[ℝ] n q) =
      ∫⁻ z, ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + ∑ a, compressedRowContribution ℍ[ℝ] (B i)
          (z a + Real.sqrt (lam a) • singularLeadingRows ℍ[ℝ] hnk U a)))
        ∂Measure.pi (fun _ : Fin n => gaussianRowWithFactor ℍ[ℝ] (trailingSelector ℍ[ℝ] k q)) := by
    apply lintegral_rectangular_matrixGaussian_eq_padded_rows ℍ[ℝ]
    · apply Measurable.ennreal_ofReal
      apply Finset.measurable_prod
      intro i hi
      apply (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      apply Continuous.measurable
      apply Continuous.add continuous_const
      apply (continuous_compress ℍ[ℝ] (B i)).comp
      have harg : Continuous (fun Z : Matrix (Fin n) (Fin q) ℍ[ℝ] => (lam, (U, Z))) :=
        continuous_const.prodMk (continuous_const.prodMk continuous_id)
      simpa only [Function.comp_def] using (continuous_singularSchurGram ℍ[ℝ] hnk).comp harg
    · apply Measurable.ennreal_ofReal
      apply Finset.measurable_prod
      intro i hi
      apply (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      apply Continuous.measurable
      apply Continuous.add continuous_const
      apply continuous_finsetSum
      intro a ha
      exact (continuous_compressedRowContribution ℍ[ℝ] (B i)).comp
        ((continuous_apply a).add continuous_const)
    · intro z
      apply congrArg ENNReal.ofReal
      apply Finset.prod_congr rfl
      intro i hi
      apply congrArg (quaternionFaceApprox (hc i) (hm i) (L i))
      apply congrArg (fun X : Hermitian (j i) => Q i + X)
      simpa only [singularSchurGram, singularLeadingFactor, realDiagonal,
        Algebra.algebraMap_eq_smul_one] using
          (compress_singularSchurGram ℍ[ℝ] hnk (B i) U lam z)
  simpa only [heq] using hmono

set_option backward.isDefEq.respectTransparency true in
theorem monotone_singularSchur_conditional_product (hnk : n ≤ k)
    {ι : Type*} [Fintype ι]
    (j : ι → ℕ) (B : ∀ i, Matrix (Fin (k + q)) (Fin (j i)) ℍ[ℝ])
    (Q : ∀ i, Hermitian (j i)) (hQ : ∀ i, PosSemidef (Q i).val)
    (h : ∀ i, (Fin (j i) → ℝ) → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (h i)) (hm : ∀ i, Monotone (h i)) (L : ι → ℕ) :
    MonotoneOn (fun lam : Fin n → ℝ => ∫⁻ z,
      ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i)
        (Q i + compress ℍ[ℝ] (B i) (singularSchurBuild hnk (lam,z))))
      ∂singularSchurNoiseLaw n k q) (Ici 0) := by
  let f : Hermitian (k + q) → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (∏ i, quaternionFaceApprox (hc i) (hm i) (L i) (Q i + compress ℍ[ℝ] (B i) X))
  have hf : Measurable f := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i hi
    exact (continuous_quaternionFaceApprox (hc i) (hm i) (L i)).measurable.comp
      (continuous_const.add (continuous_compress ℍ[ℝ] (B i))).measurable
  have hprod (lam : Fin n → ℝ) :
      (∫⁻ z, f (singularSchurBuild hnk (lam,z)) ∂singularSchurNoiseLaw n k q) =
      ∫⁻ U, ∫⁻ Z, f (singularSchurGram ℍ[ℝ] hnk U lam Z) ∂matrixGaussian ℍ[ℝ] n q
        ∂TauCeti.haarProb (unitary (Matrix (Fin k) (Fin k) ℍ[ℝ])) := by
    exact lintegral_prod _
      (hf.comp ((measurable_singularSchurBuild hnk).comp
        (measurable_const.prodMk measurable_id))).aemeasurable
  intro x hx y hy hxy
  change (∫⁻ z, f (singularSchurBuild hnk (x,z)) ∂singularSchurNoiseLaw n k q) ≤
    ∫⁻ z, f (singularSchurBuild hnk (y,z)) ∂singularSchurNoiseLaw n k q
  rw [hprod, hprod]
  exact lintegral_mono fun U =>
    monotone_singularSchur_average hnk U j B Q hQ h hc hm L hx hy hxy

end Wishart.QuaternionMatrix
end
end CanonicalSource56

section CanonicalSource57
/- Source: Wishart/FieldIntegerConditional.lean -/



/-!
# Actual integer conditional Gram representations

The independent column-block Gaussian law and the rectangular singular-value
law give a joint representation of the whole Gram matrix. The left frame is
eliminated by Gaussian invariance in each fibre. In the singular selected-block
case, the positive singular values occupy exactly the final coordinates of
the ascending spectrum. The conclusion is a pushforward of the literal law.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder ENNReal
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage6_7 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


theorem matrixGaussian_map_gram_factor {n r p : ℕ} (T : Matrix (Fin r) (Fin p) F) :
    (matrixGaussian F n r).map (fun Z => Wishart.FieldGaussian.matrixGram F (Z * T)) = gramWithFactor F n T := by
  have hmap : Measurable (fun Z : Matrix (Fin n) (Fin r) F =>
      Wishart.FieldGaussian.matrixGram F (Z * T)) := by
    apply Continuous.measurable
    simpa only [Function.comp_def, id_eq, Function.uncurry_apply_pair] using (Wishart.FieldGaussian.continuous_matrixGram F n p).comp
      (continuous_id.matrix_mul continuous_const)
  unfold matrixGaussian gramWithFactor
  rw [Measure.map_map hmap (continuous_rowsMatrix F n r).measurable,
    ← gaussianRowsWithFactor_one_map_factor F T]
  have hm : Measurable (fun z : Fin n → Row F r => fun i => rowFactorCLM F T (z i)) :=
    measurable_pi_iff.mpr fun i =>
      (rowFactorCLM F T).continuous.measurable.comp (measurable_pi_apply i)
  rw [Measure.map_map (continuous_rowsGram F n p).measurable hm]
  congr 1

theorem blockGramWithFactor_law {n p q m : ℕ}
    (hF : 0 < Module.finrank ℝ F) (T : Matrix (Fin (p+q)) (Fin m) F) :
    ((matrixGaussian F n p).prod (matrixGaussian F n q)).map
      (fun z => blockGramWithFactor F T z.1 z.2) = gramWithFactor F n T := by
  have h := congrArg (fun μ => μ.map (fun Z => Wishart.FieldGaussian.matrixGram F (Z*T)))
    (matrixGaussian_split_columns F n p q hF)
  have hmap : Measurable (fun Z : Matrix (Fin n) (Fin (p + q)) F =>
      Wishart.FieldGaussian.matrixGram F (Z * T)) := by
    apply Continuous.measurable
    simpa only [Function.comp_def, id_eq, Function.uncurry_apply_pair] using (Wishart.FieldGaussian.continuous_matrixGram F n m).comp
      (continuous_id.matrix_mul continuous_const)
  rw [Measure.map_map hmap (continuous_horizontalJoin F n p q).measurable,
    matrixGaussian_map_gram_factor] at h
  exact h

theorem map_product_reorder {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (κ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite κ]
    (f : (A × B) × C → D) (hf : Measurable f) :
    ((μ.prod ν).prod κ).map f =
      (μ.prod (κ.prod ν)).map (fun z => f ((z.1,z.2.2),z.2.1)) := by
  have hperm : MeasurePreserving
      (fun z : A × C × B => ((z.1,z.2.2),z.2.1))
      (μ.prod (κ.prod ν)) ((μ.prod ν).prod κ) :=
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc μ ν κ)).comp
      ((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := κ) (ν := ν)))
  rw [← hperm.map_eq, Measure.map_map hf hperm.measurable]
  rfl

set_option backward.isDefEq.respectTransparency true in
theorem blockGram_law_of_svd {n p q m : ℕ} {L : Type*} [MeasurableSpace L]
    (hF : 0 < Module.finrank ℝ F) (re : F →ₗ[ℝ] ℝ)
    (hstar : ∀ a : F, re (star a * a) = ‖a‖ ^ 2)
    (κ : Measure L) [SFinite κ]
    (ρ : Measure (unitary (Matrix (Fin n) (Fin n) F))) [IsProbabilityMeasure ρ]
    (η : Measure (unitary (Matrix (Fin p) (Fin p) F))) [SFinite η]
    (D : L → Matrix (Fin n) (Fin p) F) (hD : Measurable D)
    (hlaw : ((ρ.prod η).prod κ).map
      (fun z => rectangularUnitaryAction F z.1 (D z.2)) = matrixGaussian F n p)
    (T : Matrix (Fin (p+q)) (Fin m) F) :
    (κ.prod (η.prod (matrixGaussian F n q))).map
      (fun z => blockGramWithFactor F T (D z.1 * z.2.1.valᴴ) z.2.2) =
        gramWithFactor F n T := by
  let eF : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  letI : SecondCountableTopology F := eF.toHomeomorph.secondCountableTopology
  have hs : Measurable (star : F → F) := continuous_star.measurable
  letI : MeasurableMul₂ F := ⟨continuous_mul.measurable⟩
  let B : L × unitary (Matrix (Fin p) (Fin p) F) → Matrix (Fin n) (Fin p) F :=
    fun z => D z.1 * z.2.valᴴ
  have hB : Measurable B := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    simp only [B, Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.measurable_sum
    intro l hl
    exact ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp
      (hD.comp measurable_fst))).mul
        (hs.comp ((measurable_pi_apply l).comp ((measurable_pi_apply j).comp
          (measurable_subtype_coe.comp measurable_snd))))
  let A := fun z : unitary (Matrix (Fin n) (Fin n) F) ×
      (L × unitary (Matrix (Fin p) (Fin p) F)) => z.1.val * B z.2
  have hA : Measurable A := by
    have harg : Measurable (fun z : unitary (Matrix (Fin n) (Fin n) F) ×
        (L × unitary (Matrix (Fin p) (Fin p) F)) =>
          ((z.1, (1 : unitary (Matrix (Fin p) (Fin p) F))), B z.2)) :=
      (measurable_fst.prodMk measurable_const).prodMk (hB.comp measurable_snd)
    simpa only [Function.comp_def, Function.uncurry_apply_pair, rectangularUnitaryAction,
      Submonoid.coe_one, Matrix.conjTranspose_one, Matrix.mul_one, A] using
        (measurable_rectangularUnitaryAction F n p).comp harg
  have hsource : (ρ.prod (κ.prod η)).map A = matrixGaussian F n p := by
    have harg : Measurable (fun z :
        (unitary (Matrix (Fin n) (Fin n) F) × unitary (Matrix (Fin p) (Fin p) F)) × L =>
          (z.1, D z.2)) := measurable_fst.prodMk (hD.comp measurable_snd)
    have hm : Measurable (fun z :
        (unitary (Matrix (Fin n) (Fin n) F) × unitary (Matrix (Fin p) (Fin p) F)) × L =>
          rectangularUnitaryAction F z.1 (D z.2)) := by
      simpa only [Function.comp_def, id_eq, Function.uncurry_apply_pair] using (measurable_rectangularUnitaryAction F n p).comp harg
    rw [map_product_reorder ρ η κ _ hm] at hlaw
    simpa only [A,B,rectangularUnitaryAction,Matrix.mul_assoc] using hlaw
  have hdiscard := discard_left_unitary_noise F hF re hstar (κ.prod η) ρ B hB T
  have hjoined :
      ((ρ.prod (κ.prod η)).prod (matrixGaussian F n q)).map
        (fun z => blockGramWithFactor F T (A z.1) z.2) = gramWithFactor F n T := by
    have hp := Measure.map_prod_map (ρ.prod (κ.prod η)) (matrixGaussian F n q)
      hA (measurable_id : Measurable (@id (Matrix (Fin n) (Fin q) F)))
    simp only [Measure.map_id] at hp
    have h := congrArg (fun μ => μ.map (fun z => blockGramWithFactor F T z.1 z.2)) hp
    rw [hsource,blockGramWithFactor_law F hF T,
      Measure.map_map (measurable_blockGramWithFactor F T) (hA.prodMap measurable_id)] at h
    exact h.symm
  have hright : ((κ.prod η).prod (matrixGaussian F n q)).map
      (fun z => blockGramWithFactor F T (B z.1) z.2) = gramWithFactor F n T := by
    exact hdiscard.symm.trans hjoined
  have hprod := WishartVerification.map_nested_prod κ η (matrixGaussian F n q)
    B hB (fun z => blockGramWithFactor F T z.1 z.2) (measurable_blockGramWithFactor F T)
  have hp := Measure.map_prod_map (κ.prod η) (matrixGaussian F n q)
    hB (measurable_id : Measurable (@id (Matrix (Fin n) (Fin q) F)))
  simp only [Measure.map_id] at hp
  rw [hp,Measure.map_map (measurable_blockGramWithFactor F T) (hB.prodMap measurable_id)] at hprod
  exact hprod.symm.trans hright

end Wishart.FieldGaussian

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.FieldCharts

theorem gramMeasure_map_unitary {n p : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) ℂ)) :
    (gramMeasure n (1 : Matrix (Fin p) (Fin p) ℂ)).map (unitaryConjugate ℂ U) =
      gramMeasure n (1 : Matrix (Fin p) (Fin p) ℂ) := by
  rw [← matrixGaussian_gram_eq_standardGram]
  exact gram_map_unitaryConjugate ℂ (by simp [Complex.finrank_real_complex])
    Complex.reLm complex_re_star_mul U

theorem singular_schur_gram_law {n k q : ℕ} (hnk : n ≤ k) :
    ((identityEigenLaw n (k : ℝ)).prod (singularSchurNoiseLaw n k q)).map
      (singularSchurBuild hnk) = gramMeasure n (1 : Matrix (Fin (k+q)) (Fin (k+q)) ℂ) := by
  have hn : (n : ℝ) - 1 < (k : ℝ) := by exact_mod_cast (show (n : ℤ)-1 < k by omega)
  letI := identityEigenLaw_isProbability hn
  let e : Fin n ↪ Fin k := ⟨singularPositiveSlot hnk,singularPositiveSlot_injective hnk⟩
  have h := blockGram_law_of_svd ℂ (by simp [Complex.finrank_real_complex])
    Complex.reLm complex_re_star_mul (identityEigenLaw n (k : ℝ))
    (TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℂ)))
    (TauCeti.haarProb (unitary (Matrix (Fin k) (Fin k) ℂ)))
    (wideDiagonalAt ℂ e) (continuous_wideDiagonalAt ℂ e).measurable
    (matrixGaussian_svd_law_at hnk e) (1 : Matrix (Fin (k+q)) (Fin (k+q)) ℂ)
  change ((identityEigenLaw n (k : ℝ)).prod (singularSchurNoiseLaw n k q)).map
    (fun z => singularSchurBuild hnk z) = _
  simpa only [singularSchurNoiseLaw,singularSchurBuild,blockGramWithFactor,Matrix.mul_one,
    wideDiagonalAt_mul_star,e,singularLeadingFactor,singularSchurGram,Wishart.FieldGaussian.matrixGram,
    gramMeasure,CFC.sqrt_one, realDiagonal, Algebra.algebraMap_eq_smul_one,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, Function.Embedding.coeFn_mk,
    horizontalJoin] using h

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.FieldCharts

theorem gramMeasure_map_unitary {n p : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    (gramMeasure n (1 : Matrix (Fin p) (Fin p) ℍ[ℝ])).map (unitaryConjugate ℍ[ℝ] U) =
      gramMeasure n (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) := by
  rw [← matrixGaussian_gram_eq_standardGram]
  exact gram_map_unitaryConjugate ℍ[ℝ] (by simp [Quaternion.finrank_eq_four])
    (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) quaternion_re_star_mul U

theorem singular_schur_gram_law {n k q : ℕ} (hnk : n ≤ k) :
    ((identityEigenLaw n (k : ℝ)).prod (singularSchurNoiseLaw n k q)).map
      (singularSchurBuild hnk) = gramMeasure n (1 : Matrix (Fin (k+q)) (Fin (k+q)) ℍ[ℝ]) := by
  have hn : (n : ℝ) - 1 < (k : ℝ) := by exact_mod_cast (show (n : ℤ)-1 < k by omega)
  letI := identityEigenLaw_isProbability hn
  let e : Fin n ↪ Fin k := ⟨singularPositiveSlot hnk,singularPositiveSlot_injective hnk⟩
  have h := blockGram_law_of_svd ℍ[ℝ] (by simp [Quaternion.finrank_eq_four])
    (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) quaternion_re_star_mul (identityEigenLaw n (k : ℝ))
    (TauCeti.haarProb (unitary (Matrix (Fin n) (Fin n) ℍ[ℝ])))
    (TauCeti.haarProb (unitary (Matrix (Fin k) (Fin k) ℍ[ℝ])))
    (wideDiagonalAt ℍ[ℝ] e) (continuous_wideDiagonalAt ℍ[ℝ] e).measurable
    (matrixGaussian_svd_law_at hnk e) (1 : Matrix (Fin (k+q)) (Fin (k+q)) ℍ[ℝ])
  change ((identityEigenLaw n (k : ℝ)).prod (singularSchurNoiseLaw n k q)).map
    (fun z => singularSchurBuild hnk z) = _
  simpa only [singularSchurNoiseLaw,singularSchurBuild,blockGramWithFactor,Matrix.mul_one,
    wideDiagonalAt_mul_star,e,singularLeadingFactor,singularSchurGram,Wishart.FieldGaussian.matrixGram,
    gramMeasure,sqrt_one_matrix, realDiagonal, Algebra.algebraMap_eq_smul_one,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, Function.Embedding.coeFn_mk,
    horizontalJoin] using h

end Wishart.QuaternionMatrix
end
end CanonicalSource57

section CanonicalSource58
/- Source: Wishart/FieldGaussianRowBlocks.lean -/




/-!
# Independent row blocks and the actual residual Gram law

The rectangular Gaussian row split is obtained by conjugate transposition of
the already proved column split. The residual term is a Gram law at every
natural sample count, including zero and all singular dimensions.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder ENNReal

namespace Wishart.FieldGaussian
open scoped Matrix.Norms.Frobenius
open Wishart.FieldCharts

variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [StarModule ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F]

@[reducible] local instance compatibleScalarAlgebraStage6_8 : NormedAlgebra ℝ F where
  toAlgebra := Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)
  norm_smul_le r x := (norm_smul r x).le


def verticalJoin {p r q : ℕ} (A : Matrix (Fin p) (Fin q) F)
    (B : Matrix (Fin r) (Fin q) F) : Matrix (Fin (p+r)) (Fin q) F :=
  (horizontalJoin F Aᴴ Bᴴ)ᴴ

theorem continuous_verticalJoin (p r q : ℕ) :
    Continuous (fun z : Matrix (Fin p) (Fin q) F × Matrix (Fin r) (Fin q) F =>
      verticalJoin F z.1 z.2) := by
  unfold verticalJoin
  exact ((continuous_horizontalJoin F q p r).comp
    (continuous_fst.matrix_conjTranspose.prodMk continuous_snd.matrix_conjTranspose)).matrix_conjTranspose

@[simp] theorem verticalJoin_castAdd {p r q : ℕ}
    (A : Matrix (Fin p) (Fin q) F) (B : Matrix (Fin r) (Fin q) F)
    (i : Fin p) (j : Fin q) : verticalJoin F A B (Fin.castAdd r i) j = A i j := by
  simp only [verticalJoin,horizontalJoin,Matrix.conjTranspose_apply,Matrix.of_apply,
    finSumFinEquiv_symm_apply_castAdd,Sum.elim_inl,star_star]

@[simp] theorem verticalJoin_natAdd {p r q : ℕ}
    (A : Matrix (Fin p) (Fin q) F) (B : Matrix (Fin r) (Fin q) F)
    (i : Fin r) (j : Fin q) : verticalJoin F A B (Fin.natAdd p i) j = B i j := by
  simp only [verticalJoin,horizontalJoin,Matrix.conjTranspose_apply,Matrix.of_apply,
    finSumFinEquiv_symm_apply_natAdd,Sum.elim_inr,star_star]

theorem matrixGaussian_split_rows (p r q : ℕ) (hF : 0 < Module.finrank ℝ F) :
    ((matrixGaussian F p q).prod (matrixGaussian F r q)).map
      (fun z => verticalJoin F z.1 z.2) = matrixGaussian F (p+r) q := by
  let eF : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  letI : SecondCountableTopology F := eF.toHomeomorph.secondCountableTopology
  have hT (a b : ℕ) : Measurable
      (Matrix.conjTranspose : Matrix (Fin a) (Fin b) F → Matrix (Fin b) (Fin a) F) := by
    simpa only [id_eq] using
      (continuous_id : Continuous (@id (Matrix (Fin a) (Fin b) F))).matrix_conjTranspose.measurable
  have hJoin : Measurable (Matrix.conjTranspose ∘
      fun z : Matrix (Fin q) (Fin p) F × Matrix (Fin q) (Fin r) F => horizontalJoin F z.1 z.2) :=
    (hT q (p+r)).comp (continuous_horizontalJoin F q p r).measurable
  have hPair : Measurable (Prod.map
      (Matrix.conjTranspose : Matrix (Fin p) (Fin q) F → Matrix (Fin q) (Fin p) F)
      (Matrix.conjTranspose : Matrix (Fin r) (Fin q) F → Matrix (Fin q) (Fin r) F)) :=
    (hT p q).prodMap (hT r q)
  have h := congrArg (fun μ => μ.map Matrix.conjTranspose)
    (matrixGaussian_split_columns F q p r hF)
  rw [Measure.map_map (hT q (p+r)) (continuous_horizontalJoin F q p r).measurable,
    matrixGaussian_map_conjTranspose F q (p+r) hF] at h
  rw [← matrixGaussian_map_conjTranspose F p q hF,
    ← matrixGaussian_map_conjTranspose F r q hF,
    Measure.map_prod_map _ _ (hT p q) (hT r q),
    Measure.map_map hJoin hPair] at h
  exact h

theorem verticalJoin_gram {p r q : ℕ}
    (A : Matrix (Fin p) (Fin q) F) (B : Matrix (Fin r) (Fin q) F) :
    Wishart.FieldGaussian.matrixGram F (verticalJoin F A B) = Wishart.FieldGaussian.matrixGram F A + Wishart.FieldGaussian.matrixGram F B := by
  apply Subtype.ext
  ext i j
  change (∑ a : Fin (p+r), star (verticalJoin F A B a i) * verticalJoin F A B a j) =
    (∑ a : Fin p, star (A a i) * A a j) + ∑ a : Fin r, star (B a i) * B a j
  rw [← finSumFinEquiv.sum_comp,Fintype.sum_sum_type]
  simp only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
    verticalJoin_castAdd,verticalJoin_natAdd]

theorem horizontalJoin_verticalJoin {p r q k : ℕ}
    (A : Matrix (Fin p) (Fin k) F) (B : Matrix (Fin r) (Fin k) F)
    (Z : Matrix (Fin p) (Fin q) F) (H : Matrix (Fin r) (Fin q) F) :
    horizontalJoin F (verticalJoin F A B) (verticalJoin F Z H) =
      verticalJoin F (horizontalJoin F A Z) (horizontalJoin F B H) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp [horizontalJoin, verticalJoin_castAdd, verticalJoin_natAdd]

theorem zero_horizontalJoin_gram {r p q : ℕ} (H : Matrix (Fin r) (Fin q) F) :
    Wishart.FieldGaussian.matrixGram F (horizontalJoin F (0 : Matrix (Fin r) (Fin p) F) H) =
      trailingBackground F (Wishart.FieldGaussian.matrixGram F H) := by
  apply Subtype.ext
  change (horizontalJoin F (0 : Matrix (Fin r) (Fin p) F) H)ᴴ *
      horizontalJoin F 0 H = _
  rw [horizontalJoin_gram]
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
    trailingBackground, Wishart.FieldHermitian.fromBlocks, Wishart.FieldGaussian.matrixGram,
    Submodule.coe_zero]

theorem tallDiagonalFactor_mul_star {p r : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) F)) (lam : Fin p → ℝ) :
    (wideDiagonalFactor F (Nat.le_add_right p r) lam)ᴴ * U.valᴴ =
      verticalJoin F (realDiagonal F (fun i => Real.sqrt (lam i)) * U.valᴴ)
        (0 : Matrix (Fin r) (Fin p) F) := by
  have hD : (realDiagonal F (fun i => Real.sqrt (lam i)))ᴴ =
      realDiagonal F (fun i => Real.sqrt (lam i)) :=
    WishartVerification.hermitian_matrix_coe (diagonalHermitian F _)
  rw [wideDiagonalFactor, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i =>
    simp only [finSumFinEquiv_apply_left, verticalJoin_castAdd]
    change (∑ a : Fin p, (if Fin.castAdd r i = Fin.castLE (Nat.le_add_right p r) a
      then (1 : F) else 0) *
      (realDiagonal F (fun i => Real.sqrt (lam i)) * U.valᴴ) a j) = _
    have heq (a : Fin p) :
        (Fin.castAdd r i : Fin (p+r)) = Fin.castLE (Nat.le_add_right p r) a ↔ i = a := by
      constructor
      · intro h
        apply Fin.ext
        exact congrArg (fun x : Fin (p+r) => x.val) h
      · rintro rfl
        rfl
    simp only [heq, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  | inr i =>
    simp only [finSumFinEquiv_apply_right, verticalJoin_natAdd]
    change (∑ a : Fin p, (if Fin.natAdd p i = Fin.castLE (Nat.le_add_right p r) a
      then (1 : F) else 0) *
      (realDiagonal F (fun i => Real.sqrt (lam i)) * U.valᴴ) a j) = 0
    have hne (a : Fin p) :
        (Fin.natAdd p i : Fin (p+r)) ≠ Fin.castLE (Nat.le_add_right p r) a := by
      intro h
      have hval := congrArg (fun x : Fin (p+r) => x.val) h
      simp only [Fin.val_natAdd, Fin.val_castLE] at hval
      omega
    simp only [hne, ite_false, zero_mul, Finset.sum_const_zero]

theorem tallGram_row_split {p r q : ℕ}
    (U : unitary (Matrix (Fin p) (Fin p) F)) (lam : Fin p → ℝ)
    (Z : Matrix (Fin p) (Fin q) F) (H : Matrix (Fin r) (Fin q) F) :
    Wishart.FieldGaussian.matrixGram F (horizontalJoin F
      ((wideDiagonalFactor F (Nat.le_add_right p r) lam)ᴴ * U.valᴴ)
      (verticalJoin F Z H)) =
      trailingBackground F (Wishart.FieldGaussian.matrixGram F H) + spectralSchurGram F U lam Z := by
  rw [tallDiagonalFactor_mul_star, horizontalJoin_verticalJoin, verticalJoin_gram,
    zero_horizontalJoin_gram]
  change spectralSchurGram F U lam Z + trailingBackground F (Wishart.FieldGaussian.matrixGram F H) = _
  exact add_comm _ _

theorem tallGram_noise_fibre {p r q : ℕ}
    (hF : 0 < Module.finrank ℝ F)
    (U : unitary (Matrix (Fin p) (Fin p) F)) (lam : Fin p → ℝ) :
    (matrixGaussian F (p+r) q).map
      (fun G => Wishart.FieldGaussian.matrixGram F (horizontalJoin F
        ((wideDiagonalFactor F (Nat.le_add_right p r) lam)ᴴ * U.valᴴ) G)) =
      ((matrixGaussian F p q).prod (gramWithFactor F r (1 : Matrix (Fin q) (Fin q) F))).map
        (fun z => trailingBackground F z.2 + spectralSchurGram F U lam z.1) := by
  let eF : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  letI : SecondCountableTopology F := eF.toHomeomorph.secondCountableTopology
  have hleft : Measurable (fun G : Matrix (Fin (p+r)) (Fin q) F =>
      Wishart.FieldGaussian.matrixGram F (horizontalJoin F
        ((wideDiagonalFactor F (Nat.le_add_right p r) lam)ᴴ * U.valᴴ) G)) :=
    ((Wishart.FieldGaussian.continuous_matrixGram F (p+r) (p+q)).comp
      ((continuous_horizontalJoin F (p+r) p q).comp
        (continuous_const.prodMk continuous_id))).measurable
  have hright : Measurable (fun z : Matrix (Fin p) (Fin q) F × Hermitian F q =>
      trailingBackground F z.2 + spectralSchurGram F U lam z.1) := by
    have hW : Continuous (fun z : Matrix (Fin p) (Fin q) F × Hermitian F q =>
        trailingBackground F (p := p) z.2) := by
      apply Continuous.subtype_mk
      simp only [Submodule.coe_zero, Matrix.conjTranspose_zero]
      fun_prop
    have hG : Continuous (fun z : Matrix (Fin p) (Fin q) F × Hermitian F q =>
        spectralSchurGram F U lam z.1) :=
      (Wishart.FieldGaussian.continuous_matrixGram F p (p+q)).comp
        ((continuous_horizontalJoin F p p q).comp (continuous_const.prodMk continuous_fst))
    exact (hW.add hG).measurable
  rw [← matrixGaussian_split_rows F p r q hF,
    Measure.map_map hleft (continuous_verticalJoin F p r q).measurable,
    ← matrixGaussian_map_gram F r q]
  have hp := Measure.map_prod_map (matrixGaussian F p q) (matrixGaussian F r q)
    (measurable_id : Measurable (@id (Matrix (Fin p) (Fin q) F)))
    (Wishart.FieldGaussian.continuous_matrixGram F r q).measurable
  simp only [Measure.map_id] at hp
  rw [hp, Measure.map_map hright
    (measurable_id.prodMap (Wishart.FieldGaussian.continuous_matrixGram F r q).measurable)]
  congr 1
  exact funext fun z => tallGram_row_split F U lam z.1 z.2

theorem map_prod_different_noise {A B C X : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace X]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite ν] [SFinite ρ]
    (f : A × B → X) (g : A × C → X) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ᵐ a ∂μ, ν.map (fun b => f (a,b)) = ρ.map (fun c => g (a,c))) :
    (μ.prod ν).map f = (μ.prod ρ).map g := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh hf, lintegral_map hh hg]
  change (∫⁻ z, (h ∘ f) z ∂μ.prod ν) = ∫⁻ z, (h ∘ g) z ∂μ.prod ρ
  rw [lintegral_prod _ (hh.comp hf).aemeasurable,
    lintegral_prod _ (hh.comp hg).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hfg] with a ha
  have hfm : Measurable (fun b : B => f (a, b)) := hf.comp (measurable_const.prodMk measurable_id)
  have hgm : Measurable (fun c : C => g (a, c)) := hg.comp (measurable_const.prodMk measurable_id)
  have ha' := congrArg (fun θ : Measure X => ∫⁻ x, h x ∂θ) ha
  rw [lintegral_map hh hfm, lintegral_map hh hgm] at ha'
  exact ha' 

theorem map_assoc_prod {A B C X : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace X]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite ν] [SFinite ρ]
    (f : A × B × C → X) (hf : Measurable f) :
    ((μ.prod ν).prod ρ).map (fun z => f (z.1.1,z.1.2,z.2)) =
      (μ.prod (ν.prod ρ)).map f := by
  rw [← (measurePreserving_prodAssoc μ ν ρ).map_eq,
    Measure.map_map hf MeasurableEquiv.prodAssoc.measurable]
  rfl

end Wishart.FieldGaussian
end
end CanonicalSource58

section CanonicalSource59
/- Source: Wishart/FieldIntegerSchurLaw.lean -/



/-!
# Tall integer Gaussian conditional Schur law

The residual measure is the actual `(n-p)`-row Gram image, even when singular.
The spectral and Gaussian sources are independent, and the full pushforward
is the original `n`-row Gram law. No real-shape density identity is used for
an inadmissible residual parameter.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion ComplexOrder ENNReal
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace Wishart.ComplexMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.FieldCharts

variable {n p q : ℕ}

def integerSchurNoiseLaw (n p q : ℕ) : Measure (SchurNoise p q) :=
  (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ))).prod
    ((matrixGaussian ℂ p q).prod
      (gramMeasure (n-p) (1 : Matrix (Fin q) (Fin q) ℂ)))

instance integerSchurNoiseLaw_probability (n p q : ℕ) :
    IsProbabilityMeasure (integerSchurNoiseLaw n p q) := by
  unfold integerSchurNoiseLaw
  infer_instance

theorem gram_spectral_schur_fibre (r : ℕ)
    (U : unitary (Matrix (Fin p) (Fin p) ℂ)) (lam : Fin p → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) :
    (matrixGaussian ℂ (p+r) q).map
      (fun G => Wishart.FieldGaussian.matrixGram ℂ (horizontalJoin ℂ
        ((wideDiagonalFactor ℂ (Nat.le_add_right p r) lam)ᴴ * U.valᴴ) G)) =
      ((matrixGaussian ℂ p q).prod
        (gramMeasure r (1 : Matrix (Fin q) (Fin q) ℂ))).map
          (fun z => schurInput (unitaryConjugate ℂ U (diagonalHermitian ℂ lam)) z.2 z.1) := by
  have hsplit := tallGram_noise_fibre ℂ (by simp [Complex.finrank_real_complex]) U lam (r := r) (q := q)
  have hstandard : gramWithFactor ℂ r (1 : Matrix (Fin q) (Fin q) ℂ) =
      gramMeasure r (1 : Matrix (Fin q) (Fin q) ℂ) := by
    simp only [gramMeasure,CFC.sqrt_one]
  rw [hstandard] at hsplit
  rw [hsplit]
  have hrot := matrixGaussian_map_unitary_left ℂ (by simp [Complex.finrank_real_complex]) Complex.reLm complex_re_star_mul U (q := q)
  have hp := Measure.map_prod_map (matrixGaussian ℂ p q)
    (gramMeasure r (1 : Matrix (Fin q) (Fin q) ℂ))
    (f := fun Z => U.val * Z)
    (g := id) (by fun_prop) measurable_id
  rw [hrot,Measure.map_id] at hp
  have hm : Measurable (fun z : Matrix (Fin p) (Fin q) ℂ × Hermitian q =>
      schurInput (unitaryConjugate ℂ U (diagonalHermitian ℂ lam)) z.2 z.1) :=
    measurable_schurInput.comp (measurable_const.prodMk measurable_id)
  have h := congrArg (fun μ => μ.map
    (fun z => schurInput (unitaryConjugate ℂ U (diagonalHermitian ℂ lam)) z.2 z.1)) hp
  rw [Measure.map_map hm (by fun_prop)] at h
  have heq : ((fun z : Matrix (Fin p) (Fin q) ℂ × Hermitian q =>
      schurInput (unitaryConjugate ℂ U (diagonalHermitian ℂ lam)) z.2 z.1) ∘
      Prod.map (fun Z => U.val * Z) id) =
      (fun z => trailingBackground ℂ z.2 + spectralSchurGram ℂ U lam z.1) := by
    funext z
    exact schurInput_unitary_diagonal U lam hlam z.2 z.1
  rw [heq] at h
  convert h.symm using 1
  congr 1
  funext z
  apply Subtype.ext
  simp only [Submodule.coe_add, spectralSchurGram, realDiagonal, horizontalJoin,
    Algebra.algebraMap_eq_smul_one, Matrix.star_eq_conjTranspose, Complex.real_smul, mul_one,
    trailingBackground, Wishart.FieldHermitian.fromBlocks, Submodule.coe_zero]

set_option backward.isDefEq.respectTransparency true in
theorem integerSpectralSchurBuild_law (hpn : p ≤ n) :
    ((identityEigenLaw p (n : ℝ)).prod (integerSchurNoiseLaw n p q)).map
      spectralSchurBuild =
        gramMeasure n (1 : Matrix (Fin (p+q)) (Fin (p+q)) ℂ) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hpn
  have hn : (p : ℝ)-1 < ((p+r : ℕ) : ℝ) := by
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    push_cast
    linarith
  letI := identityEigenLaw_isProbability hn
  let κ := identityEigenLaw p ((p+r : ℕ) : ℝ)
  let ρ := TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℂ))
  let ν := matrixGaussian ℂ (p+r) q
  let η := (matrixGaussian ℂ p q).prod
    (gramMeasure r (1 : Matrix (Fin q) (Fin q) ℂ))
  let f : ((Fin p → ℝ) × unitary (Matrix (Fin p) (Fin p) ℂ)) ×
      Matrix (Fin (p+r)) (Fin q) ℂ → Hermitian (p+q) := fun z =>
    Wishart.FieldGaussian.matrixGram ℂ (horizontalJoin ℂ
      ((wideDiagonalFactor ℂ (Nat.le_add_right p r) z.1.1)ᴴ * z.1.2.valᴴ) z.2)
  let g : ((Fin p → ℝ) × unitary (Matrix (Fin p) (Fin p) ℂ)) ×
      (Matrix (Fin p) (Fin q) ℂ × Hermitian q) → Hermitian (p+q) := fun z =>
    spectralSchurBuild (z.1.1,z.1.2,z.2)
  have hf : Measurable f := by
    have hA : Continuous (fun z :
        ((Fin p → ℝ) × unitary (Matrix (Fin p) (Fin p) ℂ)) ×
          Matrix (Fin (p+r)) (Fin q) ℂ =>
        (wideDiagonalFactor ℂ (Nat.le_add_right p r) z.1.1)ᴴ * z.1.2.valᴴ) :=
      (((continuous_wideDiagonalFactor ℂ (Nat.le_add_right p r)).comp
        (continuous_fst.comp continuous_fst)).matrix_conjTranspose).matrix_mul
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).matrix_conjTranspose)
    have hJoin := (continuous_horizontalJoin ℂ (p+r) p q).comp
      (hA.prodMk continuous_snd)
    simpa only [Function.comp_def, f] using
      ((Wishart.FieldGaussian.continuous_matrixGram ℂ (p+r) (p+q)).comp hJoin).measurable
  have hg : Measurable g := measurable_spectralSchurBuild.comp
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hfib := map_prod_different_noise (κ.prod ρ) ν η f g hf hg (by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_identityEigenLaw_mem_chamber hn)]
      with z hz
    exact gram_spectral_schur_fibre r z.2 z.1 (fun i => (hz.2 i).le))
  have hraw := blockGram_law_of_svd ℂ (by simp [Complex.finrank_real_complex]) Complex.reLm complex_re_star_mul κ
    (TauCeti.haarProb (unitary (Matrix (Fin (p+r)) (Fin (p+r)) ℂ))) ρ
    (fun lam => (wideDiagonalFactor ℂ (Nat.le_add_right p r) lam)ᴴ)
    (continuous_wideDiagonalFactor ℂ (Nat.le_add_right p r)).matrix_conjTranspose.measurable
    (matrixGaussian_svd_law_of_ge (Nat.le_add_right p r))
    (1 : Matrix (Fin (p+q)) (Fin (p+q)) ℂ)
  have hassoc : Measurable (fun z : (Fin p → ℝ) ×
      unitary (Matrix (Fin p) (Fin p) ℂ) × Matrix (Fin (p+r)) (Fin q) ℂ =>
        ((z.1, z.2.1), z.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have hfa := hf.comp hassoc
  have hassoclaw := map_assoc_prod κ ρ ν (f ∘ fun z => ((z.1, z.2.1), z.2.2)) hfa
  have hleft : ((κ.prod ρ).prod ν).map f =
      gramMeasure (p+r) (1 : Matrix (Fin (p+q)) (Fin (p+q)) ℂ) := by
    calc
      _ = (κ.prod (ρ.prod ν)).map (f ∘ fun z => ((z.1, z.2.1), z.2.2)) := by
        simpa only [Function.comp_def, Prod.eta] using hassoclaw
      _ = _ := by
        simpa only [Function.comp_def, f, blockGramWithFactor, Matrix.mul_one,
          gramMeasure, CFC.sqrt_one] using hraw
  rw [hfib] at hleft
  have hright := map_assoc_prod κ ρ η spectralSchurBuild measurable_spectralSchurBuild
  rw [hright] at hleft
  simpa only [κ,ρ,η,integerSchurNoiseLaw,Nat.add_sub_cancel_left] using hleft

end Wishart.ComplexMatrix

namespace Wishart.QuaternionMatrix
open scoped Matrix.Norms.Frobenius
open Wishart.FieldGaussian Wishart.FieldCharts

variable {n p q : ℕ}

def integerSchurNoiseLaw (n p q : ℕ) : Measure (SchurNoise p q) :=
  (TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))).prod
    ((matrixGaussian ℍ[ℝ] p q).prod
      (gramMeasure (n-p) (1 : Matrix (Fin q) (Fin q) ℍ[ℝ])))

instance integerSchurNoiseLaw_probability (n p q : ℕ) :
    IsProbabilityMeasure (integerSchurNoiseLaw n p q) := by
  unfold integerSchurNoiseLaw
  infer_instance

theorem gram_spectral_schur_fibre (r : ℕ)
    (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) (lam : Fin p → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) :
    (matrixGaussian ℍ[ℝ] (p+r) q).map
      (fun G => Wishart.FieldGaussian.matrixGram ℍ[ℝ] (horizontalJoin ℍ[ℝ]
        ((wideDiagonalFactor ℍ[ℝ] (Nat.le_add_right p r) lam)ᴴ * U.valᴴ) G)) =
      ((matrixGaussian ℍ[ℝ] p q).prod
        (gramMeasure r (1 : Matrix (Fin q) (Fin q) ℍ[ℝ]))).map
          (fun z => schurInput (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) z.2 z.1) := by
  have hsplit := tallGram_noise_fibre ℍ[ℝ] (by simp [Quaternion.finrank_eq_four]) U lam (r := r) (q := q)
  have hstandard : gramWithFactor ℍ[ℝ] r (1 : Matrix (Fin q) (Fin q) ℍ[ℝ]) =
      gramMeasure r (1 : Matrix (Fin q) (Fin q) ℍ[ℝ]) := by
    simp only [gramMeasure,sqrt_one_matrix]
  rw [hstandard] at hsplit
  rw [hsplit]
  have hrot := matrixGaussian_map_unitary_left ℍ[ℝ] (by simp [Quaternion.finrank_eq_four]) (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) quaternion_re_star_mul U (q := q)
  have hp := Measure.map_prod_map (matrixGaussian ℍ[ℝ] p q)
    (gramMeasure r (1 : Matrix (Fin q) (Fin q) ℍ[ℝ]))
    (f := fun Z => U.val * Z)
    (g := id) (by fun_prop) measurable_id
  rw [hrot,Measure.map_id] at hp
  have hm : Measurable (fun z : Matrix (Fin p) (Fin q) ℍ[ℝ] × Hermitian q =>
      schurInput (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) z.2 z.1) :=
    measurable_schurInput.comp (measurable_const.prodMk measurable_id)
  have h := congrArg (fun μ => μ.map
    (fun z => schurInput (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) z.2 z.1)) hp
  rw [Measure.map_map hm (by fun_prop)] at h
  have heq : ((fun z : Matrix (Fin p) (Fin q) ℍ[ℝ] × Hermitian q =>
      schurInput (unitaryConjugate ℍ[ℝ] U (Wishart.FieldCharts.diagonalHermitian ℍ[ℝ] lam)) z.2 z.1) ∘
      Prod.map (fun Z => U.val * Z) id) =
      (fun z => trailingBackground ℍ[ℝ] z.2 + spectralSchurGram ℍ[ℝ] U lam z.1) := by
    funext z
    exact schurInput_unitary_diagonal U lam hlam z.2 z.1
  rw [heq] at h
  convert h.symm using 1
  congr 1
  funext z
  apply Subtype.ext
  simp only [Submodule.coe_add, spectralSchurGram, realDiagonal, horizontalJoin,
    Algebra.algebraMap_eq_smul_one, Matrix.star_eq_conjTranspose,
    ← Quaternion.coe_mul_eq_smul, mul_one, trailingBackground,
    Wishart.FieldHermitian.fromBlocks, Submodule.coe_zero]

set_option backward.isDefEq.respectTransparency true in
theorem integerSpectralSchurBuild_law (hpn : p ≤ n) :
    ((identityEigenLaw p (n : ℝ)).prod (integerSchurNoiseLaw n p q)).map
      spectralSchurBuild =
        gramMeasure n (1 : Matrix (Fin (p+q)) (Fin (p+q)) ℍ[ℝ]) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hpn
  have hn : (p : ℝ)-1 < ((p+r : ℕ) : ℝ) := by
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    push_cast
    linarith
  letI := identityEigenLaw_isProbability hn
  let κ := identityEigenLaw p ((p+r : ℕ) : ℝ)
  let ρ := TauCeti.haarProb (unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]))
  let ν := matrixGaussian ℍ[ℝ] (p+r) q
  let η := (matrixGaussian ℍ[ℝ] p q).prod
    (gramMeasure r (1 : Matrix (Fin q) (Fin q) ℍ[ℝ]))
  let f : ((Fin p → ℝ) × unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) ×
      Matrix (Fin (p+r)) (Fin q) ℍ[ℝ] → Hermitian (p+q) := fun z =>
    Wishart.FieldGaussian.matrixGram ℍ[ℝ] (horizontalJoin ℍ[ℝ]
      ((wideDiagonalFactor ℍ[ℝ] (Nat.le_add_right p r) z.1.1)ᴴ * z.1.2.valᴴ) z.2)
  let g : ((Fin p → ℝ) × unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) ×
      (Matrix (Fin p) (Fin q) ℍ[ℝ] × Hermitian q) → Hermitian (p+q) := fun z =>
    spectralSchurBuild (z.1.1,z.1.2,z.2)
  have hf : Measurable f := by
    set_option backward.isDefEq.respectTransparency false in
    have hA : Continuous (fun z :
        ((Fin p → ℝ) × unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) ×
          Matrix (Fin (p+r)) (Fin q) ℍ[ℝ] =>
        (wideDiagonalFactor ℍ[ℝ] (Nat.le_add_right p r) z.1.1)ᴴ * z.1.2.valᴴ) :=
      (((continuous_wideDiagonalFactor ℍ[ℝ] (Nat.le_add_right p r)).comp
        (continuous_fst.comp continuous_fst)).matrix_conjTranspose).matrix_mul
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).matrix_conjTranspose)
    have hJoin := (continuous_horizontalJoin ℍ[ℝ] (p+r) p q).comp
      (hA.prodMk continuous_snd)
    simpa only [Function.comp_def, f] using
      ((Wishart.FieldGaussian.continuous_matrixGram ℍ[ℝ] (p+r) (p+q)).comp hJoin).measurable
  have hg : Measurable g := measurable_spectralSchurBuild.comp
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hfib := map_prod_different_noise (κ.prod ρ) ν η f g hf hg (by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_identityEigenLaw_mem_chamber hn)]
      with z hz
    exact gram_spectral_schur_fibre r z.2 z.1 (fun i => (hz.2 i).le))
  have hraw := blockGram_law_of_svd ℍ[ℝ] (by simp [Quaternion.finrank_eq_four]) (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) quaternion_re_star_mul κ
    (TauCeti.haarProb (unitary (Matrix (Fin (p+r)) (Fin (p+r)) ℍ[ℝ]))) ρ
    (fun lam => (wideDiagonalFactor ℍ[ℝ] (Nat.le_add_right p r) lam)ᴴ)
    (continuous_wideDiagonalFactor ℍ[ℝ] (Nat.le_add_right p r)).matrix_conjTranspose.measurable
    (matrixGaussian_svd_law_of_ge (Nat.le_add_right p r))
    (1 : Matrix (Fin (p+q)) (Fin (p+q)) ℍ[ℝ])
  have hassoc : Measurable (fun z : (Fin p → ℝ) ×
      unitary (Matrix (Fin p) (Fin p) ℍ[ℝ]) × Matrix (Fin (p+r)) (Fin q) ℍ[ℝ] =>
        ((z.1, z.2.1), z.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have hfa := hf.comp hassoc
  have hassoclaw := map_assoc_prod κ ρ ν (f ∘ fun z => ((z.1, z.2.1), z.2.2)) hfa
  have hleft : ((κ.prod ρ).prod ν).map f =
      gramMeasure (p+r) (1 : Matrix (Fin (p+q)) (Fin (p+q)) ℍ[ℝ]) := by
    calc
      _ = (κ.prod (ρ.prod ν)).map (f ∘ fun z => ((z.1, z.2.1), z.2.2)) := by
        simpa only [Function.comp_def, Prod.eta] using hassoclaw
      _ = _ := by
        simpa only [Function.comp_def, f, blockGramWithFactor, Matrix.mul_one,
          gramMeasure, sqrt_one_matrix] using hraw
  rw [hfib] at hleft
  have hright := map_assoc_prod κ ρ η spectralSchurBuild measurable_spectralSchurBuild
  rw [hright] at hleft
  simpa only [κ,ρ,η,integerSchurNoiseLaw,Nat.add_sub_cancel_left] using hleft

end Wishart.QuaternionMatrix

end
end CanonicalSource59
