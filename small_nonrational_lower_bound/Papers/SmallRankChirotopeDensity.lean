module
public import Papers.ChirotopeDensity

@[expose] public section

noncomputable section

open Matrix Set Filter Topology

namespace Papers.RationalityTen.ChirotopeDensity

open PlaneRationalization

noncomputable def expand {n r : ℕ} {p : Fin n → Fin r → ℝ}
    (R : ProjectiveRepresentatives p) (q : Fin n → Fin r → ℝ) (c : Fin n → ℝ) :
    Fin n → Fin r → ℝ :=
  fun i => if p i = 0 then 0 else c i • q (R.index i)

theorem expand_base {n r : ℕ} {p : Fin n → Fin r → ℝ}
    (R : ProjectiveRepresentatives p) : expand R p R.coefficient = p := by
  classical
  ext i j
  by_cases hi : p i = 0
  · simp [expand,hi]
  · simpa [expand,hi] using congrFun (R.eq_smul i hi) j

theorem continuous_expand {n r : ℕ} {p : Fin n → Fin r → ℝ}
    (R : ProjectiveRepresentatives p) :
    Continuous (fun z : (Fin n → Fin r → ℝ) × (Fin n → ℝ) => expand R z.1 z.2) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : p i = 0
  · simp only [expand,if_pos hi]
    exact continuous_const
  · simp only [expand,if_neg hi]
    exact ((continuous_apply i).comp continuous_snd).smul
      ((continuous_apply (R.index i)).comp continuous_fst)

theorem expand_rational {n r : ℕ} {p q : Fin n → Fin r → ℝ}
    (R : ProjectiveRepresentatives p) {c : Fin n → ℝ}
    (hq : RationalCoordinates q) (hc : ∀ i, RatScalar (c i)) :
    RationalCoordinates (expand R q c) := by
  classical
  intro i j
  by_cases hi : p i = 0
  · exact ⟨0,by simp [expand,hi]⟩
  · simpa [expand,hi,Pi.smul_apply,smul_eq_mul] using (hc i).mul (hq (R.index i) j)

theorem pair_det_smul (a b : ℝ) (x y : Fin 2 → ℝ) :
    (Matrix.of ![a • x,b • y]).det = (a*b) * (Matrix.of ![x,y]).det := by
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,Pi.smul_apply,smul_eq_mul]
  ring

theorem expand_rank_two_zero_minors {n : ℕ} {p : Fin n → Fin 2 → ℝ}
    (R : ProjectiveRepresentatives p) (q : Fin n → Fin 2 → ℝ) (c : Fin n → ℝ) :
    PreservesZeroMinors p (expand R q c) := by
  classical
  intro b hb
  let i := b 0
  let j := b 1
  by_cases hi : p i = 0
  · simpa [minor,expand,i,Matrix.det_fin_two,hi]
  by_cases hj : p j = 0
  · simpa [minor,expand,j,Matrix.det_fin_two,hj]
  have hdet : (Matrix.of ![p i,p j]).det = 0 := by
    simpa [minor,Matrix.det_fin_two,i,j] using hb
  have hindex : R.index i = R.index j := by
    by_contra hij
    have hli := R.independent (R.index i) (R.index_mem i hi)
      (R.index j) (R.index_mem j hj) hij
    have hunit : IsUnit (Matrix.of ![p (R.index i),p (R.index j)]) :=
      Matrix.linearIndependent_row_iff_isUnit.mp hli
    have hrepdet : (Matrix.of ![p (R.index i),p (R.index j)]).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
    rw [← R.eq_smul i hi,← R.eq_smul j hj,pair_det_smul] at hdet
    exact mul_ne_zero
      (mul_ne_zero (R.coefficient_ne_zero i hi) (R.coefficient_ne_zero j hj))
      hrepdet hdet
  have hout : (Matrix.of ![expand R q c i,expand R q c j]).det = 0 := by
    simp only [expand,if_neg hi,if_neg hj]
    rw [pair_det_smul,hindex]
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  simpa only [minor, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, i, j] using hout

/-- Rank-two oriented matroids have rational realizations dense in every
real realization, with no restriction on the number of labels. -/
theorem rank_two_density {n : ℕ} (p : Fin n → Fin 2 → ℝ) :
    p ∈ closure (RationalRealizations p) := by
  apply density_of_zero_minor_density
  obtain ⟨R⟩ := exists_projectiveRepresentatives p
  have hprod : (p,R.coefficient) ∈ closure
      ({q : Fin n → Fin 2 → ℝ | RationalCoordinates q} ×ˢ
        {c : Fin n → ℝ | ∀ i, RatScalar (c i)}) := by
    rw [closure_prod_eq]
    exact ⟨rationalCoordinates_dense n 2 p,scalarCoordinates_dense n R.coefficient⟩
  let F := fun z : (Fin n → Fin 2 → ℝ) × (Fin n → ℝ) => expand R z.1 z.2
  have hcl : p ∈ closure (F '' ({q : Fin n → Fin 2 → ℝ | RationalCoordinates q} ×ˢ
      {c : Fin n → ℝ | ∀ i, RatScalar (c i)})) := by
    simpa only [F,expand_base] using
      mem_closure_image (continuous_expand R).continuousAt hprod
  apply closure_mono (s := F '' _) ?_ hcl
  rintro _ ⟨⟨q,c⟩,⟨hq,hc⟩,rfl⟩
  exact ⟨expand_rational R hq hc,expand_rank_two_zero_minors R q c⟩

noncomputable def zeroMask {n r : ℕ} (p q : Fin n → Fin r → ℝ) :
    Fin n → Fin r → ℝ :=
  fun i => if p i = 0 then 0 else q i

theorem zeroMask_base {n r : ℕ} (p : Fin n → Fin r → ℝ) :
    zeroMask p p = p := by
  classical
  ext i j
  by_cases hi : p i = 0 <;> simp [zeroMask,hi]

theorem continuous_zeroMask {n r : ℕ} (p : Fin n → Fin r → ℝ) :
    Continuous (zeroMask p) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : p i = 0
  · simp only [zeroMask,if_pos hi]
    exact continuous_const
  · simp only [zeroMask,if_neg hi]
    exact continuous_apply i

theorem zeroMask_rational {n r : ℕ} (p : Fin n → Fin r → ℝ)
    {q : Fin n → Fin r → ℝ} (hq : RationalCoordinates q) :
    RationalCoordinates (zeroMask p q) := by
  classical
  intro i j
  by_cases hi : p i = 0
  · exact ⟨0,by simp [zeroMask,hi]⟩
  · simpa [zeroMask,hi] using hq i j

theorem zeroMask_rank_one_zero_minors {n : ℕ} (p q : Fin n → Fin 1 → ℝ) :
    PreservesZeroMinors p (zeroMask p q) := by
  classical
  intro b hb
  have hz : p (b 0) = 0 := by
    ext j
    fin_cases j
    simpa [minor,Matrix.det_fin_one] using hb
  simp [minor,Matrix.det_fin_one,zeroMask,hz]

theorem rank_one_density {n : ℕ} (p : Fin n → Fin 1 → ℝ) :
    p ∈ closure (RationalRealizations p) := by
  apply density_of_zero_minor_density
  have hcl : p ∈ closure (zeroMask p '' {q | RationalCoordinates q}) := by
    simpa only [zeroMask_base] using
      mem_closure_image (continuous_zeroMask p).continuousAt (rationalCoordinates_dense n 1 p)
  apply closure_mono (s := zeroMask p '' _) ?_ hcl
  rintro _ ⟨q,hq,rfl⟩
  exact ⟨zeroMask_rational p hq,zeroMask_rank_one_zero_minors p q⟩

theorem rank_zero_density {n : ℕ} (p : Fin n → Fin 0 → ℝ) :
    p ∈ closure (RationalRealizations p) := by
  apply subset_closure
  refine ⟨?_,fun _ => rfl⟩
  intro i j
  exact Fin.elim0 j

/-- Full labelled rational density in ranks zero through three on at most
eight elements. In rank three this is Lemma 10, including its collinear,
repeated-point and zero-vector extensions. -/
theorem rational_chirotope_dense_le_three
    {n r : ℕ} (hn : n ≤ 8) (hr : r ≤ 3) (p : Fin n → Fin r → ℝ) :
    p ∈ closure (RationalRealizations p) := by
  rcases r with _ | r
  · exact rank_zero_density p
  rcases r with _ | r
  · exact rank_one_density p
  rcases r with _ | r
  · exact rank_two_density p
  rcases r with _ | r
  · exact rank_three_density hn p
  omega

end Papers.RationalityTen.ChirotopeDensity
