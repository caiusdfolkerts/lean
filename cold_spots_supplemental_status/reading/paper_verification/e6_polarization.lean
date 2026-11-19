module

public import PaperVerification.E6Phases
public import PaperVerification.FiniteThree

@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def l6GaussianTerm (α : ℝ) (z : TriTriple) (r : ZMod 3) : ℝ :=
  ∏ i, triangularGaussian α (z i-triPhasePoint r)

lemma l6GaussianTerm_pos {α : ℝ} (hα : 0 < α) (z : TriTriple) (r : ZMod 3) :
    0 < l6GaussianTerm α z r := Finset.prod_pos (fun i hi ↦ triangularGaussian_pos hα _)

lemma triangularGaussian_neg_two_shift (α : ℝ) (z : TriPoint) :
    triangularGaussian α (z-(2:ℝ)•triC)=triangularGaussian α (z+triC) := by
  have he : z-(2:ℝ)•triC=(z+triC)+eisEmbed (-1,1) := by
    ext <;> dsimp [triC,eisEmbed] <;> ring
  rw [he,triangularGaussian_periodic]

lemma prod_triangular_gaussian_phases (α : ℝ) (z : TriPoint) :
    (∏ r : ZMod 3, triangularGaussian α (z-triPhasePoint r))=triangularProduct α z := by
  rw [prod_zmod_three]
  norm_num [triPhasePoint,triangularGaussian_neg_two_shift,triangularProduct,mul_assoc,mul_comm,mul_left_comm]

theorem l6GaussianTerm_product (α : ℝ) (z : TriTriple) :
    l6GaussianTerm α z 0*l6GaussianTerm α z 1*l6GaussianTerm α z 2 =
      triangularProduct α (z 0)*triangularProduct α (z 1)*triangularProduct α (z 2) := by
  rw [← prod_zmod_three]
  unfold l6GaussianTerm
  rw [Finset.prod_comm]
  simp only [prod_triangular_gaussian_phases]
  simp [Fin.prod_univ_succ,mul_assoc]

theorem l6Gaussian_sum_terms {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    l6Gaussian α z=l6GaussianTerm α z 0+l6GaussianTerm α z 1+l6GaussianTerm α z 2 := by
  rw [l6Gaussian_cosets hα,sum_zmod_three]
  rfl

lemma three_product_lower (K x y z : ℝ) (hK : 0 < K) (hx : K ≤ x) (hy : K ≤ y) (hz : K ≤ z) :
    K^3 ≤ x*y*z := by
  have hxy : K*K ≤ x*y := mul_le_mul hx hy hK.le (hK.le.trans hx)
  have h := mul_le_mul hxy hz hK.le (mul_nonneg (hK.le.trans hx) (hK.le.trans hy))
  nlinarith only [h]

lemma three_product_equality (K x y z : ℝ) (hK : 0 < K)
    (hx : K ≤ x) (hy : K ≤ y) (hz : K ≤ z) (he : x*y*z=K^3) :
    x=K ∧ y=K ∧ z=K := by
  have hp : 0 < K*K := mul_pos hK hK
  have hX : x*K*K ≤ x*y*z := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul hy hz hK.le (hK.le.trans hy)) (hK.le.trans hx)
    simpa [mul_assoc] using h
  have hY : K*y*K ≤ x*y*z := by
    exact mul_le_mul (mul_le_mul_of_nonneg_right hx (hK.le.trans hy)) hz hK.le
      (mul_nonneg (hK.le.trans hx) (hK.le.trans hy))
  have hZ : K*K*z ≤ x*y*z := mul_le_mul_of_nonneg_right
    (mul_le_mul hx hy hK.le (hK.le.trans hx)) (hK.le.trans hz)
  refine ⟨le_antisymm ?_ hx,le_antisymm ?_ hy,le_antisymm ?_ hz⟩
  · apply (mul_le_mul_iff_of_pos_right hp).mp
    calc
      x*(K*K)=x*K*K := by ring
      _ ≤ x*y*z := hX
      _ = K^3 := he
      _ = K*(K*K) := by ring
  · apply (mul_le_mul_iff_of_pos_right hp).mp
    calc
      y*(K*K)=K*y*K := by ring
      _ ≤ x*y*z := hY
      _ = K^3 := he
      _ = K*(K*K) := by ring
  · apply (mul_le_mul_iff_of_pos_right hp).mp
    calc
      z*(K*K)=K*K*z := by ring
      _ ≤ x*y*z := hZ
      _ = K^3 := he
      _ = K*(K*K) := by ring

theorem l6Gaussian_lower {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    3*triangularGaussian α 0*triangularGaussian α triC^2 ≤ l6Gaussian α z := by
  let K := triangularGaussian α 0*triangularGaussian α triC^2
  have hK : 0 < K := mul_pos (triangularGaussian_pos hα _) (sq_pos_of_pos (triangularGaussian_pos hα _))
  have h0 := l6GaussianTerm_pos hα z 0
  have h1 := l6GaussianTerm_pos hα z 1
  have h2 := l6GaussianTerm_pos hα z 2
  have h := (three_term_amgm _ _ _ h0.le h1.le h2.le).1
  rw [l6GaussianTerm_product] at h
  have hp := three_product_lower K _ _ _ hK (triangularProduct_minimum hα (z 0))
    (triangularProduct_minimum hα (z 1)) (triangularProduct_minimum hα (z 2))
  rw [← l6Gaussian_sum_terms hα] at h
  have hs : 0 ≤ l6Gaussian α z := by rw [l6Gaussian_sum_terms hα]; positivity
  have hc : (3*K)^3 ≤ l6Gaussian α z^3 := by nlinarith only [h,hp]
  have hl : 3*K ≤ l6Gaussian α z := le_of_pow_le_pow_left₀ (by norm_num : (3:ℕ)≠0) hs hc
  dsimp [K] at hl
  nlinarith only [hl]

theorem l6Gaussian_equality_iff {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    l6Gaussian α z=3*triangularGaussian α 0*triangularGaussian α triC^2 ↔
      E6BalancedPhases z := by
  constructor
  · intro heq
    let a := triangularGaussian α 0
    let b := triangularGaussian α triC
    let K := a*b^2
    have ha : 0 < a := triangularGaussian_pos hα _
    have hb : 0 < b := triangularGaussian_pos hα _
    have hK : 0 < K := by dsimp [K]; positivity
    have h0 := l6GaussianTerm_pos hα z 0
    have h1 := l6GaussianTerm_pos hα z 1
    have h2 := l6GaussianTerm_pos hα z 2
    have ham := (three_term_amgm _ _ _ h0.le h1.le h2.le)
    have hp := three_product_lower K _ _ _ hK (triangularProduct_minimum hα (z 0))
      (triangularProduct_minimum hα (z 1)) (triangularProduct_minimum hα (z 2))
    have hsum : l6GaussianTerm α z 0+l6GaussianTerm α z 1+l6GaussianTerm α z 2=3*K := by
      rw [← l6Gaussian_sum_terms hα,heq]
      dsimp [K,a,b]
      ring
    have hprod : triangularProduct α (z 0)*triangularProduct α (z 1)*triangularProduct α (z 2)=K^3 := by
      have hh := ham.1
      rw [hsum,l6GaussianTerm_product] at hh
      nlinarith only [hh,hp]
    have heach := three_product_equality K _ _ _ hK (triangularProduct_minimum hα (z 0))
      (triangularProduct_minimum hα (z 1)) (triangularProduct_minimum hα (z 2)) hprod
    have hph : ∀ i, TriPhase (z i) := by
      intro i
      apply (triangularProduct_equality_iff hα _).mp
      fin_cases i
      · exact heach.1
      · exact heach.2.1
      · exact heach.2.2
    obtain ⟨r,hr⟩ := (exists_E6PhaseConfiguration_iff z).mpr hph
    have heterms : l6GaussianTerm α z 0=l6GaussianTerm α z 1 ∧
        l6GaussianTerm α z 1=l6GaussianTerm α z 2 := by
      apply ham.2.mp
      rw [hsum,l6GaussianTerm_product,hprod]
      ring
    have ht (s : ZMod 3) : l6GaussianTerm α z s=e6GaussianProfile a b r s := by
      obtain ⟨m,hm⟩ := hr
      apply Finset.prod_congr rfl
      intro i hi
      rw [hm i,show eisEmbed (m i)+triPhasePoint (r i)-triPhasePoint s =
        (triPhasePoint (r i)-triPhasePoint s)+eisEmbed (m i) by abel,
        triangularGaussian_periodic,triangularGaussian_phases hα]
    simp only [ht] at heterms
    exact ⟨r,(e6GaussianProfile_eq_iff a b hb (triangularGaussian_c_lt_zero hα) r).mp heterms,hr⟩
  · rintro ⟨r,hr,hz⟩
    rw [l6Gaussian_of_phases hα hz]
    simp only [e6GaussianProfile_bijective _ _ hr,Finset.sum_const,Finset.card_univ,
      ZMod.card,nsmul_eq_mul]
    ring

end PaperVerification.ColdSpots
