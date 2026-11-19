module
public import Papers.RankThreeIncidenceGeometry
public import Papers.ProjectiveFrameNormalization
public import Papers.RationalityTenRankThreeContradictions
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section

/-!
# The small nonreal projective incidence patterns

The hypotheses below concern actual real point and line vectors. Pair
independence expresses distinct projective points and lines. Every
normalization denominator is proved nonzero from these hypotheses, and the
frame minors are derived from the prescribed incidences themselves.
-/

namespace Papers.RationalityTen

def fanoSupports : Fin 7 → Finset (Fin 7) :=
  ![{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6}, {2,4,5}]

/-- No seven distinct real projective points and seven distinct real
projective lines realize the Fano incidence pattern. -/
theorem fano_realization_impossible
    (p l : Fin 7 → PlaneVector)
    (hpoints : ∀ i j, i ≠ j → LinearIndependent ℝ ![p i, p j])
    (hlines : ∀ i j, i ≠ j → LinearIndependent ℝ ![l i, l j])
    (hinc : ∀ i j, j ∈ fanoSupports i → dotProduct (l i) (p j) = 0) :
    False := by
  have h013 : (Matrix.of ![p 0,p 1,p 3]).det ≠ 0 :=
    triple_det_ne_zero_of_joining_lines (p 0) (p 1) (p 3) (l 0) (l 1)
      (hpoints 0 1 (by decide)) (hpoints 0 3 (by decide))
      (hlines 0 1 (by decide))
      (hinc 0 0 (by decide)) (hinc 0 1 (by decide))
      (hinc 1 0 (by decide)) (hinc 1 3 (by decide))
  have h613 : (Matrix.of ![p 6,p 1,p 3]).det ≠ 0 :=
    triple_det_ne_zero_of_joining_lines (p 6) (p 1) (p 3) (l 4) (l 5)
      (hpoints 6 1 (by decide)) (hpoints 6 3 (by decide))
      (hlines 4 5 (by decide))
      (hinc 4 6 (by decide)) (hinc 4 1 (by decide))
      (hinc 5 6 (by decide)) (hinc 5 3 (by decide))
  have h063 : (Matrix.of ![p 0,p 6,p 3]).det ≠ 0 :=
    triple_det_ne_zero_of_joining_lines (p 0) (p 6) (p 3) (l 2) (l 1)
      (hpoints 0 6 (by decide)) (hpoints 0 3 (by decide))
      (hlines 2 1 (by decide))
      (hinc 2 0 (by decide)) (hinc 2 6 (by decide))
      (hinc 1 0 (by decide)) (hinc 1 3 (by decide))
  have h016 : (Matrix.of ![p 0,p 1,p 6]).det ≠ 0 :=
    triple_det_ne_zero_of_joining_lines (p 0) (p 1) (p 6) (l 0) (l 2)
      (hpoints 0 1 (by decide)) (hpoints 0 6 (by decide))
      (hlines 0 2 (by decide))
      (hinc 0 0 (by decide)) (hinc 0 1 (by decide))
      (hinc 2 0 (by decide)) (hinc 2 6 (by decide))
  let b : Fin 3 → Fin 7 := ![0,1,3]
  have hb : Function.Injective b := by decide
  have hbd : ∀ i, b i ≠ (6 : Fin 7) := by decide
  have hA : (Matrix.of (fun i => p (b i))).det ≠ 0 := by
    convert h013 using 1
    congr 1
    ext i j
    fin_cases i <;> rfl
  have hreplace : ∀ i,
      ((Matrix.of (fun j => p (b j))).updateRow i (p 6)).det ≠ 0 := by
    intro i
    fin_cases i
    · convert h613 using 1
      congr 1
      ext i j
      fin_cases i <;> rfl
    · convert h063 using 1
      congr 1
      ext i j
      fin_cases i <;> rfl
    · convert h016 using 1
      congr 1
      ext i j
      fin_cases i <;> rfl
  obtain ⟨q, hqb, hq6, hminor, hpair⟩ :=
    exists_normalized_projective_frame p b hb 6 hbd hA hreplace
  have hq0 : q 0 = Pi.single (0 : Fin 3) 1 := hqb 0
  have hq1 : q 1 = Pi.single (1 : Fin 3) 1 := hqb 1
  have hq3 : q 3 = Pi.single (2 : Fin 3) 1 := hqb 2
  have hl : ∀ i, l i ≠ 0 := by
    intro i
    obtain ⟨j, hji⟩ := exists_ne i
    simpa using (hlines i j hji.symm).ne_zero 0
  have hzero (a i j k : Fin 7)
      (hi : i ∈ fanoSupports a) (hj : j ∈ fanoSupports a)
      (hk : k ∈ fanoSupports a) :
      (Matrix.of ![q i,q j,q k]).det = 0 := by
    apply (triple_zero_iff_of_selection_zero_iff p q hminor i j k).2
    exact triple_det_zero_of_incident_line (p i) (p j) (p k) (l a) (hl a)
      (hinc a i hi) (hinc a j hj) (hinc a k hk)
  have h22 : q 2 2 = 0 := by
    simpa [Matrix.det_fin_three, hq0, hq1, Pi.single_apply] using
      hzero 0 0 1 2 (by decide) (by decide) (by decide)
  have h41 : q 4 1 = 0 := by
    simpa [Matrix.det_fin_three, hq0, hq3, Pi.single_apply] using
      hzero 1 0 3 4 (by decide) (by decide) (by decide)
  have h50 : q 5 0 = 0 := by
    simpa [Matrix.det_fin_three, hq1, hq3, Pi.single_apply] using
      hzero 3 1 3 5 (by decide) (by decide) (by decide)
  have h21 : q 2 1 ≠ 0 := by
    intro h21
    have hp : LinearIndependent ℝ ![Pi.single (0 : Fin 3) 1, q 2] := by
      simpa only [hq0] using hpair 0 2 (hpoints 0 2 (by decide))
    obtain ⟨j, hj, hjv⟩ := independent_basis_point_has_other_coordinate 0 (q 2) hp
    fin_cases j
    · exact hj rfl
    · exact hjv h21
    · exact hjv h22
  have h42 : q 4 2 ≠ 0 := by
    intro h42
    have hp : LinearIndependent ℝ ![Pi.single (0 : Fin 3) 1, q 4] := by
      simpa only [hq0] using hpair 0 4 (hpoints 0 4 (by decide))
    obtain ⟨j, hj, hjv⟩ := independent_basis_point_has_other_coordinate 0 (q 4) hp
    fin_cases j
    · exact hj rfl
    · exact hjv h41
    · exact hjv h42
  have h52 : q 5 2 ≠ 0 := by
    intro h52
    have hp : LinearIndependent ℝ ![Pi.single (1 : Fin 3) 1, q 5] := by
      simpa only [hq1] using hpair 1 5 (hpoints 1 5 (by decide))
    obtain ⟨j, hj, hjv⟩ := independent_basis_point_has_other_coordinate 1 (q 5) hp
    fin_cases j
    · exact hjv h50
    · exact hj rfl
    · exact hjv h52
  let c : Fin 7 → ℝ := ![1,1,(q 2 1)⁻¹,1,(q 4 2)⁻¹,(q 5 2)⁻¹,1]
  let r : Fin 7 → PlaneVector := fun i => c i • q i
  let u := (q 2 1)⁻¹ * q 2 0
  let v := (q 4 2)⁻¹ * q 4 0
  let w := (q 5 2)⁻¹ * q 5 1
  have hr0 : r 0 = ![1,0,0] := by
    ext j
    fin_cases j <;> simp [r,c,hq0,Pi.single_apply]
  have hr1 : r 1 = ![0,1,0] := by
    ext j
    fin_cases j <;> simp [r,c,hq1,Pi.single_apply]
  have hr2 : r 2 = ![u,1,0] := by
    ext j
    fin_cases j <;> simp [r,c,u,Pi.smul_apply,smul_eq_mul,h21,h22]
  have hr3 : r 3 = ![0,0,1] := by
    ext j
    fin_cases j <;> simp [r,c,hq3,Pi.single_apply]
  have hr4 : r 4 = ![v,0,1] := by
    ext j
    fin_cases j <;> simp [r,c,v,Pi.smul_apply,smul_eq_mul,h41,h42]
  have hr5 : r 5 = ![0,w,1] := by
    ext j
    fin_cases j <;> simp [r,c,w,Pi.smul_apply,smul_eq_mul,h50,h52]
  have hr6 : r 6 = ![1,1,1] := by
    ext j
    fin_cases j <;> simp [r,c,hq6]
  have hrzero (i j k : Fin 7) (h : (Matrix.of ![q i,q j,q k]).det = 0) :
      (Matrix.of ![r i,r j,r k]).det = 0 := by
    have hs := det_rows_smul_zero ![q i,q j,q k] ![c i,c j,c k] h
    convert hs using 1
    congr 1
    ext a b
    fin_cases a <;> rfl
  apply RankThreeContradictions.fano_normalized_impossible u v w
  · simpa [RankThreeContradictions.determinant,hr1,hr4,hr6] using
      hrzero 1 4 6 (hzero 4 1 4 6 (by decide) (by decide) (by decide))
  · simpa [RankThreeContradictions.determinant,hr2,hr3,hr6] using
      hrzero 2 3 6 (hzero 5 2 3 6 (by decide) (by decide) (by decide))
  · simpa [RankThreeContradictions.determinant,hr0,hr5,hr6] using
      hrzero 0 5 6 (hzero 2 0 5 6 (by decide) (by decide) (by decide))
  · simpa [RankThreeContradictions.determinant,hr2,hr4,hr5] using
      hrzero 2 4 5 (hzero 6 2 4 5 (by decide) (by decide) (by decide))

def maclaneSupports : Fin 8 → Finset (Fin 8) :=
  ![{0,2,4}, {1,3,5}, {0,3,6}, {1,2,7},
    {0,5,7}, {1,4,6}, {2,5,6}, {3,4,7}]

/-- The eight-point Möbius–Kantor (MacLane) incidence pattern has no real
projective realization with distinct points and distinct lines. -/
theorem maclane_realization_impossible
    (p l : Fin 8 → PlaneVector)
    (hpoints : ∀ i j, i ≠ j → LinearIndependent ℝ ![p i, p j])
    (hlines : ∀ i j, i ≠ j → LinearIndependent ℝ ![l i, l j])
    (hinc : ∀ i j, j ∈ maclaneSupports i → dotProduct (l i) (p j) = 0) :
    False := by
  have h012 : (Matrix.of ![p 0,p 1,p 2]).det ≠ 0 := by
    have h := triple_det_ne_zero_of_joining_lines (p 2) (p 0) (p 1) (l 0) (l 3)
      (hpoints 2 0 (by decide)) (hpoints 2 1 (by decide))
      (hlines 0 3 (by decide))
      (hinc 0 2 (by decide)) (hinc 0 0 (by decide))
      (hinc 3 2 (by decide)) (hinc 3 1 (by decide))
    rw [triple_det_cycle] at h
    exact h
  have h312 : (Matrix.of ![p 3,p 1,p 2]).det ≠ 0 := by
    have h := triple_det_ne_zero_of_joining_lines (p 1) (p 2) (p 3) (l 3) (l 1)
      (hpoints 1 2 (by decide)) (hpoints 1 3 (by decide))
      (hlines 3 1 (by decide))
      (hinc 3 1 (by decide)) (hinc 3 2 (by decide))
      (hinc 1 1 (by decide)) (hinc 1 3 (by decide))
    rw [← triple_det_cycle] at h
    exact h
  have h032 : (Matrix.of ![p 0,p 3,p 2]).det ≠ 0 :=
    triple_det_ne_zero_of_joining_lines (p 0) (p 3) (p 2) (l 2) (l 0)
      (hpoints 0 3 (by decide)) (hpoints 0 2 (by decide))
      (hlines 2 0 (by decide))
      (hinc 2 0 (by decide)) (hinc 2 3 (by decide))
      (hinc 0 0 (by decide)) (hinc 0 2 (by decide))
  have h013 : (Matrix.of ![p 0,p 1,p 3]).det ≠ 0 := by
    have h := triple_det_ne_zero_of_joining_lines (p 3) (p 0) (p 1) (l 2) (l 1)
      (hpoints 3 0 (by decide)) (hpoints 3 1 (by decide))
      (hlines 2 1 (by decide))
      (hinc 2 3 (by decide)) (hinc 2 0 (by decide))
      (hinc 1 3 (by decide)) (hinc 1 1 (by decide))
    rw [triple_det_cycle] at h
    exact h
  let b : Fin 3 → Fin 8 := ![0,1,2]
  have hb : Function.Injective b := by decide
  have hbd : ∀ i, b i ≠ (3 : Fin 8) := by decide
  have hA : (Matrix.of (fun i => p (b i))).det ≠ 0 := by
    convert h012 using 1
    congr 1
    ext i j
    fin_cases i <;> rfl
  have hreplace : ∀ i,
      ((Matrix.of (fun j => p (b j))).updateRow i (p 3)).det ≠ 0 := by
    intro i
    fin_cases i
    · convert h312 using 1
      congr 1
      ext i j
      fin_cases i <;> rfl
    · convert h032 using 1
      congr 1
      ext i j
      fin_cases i <;> rfl
    · convert h013 using 1
      congr 1
      ext i j
      fin_cases i <;> rfl
  obtain ⟨q, hqb, hq3, hminor, hpair⟩ :=
    exists_normalized_projective_frame p b hb 3 hbd hA hreplace
  have hq0 : q 0 = Pi.single (0 : Fin 3) 1 := hqb 0
  have hq1 : q 1 = Pi.single (1 : Fin 3) 1 := hqb 1
  have hq2 : q 2 = Pi.single (2 : Fin 3) 1 := hqb 2
  have hl : ∀ i, l i ≠ 0 := by
    intro i
    obtain ⟨j, hji⟩ := exists_ne i
    simpa using (hlines i j hji.symm).ne_zero 0
  have hzero (a i j k : Fin 8)
      (hi : i ∈ maclaneSupports a) (hj : j ∈ maclaneSupports a)
      (hk : k ∈ maclaneSupports a) :
      (Matrix.of ![q i,q j,q k]).det = 0 := by
    apply (triple_zero_iff_of_selection_zero_iff p q hminor i j k).2
    exact triple_det_zero_of_incident_line (p i) (p j) (p k) (l a) (hl a)
      (hinc a i hi) (hinc a j hj) (hinc a k hk)
  have h41 : q 4 1 = 0 := by
    simpa [Matrix.det_fin_three, hq0, hq2, Pi.single_apply] using
      hzero 0 0 2 4 (by decide) (by decide) (by decide)
  have h50 : q 5 0 = q 5 2 := by
    have h := hzero 1 1 3 5 (by decide) (by decide) (by decide)
    simp [Matrix.det_fin_three, hq1, hq3, Pi.single_apply] at h
    linarith
  have h61 : q 6 1 = q 6 2 := by
    have h := hzero 2 0 3 6 (by decide) (by decide) (by decide)
    simp [Matrix.det_fin_three, hq0, hq3, Pi.single_apply] at h
    linarith
  have h70 : q 7 0 = 0 := by
    simpa [Matrix.det_fin_three, hq1, hq2, Pi.single_apply] using
      hzero 3 1 2 7 (by decide) (by decide) (by decide)
  have h42 : q 4 2 ≠ 0 := by
    intro h42
    have hp : LinearIndependent ℝ ![Pi.single (0 : Fin 3) 1, q 4] := by
      simpa only [hq0] using hpair 0 4 (hpoints 0 4 (by decide))
    obtain ⟨j, hj, hjv⟩ := independent_basis_point_has_other_coordinate 0 (q 4) hp
    fin_cases j
    · exact hj rfl
    · exact hjv h41
    · exact hjv h42
  have h52 : q 5 2 ≠ 0 := by
    intro h52
    have hp : LinearIndependent ℝ ![Pi.single (1 : Fin 3) 1, q 5] := by
      simpa only [hq1] using hpair 1 5 (hpoints 1 5 (by decide))
    obtain ⟨j, hj, hjv⟩ := independent_basis_point_has_other_coordinate 1 (q 5) hp
    fin_cases j
    · exact hjv (h50.trans h52)
    · exact hj rfl
    · exact hjv h52
  have h62 : q 6 2 ≠ 0 := by
    intro h62
    have hp : LinearIndependent ℝ ![Pi.single (0 : Fin 3) 1, q 6] := by
      simpa only [hq0] using hpair 0 6 (hpoints 0 6 (by decide))
    obtain ⟨j, hj, hjv⟩ := independent_basis_point_has_other_coordinate 0 (q 6) hp
    fin_cases j
    · exact hj rfl
    · exact hjv (h61.trans h62)
    · exact hjv h62
  have h72 : q 7 2 ≠ 0 := by
    intro h72
    have hp : LinearIndependent ℝ ![Pi.single (1 : Fin 3) 1, q 7] := by
      simpa only [hq1] using hpair 1 7 (hpoints 1 7 (by decide))
    obtain ⟨j, hj, hjv⟩ := independent_basis_point_has_other_coordinate 1 (q 7) hp
    fin_cases j
    · exact hjv h70
    · exact hj rfl
    · exact hjv h72
  let s : Fin 8 → ℝ :=
    ![1,1,1,1,(q 4 2)⁻¹,(q 5 2)⁻¹,(q 6 2)⁻¹,(q 7 2)⁻¹]
  let r : Fin 8 → PlaneVector := fun i => s i • q i
  let a := (q 4 2)⁻¹ * q 4 0
  let b := (q 5 2)⁻¹ * q 5 1
  let c := (q 6 2)⁻¹ * q 6 0
  let d := (q 7 2)⁻¹ * q 7 1
  have hr0 : r 0 = ![1,0,0] := by
    ext j
    fin_cases j <;> simp [r,s,hq0,Pi.single_apply]
  have hr1 : r 1 = ![0,1,0] := by
    ext j
    fin_cases j <;> simp [r,s,hq1,Pi.single_apply]
  have hr2 : r 2 = ![0,0,1] := by
    ext j
    fin_cases j <;> simp [r,s,hq2,Pi.single_apply]
  have hr3 : r 3 = ![1,1,1] := by
    ext j
    fin_cases j <;> simp [r,s,hq3]
  have hr4 : r 4 = ![a,0,1] := by
    ext j
    fin_cases j <;> simp [r,s,a,Pi.smul_apply,smul_eq_mul,h41,h42]
  have hr5 : r 5 = ![1,b,1] := by
    ext j
    fin_cases j <;> simp [r,s,b,Pi.smul_apply,smul_eq_mul,h50,h52]
  have hr6 : r 6 = ![c,1,1] := by
    ext j
    fin_cases j <;> simp [r,s,c,Pi.smul_apply,smul_eq_mul,h61,h62]
  have hr7 : r 7 = ![0,d,1] := by
    ext j
    fin_cases j <;> simp [r,s,d,Pi.smul_apply,smul_eq_mul,h70,h72]
  have hrzero (i j k : Fin 8) (h : (Matrix.of ![q i,q j,q k]).det = 0) :
      (Matrix.of ![r i,r j,r k]).det = 0 := by
    have hs := det_rows_smul_zero ![q i,q j,q k] ![s i,s j,s k] h
    convert hs using 1
    congr 1
    ext a b
    fin_cases a <;> rfl
  apply RankThreeContradictions.maclane_normalized_impossible a b c d
  · simpa [RankThreeContradictions.determinant,hr0,hr5,hr7] using
      hrzero 0 5 7 (hzero 4 0 5 7 (by decide) (by decide) (by decide))
  · simpa [RankThreeContradictions.determinant,hr1,hr4,hr6] using
      hrzero 1 4 6 (hzero 5 1 4 6 (by decide) (by decide) (by decide))
  · simpa [RankThreeContradictions.determinant,hr2,hr5,hr6] using
      hrzero 2 5 6 (hzero 6 2 5 6 (by decide) (by decide) (by decide))
  · simpa [RankThreeContradictions.determinant,hr3,hr4,hr7] using
      hrzero 3 4 7 (hzero 7 3 4 7 (by decide) (by decide) (by decide))


end Papers.RationalityTen
