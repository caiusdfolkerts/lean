module
public import PaperVerification.TriangularGeometry
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def triangularDepthSum (z : TriPoint) : ℝ :=
  triangularDepth z+triangularDepth (z+triC)+triangularDepth (z-triC)

lemma triangularDepthSum_le_integer (z : TriPoint) (v : Fin 3 → EisInt) :
    triangularDepthSum z ≤
      ∑ i, triQ (eisEmbed (v i)-(![z,z+triC,z-triC] : Fin 3 → TriPoint) i) := by
  have h0 := triangularDepth_le z (v 0)
  have h1 := triangularDepth_le (z+triC) (v 1)
  have h2 := triangularDepth_le (z-triC) (v 2)
  simp only [Fin.sum_univ_three,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  unfold triangularDepthSum
  linarith

lemma triangularDepthSum_le_glue (z : TriPoint) (g : TriGlueIndex) :
    triangularDepthSum z ≤ ∑ i, triQ (triGluePoint g i-
      (![-triTheta z,triC,-triC] : Fin 3 → TriPoint) i) := by
  have h := triangularDepthSum_le_integer z (triDFTIntegerEquiv.symm g)
  rw [triDFT_lattice_distance,triDFTIntegerEquiv.apply_symm_apply] at h
  exact h

lemma nearest_neg_c_residue (r : ZMod 3) :
    ∃ m : EisInt, eisResidue m=r ∧ triQ (eisEmbed m- -triC)=1/3 := by
  obtain ⟨m,hm,hd⟩ := exists_nearest_c_residue (-r)
  refine ⟨-m,by rw [map_neg,hm,neg_neg],?_⟩
  rw [map_neg,show -eisEmbed m- -triC = -(eisEmbed m-triC) by abel,triQ_neg,hd]

lemma nearest_neg_two_c_residue (r : ZMod 3) :
    ∃ m : EisInt, eisResidue m=r ∧ triQ (eisEmbed m- (-(2:ℝ)•triC))=1/3 := by
  obtain ⟨m,hm,hd⟩ := exists_nearest_c_residue r
  refine ⟨m+(-1,1),by simpa [map_add,eisResidue] using hm,?_⟩
  have he : eisEmbed (m+(-1,1))- (-(2:ℝ)•triC) = eisEmbed m-triC := by
    rw [map_add]
    ext <;> dsimp [eisEmbed,triC] <;> ring
  rw [he,hd]

lemma triangularDepthSum_upper_plus (z : TriPoint) :
    triangularDepthSum z ≤ 1/3+triangularDepth (triTheta z+triC) := by
  have hall (m : EisInt) : triangularDepthSum z-1/3 ≤
      triQ (eisEmbed m-(-triTheta z-triC)) := by
    obtain ⟨u,hu,hdu⟩ := nearest_neg_two_c_residue (-eisResidue m)
    let h : TriZeroSum := ⟨![m,0,u],by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_add, map_zero, add_zero, hu, add_neg_cancel]⟩
    have hb := triangularDepthSum_le_glue z ((1:ZMod 3),h)
    have he : (∑ i, triQ (triGluePoint ((1:ZMod 3),h) i-
        (![-triTheta z,triC,-triC] : Fin 3 → TriPoint) i)) =
        triQ (eisEmbed m-(-triTheta z-triC))+1/3 := by
      simp only [Fin.sum_univ_three,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,triGluePoint,
        h,zmodThree_val_one,Nat.cast_one,one_smul,map_zero,zero_add,sub_self]
      have hm' : eisEmbed m+triC- -triTheta z =
          eisEmbed m-(-triTheta z-triC) := by abel
      have hu' : eisEmbed u+triC- -triC = eisEmbed u-(-(2:ℝ)•triC) := by module
      rw [hm',hu',hdu]
      norm_num [triQ]
    rw [he] at hb
    linarith
  have hd : triangularDepthSum z-1/3 ≤ triangularDepth (-triTheta z-triC) := by
    apply le_csInf (Set.range_nonempty _)
    rintro t ⟨m,rfl⟩
    exact hall m
  rw [show -triTheta z-triC = -(triTheta z+triC) by abel,triangularDepth_even] at hd
  linarith

lemma triangularDepthSum_upper_minus (z : TriPoint) :
    triangularDepthSum z ≤ 1/3+triangularDepth (triTheta z-triC) := by
  have hall (m : EisInt) : triangularDepthSum z-1/3 ≤
      triQ (eisEmbed m-(-triTheta z-(2:ℝ)•triC)) := by
    obtain ⟨u,hu,hdu⟩ := nearest_neg_c_residue (-eisResidue m)
    let h : TriZeroSum := ⟨![m,u,(-1,1)],by
      have hr : eisResidue (-1, 1) = 0 := by norm_num [eisResidue]
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_add, hu, hr, add_neg_cancel, zero_add]⟩
    have hb := triangularDepthSum_le_glue z ((2:ZMod 3),h)
    have he : (∑ i, triQ (triGluePoint ((2:ZMod 3),h) i-
        (![-triTheta z,triC,-triC] : Fin 3 → TriPoint) i)) =
        triQ (eisEmbed m-(-triTheta z-(2:ℝ)•triC))+1/3 := by
      simp only [Fin.sum_univ_three,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,triGluePoint,
        h,zmodThree_val_two,Nat.cast_ofNat]
      have hm' : eisEmbed m+(2:ℝ)•triC- -triTheta z =
          eisEmbed m-(-triTheta z-(2:ℝ)•triC) := by abel
      have hu' : eisEmbed u+(2:ℝ)•triC-triC = eisEmbed u- -triC := by module
      have hz : eisEmbed (-1,1)+(2:ℝ)•triC- -triC = 0 := by
        ext <;> norm_num [eisEmbed,triC]
      rw [hm',hu',hdu,hz]
      norm_num [triQ]
    rw [he] at hb
    linarith
  have hd : triangularDepthSum z-1/3 ≤ triangularDepth (-triTheta z-(2:ℝ)•triC) := by
    apply le_csInf (Set.range_nonempty _)
    rintro t ⟨m,rfl⟩
    exact hall m
  have he : triTheta z+(2:ℝ)•triC = (triTheta z-triC)+eisEmbed (1,-1) := by
    ext <;> dsimp [triC,eisEmbed] <;> ring
  rw [show -triTheta z-(2:ℝ)•triC = -(triTheta z+(2:ℝ)•triC) by module,
    triangularDepth_even,he,triangularDepth_periodic] at hd
  linarith

theorem triangularDepthSum_upper (z : TriPoint) : triangularDepthSum z ≤ 2/3 := by
  have h := triangularDepthSum_upper_plus z
  have h' := triangularDepth_le_third (triTheta z+triC)
  linarith

theorem triangularDepthSum_periodic (z : TriPoint) (m : EisInt) :
    triangularDepthSum (z+eisEmbed m)=triangularDepthSum z := by
  unfold triangularDepthSum
  rw [show z+eisEmbed m+triC = (z+triC)+eisEmbed m by abel,
    show z+eisEmbed m-triC = (z-triC)+eisEmbed m by abel]
  simp only [triangularDepth_periodic]

theorem triangularDepthSum_c_periodic (z : TriPoint) :
    triangularDepthSum (z+triC)=triangularDepthSum z := by
  unfold triangularDepthSum
  have he : z+triC+triC = (z-triC)+eisEmbed (1,-1) := by
    ext <;> dsimp [triC,eisEmbed] <;> ring
  rw [he,triangularDepth_periodic,add_sub_cancel_right]
  ring

theorem triangularDepthSum_zero : triangularDepthSum 0=2/3 := by
  simp [triangularDepthSum,triangularDepth_zero,triangularDepth_c,triangularDepth_even]
  norm_num

/-- The scalar geometric equality is proved from explicit nearest residue
representatives and the same integral Fourier isometry, without a Laplace limit. -/
theorem triangularDepthSum_eq_iff (z : TriPoint) : triangularDepthSum z=2/3 ↔ TriPhase z := by
  constructor
  · intro hz
    have hp := triangularDepthSum_upper_plus z
    have hm := triangularDepthSum_upper_minus z
    have hp' := triangularDepth_le_third (triTheta z+triC)
    have hm' := triangularDepth_le_third (triTheta z-triC)
    have he1 : triangularDepth (triTheta z+triC)=1/3 := by linarith
    have he2 : triangularDepth (triTheta z-triC)=1/3 := by linarith
    exact (triPhase_iff_theta_integral z).mpr ((triHole_both_iff _).mp
      ⟨(triangularDepth_eq_third_iff _).mp he1,(triangularDepth_eq_third_iff _).mp he2⟩)
  · rintro ⟨r,m,rfl⟩
    rw [add_comm,triangularDepthSum_periodic]
    rcases (show ∀ r : ZMod 3, r = 0 ∨ r = 1 ∨ r = 2 by decide) r with
      rfl | rfl | rfl
    · change triangularDepthSum (((0 : ZMod 3).val : ℝ) • triC) = _
      rw [ZMod.val_zero]
      simpa only [Nat.cast_zero, zero_smul] using triangularDepthSum_zero
    · change triangularDepthSum (((1 : ZMod 3).val : ℝ) • triC) = _
      rw [zmodThree_val_one]
      have h := (triangularDepthSum_c_periodic 0).trans triangularDepthSum_zero
      simpa only [Nat.cast_one, one_smul, zero_add] using h
    · change triangularDepthSum (((2 : ZMod 3).val : ℝ) • triC) = _
      rw [zmodThree_val_two]
      have h1 : triangularDepthSum triC = 2 / 3 := by
        simpa only [zero_add] using
          (triangularDepthSum_c_periodic 0).trans triangularDepthSum_zero
      have he : (2:ℝ)•triC=triC+triC := by module
      simpa only [Nat.cast_ofNat, he] using (triangularDepthSum_c_periodic triC).trans h1

end PaperVerification.ColdSpots
