module
public import Papers.RelativeRankOneDensity
public import Papers.RelativeCodimensionTwoDensity

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- Rank zero means the actual matrix is zero. -/
theorem matrix_eq_zero_of_rank_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = 0) : A = 0 := by
  have hr : A.mulVecLin.range = ⊥ := Submodule.finrank_eq_zero.mp hA
  have hm : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hr
  apply Matrix.toLin'.injective
  simpa only [Matrix.toLin'_apply', Matrix.mulVecLin_zero] using hm

/-- Full dimension inside a kernel proves equality, without a selected basis. -/
theorem kernel_exact_of_rank_sum {m p n : ℕ}
    (A : Matrix (Fin m) (Fin p) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (hAC : A * C = 0) (hfull : A.rank + C.rank = p) :
    C.mulVecLin.range = A.mulVecLin.ker := by
  have hle : C.mulVecLin.range ≤ A.mulVecLin.ker := by
    rintro _ ⟨v, rfl⟩
    change A.mulVec (C.mulVec v) = 0
    rw [Matrix.mulVec_mulVec, hAC, Matrix.zero_mulVec]
  apply Submodule.eq_of_le_of_finrank_eq hle
  change C.rank = finrank ℝ A.mulVecLin.ker
  have hdim : A.rank + finrank ℝ A.mulVecLin.ker = p := by
    simpa [Matrix.rank] using A.mulVecLin.finrank_range_add_finrank_ker
  omega

/-- Equality of coordinate ranks retains zero coordinate vectors. -/
theorem coordinate_zero_of_sameSubsetRanks {p r s : ℕ}
    (u : Fin p → Fin r → ℝ) (v : Fin p → Fin s → ℝ)
    (h : SameSubsetRanks u v) (i : Fin p) (hi : u i = 0) : v i = 0 := by
  classical
  have hz : subsetRank u {i} = 0 := by simp [subsetRank, hi]
  have hv : subsetRank v {i} = 0 := (h {i}).symm.trans hz
  have hbot : Submodule.span ℝ (v '' (↑({i} : Finset (Fin p)) : Set (Fin p))) = ⊥ :=
    Submodule.finrank_eq_zero.mp hv
  have hmem : v i ∈ Submodule.span ℝ
      (v '' (↑({i} : Finset (Fin p)) : Set (Fin p))) :=
    Submodule.subset_span ⟨i, by simp, rfl⟩
  rw [hbot] at hmem
  exact hmem

/-- A nonzero row of a rank-one matrix defines its full kernel. -/
theorem rank_one_kernel_row {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) ℝ) (hA : A.rank = 1)
    (i : Fin m) (hi : A i ≠ 0) (v : Fin p → ℝ) :
    A.mulVec v = 0 ↔ A i ⬝ᵥ v = 0 := by
  have hLI : LinearIndependent ℝ (fun _ : Fin 1 => A i) :=
    linearIndependent_unique_iff.mpr hi
  have hk := kernel_row_restriction_eq_of_independent A (fun _ : Fin 1 => i) hLI
    (by simpa using hA)
  change v ∈ A.mulVecLin.ker ↔ _
  rw [hk]
  constructor
  · intro hv
    exact congrFun hv 0
  · intro hv
    ext j
    exact hv

/-- The zero-column-space rank case is a constant reconstruction. -/
theorem relative_zero_matrix_density {X : Type*} [TopologicalSpace X]
    {m p n : ℕ} (A : X → Matrix (Fin m) (Fin p) ℝ) (x : X)
    (S : Set X) (hx : x ∈ closure S) :
    (x, (0 : Matrix (Fin p) (Fin n) ℝ)) ∈ closure
      {z : X × Matrix (Fin p) (Fin n) ℝ | z.1 ∈ S ∧
        RationalCoordinates z.2 ∧ A z.1 * z.2 = 0 ∧ z.2.rank = 0 ∧
        PreservesZeroEntries 0 z.2} := by
  let F : X → X × Matrix (Fin p) (Fin n) ℝ := fun y => (y, 0)
  have hF : Continuous F := continuous_id.prodMk continuous_const
  have h := mem_closure_image hF.continuousAt hx
  change (x, (0 : Matrix (Fin p) (Fin n) ℝ)) ∈ closure (F '' S) at h
  apply closure_mono (s := F '' S) ?_ h
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨hy, fun _ _ => RatScalar.zero, ?_, Matrix.rank_zero, ?_⟩
  · exact Matrix.mul_zero _
  · intro i j _
    rfl

/-- The full-kernel rank case uses the exact relative matrix reconstruction. -/
theorem relative_full_kernel_density {X : Type*} [TopologicalSpace X]
    {m p n : ℕ} (A : X → Matrix (Fin m) (Fin p) ℝ) (x : X)
    (hA : ContinuousAt A x) (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, RationalCoordinates (A y))
    (hRanks : ∀ y ∈ S, SameSubsetRanks (A x).col (A y).col)
    (C : Matrix (Fin p) (Fin n) ℝ) (hAC : A x * C = 0)
    (hfull : (A x).rank + C.rank = p) :
    (x, C) ∈ closure {z : X × Matrix (Fin p) (Fin n) ℝ | z.1 ∈ S ∧
      RationalCoordinates z.2 ∧ A z.1 * z.2 = 0 ∧ z.2.rank = C.rank ∧
      PreservesZeroEntries C z.2} :=
  relative_kernel_matrix_density A x hA S hx hRat hRanks C hAC
    (kernel_exact_of_rank_sum (A x) C hAC hfull)

/-- When the ambient kernel is the full coordinate space, ordinary small-row
matrix density can be combined independently with the external parameter. -/
theorem relative_unconstrained_density {X : Type*} [TopologicalSpace X]
    {m p n : ℕ} (hp : p ≤ 7) (A : X → Matrix (Fin m) (Fin p) ℝ) (x : X)
    (S : Set X) (hx : x ∈ closure S) (hzero : ∀ y ∈ S, A y = 0)
    (C : Matrix (Fin p) (Fin n) ℝ) :
    (x, C) ∈ closure {z : X × Matrix (Fin p) (Fin n) ℝ | z.1 ∈ S ∧
      RationalCoordinates z.2 ∧ A z.1 * z.2 = 0 ∧ z.2.rank = C.rank ∧
      PreservesZeroEntries C z.2} := by
  have hC := rational_matrix_zero_pattern_rank_density_seven hp C
  have hprod : (x, C) ∈ closure (S ×ˢ {C' : Matrix (Fin p) (Fin n) ℝ |
      RationalCoordinates C' ∧ C'.rank = C.rank ∧ PreservesZeroEntries C C'}) := by
    rw [closure_prod_eq]
    exact ⟨hx, hC⟩
  apply closure_mono ?_ hprod
  rintro ⟨y, C'⟩ ⟨hy, hC'⟩
  refine ⟨hy, hC'.1, ?_, hC'.2.1, hC'.2.2⟩
  rw [hzero y hy, Matrix.zero_mul]

#print axioms relative_full_kernel_density
#print axioms relative_unconstrained_density

end Papers.RationalityTen.FixedCoordinateFlagDensity
