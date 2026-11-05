module
public import Papers.FixedCoordinateFlagDensity
public import Papers.RationalityTenPolygonRelationRanks
public import Papers.RelationMatrixDensity

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- Append coordinate-zero equations to a varying annihilator. -/
def withZeros {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (Z : Finset (Fin n)) : Matrix (Fin (m+n)) (Fin n) ℝ :=
  Fin.addCases A (fun i j => if i ∈ Z ∧ j = i then 1 else 0)

/-- The first block is the original matrix, with an explicit dependent-case
reduction so elaboration does not rely on higher-order simp matching. -/
theorem withZeros_left {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (Z : Finset (Fin n)) (i : Fin m) :
    withZeros A Z (Fin.castAdd n i) = A i := by
  exact Fin.addCases_left (motive := fun _ => Fin n → ℝ)
    (left := A) (right := fun i j => if i ∈ Z ∧ j = i then 1 else 0) i

theorem withZeros_right {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (Z : Finset (Fin n)) (i : Fin n) :
    withZeros A Z (Fin.natAdd m i) =
      (fun j => if i ∈ Z ∧ j = i then 1 else 0) := by
  exact Fin.addCases_right (motive := fun _ => Fin n → ℝ)
    (left := A) (right := fun i j => if i ∈ Z ∧ j = i then 1 else 0) i

theorem withZeros_mulVec_eq_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (Z : Finset (Fin n)) (v : Fin n → ℝ) :
    (withZeros A Z).mulVec v = 0 ↔ A.mulVec v = 0 ∧ ∀ i ∈ Z, v i = 0 := by
  classical
  constructor
  · intro h
    constructor
    · ext i
      have hi := congrFun h (Fin.castAdd n i)
      simpa [Matrix.mulVec, withZeros_left, withZeros_right] using hi
    · intro i hi
      have hv := congrFun h (Fin.natAdd m i)
      simpa [Matrix.mulVec, withZeros_left, withZeros_right, dotProduct, hi] using hv
  · rintro ⟨hA, hZ⟩
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simpa [Matrix.mulVec, withZeros_left, withZeros_right] using congrFun hA k
    · intro k
      by_cases hk : k ∈ Z
      · simpa [Matrix.mulVec, withZeros_left, withZeros_right, dotProduct, hk] using hZ k hk
      · simp [Matrix.mulVec, withZeros_left, withZeros_right, dotProduct, hk]

theorem withZeros_kernel {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (Z : Finset (Fin n)) :
    (withZeros A Z).mulVecLin.ker = globalRelationSpace A.col Zᶜ := by
  ext v
  change (withZeros A Z).mulVec v = 0 ↔ v ∈ globalRelationSpace A.col Zᶜ
  rw [withZeros_mulVec_eq_zero, mem_globalRelationSpace_iff]
  simp only [Finset.mem_compl, not_not, Matrix.col]
  exact and_comm

theorem withZeros_same_rank {m n : ℕ}
    (A A' : Matrix (Fin m) (Fin n) ℝ) (Z : Finset (Fin n))
    (h : subsetRank A.col Zᶜ = subsetRank A'.col Zᶜ) :
    (withZeros A Z).rank = (withZeros A' Z).rank := by
  have h1 := globalRelationSpace_finrank A.col Zᶜ
  have h2 := globalRelationSpace_finrank A'.col Zᶜ
  have h3 : (withZeros A Z).rank +
      finrank ℝ ((withZeros A Z).mulVecLin.ker) = n := by
    simpa [Matrix.rank] using (withZeros A Z).mulVecLin.finrank_range_add_finrank_ker
  have h4 : (withZeros A' Z).rank +
      finrank ℝ ((withZeros A' Z).mulVecLin.ker) = n := by
    simpa [Matrix.rank] using (withZeros A' Z).mulVecLin.finrank_range_add_finrank_ker
  rw [withZeros_kernel] at h3 h4
  omega

theorem withZeros_rational {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (Z : Finset (Fin n))
    (hA : RationalCoordinates A) : RationalCoordinates (withZeros A Z) := by
  intro i j
  refine Fin.addCases ?_ ?_ i
  · intro k
    simpa [withZeros_left] using hA k j
  · intro k
    by_cases hk : k ∈ Z ∧ j = k
    · exact ⟨1, by simp [withZeros_right, hk]⟩
    · exact ⟨0, by simp [withZeros_right, hk]⟩

theorem withZeros_continuous {m n : ℕ} (Z : Finset (Fin n)) :
    Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => withZeros A Z) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.addCases ?_ ?_ i
  · intro k
    simpa only [withZeros_left, Function.comp_def] using
      ((continuous_apply j).comp (continuous_apply k) :
        Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => A k j))
  · intro k
    simpa only [withZeros_right] using
      (continuous_const : Continuous (fun _ : Matrix (Fin m) (Fin n) ℝ =>
        if k ∈ Z ∧ j = k then (1 : ℝ) else 0))

theorem subsetRank_col_univ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    subsetRank A.col Finset.univ = A.rank := by
  rw [Matrix.rank_eq_finrank_span_cols]
  unfold subsetRank
  have hs : A.col '' (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) =
      Set.range A.col := by
    ext v
    constructor
    · rintro ⟨j, _, hj⟩
      exact ⟨j, hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, Finset.mem_univ j, hj⟩
  rw [hs]

/-- A relative kernel reconstruction with the exact rank and prescribed zeros.
The original columns span the full selected kernel. The external parameter is
retained, so this can follow one or several flag-normal approximations. -/
theorem relative_kernel_matrix_density {X : Type*} [TopologicalSpace X]
    {m p n : ℕ} (A : X → Matrix (Fin m) (Fin p) ℝ) (x : X)
    (hA : ContinuousAt A x) (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, RationalCoordinates (A y))
    (hRanks : ∀ y ∈ S, SameSubsetRanks (A x).col (A y).col)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (hAC : A x * C = 0)
    (hExact : C.mulVecLin.range = (A x).mulVecLin.ker) :
    (x, C) ∈ closure {z : X × Matrix (Fin p) (Fin n) ℝ |
      z.1 ∈ S ∧ RationalCoordinates z.2 ∧ A z.1 * z.2 = 0 ∧
      z.2.rank = C.rank ∧ PreservesZeroEntries C z.2} := by
  classical
  let Z : Fin n → Finset (Fin p) :=
    fun j => Finset.univ.filter (fun i => C i j = 0)
  let K : (j : Fin n) → RowKernelChart (withZeros (A x) (Z j)) :=
    fun j => Classical.choice (exists_rowKernelChart _)
  let W : Fin n → Fin p → ℝ := fun j i => C i j
  have hW : ∀ j, (withZeros (A x) (Z j)).mulVec (W j) = 0 := by
    intro j
    apply (withZeros_mulVec_eq_zero _ _ _).mpr
    constructor
    · ext i
      exact congrFun (congrFun hAC i) j
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  let G : X × (Fin n → Fin p → ℝ) → Matrix (Fin p) (Fin n) ℝ :=
    fun z i j => (K j).eval (withZeros (A z.1) (Z j)) (z.2 j) i
  have hGbase : G (x, W) = C := by
    ext i j
    exact congrFun ((K j).self (W j) (hW j)) i
  have hG : ContinuousAt G (x, W) := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    have hp : ContinuousAt
        (fun z : X × (Fin n → Fin p → ℝ) =>
          (withZeros (A z.1) (Z j), z.2 j)) (x, W) :=
      (((withZeros_continuous (Z j)).continuousAt.comp
        (hA.comp continuous_fst.continuousAt)).prodMk
        (((continuous_apply j).comp continuous_snd).continuousAt))
    exact (continuous_apply i).continuousAt.comp
      (((K j).continuousAt (W j)).comp_of_eq hp rfl)
  obtain ⟨B⟩ := exists_rowKernelChart C
  have hminor : ∀ᶠ z in 𝓝 (x, W),
      LinearIndependent ℝ (fun i => G z (B.rows i)) := by
    have ht : Tendsto G (𝓝 (x, W)) (𝓝 C) := by
      simpa only [hGbase] using hG.tendsto
    exact ht.eventually B.eventually_independent
  have hrows : ∀ᶠ z in 𝓝 (x, W), ∀ j,
      LinearIndependent ℝ (fun i => withZeros (A z.1) (Z j) ((K j).rows i)) := by
    apply eventually_all.mpr
    intro j
    have hp := (withZeros_continuous (Z j)).continuousAt.comp
      (hA.comp continuous_fst.continuousAt (x := (x, W)))
    exact hp.tendsto.eventually (K j).eventually_independent
  let Good : Set (X × (Fin n → Fin p → ℝ)) :=
    {z | LinearIndependent ℝ (fun i => G z (B.rows i)) ∧
      ∀ j, LinearIndependent ℝ (fun i => withZeros (A z.1) (Z j) ((K j).rows i))}
  have hGood : ∀ᶠ z in 𝓝 (x, W), z ∈ Good := hminor.and hrows
  have hprod : (x, W) ∈ closure
      (S ×ˢ {W' : Fin n → Fin p → ℝ | RationalCoordinates W'}) := by
    rw [closure_prod_eq]
    exact ⟨hx, rationalCoordinates_dense n p W⟩
  let F : X × (Fin n → Fin p → ℝ) → X × Matrix (Fin p) (Fin n) ℝ :=
    fun z => (z.1, G z)
  have hF : ContinuousAt F (x, W) := continuous_fst.continuousAt.prodMk hG
  have hcl := mem_closure_image hF (mem_closure_inter_of_eventually hprod hGood)
  have hFbase : F (x, W) = (x, C) := congrArg (fun t => (x, t)) hGbase
  rw [hFbase] at hcl
  apply closure_mono (s := F ''
    ((S ×ˢ {W' : Fin n → Fin p → ℝ | RationalCoordinates W'}) ∩ Good)) ?_ hcl
  rintro _ ⟨⟨y, W'⟩, ⟨⟨hy, hW'⟩, hgood⟩, rfl⟩
  have hcol : ∀ j, (A y).mulVec ((G (y, W')).col j) = 0 := by
    intro j
    have hk := (K j).mem (withZeros (A y) (Z j))
      (withZeros_same_rank _ _ _ (hRanks y hy (Z j)ᶜ)).symm (hgood.2 j) (W' j)
    exact ((withZeros_mulVec_eq_zero _ _ _).mp hk).1
  have hnewAC : A y * G (y, W') = 0 := by
    ext i j
    exact congrFun (hcol j) i
  have hle : (G (y, W')).mulVecLin.range ≤ (A y).mulVecLin.ker := by
    rintro _ ⟨v, rfl⟩
    change (A y).mulVec ((G (y, W')).mulVec v) = 0
    rw [Matrix.mulVec_mulVec, hnewAC, Matrix.zero_mulVec]
  have hlow : C.rank ≤ (G (y, W')).rank := by
    have hi := (hgood.1).rank_matrix
    have hl := Matrix.rank_submatrix_le (G (y, W')) B.rows id
    change ((G (y, W')).submatrix B.rows id).rank = Fintype.card (Fin B.rank) at hi
    simp only [Fintype.card_fin] at hi
    rw [hi, ← B.rank_eq] at hl
    exact hl
  have hArank : (A y).rank = (A x).rank := by
    have hr := hRanks y hy Finset.univ
    simpa only [subsetRank_col_univ] using hr.symm
  have hdim : finrank ℝ ((A y).mulVecLin.ker) = C.rank := by
    have h1 : (A x).rank + finrank ℝ ((A x).mulVecLin.ker) = p := by
      simpa [Matrix.rank] using (A x).mulVecLin.finrank_range_add_finrank_ker
    have h2 : (A y).rank + finrank ℝ ((A y).mulVecLin.ker) = p := by
      simpa [Matrix.rank] using (A y).mulVecLin.finrank_range_add_finrank_ker
    have h0 : C.rank = finrank ℝ ((A x).mulVecLin.ker) := by
      change finrank ℝ C.mulVecLin.range = _
      rw [hExact]
    omega
  refine ⟨hy, ?_, hnewAC, ?_, ?_⟩
  · intro i j
    exact (K j).rational (withZeros_rational _ _ (hRat y hy)) (hW' j) i
  · have hu := Submodule.finrank_mono hle
    change (G (y, W')).rank ≤ _ at hu
    rw [hdim] at hu
    exact Nat.le_antisymm hu hlow
  · intro i j hij
    have hk := (K j).mem (withZeros (A y) (Z j))
      (withZeros_same_rank _ _ _ (hRanks y hy (Z j)ᶜ)).symm (hgood.2 j) (W' j)
    exact ((withZeros_mulVec_eq_zero _ _ _).mp hk).2 i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)

#print axioms relative_kernel_matrix_density

end Papers.RationalityTen.FixedCoordinateFlagDensity
