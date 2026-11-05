module
public import Papers.RelativeColumnKernelDensity

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- One vector may be reconstructed in its varying kernel with its prescribed
zero coordinates. No assertion about generic points is needed. -/
theorem relative_kernel_vector_density {X : Type*} [TopologicalSpace X]
    {m p : ℕ} (A : X → Matrix (Fin m) (Fin p) ℝ) (x : X)
    (hA : ContinuousAt A x) (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, RationalCoordinates (A y))
    (hRanks : ∀ y ∈ S, SameSubsetRanks (A x).col (A y).col)
    (v : Fin p → ℝ) (hv : (A x).mulVec v = 0) :
    (x, v) ∈ closure {z : X × (Fin p → ℝ) | z.1 ∈ S ∧
      (∀ i, RatScalar (z.2 i)) ∧ (A z.1).mulVec z.2 = 0 ∧
      ∀ i, v i = 0 → z.2 i = 0} := by
  let C : Matrix (Fin p) (Fin 1) ℝ := fun i _ => v i
  have h := relative_column_kernel_density (fun y (_ : Fin 1) => A y) x
    (fun _ => hA) S hx (fun y hy _ => hRat y hy)
    (fun y hy _ => hRanks y hy) C (fun _ => hv)
  let F : X × Matrix (Fin p) (Fin 1) ℝ → X × (Fin p → ℝ) :=
    fun z => (z.1, z.2.col 0)
  have hF : Continuous F := continuous_fst.prodMk (continuous_pi fun i =>
    (continuous_apply 0).comp ((continuous_apply i).comp continuous_snd))
  have hi := mem_closure_image hF.continuousAt h
  change (x, v) ∈ closure (F '' _) at hi
  apply closure_mono (s := F '' _) ?_ hi
  rintro _ ⟨⟨y, C'⟩, hC', rfl⟩
  exact ⟨hC'.1, fun i => hC'.2.1 i 0, hC'.2.2.1 0,
    fun i hi => hC'.2.2.2 i 0 hi⟩

/-- Rational approximation inside an arbitrary coordinate subspace. -/
theorem rational_vector_zero_pattern_density {n : ℕ} (w : Fin n → ℝ) :
    w ∈ closure {w' : Fin n → ℝ | (∀ j, RatScalar (w' j)) ∧
      ∀ j, w j = 0 → w' j = 0} := by
  let F : (Fin n → ℝ) → (Fin n → ℝ) := fun u j => if w j = 0 then 0 else u j
  have hF : Continuous F := by
    apply continuous_pi
    intro j
    by_cases hj : w j = 0
    · simpa only [F, if_pos hj] using (continuous_const : Continuous (fun _ : Fin n → ℝ => (0 : ℝ)))
    · simpa only [F, if_neg hj] using continuous_apply j
  have hbase : F w = w := by
    ext j
    by_cases hj : w j = 0 <;> simp [F, hj]
  have h := mem_closure_image hF.continuousAt (scalarCoordinates_dense n w)
  rw [hbase] at h
  apply closure_mono (s := F '' {u : Fin n → ℝ | ∀ j, RatScalar (u j)}) ?_ h
  rintro _ ⟨u, hu, rfl⟩
  constructor
  · intro j
    by_cases hj : w j = 0
    · simpa [F, hj] using RatScalar.zero
    · simpa [F, hj] using hu j
  · intro j hj
    simp [F, hj]

/-- The rank-one part of the relative flag lemma. The factors are actual real
vectors of the original matrix; both are approximated with their zero patterns,
so every original zero in the outer product is retained. -/
theorem relative_outer_product_density {X : Type*} [TopologicalSpace X]
    {m p n : ℕ} (A : X → Matrix (Fin m) (Fin p) ℝ) (x : X)
    (hA : ContinuousAt A x) (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, RationalCoordinates (A y))
    (hRanks : ∀ y ∈ S, SameSubsetRanks (A x).col (A y).col)
    (v : Fin p → ℝ) (w : Fin n → ℝ) (hv : (A x).mulVec v = 0)
    (hrank : (Matrix.vecMulVec v w).rank = 1) :
    (x, Matrix.vecMulVec v w) ∈ closure
      {z : X × Matrix (Fin p) (Fin n) ℝ | z.1 ∈ S ∧
        RationalCoordinates z.2 ∧ A z.1 * z.2 = 0 ∧ z.2.rank = 1 ∧
        PreservesZeroEntries (Matrix.vecMulVec v w) z.2} := by
  let V : Set (X × (Fin p → ℝ)) := {z | z.1 ∈ S ∧
    (∀ i, RatScalar (z.2 i)) ∧ (A z.1).mulVec z.2 = 0 ∧
      ∀ i, v i = 0 → z.2 i = 0}
  let W : Set (Fin n → ℝ) := {w' | (∀ j, RatScalar (w' j)) ∧
    ∀ j, w j = 0 → w' j = 0}
  have hV : (x, v) ∈ closure V :=
    relative_kernel_vector_density A x hA S hx hRat hRanks v hv
  have hW : w ∈ closure W := rational_vector_zero_pattern_density w
  let G : (X × (Fin p → ℝ)) × (Fin n → ℝ) → Matrix (Fin p) (Fin n) ℝ :=
    fun z => Matrix.vecMulVec z.1.2 z.2
  have hG : Continuous G := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_mul.comp
      (((continuous_apply i).comp (continuous_snd.comp continuous_fst)).prodMk
        ((continuous_apply j).comp continuous_snd))
  obtain ⟨B⟩ := exists_rowKernelChart (Matrix.vecMulVec v w)
  have hgood : ∀ᶠ z in 𝓝 ((x, v), w), LinearIndependent ℝ (fun i => G z (B.rows i)) := by
    have ht : Tendsto G (𝓝 ((x, v), w)) (𝓝 (Matrix.vecMulVec v w)) :=
      hG.continuousAt.tendsto
    exact ht.eventually B.eventually_independent
  have hprod : ((x, v), w) ∈ closure (V ×ˢ W) := by
    rw [closure_prod_eq]
    exact ⟨hV, hW⟩
  let F : (X × (Fin p → ℝ)) × (Fin n → ℝ) → X × Matrix (Fin p) (Fin n) ℝ :=
    fun z => (z.1.1, G z)
  have hF : Continuous F := (continuous_fst.comp continuous_fst).prodMk hG
  have h := mem_closure_image hF.continuousAt
    (mem_closure_inter_of_eventually hprod hgood)
  change (x, Matrix.vecMulVec v w) ∈ closure (F '' _) at h
  apply closure_mono (s := F '' _) ?_ h
  rintro _ ⟨⟨⟨y, v'⟩, w'⟩, ⟨⟨hy, hw'⟩, hLI⟩, rfl⟩
  have hlow : 1 ≤ (Matrix.vecMulVec v' w').rank := by
    have hLI' : LinearIndependent ℝ
        (fun i => (Matrix.vecMulVec v' w') (B.rows i)) := hLI
    have hi := hLI'.rank_matrix
    have hl := Matrix.rank_submatrix_le (Matrix.vecMulVec v' w') B.rows id
    change ((Matrix.vecMulVec v' w').submatrix B.rows id).rank =
      Fintype.card (Fin B.rank) at hi
    simp only [Fintype.card_fin] at hi
    rw [hi, ← B.rank_eq, hrank] at hl
    exact hl
  refine ⟨hy.1, ?_, ?_, Nat.le_antisymm (Matrix.rank_vecMulVec_le _ _) hlow, ?_⟩
  · intro i j
    exact (hy.2.1 i).mul (hw'.1 j)
  · rw [Matrix.mul_vecMulVec, hy.2.2.1]
    simp
  · intro i j hij
    rcases mul_eq_zero.mp hij with hi | hj
    · change v' i * w' j = 0
      have hi' : v' i = 0 := hy.2.2.2 i hi
      rw [hi', zero_mul]
    · change v' i * w' j = 0
      have hj' : w' j = 0 := hw'.2 j hj
      rw [hj', mul_zero]

/-- Extract an actual rank-one factorization, with its column factor in the
original annihilator kernel. This is ordinary intrinsic linear algebra. -/
theorem rank_one_factor_in_kernel {m p n : ℕ}
    (A : Matrix (Fin m) (Fin p) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (hAC : A * C = 0) (hC : C.rank = 1) :
    ∃ (v : Fin p → ℝ) (w : Fin n → ℝ),
      C = Matrix.vecMulVec v w ∧ A.mulVec v = 0 := by
  obtain ⟨r, hr, u, E, hu, hE, hrec⟩ := exists_intrinsic_linear_configuration C
  have hdim := intrinsic_rank_of_reconstruction u hu E hE
  rw [hrec] at hdim
  have hCr : C.rank = r := by
    rw [Matrix.rank_eq_finrank_span_row]
    exact hdim
  have hr1 : r = 1 := hCr.symm.trans hC
  clear hdim hCr
  subst r
  let v : Fin p → ℝ := fun i => u i 0
  let w : Fin n → ℝ := E 0
  have hfactor : C = Matrix.vecMulVec v w := by
    ext i j
    rw [← hrec]
    simp [reconstruct, frameMap, v, w, Matrix.vecMulVec_apply]
  have hw0 : w ≠ 0 := hE.ne_zero 0
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hn
    apply hw0
    ext j
    exact not_not.mp (fun hh => hn ⟨j, hh⟩)
  refine ⟨v, w, hfactor, ?_⟩
  rw [hfactor, Matrix.mul_vecMulVec] at hAC
  ext i
  have hi := congrFun (congrFun hAC i) j
  exact (mul_eq_zero.mp hi).resolve_right hj

/-- Full rank-one endpoint, with no preselected factorization in its statement. -/
theorem relative_rank_one_density {X : Type*} [TopologicalSpace X]
    {m p n : ℕ} (A : X → Matrix (Fin m) (Fin p) ℝ) (x : X)
    (hA : ContinuousAt A x) (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, RationalCoordinates (A y))
    (hRanks : ∀ y ∈ S, SameSubsetRanks (A x).col (A y).col)
    (C : Matrix (Fin p) (Fin n) ℝ) (hAC : A x * C = 0) (hrank : C.rank = 1) :
    (x, C) ∈ closure {z : X × Matrix (Fin p) (Fin n) ℝ | z.1 ∈ S ∧
      RationalCoordinates z.2 ∧ A z.1 * z.2 = 0 ∧ z.2.rank = C.rank ∧
      PreservesZeroEntries C z.2} := by
  obtain ⟨v, w, hC, hv⟩ := rank_one_factor_in_kernel (A x) C hAC hrank
  have houter : (Matrix.vecMulVec v w).rank = 1 := hC ▸ hrank
  have h := relative_outer_product_density A x hA S hx hRat hRanks v w hv houter
  simpa only [hC, houter] using h

#print axioms relative_rank_one_density

#print axioms relative_outer_product_density

end Papers.RationalityTen.FixedCoordinateFlagDensity
