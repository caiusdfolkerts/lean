module
public import Papers.RelativeKernelRankCases
public import Papers.SecondNormalExtension

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- The sole remaining rank pattern in four coordinates: a rank-two column
space inside the kernel of a rank-one matrix. -/
theorem relative_rank_one_ambient_density {X : Type*} [TopologicalSpace X]
    {m n : ℕ} (A : X → Matrix (Fin m) (Fin 4) ℝ) (x : X)
    (hA : ContinuousAt A x) (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, RationalCoordinates (A y))
    (hRanks : ∀ y ∈ S, SameSubsetRanks (A x).col (A y).col)
    (C : Matrix (Fin 4) (Fin n) ℝ) (hAC : A x * C = 0)
    (hArank : (A x).rank = 1) (hCrank : C.rank = 2) :
    (x, C) ∈ closure {z : X × Matrix (Fin 4) (Fin n) ℝ | z.1 ∈ S ∧
      RationalCoordinates z.2 ∧ A z.1 * z.2 = 0 ∧ z.2.rank = C.rank ∧
      PreservesZeroEntries C z.2} := by
  classical
  have hA0 : A x ≠ 0 := by
    intro h
    rw [h, Matrix.rank_zero] at hArank
    omega
  obtain ⟨i, j, hij⟩ : ∃ i j, A x i j ≠ 0 := by
    by_contra hn
    apply hA0
    ext i j
    exact not_not.mp (fun h => hn ⟨i, j, h⟩)
  have hrow : A x i ≠ 0 := fun h => hij (congrFun h j)
  let S' : Set X := S ∩ {y | A y i j ≠ 0}
  have hcont : ContinuousAt (fun y => A y i) x :=
    (continuous_apply i).continuousAt.comp hA
  have hopen : ∀ᶠ y in 𝓝 x, A y i j ≠ 0 :=
    ((continuous_apply j).continuousAt.comp hcont).eventually_ne hij
  have hx' : x ∈ closure S' := mem_closure_inter_of_eventually hx hopen
  have hArank' : ∀ y ∈ S, (A y).rank = 1 := by
    intro y hy
    have h := hRanks y hy Finset.univ
    rw [subsetRank_col_univ, subsetRank_col_univ, hArank] at h
    exact h.symm
  have hrow' : ∀ y ∈ S', A y i ≠ 0 := by
    intro y hy h
    exact hy.2 (congrFun h j)
  have hzero : ∀ y ∈ S', ∀ k, A x i k = 0 → A y i k = 0 := by
    intro y hy k hk
    have hxk : (A x).col k = 0 := by
      have hvec : (A x).mulVec (Pi.single k 1) = 0 :=
        (rank_one_kernel_row (A x) hArank i hrow (Pi.single k 1)).mpr (by
          simpa [dotProduct, Pi.single_apply] using hk)
      simpa only [Matrix.mulVec_single_one] using hvec
    have hyk := coordinate_zero_of_sameSubsetRanks (A x).col (A y).col
      (hRanks y hy.1) k hxk
    exact congrFun hyk i
  have haC : ∀ j, A x i ⬝ᵥ C.col j = 0 := by
    intro k
    exact congrFun (congrFun hAC i) k
  obtain ⟨b, hbSpan, hbC, hbExact⟩ := exists_second_normal C (A x i) hCrank hrow haC
  have h := relative_codimension_two_density (fun y => A y i) x hcont S' hx'
    (fun y hy k => hRat y hy.1 i k) hzero b hbSpan C hbC hbExact
  apply closure_mono ?_ h
  intro z hz
  refine ⟨hz.1.1, hz.2.1, ?_, hz.2.2.2.1, hz.2.2.2.2⟩
  ext r k
  have hcol := (rank_one_kernel_row (A z.1) (hArank' z.1 hz.1.1)
    i (hrow' z.1 hz.1) (z.2.col k)).mpr (hz.2.2.1 k)
  exact congrFun hcol r

/-- Relative rational approximation in at most four coordinate directions.
The whole external parameter is retained. The conclusion preserves the
actual annihilator equations, matrix rank and every original zero entry;
there are no unproved relative-density assumptions in the statement. -/
theorem relative_four_coordinate_density {X : Type*} [TopologicalSpace X]
    {m p n : ℕ} (hp : p ≤ 4)
    (A : X → Matrix (Fin m) (Fin p) ℝ) (x : X)
    (hA : ContinuousAt A x) (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, RationalCoordinates (A y))
    (hRanks : ∀ y ∈ S, SameSubsetRanks (A x).col (A y).col)
    (C : Matrix (Fin p) (Fin n) ℝ) (hAC : A x * C = 0) :
    (x, C) ∈ closure {z : X × Matrix (Fin p) (Fin n) ℝ | z.1 ∈ S ∧
      RationalCoordinates z.2 ∧ A z.1 * z.2 = 0 ∧ z.2.rank = C.rank ∧
      PreservesZeroEntries C z.2} := by
  by_cases hCzero : C.rank = 0
  · have hC := matrix_eq_zero_of_rank_zero C hCzero
    subst C
    simpa only [Matrix.rank_zero] using relative_zero_matrix_density A x S hx (n := n)
  by_cases hAzero : (A x).rank = 0
  · apply relative_unconstrained_density (by omega) A x S hx ?_ C
    intro y hy
    apply matrix_eq_zero_of_rank_zero
    have h := hRanks y hy Finset.univ
    rw [subsetRank_col_univ, subsetRank_col_univ, hAzero] at h
    exact h.symm
  by_cases hfull : (A x).rank + C.rank = p
  · exact relative_full_kernel_density A x hA S hx hRat hRanks C hAC hfull
  by_cases hCone : C.rank = 1
  · exact relative_rank_one_density A x hA S hx hRat hRanks C hAC hCone
  have hle := Matrix.rank_add_rank_le_card_of_mul_eq_zero hAC
  simp only [Fintype.card_fin] at hle
  have hp4 : p = 4 := by omega
  have hAone : (A x).rank = 1 := by omega
  have hCtwo : C.rank = 2 := by omega
  subst p
  exact relative_rank_one_ambient_density A x hA S hx hRat hRanks C hAC hAone hCtwo

#print axioms relative_four_coordinate_density

end Papers.RationalityTen.FixedCoordinateFlagDensity
