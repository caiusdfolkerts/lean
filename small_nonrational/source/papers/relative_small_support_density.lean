module
public import Papers.CoordinateSubspaceEmbedding

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- The four-coordinate relative density theorem for a matrix supported on
any injected set of at most four ambient row coordinates. Restriction and
extension preserve the actual matrix rank and every original zero. -/
theorem relative_small_supported_matrix_density {X : Type*} [TopologicalSpace X]
    {m p s n : ℕ} (hp : p ≤ 4) (e : Fin p → Fin s) (he : Function.Injective e)
    (A : X → Matrix (Fin m) (Fin s) ℝ) (x : X) (hA : ContinuousAt A x)
    (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, RationalCoordinates (A y))
    (hRanks : ∀ y ∈ S, SameSubsetRanks (A x).col (A y).col)
    (C : Matrix (Fin s) (Fin n) ℝ) (hAC : A x * C = 0)
    (hsupport : ∀ i, i ∉ Set.range e → ∀ j, C i j = 0) :
    (x, C) ∈ closure {z : X × Matrix (Fin s) (Fin n) ℝ |
      z.1 ∈ S ∧ RationalCoordinates z.2 ∧ A z.1 * z.2 = 0 ∧
      z.2.rank = C.rank ∧ PreservesZeroEntries C z.2} := by
  let P := coordinateInclusion e
  let D := P.transpose * C
  have hreconstruct : P * D = C := coordinateInclusion_reconstruct e he C hsupport
  have hrank : D.rank = C.rank := by
    have h := coordinateInclusion_mul_rank e he D
    rw [hreconstruct] at h
    exact h.symm
  let B : X → Matrix (Fin m) (Fin p) ℝ := fun y => A y * P
  have hB : ContinuousAt B x := matrix_mul_continuousAt hA continuousAt_const
  have hBD : B x * D = 0 := by
    change (A x * P) * D = 0
    rw [Matrix.mul_assoc, hreconstruct, hAC]
  have hcl := relative_four_coordinate_density hp B x hB S hx
    (fun y hy => rationalCoordinates_mul (hRat y hy) (coordinateInclusion_rational e))
    (fun y hy => sameSubsetRanks_mul_coordinateInclusion e (A x) (A y) (hRanks y hy)) D hBD
  let F : X × Matrix (Fin p) (Fin n) ℝ → X × Matrix (Fin s) (Fin n) ℝ :=
    fun z => (z.1, P * z.2)
  have hF : Continuous F := continuous_fst.prodMk
    (continuous_const.matrix_mul continuous_snd)
  have hbase : F (x, D) = (x, C) := congrArg (fun M => (x, M)) hreconstruct
  have hc := mem_closure_image hF.continuousAt hcl
  rw [hbase] at hc
  apply closure_mono (s := F '' _) ?_ hc
  rintro _ ⟨⟨y, D'⟩, hy, rfl⟩
  refine ⟨hy.1, rationalCoordinates_mul (coordinateInclusion_rational e) hy.2.1,
    ?_, ?_, ?_⟩
  · have h := hy.2.2.1
    change (A y * P) * D' = 0 at h
    rw [Matrix.mul_assoc] at h
    exact h
  · exact (coordinateInclusion_mul_rank e he D').trans (hy.2.2.2.1.trans hrank)
  · intro i j hij
    by_cases hi : i ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hi
      have hz : D a j = 0 := by
        change ((coordinateInclusion e).transpose * C) a j = 0
        rw [coordinateInclusion_transpose_mul]
        exact hij
      have hz' : D' a j = 0 := hy.2.2.2.2 a j hz
      change (coordinateInclusion e * D') (e a) j = 0
      rw [coordinateInclusion_mul_at e he]
      exact hz'
    · exact coordinateInclusion_mul_outside e D' i hi j

#print axioms relative_small_supported_matrix_density

end Papers.RationalityTen.FixedCoordinateFlagDensity
