module

public import additional_results

/-! # Compatibility and realization of coordinate projection areas
The claims retain actual compact convex Euclidean sets and planar Lebesgue
areas. They cover the principal nonapproximation theorem, the escape and
closure characterization, strict polytopal realization with the actual vertex
bound, the boundary-quartet corollaries, weighted and open-family obstructions,
and the complete rank-at-most-three nonnegative classification.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Matrix Filter Metric
open scoped BigOperators Pointwise Topology
open ProjectionAreaTopology ProjectionAreaMixedGeometry ProjectionAreaEscape
open ProjectionAreaRankThree ProjectionAreaStrict ProjectionAreaTransforms
open ProjectionAreaBoundaryPolytope ProjectionAreaSharpness ProjectionAreaPaper

namespace PalomarProjectionAreas

theorem positive_rank_three_obstruction {n : ℕ}
    (P : PositiveHollowMatrix n) (hn : 5 ≤ n) (hrank : P.entries.rank = 3) :
    P.entries ∉ closure (realizationLocus n) ∧
      ∀ σ : Fin 4 → Fin n, Function.Injective σ →
        P.entries.submatrix σ σ ∈ realizationLocus 4 := ProjectionAreaPaper.positive_rank_three_obstruction P hn hrank
theorem positive_rank_le_three_not_realizable {n : ℕ}
    (P : PositiveHollowMatrix n) (hn : 5 ≤ n) (hrank : P.entries.rank ≤ 3) :
    P.entries ∉ realizationLocus n := ProjectionAreaPaper.positive_rank_le_three_not_realizable P hn hrank
theorem escapeCone_eq_divergingDiameterLimits (d : ℕ) :
    EscapeCone d = divergingDiameterLimits d := ProjectionAreaPaper.escapeCone_eq_divergingDiameterLimits d
theorem closure_realizationLocus_eq_union_escapeCone (d : ℕ) :
    closure (realizationLocus d) = realizationLocus d ∪ EscapeCone d := ProjectionAreaPaper.closure_realizationLocus_eq_union_escapeCone d
theorem mem_escapeCone_iff_exists_full_dimensional_symmetric_sequence
    (d : ℕ) (q : AreaArray d) :
    q ∈ EscapeCone d ↔
      ∃ K : ℕ → CoordinateBody d,
        Tendsto (fun m => coordinateAreas (K m)) atTop (𝓝 q) ∧
        Tendsto (fun m => diam (K m : Set (CoordinateSpace d))) atTop atTop ∧
        ∀ m, IsSymmetricPolytope (K m) ∧
          (interior (K m : Set (CoordinateSpace d))).Nonempty := ProjectionAreaPaper.mem_escapeCone_iff_exists_full_dimensional_symmetric_sequence d q
theorem escapeCone_isClosed (d : ℕ) : IsClosed (EscapeCone d) := ProjectionAreaPaper.escapeCone_isClosed d
theorem strict_weighted_realization_with_vertex_bound {n : ℕ} (hn : 0 < n)
    (q : Fin n → Fin n → ℝ) (w : Fin n → ℝ)
    (hsym : ∀ i j, q i j = q j i) (hdiag : ∀ i, q i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < q i j) (hw : ∀ i, 0 < w i)
    (hstrict : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      w k * q i j < w j * q i k + w i * q j k)
    (R : ℝ) :
    ∃ S : Finset (Fin n → ℝ), S.card ≤ n * (n-1) + 2 ∧
      let K := convexHull ℝ (S : Set (Fin n → ℝ))
      IsCompact K ∧ Convex ℝ K ∧ K.Nonempty ∧ -K = K ∧
      (∀ i j, (volume : Measure V2).real (projectN i j '' K) = q i j) ∧
      R < euclideanDiameter K ∧
      (K.extremePoints ℝ).Finite ∧ (K.extremePoints ℝ).ncard ≤ n * (n-1) + 2 := ProjectionAreaStrict.strict_weighted_realization_with_vertex_bound hn q w hsym hdiag hpos hw hstrict R
theorem strict_nonnegative_weighted_realization_with_vertex_bound {n : ℕ} (hn : 0 < n)
    (q : Fin n → Fin n → ℝ) (w : Fin n → ℝ)
    (hsym : ∀ i j, q i j = q j i) (hdiag : ∀ i, q i i = 0)
    (hnonneg : ∀ i j, 0 ≤ q i j) (hw : ∀ i, 0 < w i)
    (hstrict : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      w k * q i j < w j * q i k + w i * q j k)
    (R : ℝ) :
    ∃ S : Finset (Fin n → ℝ), S.card ≤ n * (n - 1) + 2 ∧
      let K := convexHull ℝ (S : Set (Fin n → ℝ))
      IsCompact K ∧ Convex ℝ K ∧ K.Nonempty ∧ -K = K ∧
      (∀ i j, (volume : Measure V2).real (projectN i j '' K) = q i j) ∧
      R < euclideanDiameter K ∧
      (K.extremePoints ℝ).Finite ∧ (K.extremePoints ℝ).ncard ≤ n * (n - 1) + 2 := ProjectionAreaStrict.strict_nonnegative_weighted_realization_with_vertex_bound hn q w hsym hdiag hnonneg hw hstrict R
theorem boundary_quartets_bound_sharp :
    (∀ K : Body 5, (∀ i j, i ≠ j → 0 < coordinateAreaMatrix K i j) →
      (Finset.univ.filter fun m : Fin 5 =>
        IsBoundaryQuartet (coordinateAreaMatrix (deleteBody m K))).card ≤ 3) ∧
    ∃ K : Body 5, (∀ i j, i ≠ j → 0 < coordinateAreaMatrix K i j) ∧
      (Finset.univ.filter fun m : Fin 5 =>
        IsBoundaryQuartet (coordinateAreaMatrix (deleteBody m K))).card = 3 := ProjectionAreaMixedGeometry.boundary_quartets_bound_sharp

theorem boundary_quartets_unique_extension (K : Body 5)
    (hpositive : ∀ i j, i ≠ j → 0 < coordinateAreaMatrix K i j)
    (hcount : 2 ≤ (Finset.univ.filter fun m : Fin 5 =>
      IsBoundaryQuartet (coordinateAreaMatrix (deleteBody m K))).card) :
    ∃! larger : Finset (Fin 5), BoundaryPartitionExtension K larger := ProjectionAreaMixedGeometry.boundary_quartets_unique_extension K hpositive hcount
theorem selected_boundary_quartets_card_le_three {d : ℕ} (K : CoordinateBody d)
    (σ : Fin 5 → Fin d) (hσ : Function.Injective σ)
    (hpositive : ∀ i j, σ i ≠ σ j → 0 < coordinateAreas K (σ i) (σ j)) :
    (Finset.univ.filter fun m : Fin 5 => IsBoundaryQuartet
      ((coordinateAreas K).submatrix (σ ∘ m.succAbove) (σ ∘ m.succAbove))).card ≤ 3 := ProjectionAreaPaper.selected_boundary_quartets_card_le_three K σ hσ hpositive
theorem selected_boundary_quartets_unique_extension {d : ℕ} (K : CoordinateBody d)
    (σ : Fin 5 → Fin d) (hσ : Function.Injective σ)
    (hpositive : ∀ i j, σ i ≠ σ j → 0 < coordinateAreas K (σ i) (σ j))
    (hcount : 2 ≤ (Finset.univ.filter fun m : Fin 5 => IsBoundaryQuartet
      ((coordinateAreas K).submatrix (σ ∘ m.succAbove) (σ ∘ m.succAbove))).card) :
    ∃! larger : Finset (Fin 5),
      BoundaryPartitionExtension (selectBody σ (asPiBody K)) larger := ProjectionAreaPaper.selected_boundary_quartets_unique_extension K σ hσ hpositive hcount
theorem exists_open_nonrealizable_strict_quartets (d : ℕ) (hd : 5 ≤ d) :
    ∃ U : Set (HollowSymmetricArray d), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U,
        PositiveArray (q : AreaArray d) ∧
        (q : AreaArray d) ∉ closure (realizationLocus d) ∧
        ∀ σ : Fin 4 → Fin d, Function.Injective σ →
          HasSignatureOneThree ((q : AreaArray d).submatrix σ σ) := ProjectionAreaPaper.exists_open_nonrealizable_strict_quartets d hd
theorem weighted_triangles_obstruction {n : ℕ} (P : PositiveHollowMatrix n) (hn : 5 ≤ n) (hrank : P.entries.rank ≤ 3) :
    ¬ ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ x ≠ 0 ∧ P.WeightedTriangles x := ProjectionAreaRankThree.PositiveHollowMatrix.weighted_triangles_obstruction P hn hrank

theorem rank_at_most_three_classification {n : ℕ} (Q : ProjectionAreaRankThree.NonnegativeHollowMatrix n) (hrank : Q.entries.rank ≤ 3) :
    (Q.entries ∈ realizationLocus n ↔ Q.entries ∈ closure (realizationLocus n)) ∧
      (Q.entries ∈ realizationLocus n ↔ Nat.card (Quot (fun i j : {i : Fin n // Q.entries i ≠ 0} => Q.entries i.val j.val = 0)) ≤ 4)  := by
  have hcard : Nat.card (Quot (fun i j : {i : Fin n // Q.entries i ≠ 0} =>
      Q.entries i.val j.val = 0)) = Fintype.card (Q.Classes hrank) := by
    change Nat.card (Q.Classes hrank) = Fintype.card (Q.Classes hrank)
    exact Nat.card_eq_fintype_card
  rw [hcard]
  exact ProjectionAreaPaper.NonnegativeHollowMatrix.rank_at_most_three_classification Q hrank

end PalomarProjectionAreas
