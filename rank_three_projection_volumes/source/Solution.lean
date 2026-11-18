module

public import rank_three_projection

/-! # Rank-three projection-volume obstructions and compactification
Theorem 1.1 excludes every positive hollow symmetric rank-three array in
n at least five from the closure of actual complementary projection volumes,
including its inertia, strict perturbation and open-family conclusions.
Theorem 3.1 represents every limit for 1 <= k < n by actual mixed volumes
with finite marked segments, with the exact affine-dimension bound.
All geometric definitions below concern literal sets and Lebesgue measure.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Module Filter QuadraticMap
open scoped BigOperators Pointwise Matrix Topology
namespace PalomarRankThree

/-- Finite coordinate space with real entries. -/
abbrev Space (n : ℕ) := Fin n → ℝ

/-- The ordinary space of n by n real matrices. -/
abbrev Array (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Coordinates remaining after a finite set has been deleted. -/
abbrev Retained {n : ℕ} (I : Finset (Fin n)) := {j : Fin n // j ∉ I}

/-- The k-element sets of deleted coordinates. -/
abbrev Deleted (n k : ℕ) := {I : Finset (Fin n) // I.card = k}

/-- Zero diagonal, symmetry, and strict positivity at every off-diagonal entry. -/
def PositiveHollowSymmetric {n : ℕ} (P : Array n) : Prop :=
  (∀ i, P i i = 0) ∧ (∀ i j, P i j = P j i) ∧ (∀ i j, i ≠ j → 0 < P i j)

/-- The subspace of symmetric hollow matrices. -/
abbrev HollowSymmetricArray (n : ℕ) :=
  {P : Array n // (∀ i, P i i = 0) ∧ (∀ i j, P i j = P j i)}

/-- One positive, n-1 negative and no zero quadratic-form directions. -/
def StrictLorentzian {n : ℕ} (P : Array n) : Prop :=
  sigPos P.toQuadraticForm' = 1 ∧
  sigNeg P.toQuadraticForm' = n - 1 ∧
  finrank ℝ P.toQuadraticForm'.radical = 0

/-- An actual nonempty compact convex subset of Euclidean space; lower affine dimensions are allowed. -/
abbrev EuclideanBody (n : ℕ) := ConvexBody (EuclideanSpace ℝ (Fin n))

/-- The continuous linear coordinate-deletion map. -/
def deleteCoordinates {n : ℕ} (I : Finset (Fin n)) :
    Space n →L[ℝ] (Retained I → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj j.val)

/-- The identity on coordinates, transported to the Euclidean norm. -/
def coordinateEuclideanEquiv (ι : Type*) [Fintype ι] :
    (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm

/-- The explicit hollow perturbation from Theorem 1.1. -/
def strictPerturb {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ) (a : ι → ℝ) (ε : ℝ) : Matrix ι ι ℝ :=
  fun i j => P i j + ε * (a i*a j - if i = j then (a i)^2 else 0)

section Maps
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Image of the literal compact convex set by a continuous linear map. -/
def mapBody (f : E →L[ℝ] F) (K : ConvexBody E) : ConvexBody F where
  carrier := f '' (K : Set E)
  convex' := K.convex.linear_image f.toLinearMap
  isCompact' := K.isCompact.image f.continuous
  nonempty' := K.nonempty.image f
end Maps

/-- Coordinate deletion between canonical Euclidean spaces. -/
def euclideanDeleteCoordinates {n : ℕ} (I : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Retained I) :=
  (coordinateEuclideanEquiv (Retained I)).toContinuousLinearMap.comp
    ((deleteCoordinates I).comp
      (coordinateEuclideanEquiv (Fin n)).symm.toContinuousLinearMap)

/-- Actual Lebesgue volume of the coordinate projection. -/
def euclideanCoordinateVolume {n : ℕ} (I : Finset (Fin n))
    (K : EuclideanBody n) : ℝ :=
  volume.real (mapBody (euclideanDeleteCoordinates I) K :
    Set (EuclideanSpace ℝ (Retained I)))

/-- The array of projection volumes indexed by all k-element deletion sets. -/
def euclideanAllProjectionArray {n k : ℕ} (K : EuclideanBody n) : Deleted n k → ℝ :=
  fun I => euclideanCoordinateVolume I.val K

/-- The actual range of projection-volume arrays. -/
def euclideanAllProjectionLocus (n k : ℕ) : Set (Deleted n k → ℝ) :=
  Set.range (euclideanAllProjectionArray (n := n) (k := k))

/-- The hollow complementary projection-volume array. -/
def euclideanProjectionArray {n : ℕ} (K : EuclideanBody n) : Array n :=
  fun i j => if i = j then 0 else euclideanCoordinateVolume {i, j} K

/-- The range of complementary projection-volume arrays. -/
def euclideanProjectionLocus (n : ℕ) : Set (Array n) :=
  Set.range (euclideanProjectionArray (n := n))

/-- Topological closure of the actual realization locus. -/
def euclideanClosedProjectionLocus (n : ℕ) : Set (Array n) :=
  closure (euclideanProjectionLocus n)

/-- Affine dimension of the actual Euclidean body. -/
def euclideanBodyDimension {n : ℕ} (K : EuclideanBody n) : ℕ :=
  finrank ℝ (affineSpan ℝ (K : Set (EuclideanSpace ℝ (Fin n)))).direction

section Segments
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The actual closed segment with its compact convex body structure. -/
def segmentBody (a b : E) : ConvexBody E where
  carrier := segment ℝ a b
  convex' := convex_segment a b
  isCompact' := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  nonempty' := ⟨a, left_mem_segment ℝ a b⟩
/-- The segment with endpoints -v/2 and v/2. -/
def centeredSegment (v : E) : ConvexBody E :=
  segmentBody (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)
end Segments

/-- The unique volume polynomial, selected by its literal volume identity.
Existence and uniqueness are proved in Solution, so this independent choice
has exactly the same value as the original proof-dependent choice. -/
def literalVolumePolynomial {n d : ℕ} (K : Fin n → EuclideanBody d) :
    MvPolynomial (Fin n) ℝ :=
  Classical.epsilon (fun p : MvPolynomial (Fin n) ℝ =>
    p.IsHomogeneous (finrank ℝ (EuclideanSpace ℝ (Fin d))) ∧
    (∀ m, 0 ≤ p.coeff m) ∧
    ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
      MvPolynomial.eval t p = volume.real ((∑ i, t i • K i : EuclideanBody d) :
        Set (EuclideanSpace ℝ (Fin d))))
/-- The normalized squarefree coefficient of the actual volume polynomial. -/
def literalMixedVolume {r d : ℕ} (K : Fin r → EuclideanBody d) : ℝ :=
  (literalVolumePolynomial K).coeff (Finsupp.equivFunOnFinite.symm (fun _ => 1)) / r.factorial

/-- The tuple with n-k copies of K and centered marked segments. -/
def euclideanMarkedTuple {n k : ℕ} (K : EuclideanBody n)
    (U : Fin n → EuclideanSpace ℝ (Fin n)) (I : Deleted n k) :
    Fin (n - k + k) → EuclideanBody n :=
  Fin.append (fun _ : Fin (n - k) => K)
    (fun j : Fin k => centeredSegment (U (I.val.orderEmbOfFin I.property j)))

/-- Normalized mixed volumes of the literal marked tuple. -/
def euclideanAllMarkedArray {n k : ℕ} (K : EuclideanBody n)
    (U : Fin n → EuclideanSpace ℝ (Fin n)) : Deleted n k → ℝ :=
  fun I => (n.factorial : ℝ) / ((n - k).factorial : ℝ) *
    literalMixedVolume (euclideanMarkedTuple K U I)

/-- Positive hollow strict Lorentzian counterexamples in Euclidean coordinates. -/
def strictCounterexampleLocus (n : ℕ) : Set (Array n) :=
  {Q | PositiveHollowSymmetric Q ∧ StrictLorentzian Q ∧ Q ∉ euclideanClosedProjectionLocus n}

/-- Independence of the volume-polynomial choice follows from its actual evaluations. -/
theorem literalVolumePolynomial_eq {n d : ℕ} (K : Fin n → EuclideanBody d) :
    literalVolumePolynomial K = VolumePolynomials.volumePolynomial volume K := by
  have hex : ∃ p : MvPolynomial (Fin n) ℝ,
      p.IsHomogeneous (finrank ℝ (EuclideanSpace ℝ (Fin d))) ∧
      (∀ m, 0 ≤ p.coeff m) ∧
      ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
        MvPolynomial.eval t p = volume.real ((∑ i, t i • K i : EuclideanBody d) :
          Set (EuclideanSpace ℝ (Fin d))) :=
    VolumePolynomials.hasPositiveVolumePolynomial volume K
  have hp := Classical.epsilon_spec hex
  exact (VolumePolynomials.volumePolynomial_eq_of_eval volume K _ hp.2.2).symm

theorem literalMixedVolume_eq {r d : ℕ} (K : Fin r → EuclideanBody d) :
    literalMixedVolume K = VolumePolynomials.mixedVolume volume K := by
  unfold literalMixedVolume VolumePolynomials.mixedVolume
  rw [literalVolumePolynomial_eq]
  rfl

theorem markedArray_eq {n k : ℕ} (K : EuclideanBody n)
    (U : Fin n → EuclideanSpace ℝ (Fin n)) :
    euclideanAllMarkedArray (k := k) K U =
      RankThreeProjection.euclideanAllMarkedArray K U := by
  funext I
  unfold euclideanAllMarkedArray RankThreeProjection.euclideanAllMarkedArray
  rw [literalMixedVolume_eq]
  rfl

theorem projectionLocus_eq (n k : ℕ) :
    euclideanAllProjectionLocus n k = RankThreeProjection.euclideanAllProjectionLocus n k := by rfl
theorem closedProjectionLocus_eq (n : ℕ) :
    euclideanClosedProjectionLocus n = RankThreeProjection.euclideanClosedProjectionLocus n := by rfl
theorem dimension_eq {n : ℕ} (K : EuclideanBody n) :
    euclideanBodyDimension K = RankThreeProjection.euclideanBodyDimension K := by rfl

/-- The independent perturbation has the complete source value as a function of epsilon. -/
theorem strictPerturb_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (a : ι → ℝ) :
    strictPerturb P a = VolumeVerification.MatrixInertia.strictPerturb P a := by rfl

/-- Every original hollow, symmetric and positive entry condition is retained. -/
theorem positiveHollowSymmetric_iff {n : ℕ} (P : Array n) :
    PositiveHollowSymmetric P ↔ RankThreeProjection.PositiveHollowSymmetric P := by rfl

/-- The full positive/negative/radical inertia predicate is identical. -/
theorem strictLorentzian_iff {n : ℕ} (P : Array n) :
    StrictLorentzian P ↔ RankThreeProjection.StrictLorentzian P := by rfl
theorem theorem11_euclidean {n : ℕ} (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    P ∉ euclideanClosedProjectionLocus n ∧
      (sigPos P.toQuadraticForm' = 1 ∧
        sigNeg P.toQuadraticForm' = 2 ∧
        finrank ℝ P.toQuadraticForm'.radical = n - 3) ∧
      ∃ a : Fin n → ℝ,
        (∀ i, 0 < a i) ∧
        Tendsto (strictPerturb P a) (𝓝 0) (𝓝 P) ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
          PositiveHollowSymmetric (strictPerturb P a ε) ∧
          StrictLorentzian (strictPerturb P a ε) ∧
          strictPerturb P a ε ∉ euclideanClosedProjectionLocus n) ∧
        (∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
          ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
            Q.val ∉ euclideanClosedProjectionLocus n) := by
  simpa only [closedProjectionLocus_eq, strictPerturb_eq,
    positiveHollowSymmetric_iff, strictLorentzian_iff] using
    RankThreeProjection.theorem11_euclidean hn P hP hrank

theorem theorem31_euclidean {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (P : Deleted n k → ℝ) :
    P ∈ closure (euclideanAllProjectionLocus n k) ↔
      ∃ (K : EuclideanBody n) (U : Fin n → EuclideanSpace ℝ (Fin n)),
        n - k + 1 ≤ euclideanBodyDimension K ∧ euclideanAllMarkedArray K U = P := by
  simpa only [markedArray_eq, projectionLocus_eq, dimension_eq] using
    RankThreeProjection.theorem31_euclidean hk hkn P

theorem theorem31_euclidean_closure {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (P : Deleted n k → ℝ) :
    P ∈ closure (euclideanAllProjectionLocus n k) ↔
      ∃ (K : EuclideanBody n) (U : Fin n → EuclideanSpace ℝ (Fin n)),
        euclideanAllMarkedArray K U = P := by
  simpa only [markedArray_eq, projectionLocus_eq] using
    RankThreeProjection.theorem31_euclidean_closure hk hkn P

theorem theorem31_euclidean_renormalize_dimension {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n) (K : EuclideanBody n)
    (U : Fin n → EuclideanSpace ℝ (Fin n)) :
    ∃ (L : EuclideanBody n) (V : Fin n → EuclideanSpace ℝ (Fin n)),
      n - k + 1 ≤ euclideanBodyDimension L ∧
        euclideanAllMarkedArray (k := k) L V = euclideanAllMarkedArray K U := by
  simpa only [markedArray_eq, dimension_eq] using
    RankThreeProjection.theorem31_euclidean_renormalize_dimension hk hkn K U

theorem exists_open_counterexamples {n : ℕ} (hn : 5 ≤ n) :
    ∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
      ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
        Q.val ∉ euclideanClosedProjectionLocus n := by
  simpa only [closedProjectionLocus_eq, RankThreeProjection.euclideanClosedProjectionLocus_eq,
    positiveHollowSymmetric_iff, strictLorentzian_iff]
    using RankThreeProjection.exists_open_counterexamples hn

end PalomarRankThree
