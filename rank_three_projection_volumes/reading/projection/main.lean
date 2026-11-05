module

public import Projection.Normalization.Theorem31
public import Projection.CoordinateMeaning
public import Projection.SignatureMeaning
public import Projection.Rigidity.FullDimensional

/-!
# Principal statements of the projection-volume paper

The statements below retain the paper's unrestricted dimensions, positive
off-diagonal entries, actual matrix rank and inertia, actual coordinate
projection volumes, and topological closure. No rigidity proposition occurs
as an additional theorem hypothesis.

The project's status file, complete build log, and signature/axiom audit record
the verification evidence. The presence of these source statements alone is
not a certificate of mechanical verification.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Module Filter
open scoped Matrix Topology

namespace RankThreeProjection
open VolumeVerification.MatrixInertia

/-- The actual strict counterexamples, as a subset of the ordinary matrix
space. This set is used to state the paper's limit conclusion directly. -/
def strictCounterexampleLocus (n : ℕ) : Set (Array n) :=
  {Q | PositiveHollowSymmetric Q ∧ StrictLorentzian Q ∧
    Q ∉ closedProjectionLocus n}

/-- The exclusion conclusion of Theorem 1.1, for every n≥5. -/
theorem rank_three_projection_exclusion {n : ℕ} (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    P ∉ closedProjectionLocus n := by
  letI : NeZero n := ⟨by omega⟩
  exact rank_three_exclusion_of_rigidity hn (fullDimensionalRigidity n) P hP hrank

/-- Theorem 1.1, including inertia, strict perturbations converging to each
rank-three matrix, and a nonempty relative-open family of strict counterexamples. -/
theorem theorem11 {n : ℕ} (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    P ∉ closedProjectionLocus n ∧
      (sigPos P.toQuadraticForm' = 1 ∧
        sigNeg P.toQuadraticForm' = 2 ∧
        finrank ℝ P.toQuadraticForm'.radical = n - 3) ∧
      ∃ a : Fin n → ℝ,
        (∀ i, 0 < a i) ∧
        Tendsto (strictPerturb P a) (𝓝 0) (𝓝 P) ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
          PositiveHollowSymmetric (strictPerturb P a ε) ∧
          StrictLorentzian (strictPerturb P a ε) ∧
          strictPerturb P a ε ∉ closedProjectionLocus n) ∧
        (∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
          ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
            Q.val ∉ closedProjectionLocus n) := by
  letI : NeZero n := ⟨by omega⟩
  exact theorem11_from_rigidity hn (fullDimensionalRigidity n) P hP hrank

/-- The limit assertion of Theorem 1.1 in its direct topological form.
This formally derives closure membership from the positive-parameter
perturbation family, rather than leaving that passage informal. -/
theorem rank_three_limit_strict_counterexamples {n : ℕ} (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    P ∈ closure (strictCounterexampleLocus n) := by
  obtain ⟨a, _ha, hlim, ⟨δ, hδ, hsmall⟩, _hopen⟩ :=
    (theorem11 hn P hP hrank).2.2
  apply mem_closure_of_tendsto
    (hlim.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  have hδ' : Iio δ ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, hδ'] with ε hε hεδ
  exact hsmall ε hε hεδ

/-- The nonempty open counterexample family exists in every dimension n≥5,
without taking the existence of a rank-three example as a hypothesis. -/
theorem exists_open_counterexamples {n : ℕ} (hn : 5 ≤ n) :
    ∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
      ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
        Q.val ∉ closedProjectionLocus n := by
  letI : NeZero n := ⟨by omega⟩
  exact exists_open_counterexamples_from_rigidity hn (fullDimensionalRigidity n)

/-- Theorem 1.1 with canonical Euclidean bodies and Euclidean projection
volume throughout. The exact coordinate-model equivalence has been proved,
including equality of realization loci, rather than assumed informally. -/
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
  simpa only [euclideanClosedProjectionLocus_eq] using theorem11 hn P hP hrank

end RankThreeProjection
