module

public import Projection.ComplementaryCompactification
public import Projection.FullDimensionalReduction
public import Projection.BodyDimension
public import Projection.StrictTopology
public import VolumeVerification.RankThreeExamples

/-!
# Conditional assembly with the rigidity obligation displayed

This file assembles the geometric branches under an explicit rigidity
interface. `Rigidity.FullDimensional` supplies that interface, and `Main`
states the unconditional Theorem 1.1. This intermediate file alone does not
establish the principal theorem. Verification of the complete chain is recorded
in the project's build and endpoint-audit reports.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Module Filter
open scoped Matrix Topology

namespace RankThreeProjection
open VolumeVerification.MatrixInertia

section
variable {n : ℕ} [NeZero n]

/-- The repeated-body equality theorem, restricted to precisely the actual
coordinate-space bodies needed in the final argument. Its proof is supplied by
`Rigidity.FullDimensional`, and `Main` discharges it in the principal statements. -/
def FullDimensionalRigidity : Prop :=
  ∀ (K : Body n) (d : ℕ) (hdim : finrank ℝ (Space n) = d + 2),
    (interior (K : Set (Space n))).Nonempty → SegmentAreaRigidity K hdim

/-- The two dimension branches and the exact compactification imply closure
exclusion once the remaining geometric rigidity theorem has been supplied. -/
theorem rank_three_exclusion_of_rigidity (hn : 5 ≤ n)
    (hR : FullDimensionalRigidity (n := n))
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    P ∉ closedProjectionLocus n := by
  intro hclosure
  obtain ⟨K,U,_hdimension,hrep⟩ :=
    (complementary_compactification (by omega) P).mp hclosure
  have hdim : finrank ℝ (Space n) = (n - 2) + 2 := by
    simp only [Space, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  have hpositive : ∀ i j, i ≠ j →
      0 < complementaryMixedMatrix (d := n - 2) K U i j := by
    simpa only [hrep] using hP.2.2
  have hrank' : (complementaryMixedMatrix (d := n - 2) K U).rank = 3 := by
    simpa only [hrep] using hrank
  by_cases hfull : (interior (K : Set (Space n))).Nonempty
  · exact full_dimensional_obstruction_from_segment_rigidity K hdim hn U
      hpositive hrank' (hR K (n - 2) hdim hfull)
  · apply nonfull_representation_impossible hn K hdim U ?_ hpositive hrank'.le
    have hbody : bodyDimension K < n :=
      (bodyDimension_lt_iff_interior_empty K).mpr
        (Set.not_nonempty_iff_eq_empty.mp hfull)
    simpa only [bodyDimension, Space, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using hbody

/-- The inertia assertion itself uses no geometric rigidity hypothesis. -/
theorem rank_three_signature (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3) :
    sigPos P.toQuadraticForm' = 1 ∧
      sigNeg P.toQuadraticForm' = 2 ∧
      finrank ℝ P.toQuadraticForm'.radical = n - 3 := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let i₂ : Fin n := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by intro h; have := congrArg Fin.val h; simp [i₀, i₁] at this
  have h02 : i₀ ≠ i₂ := by intro h; have := congrArg Fin.val h; simp [i₀, i₂] at this
  have h12 : i₁ ≠ i₂ := by intro h; have := congrArg Fin.val h; simp [i₁, i₂] at this
  simpa only [Fintype.card_fin] using positive_hollow_rank_three_signature
    P hP.2.1 hP.1 hP.2.2 hrank i₀ i₁ i₂ h01 h02 h12

/-- Assembly of all conclusions, still conditional on the one named
geometric obligation. This conditional statement is not a verification of
the paper's unconditional principal theorem. -/
theorem theorem11_from_rigidity (hn : 5 ≤ n)
    (hR : FullDimensionalRigidity (n := n))
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
  have hout := rank_three_exclusion_of_rigidity hn hR P hP hrank
  exact ⟨hout, rank_three_signature hn P hP hrank,
    rank_three_strict_family hn P hP hrank hout⟩

/-- The relative-open family is nonempty in every dimension at least five,
once the remaining geometric rigidity theorem has been supplied. -/
theorem exists_open_counterexamples_from_rigidity (hn : 5 ≤ n)
    (hR : FullDimensionalRigidity (n := n)) :
    ∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
      ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
        Q.val ∉ closedProjectionLocus n := by
  let P := VolumeVerification.RankThreeExamples.squaredIndexMatrix n
  have hP : PositiveHollowSymmetric P :=
    ⟨VolumeVerification.RankThreeExamples.squaredIndexMatrix_diagonal n,
      VolumeVerification.RankThreeExamples.squaredIndexMatrix_symmetric n,
      VolumeVerification.RankThreeExamples.squaredIndexMatrix_positive n⟩
  have hrank : P.rank = 3 :=
    VolumeVerification.RankThreeExamples.squaredIndexMatrix_rank n (by omega)
  obtain ⟨a, _ha, _hlim, _hsmall, hopen⟩ :=
    rank_three_strict_family hn P hP hrank
      (rank_three_exclusion_of_rigidity hn hR P hP hrank)
  exact hopen

end
end RankThreeProjection

