module
public import wishart_main
@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace WishartVerification.MomentAssembly
variable {ι : Type*} [DecidableEq ι]
/-- The complete original rank threshold, including both exact indices and every input. -/
theorem orderedRankThreshold_original_value (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ) :
    orderedRankThreshold rank A p n =
      (∀ h : 3 ≤ Fintype.card A,
        min ((descendingRanks rank A ⟨0, by omega⟩ : ℝ) +
          descendingRanks rank A ⟨2, by omega⟩) ((p : ℝ) + 1) ≤ n) := by rfl
/-- The complete original gauge threshold uses the same literal third index. -/
theorem orderedGaugeRankThreshold_original_value (rank : ι → ℕ) (A : Finset ι) (n : ℝ) :
    orderedGaugeRankThreshold rank A n =
      (∀ h : 3 ≤ Fintype.card A, (descendingRanks rank A ⟨2, by omega⟩ : ℝ) + 1 ≤ n) := by rfl
/-- The complete original pair threshold, without any additional rank assumption. -/
theorem orderedPairRankThreshold_original_value (rank : ι → ℕ) (A : Finset ι) (p : ℕ) (n : ℝ) :
    orderedPairRankThreshold rank A p n =
      (∀ h : 2 ≤ Fintype.card A,
        min ((descendingRanks rank A ⟨0, by omega⟩ : ℝ) +
          descendingRanks rank A ⟨1, by omega⟩) ((p : ℝ) + 1) ≤ n) := by rfl
/-- The complete original singular-sample threshold keeps its natural sample parameter. -/
theorem gramOrderedRankThreshold_original_value (rank : ι → ℕ) (A : Finset ι) (n : ℕ) :
    gramOrderedRankThreshold rank A n =
      (∀ h : 3 ≤ Fintype.card A,
        descendingRanks rank A ⟨0, by omega⟩ + descendingRanks rank A ⟨2, by omega⟩ ≤ n) := by rfl
end WishartVerification.MomentAssembly
namespace Wishart.Spectral
/-- The exact original cardinality cast gives the same full permutation. -/
theorem ascendingIndexEquiv_original_value (p : ℕ) :
    ascendingIndexEquiv p = Fin.revPerm.trans ((finCongr (Fintype.card_fin p).symm).trans
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin p))))) := by rfl
/-- The identity matrix's entire subtype value is unchanged. -/
theorem identitySymmetric_original_value (p : ℕ) :
    identitySymmetric p = ⟨1, Matrix.isHermitian_one.isSelfAdjoint⟩ := by rfl
end Wishart.Spectral
