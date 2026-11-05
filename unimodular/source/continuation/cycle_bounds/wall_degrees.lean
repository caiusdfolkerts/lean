module

public import Continuation.CycleBounds.FanStrata
public import Continuation.Divisor.WallCurves

@[expose] public section

/-! # Proposition6.8 on the genuine invariant wall curves

The numerical slack is identified with the degree of the actual pullback sheaf,
using the recovered scheme-theoretic wall-curve theorem. No numerical definition
of line-bundle degree is substituted for the geometric one.
-/

noncomputable section
universe u
namespace PaperVerification.ToricGeometry.SmoothCompleteFan
open AlgebraicGeometry CategoryTheory
open Unimodular.CycleBounds Unimodular.SeriesParallel
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (F : SmoothCompleteFan n)

/-- Every actual wall curve carries the indicated ordinary line-bundle degree,
which is bounded by the geometric dimension of the Thomsen stratum. -/
theorem thomsen_wallCurve_degree_bound {V : Type*} [Fintype V]
    (G : IncidenceGraph V F.rays) (hG : G.edges = Set.univ) (hK : ¬G.HasK4Minor)
    (δ : Lattice n →ₗ[ℤ] (V → ℤ)) (hinj : Function.Injective δ)
    (hδ : ∀ u : F.rays, δ u.val = Pi.single (G.source u) 1 - Pi.single (G.target u) 1)
    (k : Type u) [Field k] (hpure : F.IsPure)
    (θ : Module.Dual ℝ (Ambient n)) (s : F.fullCones) (j : Fin n)
    (t : F.fullCones) (w : Lattice n)
    (ht : t.val = insert w ((F.wallIndices s j).image (F.fullConeBasis s)))
    (hwj : (F.fullConeBasis s).repr w j = -1) :
    ∃ d : ℤ,
      (F.wallCurveFan s j).OneDimensionalHasDegree (F.wallIndices_codimension s j) k
        ((Scheme.Modules.pullback (F.wallCurveInclusion s j k)).obj
          (F.fanCartierData k hpure (F.thomsenCoefficients θ)).sheaf) d ∧
      d ≤ (F.thomsenStratumDimension θ : ℤ) := by
  have hw : w ∈ F.rays := F.ray_mem_of_mem_cone (F.fullCones_mem t)
    (by rw [ht]; exact Finset.mem_insert_self _ _)
  refine ⟨F.integerWallSlack (F.thomsenCoefficients θ) s w,
    F.wallCurve_fanCartier_hasDegree s j k hpure (F.thomsenCoefficients θ) t w ht hwj, ?_⟩
  exact F.thomsen_wall_slack_le_stratum_dimension G hG hK δ hinj hδ θ s ⟨w, hw⟩

#print axioms thomsen_wallCurve_degree_bound
end PaperVerification.ToricGeometry.SmoothCompleteFan
