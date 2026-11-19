module

public import Recovery.Unimodular.ProductFanRays

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open TauCeti.Toric

namespace Unimodular.FanProducts

variable {J E : Type*} [Fintype J] [DecidableEq J] [Fintype E]
variable {N V : J → Type*} [∀ j, AddCommGroup (N j)]
  [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
  [∀ j, FiniteDimensional ℝ (V j)]

/-- The first clause of Proposition 4.1 in arbitrary finite direct-product
lattice coordinates. Every factor has exactly its assigned original rays,
every cone is retained, all choices of factor cones occur, and the actual
factor fans are unique. Unimodularity, simpliciality and projectivity are not
required for this geometric assertion. -/
theorem proposition_4_1_exact_rays (i : ∀ j, N j →+ V j)
    (hi : ∀ j, IsIntegralLattice (i j)) (u : E → ∀ j, N j) (f : E → J)
    (Φ : Fan (piEmbedding i)) (hc : Φ.IsComplete)
    (hr : AllowedBlocks.HasRays (piEmbedding i) u Φ)
    (hnz : ∀ e, (piEmbedding i) (u e) ≠ 0)
    (hs : ∀ e k, k ≠ f e → i k (u e k) = 0) :
    ∃ Ψ : ∀ j, Fan (i j),
      (∀ j, (Ψ j).IsComplete) ∧
      (∀ j, AllowedBlocks.HasRays (i j)
        (fun e : {e : E // f e = j} => u e.val j) (Ψ j)) ∧
      (∀ C : PointedCone ℝ (∀ j, V j), C ∈ Φ.cones ↔
        ∃ D : ∀ j, PointedCone ℝ (V j), (∀ j, D j ∈ (Ψ j).cones) ∧ C = conePi D) ∧
      (∀ j (C : PointedCone ℝ (V j)),
        C.map (LinearMap.single ℝ V j) ∈ Φ.cones ↔ C ∈ (Ψ j).cones) ∧
      (∀ Ω : ∀ j, Fan (i j), (∀ j, (Ω j).IsComplete) →
        (∀ C : PointedCone ℝ (∀ j, V j), C ∈ Φ.cones ↔
          ∃ D : ∀ j, PointedCone ℝ (V j), (∀ j, D j ∈ (Ω j).cones) ∧ C = conePi D) →
        Ψ = Ω) := by
  let h := hasSummandRays_of_hasRays i u f Φ hr hs
  refine ⟨factorFan i hi Φ h, fun j => factorFan_complete i hi Φ h hc j,
    factorFan_hasRays i u f Φ hi hr hnz hs, proposition_4_1_cones i hi Φ h hc,
    map_single_mem_iff i hi Φ h, ?_⟩
  intro Ω hΩc hΩ
  exact funext (factorFan_unique i hi Φ h Ω hΩc hΩ)

end Unimodular.FanProducts

#print axioms Unimodular.FanProducts.proposition_4_1_exact_rays
#check "UNIMODULAR_GENERAL_PRODUCT_DECOMPOSITION_EOF_V1"
