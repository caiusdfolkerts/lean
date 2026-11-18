module
public import theorem94

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PalomarBarycentricScalar
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical MvPolynomial Finset
open FourPapers.Universal FourPapers.Universal.ScalarFamilies
universe uScalar
variable (V K : Type uScalar) [Fintype V] [CommRing K]

theorem exactScalarIdeal (c : K) :
    (∃ F : comparisonModule (P := Finset V) K,
      (∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F) ∧ scalar K F = c) ↔
      c ∈ Ideal.span {((Fintype.card V - 1).factorial : K)} := by
  rw [← scalar_mem_invariantIdeal_iff K (fun σ : Equiv.Perm V => finsetOrderCongr σ)
    simplexOrderAction_one simplexOrderAction_mul c, theorem_9_4_scalarIdeal]
end
end PalomarBarycentricScalar

namespace PalomarBarycentricScalar
section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Classical MvPolynomial Finset
open FourPapers.Universal FourPapers.Universal.ScalarFamilies
universe uScalar
variable (V K : Type uScalar) [Fintype V] [CommRing K]

theorem cohomologicalObstructionModule :
    Nonempty (Submodule.span K {(comparisonObstruction K (simplex_isSimplicialPoset (V := V))
      (fun σ : Equiv.Perm V => finsetOrderCongr σ) simplexOrderAction_one simplexOrderAction_mul)} ≃ₗ[K]
      (K ⧸ Ideal.span {((Fintype.card V - 1).factorial : K)})) := ⟨FourPapers.Universal.ScalarFamilies.theorem_9_4_obstructionModule K⟩
end
end PalomarBarycentricScalar

