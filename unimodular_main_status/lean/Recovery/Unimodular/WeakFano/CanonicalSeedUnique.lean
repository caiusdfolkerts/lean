module

public import Recovery.Unimodular.WeakFano.CanonicalSeedOriginal

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set TauCeti.Toric

namespace Unimodular.OriginalSeedGeometry

variable {n : ℕ} {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : N →+ V}

/-- The seed fan in the original lattice is unique. Thus the coordinate
witness used to construct it introduces no choice of a different fan. -/
theorem exists_unique_canonical_seed (hn : 0 < n) (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Finset N)
    (hU : IntegralRigidity.Uniform b (fun u : (U : Set N) => u.val))
    (hpos : PointedCone.hull ℝ (ι '' (U : Set N)) = ⊤) (hzero : (0 : N) ∉ U) :
    ∃! Φ : Fan ι, Φ.IsComplete ∧
      AllowedBlocks.HasRays ι (fun u : (U : Set N) => u.val) Φ ∧
      (∀ C, C ∈ Φ.cones ↔ ∃ F : Set V, Convex ℝ F ∧
        IsExtreme ℝ (originalHull (ι := ι) U) F ∧
        F ≠ originalHull (ι := ι) U ∧ C = PointedCone.hull ℝ F) ∧
      (∀ C, C ∈ Φ.cones ↔ ∃ f ∈ polar (originalHull (ι := ι) U),
        C = NormalFanSupport.normalCone (polar (originalHull (ι := ι) U)) f) := by
  obtain ⟨_hz, _hdual, _hext, _hpoints, Φ, hΦ⟩ :=
    lemma_3_2_original hn hι b U hU hpos hzero
  refine ⟨Φ, hΦ, ?_⟩
  intro Ψ hΨ
  apply Fan.ext
  ext C
  exact (hΨ.2.2.1 C).trans (hΦ.2.2.1 C).symm

end Unimodular.OriginalSeedGeometry

#print axioms Unimodular.OriginalSeedGeometry.exists_unique_canonical_seed
#check Unimodular.OriginalSeedGeometry.exists_unique_canonical_seed
