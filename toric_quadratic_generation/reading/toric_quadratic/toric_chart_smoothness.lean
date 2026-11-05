module
public import PaperVerification.ToricIntegralAffine
@[expose] public section
/-!
# Smoothness transferred from saturated local face coordinates

At each face vertex, one may choose a different saturated coordinate chart.
The integral transition map converts its standard primitive edge basis into a
basis in any fixed chart, proving the literal global smoothness definition.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange

/-- Standard primitive edge charts at every actual vertex prove that any
fixed saturated lattice-polytope chart of the same set is smooth. -/
theorem smooth_of_local_saturated_charts {d n : ℕ} (F : Set (Ambient n))
    (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n)
    (heF : e.realMap '' Q.carrier = F)
    (hlocal : ∀ v ∈ F.extremePoints ℝ,
      ∃ (k : ℕ) (R : LatticePolytope k) (f : IntegralAffineEmbedding k n)
        (lengths : Fin k → ℕ),
        f.realMap 0 = v ∧ f.realMap '' R.carrier = F ∧
        (∀ i, 0 < lengths i ∧
          R.IsEdge 0 (embed k ((lengths i : ℤ) • Pi.basisFun ℤ (Fin k) i))) ∧
        (∀ w, R.IsEdge 0 w →
          ∃ i, w = embed k ((lengths i : ℤ) • Pi.basisFun ℤ (Fin k) i))) :
    Q.Smooth := by
  classical
  intro v hv
  have hvF : e.realMap v ∈ F.extremePoints ℝ := by
    rw [← heF]
    exact affine_mem_extremePoints_image e.realMap e.realMap_injective hv
  obtain ⟨k, R, f, lengths, hf0, hfF, hedge, hall⟩ := hlocal (e.realMap v) hvF
  obtain ⟨z0, hz0Q, hz0⟩ := Q.extreme_integral hv
  have hlinearRange : Set.range e.realLinear = Set.range f.realLinear :=
    e.linear_range_eq_of_affine_range_eq f
      (e.realMap_range_eq_of_image_eq f Q R (heF.trans hfF.symm))
  let T : Lattice k ≃ₗ[ℤ] Lattice d := e.changeLinear f hlinearRange
  let b0 : Module.Basis (Fin k) ℤ (Lattice d) := (Pi.basisFun ℤ (Fin k)).map T
  let index : Fin k ≃ Fin d := b0.indexEquiv (Pi.basisFun ℤ (Fin d))
  let b : Module.Basis (Fin d) ℤ (Lattice d) := b0.reindex index
  have hb (i : Fin d) : b i = T (Pi.basisFun ℤ (Fin k) (index.symm i)) := by
    simp [b, b0]
  have horigin : e.latticeMap z0 = f.origin := by
    apply embed_injective n
    rw [e.embed_latticeMap, hz0, ← hf0]
    simp [IntegralAffineEmbedding.realMap_apply]
  have hpoint (z : Lattice k) :
      e.realMap (embed d (z0 + T z)) = f.realMap (embed k z) :=
    e.realMap_changeLinear f hlinearRange z0 horigin z
  refine ⟨z0, b, fun i => lengths (index.symm i), hz0, ?_, ?_⟩
  · intro i
    let j : Fin k := index.symm i
    refine ⟨(hedge j).1, ?_⟩
    have hmap : e.realMap (embed d (z0 + (lengths j : ℤ) • b i)) =
        f.realMap (embed k ((lengths j : ℤ) • Pi.basisFun ℤ (Fin k) j)) := by
      rw [hb]
      rw [← T.map_smul]
      exact hpoint ((lengths j : ℤ) • Pi.basisFun ℤ (Fin k) j)
    exact (e.edge_transfer_iff f Q R (heF.trans hfF.symm)
      v (embed d (z0 + (lengths j : ℤ) • b i))
      0 (embed k ((lengths j : ℤ) • Pi.basisFun ℤ (Fin k) j)) hf0.symm hmap).mpr
      (hedge j).2
  · intro w hw
    have hwF : e.realMap w ∈ F := by
      rw [← heF]
      exact ⟨w, (Q.edge_endpoints_extreme hw).2.1, rfl⟩
    rw [← hfF] at hwF
    obtain ⟨u, huR, hu⟩ := hwF
    have huEdge : R.IsEdge 0 u :=
      (e.edge_transfer_iff f Q R (heF.trans hfF.symm) v w 0 u hf0.symm hu.symm).mp hw
    obtain ⟨j, hj⟩ := hall u huEdge
    refine ⟨index j, ?_⟩
    apply e.realMap_injective
    rw [← hu, hj]
    have he := hpoint ((lengths j : ℤ) • Pi.basisFun ℤ (Fin k) j)
    simpa only [hb, Equiv.symm_apply_apply, LinearEquiv.map_smul] using he.symm

end PaperVerification.ToricGeometry
