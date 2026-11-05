module

public import PaperVerification.ToricBundleFanPolytopes
public import PaperVerification.ToricSupportAveragedEdges


@[expose] public section
/-!
# Actual base polytopes at arbitrary integral homogeneous weights

Every nonnegative integral homogeneous weight gives an actual smooth lattice
polytope with the same base normal fan.  All its edge lengths retain the
original bound.  The proof transfers the endpoint faces through saturated
charts and then averages feasible primitive axis segments on the fixed fan.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace LatticePolytope

theorem edgesAtLeast_of_le {n : ℕ} (P : LatticePolytope n) {a b : ℕ}
    (h : P.EdgesAtLeast b) (hab : a ≤ b) : P.EdgesAtLeast a := by
  intro v w hedge
  obtain ⟨vZ, wZ, hv, hw, hlength⟩ := h v w hedge
  exact ⟨vZ, wZ, hv, hw, hab.trans hlength⟩

theorem edgesAtLeast_congr {n : ℕ} {P Q : LatticePolytope n}
    (h : P.carrier = Q.carrier) {bound : ℕ} :
    P.EdgesAtLeast bound ↔ Q.EdgesAtLeast bound := by
  simp only [EdgesAtLeast, IsEdge, h]

end LatticePolytope

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem integerBaseWeight_isStrictSupport (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v) :
    c.baseFan.IsStrictSupport (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) := by
  have hαR : (∑ v ∈ R.positive, (α v : ℝ)) = ∑ v ∈ R.positive, (a v : ℝ) := by
    exact_mod_cast hα
  have hαR0 (v : Lattice n) (hv : v ∈ R.positive) : (0 : ℝ) ≤ α v := by
    exact_mod_cast hα0 v hv
  have he : (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) =
      c.baseWeight hR hN (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) := by
    funext q
    exact c.integerBaseWeight_cast hR hN a α q
  rw [he]
  exact c.baseWeight_isStrictSupport hR hN _ _ ha hαR hαR0

theorem support_basePolytope_edgesAtLeast (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (hpure : «Σ».IsPure) (a α : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v)
    (P : LatticePolytope n) (hP : P.carrier = «Σ».fanPolytope (fun v => (a v : ℝ)))
    {bound : ℕ} (hbound : P.EdgesAtLeast bound) :
    (c.baseFan.supportLatticePolytope (c.baseFan_isPure hpure)
      (c.integerBaseWeight hR hN a α)
      (c.integerBaseWeight_isStrictSupport hR hN a α ha hα hα0)).EdgesAtLeast bound := by
  let aR : Lattice n → ℝ := fun v => (a v : ℝ)
  let αR : Lattice n → ℝ := fun v => (α v : ℝ)
  let A : Lattice n → Lattice (n - c.fiberIndices.card) → ℤ :=
    fun u => c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u)
  have hA (u : Lattice n) (hu : u ∈ R.positive) :
      c.baseFan.IsStrictSupport (fun q => (A u q : ℝ)) := by
    change c.baseFan.IsStrictSupport
      (fun q => (c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u) q : ℝ))
    rw [c.endpoint_integerBaseWeight_cast hR hN a u]
    exact c.endpoint_isStrictSupport hR hN _ ha hu
  have hsum : (∑ v ∈ R.positive, αR v) = ∑ v ∈ R.positive, aR v := by
    change (∑ v ∈ R.positive, (α v : ℝ)) = ∑ v ∈ R.positive, (a v : ℝ)
    exact_mod_cast hα
  have hk : 0 < ∑ v ∈ R.positive, aR v := c.fiberDegree_pos hN aR ha
  have hweights (v : Lattice n) (hv : v ∈ R.positive) :
      0 ≤ αR v / (∑ w ∈ R.positive, aR w) := by
    apply div_nonneg _ hk.le
    change (0 : ℝ) ≤ (α v : ℝ)
    exact_mod_cast hα0 v hv
  have hcoeff : (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) =
      fun q => ∑ u ∈ R.positive, (αR u / (∑ v ∈ R.positive, aR v)) * (A u q : ℝ) := by
    funext q
    rw [c.integerBaseWeight_cast]
    have he := congrFun (c.baseWeight_convex_combination hR hN aR αR hk.ne' hsum) q
    change c.baseWeight hR hN aR αR q =
      ∑ u ∈ R.positive, (αR u / (∑ v ∈ R.positive, aR v)) *
        (c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u) q : ℝ)
    calc
      c.baseWeight hR hN aR αR q =
          ∑ u ∈ R.positive, (αR u / (∑ v ∈ R.positive, aR v)) *
            c.baseWeight hR hN aR (c.endpointWeight aR u) q := he
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        exact congrArg (fun t : ℝ => (αR u / (∑ v ∈ R.positive, aR v)) * t)
          (congrFun (c.endpoint_integerBaseWeight_cast hR hN a u) q).symm
  apply c.baseFan.support_edgesAtLeast_convex_combination R.positive
    (c.baseFan_isPure hpure) _ _ A hA
    (fun u => αR u / (∑ v ∈ R.positive, aR v)) hweights
    (c.normalized_weights_sum aR αR hk.ne' hsum) hcoeff bound
  intro u hu
  obtain ⟨Q, hQ, _, _, hQbound, _⟩ :=
    c.exists_endpoint_basePolytope hR hN hpure a ha P hP hbound hu
  have he : Q.carrier = (c.baseFan.supportLatticePolytope
      (c.baseFan_isPure hpure) (A u) (hA u hu)).carrier := by
    rw [c.baseFan.supportLatticePolytope_carrier, hQ]
    congr 1
    exact (c.endpoint_integerBaseWeight_cast hR hN a u).symm
  exact (LatticePolytope.edgesAtLeast_congr he).mp hQbound

/-- Full induction data for every integral homogeneous fiber weight, with
the actual carrier, actual normal fan, and unchanged geometric edge bound. -/
theorem exists_basePolytope (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (hpure : «Σ».IsPure) (a α : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v)
    (P : LatticePolytope n) (hP : P.carrier = «Σ».fanPolytope (fun v => (a v : ℝ)))
    {bound : ℕ} (hbound : P.EdgesAtLeast bound) :
    ∃ Q : LatticePolytope (n - c.fiberIndices.card),
      Q.carrier = c.baseFan.fanPolytope
        (fun q => (c.integerBaseWeight hR hN a α q : ℝ)) ∧
      Q.Smooth ∧ Q.normalFan = c.baseFan.realCones ∧ Q.EdgesAtLeast bound := by
  let hA := c.integerBaseWeight_isStrictSupport hR hN a α ha hα hα0
  let Q := c.baseFan.supportLatticePolytope (c.baseFan_isPure hpure)
    (c.integerBaseWeight hR hN a α) hA
  exact ⟨Q, c.baseFan.supportLatticePolytope_carrier _ _ _,
    c.baseFan.supportLatticePolytope_smooth _ _ _,
    c.baseFan.supportLatticePolytope_normalFan _ _ _,
    c.support_basePolytope_edgesAtLeast hR hN hpure a α ha hα hα0 P hP hbound⟩

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
