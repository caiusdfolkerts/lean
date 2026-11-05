module

public import PaperVerification.ToricBundleFanFaces
public import PaperVerification.ToricFanPolytopeSmoothness
public import PaperVerification.ToricSmoothFaces


@[expose] public section
/-!
# Genuine endpoint base polytopes and inherited edge lengths

This combines the explicit quotient construction with the independently
proved fan/polytope dictionary.  Each endpoint divisor produces an actual
smooth lattice polytope with exactly the base normal fan; its edges inherit
the original bound through its saturated embedding as an actual face.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem fiberDegree_pos (c : R.BundleCoordinates) (hN : R.negative = ∅) (a : Lattice n → ℝ)
    (ha : «Σ».IsStrictSupport a) : 0 < ∑ v ∈ R.positive, a v := by
  have h := R.degree_pos_of_strictSupport ha
  simpa only [SmoothCompleteFan.PrimitiveRelation.degree, hN, Finset.sum_empty, sub_zero] using h

theorem endpoint_integerBaseWeight_cast (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a : Lattice n → ℤ) (u : Lattice n) :
    (fun q => (c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u) q : ℝ)) =
      c.baseWeight hR hN (fun v => (a v : ℝ))
        (c.endpointWeight (fun v => (a v : ℝ)) u) := by
  funext q
  rw [c.integerBaseWeight_cast]
  congr 1
  funext v
  exact c.endpointIntegerWeight_cast a u v

/-- Complete geometric input for induction on the base: the actual
endpoint polytope, smoothness, its exact normal fan, unchanged edge bound,
and the saturated endpoint-face chart. -/
theorem exists_endpoint_basePolytope (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun v => (a v : ℝ)))
    (P : LatticePolytope n) (hP : P.carrier = «Σ».fanPolytope (fun v => (a v : ℝ)))
    {bound : ℕ} (hbound : P.EdgesAtLeast bound) {u : Lattice n} (hu : u ∈ R.positive) :
    ∃ Q : LatticePolytope (n - c.fiberIndices.card),
      Q.carrier = c.baseFan.fanPolytope
        (c.baseWeight hR hN (fun v => (a v : ℝ))
          (c.endpointWeight (fun v => (a v : ℝ)) u)) ∧
      Q.Smooth ∧ Q.normalFan = c.baseFan.realCones ∧ Q.EdgesAtLeast bound ∧
      (c.fiberChart a (c.endpointIntegerWeight a u)).realMap '' Q.carrier =
        c.endpointFace (fun v => (a v : ℝ)) u := by
  let A := c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u)
  have hA : c.baseFan.IsStrictSupport (fun q => (A q : ℝ)) := by
    change c.baseFan.IsStrictSupport
      (fun q => (c.integerBaseWeight hR hN a (c.endpointIntegerWeight a u) q : ℝ))
    rw [c.endpoint_integerBaseWeight_cast hR hN a u]
    exact c.endpoint_isStrictSupport hR hN _ ha hu
  obtain ⟨Q, hQ, hQsm, hQfan⟩ := c.baseFan.exists_smooth_latticePolytope_of_integral_strictSupport
    (c.baseFan_isPure hpure) A hA
  have hQ' : Q.carrier = c.baseFan.fanPolytope
      (c.baseWeight hR hN (fun v => (a v : ℝ))
        (c.endpointWeight (fun v => (a v : ℝ)) u)) := by
    simpa only [A, c.endpoint_integerBaseWeight_cast hR hN a u] using hQ
  have hk : 0 ≤ ∑ v ∈ R.positive, a v := by
    have hpos := c.fiberDegree_pos hN (fun v => (a v : ℝ)) ha
    exact_mod_cast hpos.le
  have himage : (c.fiberChart a (c.endpointIntegerWeight a u)).realMap '' Q.carrier =
      c.endpointFace (fun v => (a v : ℝ)) u := by
    rw [hQ']
    exact c.endpointChart_image hR hN a hk hu
  have hface : IsExtreme ℝ P.carrier (c.endpointFace (fun v => (a v : ℝ)) u) := by
    rw [hP]
    exact c.endpointFace_isExtreme _ _
  have hlength : Q.EdgesAtLeast bound := P.edgesAtLeast_face_chart hbound _ hface Q
    (c.fiberChart a (c.endpointIntegerWeight a u)) himage
  exact ⟨Q, hQ', hQsm, hQfan, hlength, himage⟩

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
