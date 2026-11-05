module

public import paper_verification.toric018

@[expose] public section

/-!
# The literal unit-corner-box hypothesis

This defines the geometric box-containment hypothesis of Lemma 4.2 and
proves that it is independent of the complete primitive-edge basis. The
mixed multiplication conclusion, including boundary points, is established
in `MixedUnitBoxes`.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange
open PaperVerification.Toric
open scoped BigOperators Classical Pointwise

namespace LatticePolytope

/-- At each vertex the unit box in the complete primitive edge basis lies in
the polytope. The existential indexing is immaterial; a permutation-invariance
lemma below allows any supporting primitive edge basis to be used. -/
def UnitCornerBoxes {n : ℕ} (P : LatticePolytope n) : Prop :=
  ∀ v ∈ P.carrier.extremePoints ℝ,
    ∃ (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
      (lengths : Fin n → ℕ),
      embed n vZ = v ∧
      (∀ i, 0 < lengths i ∧
        P.IsEdge v (embed n (vZ + (lengths i : ℤ) • b i))) ∧
      (∀ w : Ambient n, P.IsEdge v w →
        ∃ i, w = embed n (vZ + (lengths i : ℤ) • b i)) ∧
      (∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) →
        v + ∑ i, t i • integralBasisReal b i ∈ P.carrier)

theorem UnitCornerBoxes.smooth {n : ℕ} {P : LatticePolytope n}
    (h : P.UnitCornerBoxes) : P.Smooth := by
  intro v hv
  obtain ⟨vZ, b, l, he, hl, hall, _⟩ := h v hv
  exact ⟨vZ, b, l, he, hl, hall⟩

/-- Box containment is independent of the ordering or choice of a primitive
edge basis: integral supporting bases for the same vertex differ by a permutation. -/
theorem UnitCornerBoxes.in_supporting_basis {n : ℕ} {P : LatticePolytope n}
    (h : P.UnitCornerBoxes) (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ)
    (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (lengths : Fin n → ℕ) (he : embed n vZ = v)
    (hl : ∀ i, 0 < lengths i ∧
      P.IsEdge v (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - v) i)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    v + ∑ i, t i • integralBasisReal b i ∈ P.carrier := by
  obtain ⟨wZ, c, ls, hw, hls, hall, hbox⟩ := h v hv
  have hc := P.basis_cone_of_incident_edges v hv wZ c ls hw hall
  have hbc : ∀ i j, 0 ≤ b.repr (c j) i := by
    intro i j
    apply basis_coordinates_nonneg_of_edge b wZ (c j) (ls j) (hls j).1
    intro k
    have hh := hcone _ (P.edge_endpoints_extreme (hls j).2).2.1 k
    simpa only [hw] using hh
  have hcb : ∀ i j, 0 ≤ c.repr (b j) i := by
    intro i j
    apply basis_coordinates_nonneg_of_edge c vZ (b j) (lengths j) (hl j).1
    intro k
    have hh := hc _ (P.edge_endpoints_extreme (hl j).2).2.1 k
    simpa only [he] using hh
  obtain ⟨σ, hσ⟩ := integral_bases_perm_of_nonnegative_coordinates b c hbc hcb
  have hσR (i : Fin n) : integralBasisReal b i = integralBasisReal c (σ i) := by
    simp only [integralBasisReal_apply, hσ i]
  have hh := hbox (fun j => t (σ.symm j)) (fun j => ht (σ.symm j))
  have hsum : (∑ i, t i • integralBasisReal b i) =
      ∑ j, t (σ.symm j) • integralBasisReal c j := by
    rw [← Equiv.sum_comp σ (fun j => t (σ.symm j) • integralBasisReal c j)]
    simp only [Equiv.symm_apply_apply, hσR]
  simpa only [hsum] using hh

/-- The existential presentation of the corner basis is equivalent to
smoothness together with containment for every complete primitive edge basis.
Thus no particular basis choice is part of the geometric hypothesis. -/
theorem unitCornerBoxes_iff_all_edge_bases {n : ℕ} (P : LatticePolytope n) :
    P.UnitCornerBoxes ↔ P.Smooth ∧
      ∀ (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ)
        (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
        (lengths : Fin n → ℕ),
        embed n vZ = v →
        (∀ i, 0 < lengths i ∧
          P.IsEdge v (embed n (vZ + (lengths i : ℤ) • b i))) →
        (∀ w : Ambient n, P.IsEdge v w →
          ∃ i, w = embed n (vZ + (lengths i : ℤ) • b i)) →
        ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) →
          v + ∑ i, t i • integralBasisReal b i ∈ P.carrier := by
  constructor
  · intro h
    refine ⟨h.smooth, ?_⟩
    intro v hv vZ b lengths he hl hall t ht
    exact h.in_supporting_basis v hv vZ b lengths he hl
      (P.basis_cone_of_incident_edges v hv vZ b lengths he hall) t ht
  · rintro ⟨hP, hbox⟩ v hv
    obtain ⟨vZ, b, lengths, he, hl, hall⟩ := hP v hv
    exact ⟨vZ, b, lengths, he, hl, hall, hbox v hv vZ b lengths he hl hall⟩

/-- The paper's long-edge hypothesis implies literal unit-box containment.
This implication is not used as a replacement for the full Lemma 4.2 hypothesis. -/
theorem unitCornerBoxes_of_long_edges {n : ℕ} (P : LatticePolytope n)
    (hP : P.Smooth) (hbound : P.EdgesAtLeast n) : P.UnitCornerBoxes := by
  intro v hv
  obtain ⟨vZ, b, l, he, hl, hall⟩ := hP v hv
  refine ⟨vZ, b, l, he, hl, hall, ?_⟩
  intro t ht
  have hbox := P.integral_edges_unit_corner_box hbound vZ
    (by simpa only [he] using hv.1) b l
    (fun i => by simpa only [he] using (hl i).2) t ht
  simpa only [he] using hbox

end LatticePolytope

end PaperVerification.ToricGeometry
