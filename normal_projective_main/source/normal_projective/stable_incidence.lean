module
public import normal_projective.simple_stability
public import normal_projective.face_correspondence
/-! # Actual labelled face-lattice stability -/
@[expose] public section
noncomputable section
open Set Filter Matrix
open scoped Topology
namespace NormalProjective
variable {d : ℕ} {ι : Type*} [Fintype ι]

abbrev DataVertices (p : HalfspaceData ι (Fin d → ℝ)) :=
  (dataRegion p).extremePoints ℝ

def MinorStable (p q : HalfspaceData ι (Fin d → ℝ)) : Prop :=
  ∀ I : Fin d ↪ ι, (FeasibleMinor p I → GoodMinor q I) ∧
    (¬FeasibleMinor p I → ¬FeasibleMinor q I)

theorem GoodMinor.vertex {p : HalfspaceData ι (Fin d → ℝ)} {I : Fin d ↪ ι}
    (hI : GoodMinor p I) : minorVertex p I ∈ DataVertices p :=
  nonsingular_tight_minor_is_vertex (fun i => (p.1 i).toLinearMap) p.2 I
    hI.1 hI.2.1 (minorVertex_tight p I hI.1)

theorem GoodMinor.active_iff {p : HalfspaceData ι (Fin d → ℝ)} {I : Fin d ↪ ι}
    (hI : GoodMinor p I) (i : ι) :
    p.1 i (minorVertex p I) = p.2 i ↔ i ∈ Set.range I := by
  constructor
  · intro heq
    by_contra hi
    exact (ne_of_lt (hI.2.2 i hi)) heq
  · rintro ⟨j, rfl⟩
    exact minorVertex_tight p I hI.1 j

theorem dataVertices_eq_of_incidence
    (p : HalfspaceData ι (Fin d → ℝ)) (v w : DataVertices p)
    (hv : ∀ i, p.1 i v.val = p.2 i ↔ p.1 i w.val = p.2 i) : v = w := by
  apply extreme_activeFacetSet_injective (fun i => (p.1 i).toLinearMap) p.2
  ext i
  exact hv i

theorem stable_exists_vertex_forward
    (p q : HalfspaceData ι (Fin d → ℝ))
    (hs : IsSimpleHalfspace (fun i => (p.1 i).toLinearMap) p.2)
    (hst : MinorStable p q) (v : DataVertices p) :
    ∃ w : DataVertices q, ∀ i, p.1 i v.val = p.2 i ↔ q.1 i w.val = q.2 i := by
  obtain ⟨I, hI, _⟩ := extremePoint_has_active_basis
    (fun i => (p.1 i).toLinearMap) p.2 v.property
  have hpI : FeasibleMinor p I := ⟨v.val, v.property.1, hI⟩
  have hqI := (hst I).1 hpI
  have hrange := (simple_active_minor_spans
    (fun i => (p.1 i).toLinearMap) p.2 hs v.property I hI).1
  refine ⟨⟨minorVertex q I, hqI.vertex⟩, fun i => ?_⟩
  change p.1 i v.val = p.2 i ↔ q.1 i (minorVertex q I) = q.2 i
  rw [hqI.active_iff]
  rw [hrange]
  rfl

theorem stable_exists_vertex_backward
    (p q : HalfspaceData ι (Fin d → ℝ))
    (hc : IsCompact (dataRegion p))
    (hs : IsSimpleHalfspace (fun i => (p.1 i).toLinearMap) p.2)
    (hst : MinorStable p q) (w : DataVertices q) :
    ∃ v : DataVertices p, ∀ i, p.1 i v.val = p.2 i ↔ q.1 i w.val = q.2 i := by
  classical
  obtain ⟨I, hI, _⟩ := extremePoint_has_active_basis
    (fun i => (q.1 i).toLinearMap) q.2 w.property
  have hqfeas : FeasibleMinor q I := ⟨w.val, w.property.1, hI⟩
  have hpfeas : FeasibleMinor p I := by
    by_contra hno
    exact (hst I).2 hno hqfeas
  have hpI := goodMinor_of_simple_feasible p hc hs I hpfeas
  have hqI := (hst I).1 hpfeas
  have hw := minorVertex_eq q I hqI.1 hI
  refine ⟨⟨minorVertex p I, hpI.vertex⟩, fun i => ?_⟩
  change p.1 i (minorVertex p I) = p.2 i ↔ q.1 i w.val = q.2 i
  rw [← hw, hpI.active_iff, hqI.active_iff]

def stableVertexEquiv
    (p q : HalfspaceData ι (Fin d → ℝ))
    (hc : IsCompact (dataRegion p))
    (hs : IsSimpleHalfspace (fun i => (p.1 i).toLinearMap) p.2)
    (hst : MinorStable p q) : DataVertices p ≃ DataVertices q := by
  classical
  let t : DataVertices p → DataVertices q :=
    fun v => (stable_exists_vertex_forward p q hs hst v).choose
  have ht (v : DataVertices p) :
      ∀ i, p.1 i v.val = p.2 i ↔ q.1 i (t v).val = q.2 i :=
    (stable_exists_vertex_forward p q hs hst v).choose_spec
  apply Equiv.ofBijective t
  constructor
  · intro v w hvw
    apply dataVertices_eq_of_incidence p
    intro i
    exact (ht v i).trans (by rw [hvw]; exact (ht w i).symm)
  · intro w
    obtain ⟨v, hv⟩ := stable_exists_vertex_backward p q hc hs hst w
    refine ⟨v, dataVertices_eq_of_incidence q _ _ (fun i => ?_)⟩
    exact (ht v i).symm.trans (hv i)

theorem stableVertexEquiv_incidence
    (p q : HalfspaceData ι (Fin d → ℝ))
    (hc : IsCompact (dataRegion p))
    (hs : IsSimpleHalfspace (fun i => (p.1 i).toLinearMap) p.2)
    (hst : MinorStable p q) (v : DataVertices p) (i : ι) :
    p.1 i v.val = p.2 i ↔
      q.1 i (stableVertexEquiv p q hc hs hst v).val = q.2 i :=
  (stable_exists_vertex_forward p q hs hst v).choose_spec i

/-- A genuinely open neighbourhood of the same labelled exposed-face lattice. -/
theorem normalized_data_eventually_face_isomorphic
    (f : ι → (Fin d → ℝ) →L[ℝ] ℝ)
    (hc : IsCompact (dataRegion (f, fun _ => 1)))
    (hs : IsSimpleHalfspace (fun i => (f i).toLinearMap) (fun _ => 1)) :
    ∀ᶠ p : HalfspaceData ι (Fin d → ℝ) in 𝓝 (f, fun _ => 1),
      IsCompact (dataRegion p) ∧ 0 ∈ interior (dataRegion p) ∧
      ∃ e : HalfspaceFaces (fun i => (f i).toLinearMap) (fun _ => 1) ≃o
          HalfspaceFaces (fun i => (p.1 i).toLinearMap) p.2,
        ∀ i, e ⟨tightFace (fun j => (f j).toLinearMap) (fun _ => 1) {i},
              tightFace_isExposed _ _ _⟩ =
            ⟨tightFace (fun j => (p.1 j).toLinearMap) p.2 {i},
              tightFace_isExposed _ _ _⟩ := by
  obtain ⟨C, _, hevent⟩ := normalized_data_eventually_minor_stable f hc hs
  filter_upwards [hevent] with p hp
  have hcq : IsCompact (dataRegion p) :=
    (isCompact_closedBall (0 : Fin d → ℝ) C).of_isClosed_subset (dataRegion_closed p) hp.1
  let e := stableVertexEquiv (f, fun _ => 1) p hc hs hp.2.2
  have he := stableVertexEquiv_incidence (f, fun _ => 1) p hc hs hp.2.2
  refine ⟨hcq, hp.2.1,
    halfspaceFaceOrderIso (fun i => (f i).toLinearMap)
      (fun i => (p.1 i).toLinearMap) (fun _ => 1) p.2 hc hcq e he, ?_⟩
  exact fun i => halfspaceFaceOrderIso_facet _ _ _ _ _ _ _ _ i

end NormalProjective

