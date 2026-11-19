module

public import Unimodular.AllowedBlocks

@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.AllowedBlocks

attribute [local instance] Classical.propDecidable

variable {E N V : Type*} [Fintype E] [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ι : N →+ V) (u : E → N)

def FacetBlock := {s : Finset E // Allowed ι u s ∧
  Module.finrank ℝ (Submodule.span ℝ (blockCone ι u s : Set V)) + 1 = Module.finrank ℝ V}

noncomputable instance : Fintype (FacetBlock ι u) := by
  unfold FacetBlock
  exact Fintype.ofFinite _

theorem full_rank_iff (s : Finset E) :
    Submodule.span ℝ (blockCone ι u s : Set V) = ⊤ ↔
      Module.finrank ℝ (Submodule.span ℝ (blockCone ι u s : Set V)) = Module.finrank ℝ V := by
  constructor
  · intro h
    rw [h, finrank_top]
  · exact Submodule.eq_top_of_finrank_eq

theorem facet_rank_iff (hn : 0 < Module.finrank ℝ V) (s : Finset E) :
    Module.finrank ℝ (Submodule.span ℝ (blockCone ι u s : Set V)) + 1 = Module.finrank ℝ V ↔
      Module.finrank ℝ (Submodule.span ℝ (blockCone ι u s : Set V)) = Module.finrank ℝ V - 1 := by
  omega

def HasFullCoface (b : FacetBlock ι u) : Prop :=
  ∃ s : FullBlock ι u, (blockCone ι u b.1).IsFaceOf (blockCone ι u s.1)

noncomputable def facetIndex (b : FacetBlock ι u) (h : HasFullCoface ι u b) : (family ι u).Facet :=
  ⟨blockCone ι u b.1, h, b.2.2⟩

/-- One oriented nonzero normal for every allowed codimension-one block, including rows
which have no full-dimensional coface. -/
noncomputable def facetNormal (b : FacetBlock ι u) : V →ₗ[ℝ] ℝ :=
  if h : HasFullCoface ι u b then (family ι u).normal (facetIndex ι u b h)
  else (ConeInterior.exists_normal (Submodule.span ℝ (blockCone ι u b.1 : Set V)) b.2.2).choose

theorem facetNormal_ne_zero (b : FacetBlock ι u) : facetNormal ι u b ≠ 0 := by
  unfold facetNormal
  split_ifs with h
  · exact (family ι u).normal_ne_zero _
  · exact (ConeInterior.exists_normal _ b.2.2).choose_spec.1

theorem facetNormal_ker (b : FacetBlock ι u) :
    LinearMap.ker (facetNormal ι u b) = Submodule.span ℝ (blockCone ι u b.1 : Set V) := by
  unfold facetNormal
  split_ifs with h
  · exact (family ι u).normal_ker _
  · exact (ConeInterior.exists_normal _ b.2.2).choose_spec.2

/-- The paper's boundary matrix is indexed by *all* allowed codimension-one blocks.
Rows with no full coface are retained and are zero. -/
noncomputable def boundary (b : FacetBlock ι u) (s : FullBlock ι u) : ℤ :=
  if h : HasFullCoface ι u b then (family ι u).boundary (facetIndex ι u b h) s else 0

/-- The matrix entry is precisely the oriented side sign when the block is a facet,
and zero otherwise. -/
theorem boundary_eq_geometric (b : FacetBlock ι u) (s : FullBlock ι u) :
    boundary ι u b s = if (blockCone ι u b.1).IsFaceOf (blockCone ι u s.1) then
      FacetLine.signZ (facetNormal ι u b ((family ι u).center s)) else 0 := by
  by_cases hb : HasFullCoface ι u b
  · rw [boundary, dif_pos hb, facetNormal, dif_pos hb]
    rfl
  · have hn : ¬ (blockCone ι u b.1).IsFaceOf (blockCone ι u s.1) := fun h => hb ⟨s, h⟩
    simp [boundary, facetNormal, hb, hn]

theorem familyFacet_eq_facetBlock (hnz : ∀ e, ι (u e) ≠ 0) (F : (family ι u).Facet) :
    ∃ b : FacetBlock ι u, blockCone ι u b.1 = F.1 := by
  obtain ⟨s, hFs⟩ := F.2.1
  obtain ⟨hb, he⟩ := face_allowed ι u hnz s.2.1 hFs
  refine ⟨⟨blockOfCone ι u F.1, hb, ?_⟩, he⟩
  rw [he]
  exact F.2.2

def BoundaryCycle (c : FullBlock ι u → ℤ) : Prop :=
  ∀ b : FacetBlock ι u, ∑ s, boundary ι u b s * c s = 0

/-- The full block-indexed matrix has exactly the same integer kernel as the matrix of
actual geometric facets. This also checks the otherwise harmless zero rows. -/
theorem boundaryCycle_iff (hnz : ∀ e, ι (u e) ≠ 0) (c : FullBlock ι u → ℤ) :
    BoundaryCycle ι u c ↔ (family ι u).IsCycle c := by
  constructor
  · intro hc F
    obtain ⟨b, hb⟩ := familyFacet_eq_facetBlock ι u hnz F
    have hco : HasFullCoface ι u b := by
      change ∃ s : FullBlock ι u, (blockCone ι u b.1).IsFaceOf ((family ι u).cone s)
      rw [hb]
      exact F.2.1
    have hidx : facetIndex ι u b hco = F := Subtype.ext hb
    have hrow := hc b
    simpa only [boundary, dif_pos hco, hidx, mul_comm] using hrow
  · intro hc b
    by_cases hco : HasFullCoface ι u b
    · simpa only [boundary, dif_pos hco, mul_comm] using hc (facetIndex ι u b hco)
    · simp [boundary, hco]

noncomputable def degreeRow (w : V) (s : FullBlock ι u) : ℤ :=
  if w ∈ interior (blockCone ι u s.1 : Set V) then 1 else 0

theorem degree_eq_multiplicity (w : V) (c : FullBlock ι u → ℤ) :
    (∑ s, degreeRow ι u w s * c s) = (family ι u).multiplicity c w := by
  unfold degreeRow CycleDegree.FullCones.multiplicity
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp_all [family]

theorem fanOfDecomposition_hasRays (hι : IsIntegralLattice ι)
    {c : FullBlock ι u → ℤ} (hd : (family ι u).CompleteDecomposition c) :
    HasRays ι u ((family ι u).fanOfDecomposition hι (family_isToric ι u) hd) := by
  intro R
  constructor
  · rintro ⟨hR, hrank⟩
    obtain ⟨s, _, hRs⟩ := ((family ι u).mem_fanOfDecomposition_cones hι
      (family_isToric ι u) hd R).1 hR
    obtain ⟨e, _, he⟩ := (s.2.1.2.1 R).1 ⟨hRs, hrank⟩
    exact ⟨e, he⟩
  · rintro ⟨e, rfl⟩
    obtain ⟨s, hs, hes⟩ := hd.cover (ι (u e))
    have hem := (s.2.1.2.2 e).1 hes
    have hr := (s.2.1.2.1 (ray (ι (u e)))).2 ⟨e, hem, rfl⟩
    refine ⟨?_, hr.2⟩
    exact ((family ι u).mem_fanOfDecomposition_cones hι (family_isToric ι u) hd _).2
      ⟨s, hs, hr.1⟩

/-- Exact gluing and the converse, now with the full prescribed ray configuration and the
ordinary bundled Mathlib/Tau Ceti fan object. -/
theorem positive_degree_one_iff_fan_rays (hι : IsIntegralLattice ι)
    (hnz : ∀ e, ι (u e) ≠ 0) (c : FullBlock ι u → ℤ)
    {w : V} (hw : (family ι u).Generic w) :
    ((∀ s, 0 ≤ c s) ∧ (family ι u).IsCycle c ∧ (family ι u).multiplicity c w = 1) ↔
      ∃ Φ : Fan ι, Φ.IsComplete ∧ HasRays ι u Φ ∧
        (∀ s, c s = if blockCone ι u s.1 ∈ Φ.cones then 1 else 0) := by
  rw [(family ι u).positive_degree_one_iff_completeDecomposition (family_injective ι u) c hw]
  constructor
  · intro hd
    exact ⟨(family ι u).fanOfDecomposition hι (family_isToric ι u) hd,
      (family ι u).fanOfDecomposition_complete hι (family_isToric ι u) hd,
      fanOfDecomposition_hasRays ι u hι hd,
      (family ι u).coefficient_eq_fan_indicator hι (family_isToric ι u)
        (family_injective ι u) hd⟩
  · rintro ⟨Φ, hΦ, hr, hind⟩
    apply ((family ι u).positive_degree_one_iff_completeDecomposition
      (family_injective ι u) c hw).1
    apply ((family ι u).positive_degree_one_iff_fan hι (family_isToric ι u)
      (family_injective ι u) c hw).2
    exact ⟨Φ, hΦ, hind, fun C hC hfull => full_fan_cone_eq_block ι u hnz hr hC hfull⟩

/-- Theorem 3.1, with every allowed facet block retained as a matrix row. The generic
direction condition is expressed by the finite geometric face arrangement. -/
theorem theorem_3_1_generic (hι : IsIntegralLattice ι)
    (hnz : ∀ e, ι (u e) ≠ 0) (c : FullBlock ι u → ℤ)
    {w : V} (hw : (family ι u).Generic w) :
    ((∀ s, 0 ≤ c s) ∧ BoundaryCycle ι u c ∧ (∑ s, degreeRow ι u w s * c s) = 1) ↔
      ∃ Φ : Fan ι, Φ.IsComplete ∧ HasRays ι u Φ ∧
        (∀ s, c s = if blockCone ι u s.1 ∈ Φ.cones then 1 else 0) := by
  rw [boundaryCycle_iff ι u hnz c, degree_eq_multiplicity ι u w c]
  exact positive_degree_one_iff_fan_rays ι u hι hnz c hw

end Unimodular.AllowedBlocks
