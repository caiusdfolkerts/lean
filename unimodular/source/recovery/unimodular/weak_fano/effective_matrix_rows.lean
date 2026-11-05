module

public import Recovery.Unimodular.WeakFano.EffectiveMatrixData

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set

namespace Unimodular.EffectiveMatrix

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
local notation "ι₀" => EffectiveAllowed.embedding n

/-- The arithmetically computed center is in the actual full cone's interior. -/
theorem computed_center_interior (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (s : Column u) :
    embed (EffectiveMatrixGeometry.center (fun e : {e // e ∈ s.val} => u e.val)) ∈
      interior (AllowedBlocks.blockCone ι₀ u s.val : Set (Ambient n)) := by
  have hcone := EffectiveAllowed.cone_subtype u s.val
  have hfull := (columnEquiv u hnz s).property.2
  change Submodule.span ℝ (AllowedBlocks.blockCone ι₀ u s.val : Set (Ambient n)) = ⊤ at hfull
  rw [← hcone] at hfull
  change Submodule.span ℝ
    (PointedCone.hull ℝ (Set.range (fun e : {e // e ∈ s.val} => embed (u e.val))) :
      Set (Ambient n)) = ⊤ at hfull
  rw [RayHyperplanes.span_hull_eq] at hfull
  have hh := EffectiveMatrixGeometry.center_interior
    (fun e : {e // e ∈ s.val} => u e.val) hfull
  change embed (EffectiveMatrixGeometry.center (fun e : {e // e ∈ s.val} => u e.val)) ∈
    interior (EffectiveFaces.cone (fun e : {e // e ∈ s.val} => u e.val) : Set (Ambient n)) at hh
  simpa only [hcone] using hh

/-- Each accepted computed row is exactly an original geometric boundary
row or its negative, simultaneously for every column. -/
theorem boundaryEntry_row (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (r : Row n E) (hr : rowTest u r) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ s : Column u,
      boundaryEntry u r s = ε * AllowedBlocks.boundary ι₀ u
        (facetOfRow u hnz r hr) (columnEquiv u hnz s) := by
  let b := facetOfRow u hnz r hr
  let g := EffectiveDirection.realRowForm (u ∘ r.2.1) r.2.2
  have hg : g ≠ 0 := EffectiveMatrixGeometry.realRowForm_ne_zero _ _ hr.2.2.2.1
  have hd : Module.finrank ℝ (RayHyperplanes.raySpan (fun e => embed (u e)) r.1) + 1 = n := by
    have h := b.property.2
    rw [block_span] at h
    simpa [Ambient, b] using h
  have hker : LinearMap.ker g =
      Submodule.span ℝ (AllowedBlocks.blockCone ι₀ u b.val : Set (Ambient n)) := by
    exact (EffectiveMatrixGeometry.normalTest_kernel u r.1 hd r.2 hr.2.2.2).trans
      (block_span u b.val).symm
  obtain ⟨ε, hε, hsign⟩ := AllowedBlocks.signs_eq_of_same_kernel
    (AllowedBlocks.facetNormal ι₀ u b) g (AllowedBlocks.facetNormal_ne_zero ι₀ u b) hg
    ((AllowedBlocks.facetNormal_ker ι₀ u b).trans hker.symm)
  refine ⟨ε, hε, ?_⟩
  intro s
  have hface_iff := EffectiveAllowed.faceTest_iff u r.1 s.val
    b.property.1 (columnEquiv u hnz s).property.1
  by_cases hface : (AllowedBlocks.blockCone ι₀ u r.1).IsFaceOf
      (AllowedBlocks.blockCone ι₀ u s.val)
  · have htest : EffectiveAllowed.faceTest u r.1 s.val := hface_iff.2 hface
    rw [boundaryEntry, if_pos ⟨hr, htest⟩,
      AllowedBlocks.boundary_eq_geometric]
    simp only [facetOfRow_val, columnEquiv_val, if_pos hface]
    have hne : AllowedBlocks.blockCone ι₀ u b.val ≠ AllowedBlocks.blockCone ι₀ u s.val := by
      intro he
      have hh := b.property.2
      have hfull : Submodule.span ℝ
          (AllowedBlocks.blockCone ι₀ u s.val : Set (Ambient n)) = ⊤ :=
        (columnEquiv u hnz s).property.2
      rw [he, hfull, finrank_top] at hh
      omega
    have hcenter := computed_center_interior u hnz s
    have hold := (AllowedBlocks.family ι₀ u).center_mem_interior (columnEquiv u hnz s)
    calc
      _ = FacetLine.signZ (g (embed (EffectiveMatrixGeometry.center
          (fun e : {e // e ∈ s.val} => u e.val)))) := by
        dsimp [g]
        rw [EffectiveDirection.realRowForm_embed, EffectiveMatrixGeometry.sign_cast]
        rfl
      _ = FacetLine.signZ (g ((AllowedBlocks.family ι₀ u).center
          (columnEquiv u hnz s))) :=
        EffectiveMatrixGeometry.sign_eq_on_interior hface hne g hker hcenter hold
      _ = _ := hsign _
  · have htest : ¬EffectiveAllowed.faceTest u r.1 s.val := mt hface_iff.1 hface
    rw [boundaryEntry, if_neg (fun h => htest h.2),
      AllowedBlocks.boundary_eq_geometric]
    simp only [facetOfRow_val, columnEquiv_val, if_neg hface, mul_zero]

/-- Reindexing and the single row sign account for the entire integer sum. -/
theorem boundaryEntry_sum (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (r : Row n E) (hr : rowTest u r) (c : Column u → ℤ) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (∑ s, boundaryEntry u r s * c s) = ε *
        ∑ s, AllowedBlocks.boundary ι₀ u (facetOfRow u hnz r hr) s *
          coefficientEquiv u hnz c s := by
  obtain ⟨ε, hε, he⟩ := boundaryEntry_row u hnz r hr
  refine ⟨ε, hε, ?_⟩
  calc
    _ = ε * ∑ s : Column u, AllowedBlocks.boundary ι₀ u
        (facetOfRow u hnz r hr) (columnEquiv u hnz s) * c s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [he]
      ring
    _ = _ := congrArg (fun z : ℤ => ε * z)
      (Fintype.sum_equiv (columnEquiv u hnz) _ _ (fun s => by
        rw [coefficientEquiv_apply_column]))

/-- Duplicate orientations and zero padding leave exactly the original
integer boundary kernel, including every nonsimplicial block and facet. -/
theorem boundary_sums_iff (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (c : Column u → ℤ) :
    (∀ r : Row n E, ∑ s, boundaryEntry u r s * c s = 0) ↔
      AllowedBlocks.BoundaryCycle ι₀ u (coefficientEquiv u hnz c) := by
  constructor
  · intro hc b
    obtain ⟨r, hr, hb⟩ := exists_row_for_facet u hnz hspan b
    obtain ⟨ε, hε, he⟩ := boundaryEntry_sum u hnz r hr c
    have hz := hc r
    rw [he, hb] at hz
    rcases hε with rfl | rfl <;> simpa using hz
  · intro hc r
    by_cases hr : rowTest u r
    · obtain ⟨ε, hε, he⟩ := boundaryEntry_sum u hnz r hr c
      rw [he, hc, mul_zero]
    · have hz : ∀ s : Column u, boundaryEntry u r s = 0 := by
        intro s
        exact if_neg (fun h => hr h.1)
      simp only [hz, zero_mul, Finset.sum_const_zero]

end
end Unimodular.EffectiveMatrix

#print axioms Unimodular.EffectiveMatrix.computed_center_interior
#print axioms Unimodular.EffectiveMatrix.boundaryEntry_row
#print axioms Unimodular.EffectiveMatrix.boundary_sums_iff
#check Unimodular.EffectiveMatrix.boundary_sums_iff
