module

public import Unimodular.MainFanTheorems

@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.AllowedBlocks

attribute [local instance] Classical.propDecidable

theorem signZ_mul (a b : ℝ) : FacetLine.signZ (a * b) = FacetLine.signZ a * FacetLine.signZ b := by
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases hb0 : b = 0
  · simp [hb0]
  rcases lt_or_gt_of_ne ha0 with ha | ha
  · rcases lt_or_gt_of_ne hb0 with hb | hb
    · rw [FacetLine.signZ_of_pos (mul_pos_of_neg_of_neg ha hb),
        FacetLine.signZ_of_neg ha, FacetLine.signZ_of_neg hb]
      norm_num
    · rw [FacetLine.signZ_of_neg (mul_neg_of_neg_of_pos ha hb),
        FacetLine.signZ_of_neg ha, FacetLine.signZ_of_pos hb]
      norm_num
  · rcases lt_or_gt_of_ne hb0 with hb | hb
    · rw [FacetLine.signZ_of_neg (mul_neg_of_pos_of_neg ha hb),
        FacetLine.signZ_of_pos ha, FacetLine.signZ_of_neg hb]
      norm_num
    · rw [FacetLine.signZ_of_pos (mul_pos ha hb),
        FacetLine.signZ_of_pos ha, FacetLine.signZ_of_pos hb]
      norm_num

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Two nonzero normals to the same real hyperplane induce identical or opposite side signs. -/
theorem signs_eq_of_same_kernel (f g : V →ₗ[ℝ] ℝ) (hf : f ≠ 0) (hg : g ≠ 0)
    (hker : LinearMap.ker f = LinearMap.ker g) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ y, FacetLine.signZ (g y) = ε * FacetLine.signZ (f y) := by
  have hex : ∃ x, f x ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hf
    ext x
    exact hn x
  obtain ⟨x, hx⟩ := hex
  have hgx : g x ≠ 0 := by
    intro h
    have hm : x ∈ LinearMap.ker g := h
    rw [← hker] at hm
    exact hx hm
  let a : ℝ := g x / f x
  have ha : a ≠ 0 := div_ne_zero hgx hx
  have heq : ∀ y, g y = a * f y := by
    intro y
    have hz : y - (f y / f x) • x ∈ LinearMap.ker f := by
      change f (y - (f y / f x) • x) = 0
      simp [map_sub, map_smul, div_mul_cancel₀ _ hx]
    rw [hker] at hz
    change g (y - (f y / f x) • x) = 0 at hz
    simp only [map_sub, map_smul, smul_eq_mul] at hz
    dsimp [a]
    calc
      g y = (f y / f x) * g x := sub_eq_zero.1 hz
      _ = (g x / f x) * f y := by ring
  refine ⟨FacetLine.signZ a, ?_, ?_⟩
  · rcases lt_or_gt_of_ne ha with ha | ha
    · exact Or.inr (FacetLine.signZ_of_neg ha)
    · exact Or.inl (FacetLine.signZ_of_pos ha)
  · intro y
    rw [heq y, signZ_mul]

variable {E N : Type*} [Fintype E] [AddCommGroup N] [FiniteDimensional ℝ V]
  (ι : N →+ V) (u : E → N)

/-- The facet matrix for an arbitrary family of nonzero supporting normals. -/
noncomputable def orientedBoundary (ν : FacetBlock ι u → V →ₗ[ℝ] ℝ)
    (b : FacetBlock ι u) (s : FullBlock ι u) : ℤ :=
  if (blockCone ι u b.1).IsFaceOf (blockCone ι u s.1) then
    FacetLine.signZ (ν b ((family ι u).center s)) else 0

theorem orientedBoundary_row (ν : FacetBlock ι u → V →ₗ[ℝ] ℝ)
    (hν0 : ∀ b, ν b ≠ 0)
    (hνker : ∀ b, LinearMap.ker (ν b) = Submodule.span ℝ (blockCone ι u b.1 : Set V))
    (b : FacetBlock ι u) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ s,
      orientedBoundary ι u ν b s = ε * boundary ι u b s := by
  obtain ⟨ε, hε, he⟩ := signs_eq_of_same_kernel (facetNormal ι u b) (ν b)
    (facetNormal_ne_zero ι u b) (hν0 b) ((facetNormal_ker ι u b).trans (hνker b).symm)
  refine ⟨ε, hε, ?_⟩
  intro s
  rw [boundary_eq_geometric ι u b s]
  unfold orientedBoundary
  split_ifs
  · exact he _
  · simp

theorem oriented_boundary_cycle_iff (ν : FacetBlock ι u → V →ₗ[ℝ] ℝ)
    (hν0 : ∀ b, ν b ≠ 0)
    (hνker : ∀ b, LinearMap.ker (ν b) = Submodule.span ℝ (blockCone ι u b.1 : Set V))
    (c : FullBlock ι u → ℤ) :
    (∀ b, ∑ s, orientedBoundary ι u ν b s * c s = 0) ↔ BoundaryCycle ι u c := by
  have hrow : ∀ b, (∑ s, orientedBoundary ι u ν b s * c s = 0) ↔
      ∑ s, boundary ι u b s * c s = 0 := by
    intro b
    obtain ⟨ε, hε, he⟩ := orientedBoundary_row ι u ν hν0 hνker b
    have heq : (∑ s, orientedBoundary ι u ν b s * c s) =
        ε * ∑ s, boundary ι u b s * c s := by
      simp_rw [he, mul_assoc, Finset.mul_sum]
    rw [heq]
    rcases hε with rfl | rfl <;> simp
  exact forall_congr' hrow

/-- The full gluing theorem for every orientation choice on every allowed facet row. -/
theorem theorem_3_1_any_orientation (hι : IsIntegralLattice ι)
    (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    (ν : FacetBlock ι u → V →ₗ[ℝ] ℝ) (hν0 : ∀ b, ν b ≠ 0)
    (hνker : ∀ b, LinearMap.ker (ν b) = Submodule.span ℝ (blockCone ι u b.1 : Set V))
    (c : FullBlock ι u → ℤ) {w : V}
    (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w) :
    ((∀ s, 0 ≤ c s) ∧ (∀ b, ∑ s, orientedBoundary ι u ν b s * c s = 0) ∧
      (∑ s, degreeRow ι u w s * c s) = 1) ↔
      ∃ Φ : Fan ι, Φ.IsComplete ∧ HasRays ι u Φ ∧
        (∀ s, c s = if blockCone ι u s.1 ∈ Φ.cones then 1 else 0) := by
  rw [oriented_boundary_cycle_iff ι u ν hν0 hνker c]
  exact theorem_3_1 ι u hι hnz hpos c hw

end Unimodular.AllowedBlocks
