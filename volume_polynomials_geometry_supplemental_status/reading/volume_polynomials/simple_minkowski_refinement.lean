module

public import VolumePolynomials.PolyhedralRefinement
public import VolumePolynomials.CenteredFacetFamily

@[expose] public section
set_option autoImplicit false

/-!
# Minkowski sums with a common simple refinement

Every vertex of the perturbed total sum determines compatible supporting
vertices in each summand. Adding any positive multiple of the refinement to
each summand therefore produces exactly the same finite vertex/facet
incidence structure. This proves the common-refinement step directly from
support inequalities and finite convex hulls.
-/

noncomputable section
open Set Module
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem minkowski_eq_halfspaces_of_refinement
    (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hsimple : ∀ b ∈ feasibleBases l h, ∀ i ∉ b.val, l i (vertexMap l b h) < h i)
    (R Q : ConvexBody E) (hR : (R : Set E) = body l h) (g : ι → ℝ)
    (hbound : ∀ x ∈ Q, ∀ i, l i x ≤ g i)
    (hvertex : ∀ b ∈ feasibleBases l h, vertexMap l b g ∈ Q)
    {r : ℝ} (hr : 0 < r) :
    (↑(Q + r • R) : Set E) = body l (g + r • h) := by
  first
  | ext x
    constructor
    · change x ∈ (Q : Set E) + r • (R : Set E) → _
      rintro ⟨q, hq, y, ⟨p, hp, rfl⟩, rfl⟩ i
      rw [hR] at hp
      simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        add_le_add (hbound q hq i) (mul_le_mul_of_nonneg_left (hp i) hr.le)
    · intro hx
      apply (BodySupport.mem_iff_le_support (Q + r • R)).mpr
      intro f
      obtain ⟨b, hb, hbmax⟩ := exists_maximizing_basis l h
        (hR ▸ R.isCompact) (hR ▸ R.nonempty) f
      have hcoeff := maximizing_coefficients_nonnegative l h b hb
        (hsimple b hb) f hbmax
      have hle := functional_le_vertex_of_normal_bounds l b f hcoeff
        (g + r • h) (fun j => hx j)
      have hp : vertexMap l b g + r • vertexMap l b h ∈ Q + r • R := by
        exact Set.add_mem_add (hvertex b hb)
          (Set.smul_mem_smul_set (by rwa [hR]))
      have hmap : vertexMap l b (g + r • h) =
          vertexMap l b g + r • vertexMap l b h := by rw [map_add, map_smul]
      rw [hmap] at hle
      exact hle.trans (BodySupport.le_support (Q + r • R) f hp)

theorem minkowski_eq_convexHull_refinement_vertices
    (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hsimple : ∀ b ∈ feasibleBases l h, ∀ i ∉ b.val, l i (vertexMap l b h) < h i)
    (R Q : ConvexBody E) (hR : (R : Set E) = body l h) (g : ι → ℝ)
    (hbound : ∀ x ∈ Q, ∀ i, l i x ≤ g i)
    (hvertex : ∀ b ∈ feasibleBases l h, vertexMap l b g ∈ Q)
    {r : ℝ} (hr : 0 < r) :
    (↑(Q + r • R) : Set E) = convexHull ℝ
      ((fun b : BasisIndex l => vertexMap l b (g + r • h)) '' feasibleBases l h) := by
  first
  | let V : Set E :=
      (fun b : BasisIndex l => vertexMap l b (g + r • h)) '' feasibleBases l h
    have hVfin : V.Finite := (Set.toFinite _).image _
    have hVsub : V ⊆ (↑(Q + r • R) : Set E) := by
      rintro x ⟨b, hb, rfl⟩
      dsimp only
      rw [map_add, map_smul]
      exact Set.add_mem_add (hvertex b hb)
        (Set.smul_mem_smul_set (by rwa [hR]))
    apply Subset.antisymm
    · intro x hx
      by_contra hnot
      obtain ⟨f, a, hf, hfx⟩ := geometric_hahn_banach_closed_point
        (convex_convexHull ℝ V) (hVfin.isClosed_convexHull ℝ) hnot
      obtain ⟨b, hb, hbmax⟩ := exists_maximizing_basis l h
        (hR ▸ R.isCompact) (hR ▸ R.nonempty) f
      have hcoeff := maximizing_coefficients_nonnegative l h b hb
        (hsimple b hb) f hbmax
      have hxb : x ∈ body l (g + r • h) := by
        rwa [← minkowski_eq_halfspaces_of_refinement l h hsimple R Q hR g hbound hvertex hr]
      have hle := functional_le_vertex_of_normal_bounds l b f hcoeff
        (g + r • h) (fun j => hxb j)
      have hv : vertexMap l b (g + r • h) ∈ convexHull ℝ V :=
        subset_convexHull ℝ V ⟨b, hb, rfl⟩
      exact (hfx.trans_le (hle.trans (hf _ hv).le)).false
    · exact convexHull_min hVsub (Q + r • R).convex

theorem refinement_vertex_strict_inactive
    (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hsimple : ∀ b ∈ feasibleBases l h, ∀ i ∉ b.val, l i (vertexMap l b h) < h i)
    (Q : ConvexBody E) (g : ι → ℝ)
    (hbound : ∀ x ∈ Q, ∀ i, l i x ≤ g i)
    (hvertex : ∀ b ∈ feasibleBases l h, vertexMap l b g ∈ Q)
    {r : ℝ} (hr : 0 < r) (b : BasisIndex l) (hb : b ∈ feasibleBases l h)
    (i : ι) (hi : i ∉ b.val) :
    l i (vertexMap l b (g + r • h)) < (g + r • h) i := by
  first
  | have hq := hbound _ (hvertex b hb) i
    have hp := hsimple b hb i hi
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_lt_add_of_le_of_lt hq (mul_lt_mul_of_pos_left hp hr)

theorem active_eq_basis_of_strict (l : ι → E →L[ℝ] ℝ)
    (h : ι → ℝ) (b : BasisIndex l)
    (hs : ∀ i ∉ b.val, l i (vertexMap l b h) < h i) :
    active l h (vertexMap l b h) = b.val := by
  first
  | ext i
    rw [mem_active]
    constructor
    · intro hi
      by_contra hni
      exact (hs i hni).ne hi
    · intro hi
      exact vertexMap_active l b h ⟨i, hi⟩

theorem feasibleBases_minkowski_refinement
    (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hsimple : ∀ b ∈ feasibleBases l h, ∀ i ∉ b.val, l i (vertexMap l b h) < h i)
    (R Q : ConvexBody E) (hR : (R : Set E) = body l h) (g : ι → ℝ)
    (hbound : ∀ x ∈ Q, ∀ i, l i x ≤ g i)
    (hvertex : ∀ b ∈ feasibleBases l h, vertexMap l b g ∈ Q)
    {r : ℝ} (hr : 0 < r) :
    feasibleBases l (g + r • h) = feasibleBases l h := by
  first
  | ext b
    constructor
    · intro hb
      have he := vertexMap_mem_extremePoints l b (g + r • h) hb
      rw [← minkowski_eq_halfspaces_of_refinement l h hsimple R Q hR g hbound hvertex hr,
        minkowski_eq_convexHull_refinement_vertices l h hsimple R Q hR g hbound hvertex hr] at he
      obtain ⟨a, ha, hab⟩ := extremePoints_convexHull_subset he
      dsimp only at hab
      have hactive : active l (g + r • h) (vertexMap l a (g + r • h)) = a.val :=
        active_eq_basis_of_strict l _ a
          (refinement_vertex_strict_inactive l h hsimple Q g hbound hvertex hr a ha)
      have hsub : b.val ⊆ a.val := by
        intro i hi
        rw [← hactive, mem_active, hab]
        exact vertexMap_active l b _ ⟨i, hi⟩
      have hba : b.val = a.val := Finset.eq_of_subset_of_card_le hsub (by
        rw [basisIndex_card l b, basisIndex_card l a])
      simpa only [show b = a from Subtype.ext hba] using ha
    · intro hb i
      by_cases hi : i ∈ b.val
      · exact (vertexMap_active l b _ ⟨i, hi⟩).le
      · exact (refinement_vertex_strict_inactive l h hsimple Q g hbound hvertex hr b hb i hi).le

/-- A feasible coordinate vertex of the total sum determines a feasible
supporting vertex of each summand. No simplicity of the summands is assumed. -/
theorem summand_vertex_mem {κ : Type*} [Fintype κ]
    (K : κ → ConvexBody E) (l : ι → E →L[ℝ] ℝ)
    (hbody : (↑(∑ k, K k) : Set E) =
      body l (fun i => ∑ k, BodySupport.support (K k) (l i)))
    (b : BasisIndex l)
    (hb : b ∈ feasibleBases l (fun i => ∑ k, BodySupport.support (K k) (l i)))
    (k : κ) : vertexMap l b (fun i => BodySupport.support (K k) (l i)) ∈ K k := by
  first
  | have hx : vertexMap l b (fun i => ∑ k, BodySupport.support (K k) (l i)) ∈ ∑ k, K k := by
      change vertexMap l b (fun i => ∑ k, BodySupport.support (K k) (l i)) ∈
        (↑(∑ k, K k) : Set E)
      rwa [hbody]
    obtain ⟨p, hp, hsum⟩ := (mem_sum_body K _).mp hx
    have heq : ∀ i ∈ b.val, l i (p k) = BodySupport.support (K k) (l i) := by
      intro i hi
      have hs : (∑ j, l i (p j)) = ∑ j, BodySupport.support (K j) (l i) := by
        rw [← map_sum, hsum, vertexMap_active l b _ ⟨i, hi⟩]
      exact (Finset.sum_eq_sum_iff_of_le
        (fun j (_ : j ∈ Finset.univ) => BodySupport.le_support (K j) (l i) (hp j))).mp hs
          k (Finset.mem_univ k)
    rw [vertexMap_unique l b _ heq]
    exact hp k

end VolumePolynomials.PolyhedralSupport
