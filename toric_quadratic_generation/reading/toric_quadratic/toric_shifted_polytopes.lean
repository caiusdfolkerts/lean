module
public import PaperVerification.ToricIntegralBasis
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology
@[expose] public section
/-!
# Shifted supporting halfspaces and matched corner centers

The following separation argument proves the center-polytope identity used in
Lemma 4.2. The hypotheses are actual supporting linear functionals and genuine
bases, and the conclusion is equality of ordinary subsets of a real vector space.
The remaining normal-fan construction is independent of this convex argument.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators

variable {E I J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- The intersection of the specified closed supporting halfspaces. -/
def normalHalfspaces (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ) : Set E :=
  {x | ∀ i, a i ≤ u i x}

theorem convex_normalHalfspaces (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ) :
    Convex ℝ (normalHalfspaces u a) := by
  intro x hx y hy r s hr hs hrs i
  simp only [map_add, map_smul, smul_eq_mul]
  have hbound := add_le_add (mul_le_mul_of_nonneg_left (hx i) hr)
    (mul_le_mul_of_nonneg_left (hy i) hs)
  simpa only [← add_mul, hrs, one_mul] using hbound

/-- A finite convex hull is characterized by its lower support values. -/
theorem mem_finite_convexHull_of_lower_support [Finite J] (c : J → E) (x : E)
    (h : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, f (c j) ≤ f x) :
    x ∈ convexHull ℝ (Set.range c) := by
  by_contra hx
  obtain ⟨f, t, hxt, ht⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (Set.range c))
    ((Set.finite_range c).isClosed_convexHull ℝ) hx
  obtain ⟨j, hj⟩ := h f.toLinearMap
  have hjt := ht (c j) (subset_convexHull ℝ _ (Set.mem_range_self j))
  exact (not_lt_of_ge hj) (hxt.trans hjt)

/-- Nonnegative coordinates in a basis cone give the expected lower bound
for every linear functional nonnegative on its generating vectors. -/
theorem linear_le_of_basis_coordinates [Fintype K]
    (b : Module.Basis K ℝ E) (f : E →ₗ[ℝ] ℝ) (c x : E)
    (hf : ∀ i, 0 ≤ f (b i)) (hx : ∀ i, 0 ≤ b.repr (x - c) i) :
    f c ≤ f x := by
  have hsum : f (x - c) = ∑ i, b.repr (x - c) i * f (b i) := by
    conv_lhs => rw [← b.sum_repr (x - c)]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hnonneg : 0 ≤ f (x - c) := by
    rw [hsum]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (hf i))
  simpa only [map_sub, sub_nonneg] using hnonneg

/-- Feasible Cartier points indexed by a complete collection of basis cones
generate precisely the shifted halfspace polytope. The active supporting
functionals are the dual coordinates of each basis. -/
theorem shifted_halfspaces_eq_convexHull [Finite J] [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (b : J → Module.Basis K ℝ E) (active : J → K → I) (c : J → E)
    (hdual : ∀ j i x, u (active j i) x = (b j).repr x i)
    (hcomplete : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, ∀ i, 0 ≤ f (b j i))
    (hactive : ∀ j i, u (active j i) (c j) = a (active j i))
    (hfeasible : ∀ j, c j ∈ normalHalfspaces u a) :
    normalHalfspaces u a = convexHull ℝ (Set.range c) := by
  apply Set.Subset.antisymm
  · intro x hx
    apply mem_finite_convexHull_of_lower_support c x
    intro f
    obtain ⟨j, hj⟩ := hcomplete f
    refine ⟨j, linear_le_of_basis_coordinates (b j) f (c j) x hj ?_⟩
    intro i
    rw [← hdual, map_sub, hactive]
    exact sub_nonneg.mpr (hx (active j i))
  · exact convexHull_min (by rintro _ ⟨j, rfl⟩; exact hfeasible j)
      (convex_normalHalfspaces u a)

/-- A nonzero supporting functional is strictly above its support value at
an interior point. The proof uses the open-map theorem for a surjective real
linear functional, so it applies to the actual topological interior. -/
theorem strict_support_of_interior (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (x : E) (hx : x ∈ interior (normalHalfspaces u a)) (i : I) (hi : u i ≠ 0) :
    a i < u i x := by
  have hne : ∃ v : E, u i v ≠ 0 := by
    by_contra h
    apply hi
    ext v
    by_contra hv
    exact h ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hne
  have hsurj : Function.Surjective (u i) := by
    intro r
    refine ⟨(r / u i v) • v, ?_⟩
    simp only [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ r hv
  have hopen := (u i).isOpenMap_of_finiteDimensional hsurj
  have hmaps : Set.MapsTo (u i) (normalHalfspaces u a) (Set.Ici (a i)) :=
    fun y hy => hy i
  have h := hopen.mapsTo_interior hmaps hx
  simpa only [interior_Ici, Set.mem_Ioi] using h

/-- Integrality upgrades strict support to an entire unit of facet slack. -/
theorem integral_support_of_interior {n : ℕ}
    (u : I → Ambient n →ₗ[ℝ] ℝ) (a : I → ℤ)
    (hu : ∀ i z, ∃ k : ℤ, u i (embed n z) = k)
    (hne : ∀ i, u i ≠ 0) (m : Lattice n)
    (hm : embed n m ∈ interior (normalHalfspaces u (fun i => (a i : ℝ)))) :
    ∀ i, (a i : ℝ) + 1 ≤ u i (embed n m) := by
  intro i
  have hstrict := strict_support_of_interior u (fun i => (a i : ℝ))
    (embed n m) hm i (hne i)
  obtain ⟨k, hk⟩ := hu i m
  rw [hk] at hstrict ⊢
  have hki : a i < k := by exact_mod_cast hstrict
  have hki' : a i + 1 ≤ k := by omega
  exact_mod_cast hki'

/-- The center of the unit corner box at a specified vertex. -/
def cornerCenter [Fintype K] (v : E) (b : Module.Basis K ℝ E) : E :=
  v + ∑ i, (1 / 2 : ℝ) • b i

/-- Translation from corner coordinates in `[0,1]` to centered coordinates
in `[-1/2,1/2]` does not change the actual box. -/
theorem cornerCenter_box_mem [Fintype K] (P : Set E)
    (v : E) (b : Module.Basis K ℝ E)
    (hbox : ∀ t : K → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) →
      v + ∑ i, t i • b i ∈ P)
    (t : K → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
    cornerCenter v b + ∑ i, t i • b i ∈ P := by
  have hshift : ∀ i, 0 ≤ 1 / 2 + t i ∧ 1 / 2 + t i ≤ 1 := by
    intro i
    have h := abs_le.mp (ht i)
    constructor <;> linarith
  have h := hbox (fun i => 1 / 2 + t i) hshift
  simpa only [cornerCenter, add_smul, Finset.sum_add_distrib, add_assoc] using h

/-- A corner-box center satisfies all integral supporting inequalities shifted
inward by one half, including normals not incident to its own vertex. -/
theorem integral_cornerCenter_feasible [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (v : E) (b : Module.Basis K ℝ E)
    (hu : ∀ i, u i ≠ 0)
    (hint : ∀ i k, ∃ z : ℤ, (z : ℝ) = u i (b k))
    (hbox : ∀ t : K → ℝ, (∀ k, 0 ≤ t k ∧ t k ≤ 1) →
      v + ∑ k, t k • b k ∈ normalHalfspaces u a) :
    cornerCenter v b ∈ normalHalfspaces u (fun i => a i + 1 / 2) := by
  classical
  intro i
  let f : E →ᵃ[ℝ] ℝ := (u i).toAffineMap - AffineMap.const ℝ E (a i)
  have hf : f.linear = u i := by simp [f]
  choose z hz using hint i
  have hboxf : ∀ t : K → ℝ, (∀ k, |t k| ≤ 1 / 2) →
      0 ≤ f (cornerCenter v b + ∑ k, t k • b k) := by
    intro t ht
    have hmem := cornerCenter_box_mem (normalHalfspaces u a) v b hbox t ht
    change 0 ≤ u i (cornerCenter v b + ∑ k, t k • b k) - a i
    exact sub_nonneg.mpr (hmem i)
  have h := PaperVerification.Toric.integral_unit_box_center_slack
    f (by simpa only [hf] using hu i) (cornerCenter v b) b z
    (by simpa only [hf] using hz) hboxf
  change (1 / 2 : ℝ) ≤ u i (cornerCenter v b) - a i at h
  linarith

/-- The active dual coordinate increases by precisely one half at a corner-box
center. This is the Cartier equation behind the shifted-polytope identity. -/
theorem cornerCenter_dual_coordinate [Fintype K] (v : E)
    (b : Module.Basis K ℝ E) (u : E →ₗ[ℝ] ℝ) (k : K)
    (hu : ∀ x, u x = b.repr x k) :
    u (cornerCenter v b) = u v + 1 / 2 := by
  classical
  simp only [cornerCenter, map_add, map_sum, map_smul, smul_eq_mul]
  rw [show (∑ i, (1 / 2 : ℝ) * u (b i)) = 1 / 2 by
    simp [hu, Module.Basis.repr_self, Finsupp.single_apply]]

/-- The exact shifted halfspace description of the convex hull of all unit-box
centers, with every geometric and integrality requirement displayed. -/
theorem corner_centers_convexHull [Finite J] [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a : I → ℝ)
    (v : J → E) (b : J → Module.Basis K ℝ E) (active : J → K → I)
    (hdual : ∀ j k x, u (active j k) x = (b j).repr x k)
    (hcomplete : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, ∀ k, 0 ≤ f (b j k))
    (hactive : ∀ j k, u (active j k) (v j) = a (active j k))
    (hu : ∀ i, u i ≠ 0)
    (hint : ∀ i j k, ∃ z : ℤ, (z : ℝ) = u i (b j k))
    (hbox : ∀ (j : J) (t : K → ℝ), (∀ k, 0 ≤ t k ∧ t k ≤ 1) →
      v j + ∑ k, t k • b j k ∈ normalHalfspaces u a) :
    normalHalfspaces u (fun i => a i + 1 / 2) =
      convexHull ℝ (Set.range fun j => cornerCenter (v j) (b j)) := by
  apply shifted_halfspaces_eq_convexHull u (fun i => a i + 1 / 2)
    b active (fun j => cornerCenter (v j) (b j)) hdual hcomplete
  · intro j k
    rw [cornerCenter_dual_coordinate (v j) (b j) _ k (hdual j k), hactive]
  · intro j
    exact integral_cornerCenter_feasible u a (v j) (b j) hu
      (fun i k => hint i j k) (hbox j)

/-- Sums of matched feasible Cartier points generate the halfspace polytope
with summed support values. This is the normal-fan part of equation (7). -/
theorem matched_centers_convexHull [Finite J] [Fintype K]
    (u : I → E →ₗ[ℝ] ℝ) (a d : I → ℝ)
    (b : J → Module.Basis K ℝ E) (active : J → K → I) (c e : J → E)
    (hdual : ∀ j k x, u (active j k) x = (b j).repr x k)
    (hcomplete : ∀ f : E →ₗ[ℝ] ℝ, ∃ j, ∀ k, 0 ≤ f (b j k))
    (hcactive : ∀ j k, u (active j k) (c j) = a (active j k))
    (heactive : ∀ j k, u (active j k) (e j) = d (active j k))
    (hc : ∀ j, c j ∈ normalHalfspaces u a)
    (he : ∀ j, e j ∈ normalHalfspaces u d) :
    normalHalfspaces u (fun i => a i + d i) =
      convexHull ℝ (Set.range fun j => c j + e j) := by
  apply shifted_halfspaces_eq_convexHull u (fun i => a i + d i)
    b active (fun j => c j + e j) hdual hcomplete
  · intro j k
    rw [map_add, hcactive, heactive]
  · intro j i
    rw [map_add]
    exact add_le_add (hc j i) (he j i)

end PaperVerification.ToricGeometry
