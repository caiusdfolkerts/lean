module

public import PaperVerification.ToricDisplacedEdgeBounds
public import PaperVerification.ToricQuotientFaceSupport
public import PaperVerification.ToricSliceReserve

@[expose] public section

/-!
# Nonincident facets do not cut short displaced faces

The local integral slack estimate is applied to the actual primitive dual
coordinates of every Cartier vertex. Convexity then gives the same reserve
on the entire displaced face, including its real points and nef endpoints.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem sum_fullConeBasis_subset (s : «Σ».fullCones)
    (T : Finset (Lattice n)) (hTs : T ⊆ (s : Finset (Lattice n)))
    (h : Lattice n → ℝ) :
    (∑ i, facetWeight T h («Σ».fullConeBasis s i)) = ∑ u ∈ T, h u := by
  calc
    (∑ i, facetWeight T h («Σ».fullConeBasis s i)) =
        ∑ u ∈ (s : Finset (Lattice n)), facetWeight T h u := by
      rw [«Σ».fullConeBasis_ray_set, Finset.sum_image]
      exact fun i _ j _ he => («Σ».fullConeBasis s).injective he
    _ = ∑ u ∈ T, facetWeight T h u := by
      symm
      apply Finset.sum_subset hTs
      intro u hu huT
      simp only [facetWeight, if_neg huT]
    _ = ∑ u ∈ T, h u :=
      Finset.sum_congr rfl (fun u hu => by simp only [facetWeight, if_pos hu])

theorem cartierPoint_displacedSupport (a : Lattice n → ℝ)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ) (s : «Σ».fullCones) :
    «Σ».cartierPoint (displacedSupport a T h) s = «Σ».cartierPoint a s +
      ∑ i, facetWeight T h («Σ».fullConeBasis s i) • «Σ».cartierBasis s i := by
  simp only [cartierPoint, displacedSupport, Pi.sub_apply, sub_smul,
    Finset.sum_sub_distrib, neg_sub, cartierBasis]
  abel

/-- The exact `e - sum h` reserve on every displaced Cartier point, derived
from actual contained axis segments and primitive integral normal vectors. -/
theorem displaced_cartier_nonincident_reserve (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (e : ℝ)
    (haxis : ∀ s : «Σ».fullCones, ∀ i,
      «Σ».cartierPoint a s + e • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) ≤ e)
    (s : «Σ».fullCones) (hTs : T ⊆ (s : Finset (Lattice n)))
    (u : Lattice n) (hu : u ∈ «Σ».rays) (hus : u ∉ (s : Finset (Lattice n))) :
    e - ∑ v ∈ T, h v ≤
      a u + (dotProductEquiv ℝ (Fin n) (embed n u))
        («Σ».cartierPoint (displacedSupport a T h) s) := by
  let v := «Σ».cartierPoint a s
  let B := «Σ».cartierBasis s
  let f : Ambient n →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ _ (a u) + (dotProductEquiv ℝ (Fin n) (embed n u)).toAffineMap
  let α : Fin n → ℝ := fun i => facetWeight T h («Σ».fullConeBasis s i)
  have hα (i : Fin n) : 0 ≤ α i := by
    dsimp only [α, facetWeight]
    split_ifs with hi
    · exact hh _ hi
    · exact le_rfl
  have hsum : (∑ i, α i) = ∑ w ∈ T, h w := «Σ».sum_fullConeBasis_subset s T hTs h
  have hfeasible : ∀ x ∈ «Σ».fanPolytope a, 0 ≤ f x := by
    intro x hx
    have hxu := hx u hu
    change 0 ≤ a u + (dotProductEquiv ℝ (Fin n) (embed n u)) x
    linarith
  have hfv : 0 < f v := by
    have h := «Σ».cartierPoint_support_lt_of_not_mem ha s hu hus
    change 0 < a u + (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s)
    linarith
  have htouch : ∃ y ∈ «Σ».fanPolytope a, f y = 0 := by
    obtain ⟨C, hC, huC⟩ := («Σ».mem_rays_iff u).mp hu
    obtain ⟨U, hU, hCU, hcard⟩ := hpure C hC
    let U' : «Σ».fullCones := ⟨U, Finset.mem_filter.mpr ⟨hU, hcard⟩⟩
    refine ⟨«Σ».cartierPoint a U', «Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) U', ?_⟩
    change a u + (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a U') = 0
    rw [«Σ».cartierPoint_support_eq a U' (hCU huC), add_neg_cancel]
  have hintegral (i : Fin n) : ∃ z : ℤ, (z : ℝ) = f.linear (B i) := by
    refine ⟨∑ j, u j * integralDualBasis («Σ».fullConeBasis s) i j, ?_⟩
    have hf : f.linear = dotProductEquiv ℝ (Fin n) (embed n u) := by
      simp only [f, AffineMap.add_linear, AffineMap.const_linear,
        LinearMap.toAffineMap_linear, zero_add]
    rw [hf]
    change _ = (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierBasis s i)
    rw [cartierBasis, integralBasisReal_apply]
    exact (normalRay_pairing_lattice u (integralDualBasis («Σ».fullConeBasis s) i)).symm
  have hreserve := nonincident_facet_displacement_reserve
    («Σ».fanPolytope a) v B
    (fun x hx i => «Σ».cartierPoint_orthant s hx i)
    (fun _ => e) e (fun _ => le_rfl) (haxis s) f hfeasible hfv htouch hintegral
    α hα (by rw [hsum]; exact hbudget)
  rw [hsum] at hreserve
  rw [«Σ».cartierPoint_displacedSupport]
  exact hreserve

/-- A primitive facet not incident to the original face retains the same
reserve on every point of the displaced face. -/
theorem displaced_supportFace_nonincident_reserve (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (e : ℝ)
    (haxis : ∀ s : «Σ».fullCones, ∀ i,
      «Σ».cartierPoint a s + e • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a)
    (T : Finset (Lattice n)) (hT : T ∈ «Σ».cones)
    (h : Lattice n → ℝ) (hh : ∀ u ∈ T, 0 ≤ h u)
    (hbudget : (∑ u ∈ T, h u) ≤ e)
    (hD : «Σ».IsNef (displacedSupport a T h))
    (u : Lattice n) (hu : u ∈ «Σ».rays) (huT : insert u T ∉ «Σ».cones)
    (x : Ambient n) (hx : x ∈ «Σ».supportFace (displacedSupport a T h) T) :
    e - ∑ v ∈ T, h v ≤ a u + (dotProductEquiv ℝ (Fin n) (embed n u)) x := by
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n u)
  have hall : «Σ».supportFace (displacedSupport a T h) T ⊆
      f ⁻¹' Ici (e - (∑ v ∈ T, h v) - a u) := by
    rw [«Σ».supportFace_eq_convexHull_cartier hpure _ hD T hT]
    apply convexHull_min
    · rintro z ⟨s, rfl⟩
      have hTs := (Finset.mem_filter.mp s.property).2
      have hus : u ∉ ((s : «Σ».fullCones) : Finset (Lattice n)) := by
        intro hus
        exact huT («Σ».downward _ («Σ».fullCones_mem s) _ (Finset.insert_subset hus hTs))
      have hreserveVertex := «Σ».displaced_cartier_nonincident_reserve hpure a ha e haxis
        T h hh hbudget s hTs u hu hus
      change e - (∑ v ∈ T, h v) - a u ≤ _
      linarith
    · exact (convex_Ici _).linear_preimage f
  have hl := hall hx
  change e - (∑ v ∈ T, h v) - a u ≤ f x at hl
  change _ ≤ a u + f x
  linarith

/-- The preceding real-height reserve follows from the literal original
edge bound of the integral support polytope. -/
theorem displaced_supportFace_reserve_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (T : Finset (Lattice n)) (hT : T ∈ «Σ».cones)
    (h : Lattice n → ℝ) (hh : ∀ u ∈ T, 0 ≤ h u)
    (hbudget : (∑ u ∈ T, h u) ≤ e)
    (hD : «Σ».IsNef (displacedSupport (fun u => (a u : ℝ)) T h))
    (u : Lattice n) (hu : u ∈ «Σ».rays) (huT : insert u T ∉ «Σ».cones)
    (x : Ambient n) (hx : x ∈ «Σ».supportFace
      (displacedSupport (fun u => (a u : ℝ)) T h) T) :
    (e : ℝ) - ∑ v ∈ T, h v ≤ (a u : ℝ) +
      (dotProductEquiv ℝ (Fin n) (embed n u)) x :=
  «Σ».displaced_supportFace_nonincident_reserve hpure _ ha e
    («Σ».support_axis_point_of_edgesAtLeast hpure a ha hedges)
    T hT h hh hbudget hD u hu huT x hx

end PaperVerification.ToricGeometry.SmoothCompleteFan
