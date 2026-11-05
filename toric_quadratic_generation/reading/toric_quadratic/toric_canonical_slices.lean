module

public import PaperVerification.ToricDisplacedFaceReserve
public import PaperVerification.ToricNefBoxes

@[expose] public section

/-!
# Exact canonical slices on the saturated face lattice

The canonical shift is literally subtraction of one at every primitive
normal. Active normal heights at least one satisfy the deleted inequalities.
Adjacent rays give exactly the quotient canonical shift; the proved reserve
shows that nonincident original facets make no further cut.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

/-- Exact adjunction on the actual affine slice. The reserve premise is
discharged from original edge lengths in the next theorem. -/
theorem canonical_slice_eq_of_reserve (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ I.image b, 1 ≤ h u)
    (hD : «Σ».IsNef (displacedSupport a (I.image b) h))
    (hreserve : ∀ u ∈ «Σ».rays, insert u (I.image b) ∉ «Σ».cones →
      ∀ x ∈ «Σ».supportFace (displacedSupport a (I.image b) h) (I.image b),
        1 ≤ a u + (dotProductEquiv ℝ (Fin n) (embed n u)) x) :
    quotientFaceMap (displacedSupport a (I.image b) h) b I ''
      («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => «Σ».faceSupport b I hF (displacedSupport a (I.image b) h) u - 1) =
      {x ∈ «Σ».fanPolytope (fun u => a u - 1) | ∀ u ∈ I.image b,
        (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u = h u} := by
  let D := displacedSupport a (I.image b) h
  let Ψ := «Σ».completeQuotientStarFan b I hF
  have hh0 : ∀ u ∈ I.image b, 0 ≤ h u := fun u hu => (by norm_num : (0 : ℝ) ≤ 1).trans (hh u hu)
  have himage := «Σ».quotientFaceMap_image_fanPolytope b I hF hpure D hD
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    have hzparent : z ∈ Ψ.fanPolytope («Σ».faceSupport b I hF D) := by
      apply Ψ.fanPolytope_mono (a := fun u => «Σ».faceSupport b I hF D u - 1)
        (fun u hu => by linarith) hz
    have hface : quotientFaceMap D b I z ∈ «Σ».supportFace D (I.image b) := by
      rw [← himage]
      exact ⟨z, hzparent, rfl⟩
    have hslice : quotientFaceMap D b I z ∈
        {x ∈ «Σ».fanPolytope a | ∀ u ∈ I.image b,
          (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u = h u} := by
      rw [← «Σ».displaced_supportFace_eq_slice a (I.image b) h hh0]
      exact hface
    refine ⟨?_, hslice.2⟩
    intro u hu
    by_cases huF : u ∈ I.image b
    · have hheight := hslice.2 u huF
      have hhu := hh u huF
      change -(a u - 1) ≤ _
      linarith
    · by_cases hadj : insert u (I.image b) ∈ «Σ».cones
      · have hv : u ∈ insert u (I.image b) \ I.image b :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, huF⟩
        have hqray := «Σ».projected_starRay_mem b I hF hadj (Finset.subset_insert _ _) hv
        have hq := hz (coneQuotientLattice b I u) hqray
        have hcoeff := «Σ».faceSupport_projected b I hF D hadj (Finset.subset_insert _ _) hv
        have hDu : D u = a u := by
          simp only [D, displacedSupport, Pi.sub_apply, facetWeight, if_neg huF, sub_zero]
        rw [hDu] at hcoeff
        change -(«Σ».faceSupport b I hF D (coneQuotientLattice b I u) - 1) ≤ _ at hq
        rw [hcoeff] at hq
        rw [quotientFaceMap_pairing]
        change -(a u - 1) ≤ _
        linarith
      · have hr := hreserve u hu hadj (quotientFaceMap D b I z) hface
        change -(a u - 1) ≤ _
        linarith
  · intro x hx
    have hxparent : x ∈ «Σ».fanPolytope a :=
      «Σ».fanPolytope_mono (a := fun u => a u - 1) (fun u hu => by linarith) hx.1
    have hface : x ∈ «Σ».supportFace D (I.image b) := by
      rw [«Σ».displaced_supportFace_eq_slice a (I.image b) h hh0]
      exact ⟨hxparent, hx.2⟩
    have hactive : ∀ i ∈ I,
        (dotProductEquiv ℝ (Fin n) (embed n (b i))) x = -D (b i) :=
      fun i hi => hface.2 _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    obtain ⟨z, rfl⟩ := (mem_range_quotientFaceMap_iff D b I x).mpr hactive
    refine ⟨z, ?_, rfl⟩
    intro u hu
    let u' : Ψ.rays := ⟨u, hu⟩
    obtain ⟨s, hs, hFs, hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
    let v := «Σ».starRayLift b I hF u'
    have hvray := «Σ».ray_mem_of_mem_cone hs (Finset.mem_sdiff.mp hv).1
    have hvF : v ∉ I.image b := (Finset.mem_sdiff.mp hv).2
    have hbound := hx.1 v hvray
    rw [quotientFaceMap_pairing, hproj] at hbound
    have hcoeff := «Σ».faceSupport_lift b I hF D u'
    have hDv : D v = a v := by
      simp only [D, displacedSupport, Pi.sub_apply, facetWeight, if_neg hvF, sub_zero]
    rw [hDv] at hcoeff
    change -(«Σ».faceSupport b I hF D u - 1) ≤ _
    rw [hcoeff]
    change -(a v - 1) ≤ _ at hbound
    linarith

/-- Equation (13) with the nonincident-facet reserve proved from the
literal original edge bound. The heights are arbitrary real numbers. -/
theorem canonical_slice_eq_of_edges (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (h : Lattice n → ℝ) (hh : ∀ u ∈ I.image b, 1 ≤ h u)
    (hbudget : (∑ u ∈ I.image b, h u) + 1 ≤ (e : ℝ)) :
    quotientFaceMap (displacedSupport (fun u => (a u : ℝ)) (I.image b) h) b I ''
      («Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => «Σ».faceSupport b I hF
          (displacedSupport (fun u => (a u : ℝ)) (I.image b) h) u - 1) =
      {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ) - 1) | ∀ u ∈ I.image b,
        (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = h u} := by
  have hh0 : ∀ v ∈ I.image b, 0 ≤ h v :=
    fun v hv => (by norm_num : (0 : ℝ) ≤ 1).trans (hh v hv)
  have hD := «Σ».displacedSupport_isNef_of_edges hpure a ha hedges (I.image b) h hh0
    (by linarith)
  apply «Σ».canonical_slice_eq_of_reserve b I hF hpure _ h hh hD
  intro u hu huF x hx
  have hr := «Σ».displaced_supportFace_reserve_of_edges hpure a ha hedges
    (I.image b) hF h hh0 (by linarith) hD u hu huF x hx
  linarith

end PaperVerification.ToricGeometry.SmoothCompleteFan
