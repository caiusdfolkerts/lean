module

public import PaperVerification.ToricNearFacetAdjoint

@[expose] public section

/-!
# Exact targets and lattice reconstruction on a pair of normal slices

Normal heights determine an actual saturated affine lattice. The target's
remaining coordinates are integral, and strict incident inequalities give
the ordinary topological interior of the sum of the quotient polytopes.
The canonical slice identity gives the interior-summand reconstruction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical Pointwise

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

theorem exists_quotient_slice_sum_target
    (a c : Lattice n → ℤ) (h k : Lattice n → ℕ) (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun u => ((a + c) u : ℝ))))
    (hnormal : ∀ u ∈ I.image b,
      latticeSlack (a + c) m u = (h u : ℤ) + (k u : ℤ)) :
    ∃ mQ : Lattice (n - I.card),
      (quotientFaceIntegralChart
        (displacedSupportLattice a (I.image b) h + displacedSupportLattice c (I.image b) k)
        b I).latticeMap mQ = m ∧
      embed (n - I.card) mQ ∈ interior ((«Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => ((«Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) +
          «Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k)) u : ℝ))) := by
  let dA := displacedSupportLattice a (I.image b) h
  let dC := displacedSupportLattice c (I.image b) k
  let eSum := quotientFaceIntegralChart (dA + dC) b I
  have hcoeff (u : Lattice n) : (dA + dC) u =
      (a + c) u - if u ∈ I.image b then (h u : ℤ) + (k u : ℤ) else 0 := by
    dsimp only [dA, dC, displacedSupportLattice, Pi.add_apply]
    split_ifs <;> omega
  have hcoeffR : (fun u => ((dA + dC) u : ℝ)) =
      displacedSupport (fun u => ((a + c) u : ℝ)) (I.image b)
        (fun u => (h u : ℝ) + (k u : ℝ)) := by
    funext u
    rw [hcoeff]
    simp only [displacedSupport, Pi.sub_apply, facetWeight]
    split_ifs <;> simp
  have hmactive : ∀ i ∈ I,
      (dotProductEquiv ℝ (Fin n) (embed n (b i))) (embed n m) = -((dA + dC) (b i) : ℝ) := by
    intro i hi
    have hbi : b i ∈ I.image b := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hnormal' := hnormal (b i) hbi
    rw [normalRay_pairing_lattice, hcoeff, if_pos hbi]
    have hz : (∑ j, b i j * m j) = -((a + c) (b i) - ((h (b i) : ℤ) + (k (b i) : ℤ))) := by
      dsimp only [latticeSlack] at hnormal'
      omega
    exact_mod_cast hz
  obtain ⟨mQ, hmQmap⟩ := eSum.exists_latticeMap_of_mem_range m (by
    rw [quotientFaceIntegralChart_realMap]
    exact (mem_range_quotientFaceMap_iff _ b I _).mpr hmactive)
  have hmQreal : quotientFaceMap (fun u => ((dA + dC) u : ℝ)) b I
      (embed (n - I.card) mQ) = embed n m := by
    rw [← quotientFaceIntegralChart_realMap, ← IntegralAffineEmbedding.embed_latticeMap]
    exact congrArg (embed n) hmQmap
  refine ⟨mQ, hmQmap, ?_⟩
  have hinterior : embed (n - I.card) mQ ∈ interior
      ((«Σ».completeQuotientStarFan b I hF).fanPolytope
        («Σ».faceSupport b I hF (fun u => ((dA + dC) u : ℝ)))) := by
    rw [hcoeffR]
    apply «Σ».quotient_slice_interior b I hF _ (fun u => (h u : ℝ) + (k u : ℝ))
    rw [← hcoeffR, hmQreal]
    exact hm
  rw [← «Σ».faceSupportLattice_cast, «Σ».faceSupportLattice_add] at hinterior
  exact hinterior

theorem quotient_slice_sum_target_interior
    (a c : Lattice n → ℤ) (h k : Lattice n → ℕ)
    (A C : LatticePolytope (n - I.card))
    (hA : A.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
      (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) u : ℝ)))
    (hC : C.carrier = («Σ».completeQuotientStarFan b I hF).fanPolytope
      (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k) u : ℝ)))
    (hpure : «Σ».IsPure)
    (hqa : («Σ».completeQuotientStarFan b I hF).IsNef
      (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) u : ℝ)))
    (hqc : («Σ».completeQuotientStarFan b I hF).IsNef
      (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k) u : ℝ)))
    (mQ : Lattice (n - I.card))
    (hmQ : embed (n - I.card) mQ ∈ interior ((«Σ».completeQuotientStarFan b I hF).fanPolytope
      (fun u => ((«Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) +
        «Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k)) u : ℝ)))) :
    embed (n - I.card) mQ ∈ interior (A.minkowskiSum C) := by
  have hcast : (fun u => ((«Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) +
        «Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k)) u : ℝ)) =
      (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) u : ℝ)) +
        (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice c (I.image b) k) u : ℝ)) := by
    funext u
    simp only [Pi.add_apply, Int.cast_add]
  rw [hcast, («Σ».completeQuotientStarFan b I hF).fanPolytope_add
    («Σ».completeQuotientStarFan_isPure hpure b I hF) _ _ hqa hqc, ← hA, ← hC] at hmQ
  exact hmQ

/-- A genuine interior lattice point of the parent quotient slice maps
back to an interior lattice point of the original polytope, with the
normal height at least one and the proved nonincident reserve. -/
theorem quotient_slice_interior_lattice_image (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (h : Lattice n → ℕ) (hh : ∀ u ∈ I.image b, 1 ≤ h u)
    (hbudget : (∑ u ∈ I.image b, h u) + 1 ≤ e)
    (z : Lattice (n - I.card))
    (hz : embed (n - I.card) z ∈ interior
      ((«Σ».completeQuotientStarFan b I hF).fanPolytope
        (fun u => («Σ».faceSupportLattice b I hF (displacedSupportLattice a (I.image b) h) u : ℝ)))) :
    embed n ((quotientFaceIntegralChart (displacedSupportLattice a (I.image b) h) b I).latticeMap z) ∈
      interior («Σ».fanPolytope (fun u => (a u : ℝ))) := by
  let d := displacedSupportLattice a (I.image b) h
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let eQ := quotientFaceIntegralChart d b I
  have hzadj := (Ψ.lattice_mem_interior_iff_adjointSupport
    («Σ».faceSupportLattice b I hF d) z).mp hz
  have hzcanonical : embed (n - I.card) z ∈ Ψ.fanPolytope
      (fun u => «Σ».faceSupport b I hF (fun u => (d u : ℝ)) u - 1) := by
    simpa only [← «Σ».faceSupportLattice_cast, Int.cast_sub, Int.cast_one] using hzadj
  have hcanonical := «Σ».canonical_slice_eq_of_edges b I hF hpure a ha hedges
    (fun u => (h u : ℝ)) (fun u hu => by exact_mod_cast hh u hu)
    (by exact_mod_cast hbudget)
  rw [← displacedSupportLattice_cast] at hcanonical
  have hzimage : eQ.realMap (embed (n - I.card) z) ∈
      {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ) - 1) | ∀ u ∈ I.image b,
        (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = (h u : ℝ)} := by
    rw [← hcanonical, quotientFaceIntegralChart_realMap]
    exact Set.mem_image_of_mem _ hzcanonical
  apply («Σ».lattice_mem_interior_iff_adjointSupport a (eQ.latticeMap z)).mpr
  simpa only [IntegralAffineEmbedding.embed_latticeMap, Int.cast_sub, Int.cast_one] using hzimage.1

end PaperVerification.ToricGeometry.SmoothCompleteFan
