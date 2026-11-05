module

public import PaperVerification.ToricQuotientFacePolytopes
public import PaperVerification.ToricCanonicalSlices

@[expose] public section

/-!
# Addition, interior targets, and prescribed parity in exact face charts

The two affine origins add, the tangent lattice map is shared, and every
integral target satisfying the active equations has integral quotient
coordinates. Normal parity compatibility is exactly the condition needed
to represent an ambient parity class in the selected affine chart.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange
open scoped BigOperators Classical

variable {n : ℕ}

theorem quotientFaceOrigin_add (a c : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    quotientFaceOrigin (a + c) b I = quotientFaceOrigin a b I + quotientFaceOrigin c b I := by
  simp only [quotientFaceOrigin, Pi.add_apply, add_smul, Finset.sum_add_distrib, neg_add]

theorem quotientFaceMap_add (a c : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x y : Ambient (n - I.card)) :
    quotientFaceMap (a + c) b I (x + y) =
      quotientFaceMap a b I x + quotientFaceMap c b I y := by
  simp only [quotientFaceMap_apply, quotientFaceOrigin_add, map_add]
  abel

theorem quotientFaceIntegralChart_add (a c : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x y : Lattice (n - I.card)) :
    (quotientFaceIntegralChart (a + c) b I).latticeMap (x + y) =
      (quotientFaceIntegralChart a b I).latticeMap x +
        (quotientFaceIntegralChart c b I).latticeMap y := by
  apply embed_injective n
  rw [map_add, IntegralAffineEmbedding.embed_latticeMap,
    IntegralAffineEmbedding.embed_latticeMap, IntegralAffineEmbedding.embed_latticeMap,
    quotientFaceIntegralChart_realMap, quotientFaceIntegralChart_realMap,
    quotientFaceIntegralChart_realMap, map_add]
  have hcast : (fun u => ((a + c) u : ℝ)) =
      (fun u => (a u : ℝ)) + (fun u => (c u : ℝ)) := by
    funext u
    simp
  rw [hcast, quotientFaceMap_add]

theorem quotientFaceOriginLattice_coordinate (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) (i : Fin n) :
    (integralDualBasis b).repr (quotientFaceOriginLattice a b I) i =
      if i ∈ I then -a (b i) else 0 := by
  simp only [quotientFaceOriginLattice, map_neg, map_sum, LinearEquiv.map_smul,
    Finsupp.neg_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self_apply]
  by_cases hi : i ∈ I <;> simp [hi, smul_eq_mul]

/-- A parity class is represented in an actual saturated selected-basis
chart whenever its omitted coordinates have the required even residual. -/
theorem selectedBasisChart_parity_representative {d : ℕ}
    (v : Lattice n) (B : Module.Basis (Fin n) ℤ (Lattice n))
    (a : Fin d ↪ Fin n) (p : Lattice n)
    (hpar : ∀ i ∉ Set.range a, ∃ w : ℤ, B.repr (p - v) i = w + w) :
    ∃ q : Lattice d, SameParity ((selectedBasisChart v B a).latticeMap q) p := by
  let q : Lattice d := fun j => B.repr (p - v) (a j)
  let w : Fin n → ℤ := fun i => if hi : i ∉ Set.range a then Classical.choose (hpar i hi) else 0
  have hw (i : Fin n) (hi : i ∉ Set.range a) : B.repr (p - v) i = w i + w i := by
    simpa only [w, dif_pos hi] using Classical.choose_spec (hpar i hi)
  have hsum (i : Fin n) : B.repr (∑ j, w j • B j) i = w i := by
    simp only [map_sum, LinearEquiv.map_smul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, Module.Basis.repr_self_apply]
    simp [smul_eq_mul]
  refine ⟨q, -(∑ j, w j • B j), ?_⟩
  apply B.ext_elem
  intro i
  change B.repr (v + selectedBasisMap B a q - p) i = _
  simp only [map_add, map_sub, map_neg, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.neg_apply, hsum]
  by_cases hi : i ∈ Set.range a
  · obtain ⟨j, rfl⟩ := hi
    rw [selectedBasisMap_coordinate]
    have hwzero : w (a j) = 0 := by
      have hjmem : a j ∈ Set.range a := ⟨j, rfl⟩
      simp only [w, dif_neg (not_not.mpr hjmem)]
    rw [hwzero]
    simp only [q, map_sub, Finsupp.sub_apply]
    ring
  · rw [selectedBasisMap_coordinate_eq_zero B a q i hi]
    have hwi := hw i hi
    simp only [map_sub, Finsupp.sub_apply] at hwi
    omega

/-- Prescribed normal parity lifts to the actual quotient face chart. -/
theorem quotientFace_parity_representative (a : Lattice n → ℤ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (p : Lattice n)
    (hpar : ∀ i ∈ I, ∃ w : ℤ, (∑ j, p j * b i j) + a (b i) = w + w) :
    ∃ q : Lattice (n - I.card),
      SameParity ((quotientFaceIntegralChart a b I).latticeMap q) p := by
  apply selectedBasisChart_parity_representative
    (quotientFaceOriginLattice a b I) (integralDualBasis b) (complementaryEmbedding I) p
  intro i hi
  have hiI : i ∈ I := by
    simpa only [mem_range_complementaryEmbedding_iff, not_not] using hi
  obtain ⟨w, hw⟩ := hpar i hiI
  refine ⟨w, ?_⟩
  rw [map_sub, Finsupp.sub_apply, quotientFaceOriginLattice_coordinate,
    if_pos hiI, integralDualBasis_repr, sub_neg_eq_add, hw]

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones)

theorem faceSupport_add (a c : Lattice n → ℝ) :
    «Σ».faceSupport b I hF (a + c) = «Σ».faceSupport b I hF a + «Σ».faceSupport b I hF c := by
  funext u
  by_cases hu : u ∈ («Σ».completeQuotientStarFan b I hF).rays
  · simp only [faceSupport, dif_pos hu, Pi.add_apply, quotientFaceOrigin_add, map_add]
    ring
  · simp only [faceSupport, dif_neg hu, Pi.add_apply, zero_add]

theorem faceSupportLattice_add (a c : Lattice n → ℤ) :
    «Σ».faceSupportLattice b I hF (a + c) =
      «Σ».faceSupportLattice b I hF a + «Σ».faceSupportLattice b I hF c := by
  funext u
  apply Int.cast_injective (α := ℝ)
  have he := congrFun («Σ».faceSupport_add b I hF
    (fun v => (a v : ℝ)) (fun v => (c v : ℝ))) u
  have hcast : (fun v => ((a + c) v : ℝ)) =
      (fun v => (a v : ℝ)) + (fun v => (c v : ℝ)) := by funext v; simp
  rw [← hcast, ← «Σ».faceSupportLattice_cast, ← «Σ».faceSupportLattice_cast,
    ← «Σ».faceSupportLattice_cast] at he
  simpa only [Pi.add_apply, Int.cast_add] using he

/-- A strictly interior original target remains strictly interior in the
exact quotient slice. Only adjacent primitive inequalities are relevant. -/
theorem quotient_slice_interior (a : Lattice n → ℝ) (h : Lattice n → ℝ)
    (x : Ambient (n - I.card))
    (hx : quotientFaceMap (displacedSupport a (I.image b) h) b I x ∈
      interior («Σ».fanPolytope a)) :
    x ∈ interior ((«Σ».completeQuotientStarFan b I hF).fanPolytope
      («Σ».faceSupport b I hF (displacedSupport a (I.image b) h))) := by
  rw [(«Σ».completeQuotientStarFan b I hF).interior_fanPolytope_eq]
  rw [«Σ».interior_fanPolytope_eq] at hx
  intro u hu
  let u' : («Σ».completeQuotientStarFan b I hF).rays := ⟨u, hu⟩
  obtain ⟨s, hs, hFs, hv, hproj⟩ := «Σ».starRayLift_spec b I hF u'
  let v := «Σ».starRayLift b I hF u'
  have hvF : v ∉ I.image b := (Finset.mem_sdiff.mp hv).2
  have hvray := «Σ».ray_mem_of_mem_cone hs (Finset.mem_sdiff.mp hv).1
  have hbound := hx v hvray
  rw [quotientFaceMap_pairing, hproj] at hbound
  have hcoeff := «Σ».faceSupport_lift b I hF (displacedSupport a (I.image b) h) u'
  change «Σ».faceSupport b I hF (displacedSupport a (I.image b) h) u =
    displacedSupport a (I.image b) h v +
      (dotProductEquiv ℝ (Fin n) (embed n v))
        (quotientFaceOrigin (displacedSupport a (I.image b) h) b I) at hcoeff
  have hvalue : displacedSupport a (I.image b) h v = a v := by
    simp only [displacedSupport, Pi.sub_apply, facetWeight, if_neg hvF, sub_zero]
  rw [hvalue] at hcoeff
  rw [hcoeff]
  linarith

end SmoothCompleteFan

end PaperVerification.ToricGeometry
