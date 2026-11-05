module

public import PaperVerification.ToricBundleFanStar
public import PaperVerification.ToricQuotientStarCovering


@[expose] public section
/-!
# The fan of a projective-space bundle from a zero-focus relation

The lattice splitting and the exact product description of cones are derived
from the primitive relation and its cone replacement property.  In particular,
no bundle, contraction morphism, or quotient-fan conclusion is included in the
input data.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- A choice of an integral basis extending all but one positive ray.
This contains only coordinate choices, not a quotient-fan assertion. -/
structure BundleCoordinates where
  omitted : Lattice n
  omitted_mem : omitted ∈ R.positive
  basis : Module.Basis (Fin n) ℤ (Lattice n)
  fiberIndices : Finset (Fin n)
  fiber_ray_set : fiberIndices.image basis = R.positive.erase omitted

theorem bundleCoordinates_nonempty : Nonempty R.BundleCoordinates := by
  obtain ⟨u, hu⟩ := «Σ».primitiveCollection_nonempty R.primitive
  obtain ⟨b, I, hI⟩ := «Σ».smooth (R.positive.erase u)
    (R.primitive.2.2 _ (Finset.erase_ssubset hu))
  exact ⟨⟨u, hu, b, I, hI.symm⟩⟩

def bundleCoordinates : R.BundleCoordinates := Classical.choice R.bundleCoordinates_nonempty

namespace BundleCoordinates

variable {R} (c : R.BundleCoordinates)

theorem fiberIndices_card : c.fiberIndices.card = R.fiberDimension := by
  rw [← Finset.card_image_of_injective c.fiberIndices c.basis.injective,
    c.fiber_ray_set, Finset.card_erase_of_mem c.omitted_mem]
  rfl

theorem fiber_cone : c.fiberIndices.image c.basis ∈ «Σ».cones := by
  rw [c.fiber_ray_set]
  exact R.primitive.2.2 _ (Finset.erase_ssubset c.omitted_mem)

theorem fiber_subset_positive : c.fiberIndices.image c.basis ⊆ R.positive := by
  rw [c.fiber_ray_set]
  exact Finset.erase_subset _ _

abbrev quotientLattice : Lattice n →ₗ[ℤ] Lattice (n - c.fiberIndices.card) :=
  coneQuotientLattice c.basis c.fiberIndices

abbrev quotientReal : Ambient n →ₗ[ℝ] Ambient (n - c.fiberIndices.card) :=
  coneQuotientReal c.basis c.fiberIndices

/-- The genuine smooth complete base fan in the saturated quotient lattice. -/
def baseFan : SmoothCompleteFan (n - c.fiberIndices.card) :=
  «Σ».completeQuotientStarFan c.basis c.fiberIndices c.fiber_cone

theorem baseFan_isPure (hpure : «Σ».IsPure) : c.baseFan.IsPure :=
  «Σ».completeQuotientStarFan_isPure hpure c.basis c.fiberIndices c.fiber_cone

theorem base_dimension : n - c.fiberIndices.card = n - R.fiberDimension := by
  rw [c.fiberIndices_card]

theorem omitted_eq_negative_sum (hN : R.negative = ∅) :
    c.omitted = -(∑ i ∈ c.fiberIndices, c.basis i) := by
  have hsum : (∑ v ∈ R.positive.erase c.omitted, v) + c.omitted = 0 := by
    calc
      (∑ v ∈ R.positive.erase c.omitted, v) + c.omitted =
          ∑ v ∈ R.positive, v :=
        Finset.sum_erase_add R.positive (fun v : Lattice n => v) c.omitted_mem
      _ = 0 := by
        rw [R.equation, hN]
        simp
  have he : (∑ v ∈ R.positive.erase c.omitted, v) =
      ∑ i ∈ c.fiberIndices, c.basis i := by
    rw [← c.fiber_ray_set, Finset.sum_image]
    exact fun i _ j _ hij => c.basis.injective hij
  rw [he] at hsum
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hsum

theorem omitted_coordinate (hN : R.negative = ∅) (i : Fin n) :
    c.basis.repr c.omitted i = if i ∈ c.fiberIndices then -1 else 0 := by
  rw [c.omitted_eq_negative_sum hN]
  by_cases hi : i ∈ c.fiberIndices <;>
    simp [map_sum, Module.Basis.repr_self_apply, Finsupp.single_apply, hi]

theorem quotient_omitted (hN : R.negative = ∅) : c.quotientLattice c.omitted = 0 := by
  rw [c.omitted_eq_negative_sum hN, map_neg, map_sum]
  have hz : (∑ i ∈ c.fiberIndices, c.quotientLattice (c.basis i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact coneQuotientLattice_of_mem c.basis c.fiberIndices
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  rw [hz, neg_zero]

theorem quotient_positive (hN : R.negative = ∅) {v : Lattice n}
    (hv : v ∈ R.positive) : c.quotientLattice v = 0 := by
  by_cases hvu : v = c.omitted
  · rw [hvu, c.quotient_omitted hN]
  · apply coneQuotientLattice_of_mem c.basis c.fiberIndices
    rw [c.fiber_ray_set]
    exact Finset.mem_erase.mpr ⟨hvu, hv⟩

theorem omitted_not_mem_over_fiber {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hF : c.fiberIndices.image c.basis ⊆ s) :
    c.omitted ∉ s := by
  intro hu
  apply R.primitive.2.1
  apply «Σ».downward s hs R.positive
  intro v hv
  by_cases hvu : v = c.omitted
  · simpa only [hvu] using hu
  · apply hF
    rw [c.fiber_ray_set]
    exact Finset.mem_erase.mpr ⟨hvu, hv⟩

theorem over_fiber_sdiff_eq {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hF : c.fiberIndices.image c.basis ⊆ s) :
    s \ c.fiberIndices.image c.basis = s \ R.positive := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvs, hvF⟩ := Finset.mem_sdiff.mp hv
    refine Finset.mem_sdiff.mpr ⟨hvs, ?_⟩
    intro hvP
    by_cases hvu : v = c.omitted
    · exact c.omitted_not_mem_over_fiber hs hF (hvu ▸ hvs)
    · apply hvF
      rw [c.fiber_ray_set]
      exact Finset.mem_erase.mpr ⟨hvu, hvP⟩
  · intro hv
    obtain ⟨hvs, hvP⟩ := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr ⟨hvs, fun hvF => hvP (c.fiber_subset_positive hvF)⟩

/-- Every base-ray cone combines with every proper projective-fiber cone. -/
theorem fill_nonfiber_cone (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {D : Finset (Lattice n)}
    (hD : D ∈ «Σ».cones) (hDP : Disjoint D R.positive) :
    c.fiberIndices.image c.basis ∪ D ∈ «Σ».cones := by
  rw [c.fiber_ray_set]
  exact R.fill_cone_with_positive_except hR hD
    (by rw [hN]; exact Finset.empty_subset _) c.omitted_mem
    (fun hu => Finset.disjoint_left.mp hDP hu c.omitted_mem)

theorem quotient_injective_nonfiber (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {v w : Lattice n}
    (hv : v ∈ «Σ».rays \ R.positive) (hw : w ∈ «Σ».rays \ R.positive)
    (he : c.quotientLattice v = c.quotientLattice w) : v = w := by
  have hvs := «Σ».singleton_mem_of_mem_rays (Finset.mem_sdiff.mp hv).1
  have hws := «Σ».singleton_mem_of_mem_rays (Finset.mem_sdiff.mp hw).1
  have hDv : Disjoint ({v} : Finset (Lattice n)) R.positive := by
    simpa only [Finset.disjoint_singleton_left] using (Finset.mem_sdiff.mp hv).2
  have hDw : Disjoint ({w} : Finset (Lattice n)) R.positive := by
    simpa only [Finset.disjoint_singleton_left] using (Finset.mem_sdiff.mp hw).2
  exact «Σ».coneQuotient_injective_star_rays c.basis c.fiberIndices
    (c.fill_nonfiber_cone hR hN hvs hDv) (c.fill_nonfiber_cone hR hN hws hDw)
    Finset.subset_union_left Finset.subset_union_left
    (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_singleton_self v),
      fun h => (Finset.mem_sdiff.mp hv).2 (c.fiber_subset_positive h)⟩)
    (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_singleton_self w),
      fun h => (Finset.mem_sdiff.mp hw).2 (c.fiber_subset_positive h)⟩) he

theorem union_fiber_sdiff {D : Finset (Lattice n)}
    (hDP : Disjoint D R.positive) :
    (c.fiberIndices.image c.basis ∪ D) \ c.fiberIndices.image c.basis = D := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvU, hvF⟩ := Finset.mem_sdiff.mp hv
    rcases Finset.mem_union.mp hvU with hvF' | hvD
    · exact (hvF hvF').elim
    · exact hvD
  · intro hvD
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hvD,
      fun hvF => Finset.disjoint_left.mp hDP hvD (c.fiber_subset_positive hvF)⟩

/-- The base cones are precisely the images of cones on nonfiber rays.
The reverse direction uses the proved uniqueness of actual ray lifts. -/
theorem nonfiber_cone_iff_projected_cone (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {D : Finset (Lattice n)}
    (hDrays : D ⊆ «Σ».rays) (hDP : Disjoint D R.positive) :
    D ∈ «Σ».cones ↔ D.image c.quotientLattice ∈
      «Σ».quotientStarCones c.basis c.fiberIndices := by
  constructor
  · intro hD
    apply («Σ».mem_quotientStarCones c.basis c.fiberIndices _).mpr
    refine ⟨c.fiberIndices.image c.basis ∪ D,
      c.fill_nonfiber_cone hR hN hD hDP, Finset.subset_union_left, ?_⟩
    rw [c.union_fiber_sdiff hDP]
  · intro hD
    obtain ⟨S, hS, hFS, he⟩ :=
      («Σ».mem_quotientStarCones c.basis c.fiberIndices _).mp hD
    have hDS : D = S \ c.fiberIndices.image c.basis := by
      ext v
      constructor
      · intro hv
        have himage : c.quotientLattice v ∈
            (S \ c.fiberIndices.image c.basis).image c.quotientLattice := by
          rw [← he]
          exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
        obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp himage
        have hwP : w ∉ R.positive := by
          rw [c.over_fiber_sdiff_eq hS hFS] at hw
          exact (Finset.mem_sdiff.mp hw).2
        have hvw := c.quotient_injective_nonfiber hR hN
          (Finset.mem_sdiff.mpr ⟨hDrays hv, fun hvP => Finset.disjoint_left.mp hDP hv hvP⟩)
          (Finset.mem_sdiff.mpr ⟨(«Σ».mem_rays_iff w).mpr
            ⟨S, hS, (Finset.mem_sdiff.mp hw).1⟩, hwP⟩) hwe.symm
        simpa only [hvw] using hw
      · intro hv
        have himage : c.quotientLattice v ∈ D.image c.quotientLattice := by
          rw [he]
          exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
        obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp himage
        have hvP : v ∉ R.positive := by
          rw [c.over_fiber_sdiff_eq hS hFS] at hv
          exact (Finset.mem_sdiff.mp hv).2
        have hvw := c.quotient_injective_nonfiber hR hN
          (Finset.mem_sdiff.mpr ⟨(«Σ».mem_rays_iff v).mpr
            ⟨S, hS, (Finset.mem_sdiff.mp hv).1⟩, hvP⟩)
          (Finset.mem_sdiff.mpr ⟨hDrays hw, fun hwP => Finset.disjoint_left.mp hDP hw hwP⟩)
          hwe.symm
        simpa only [hvw] using hw
    rw [hDS]
    exact «Σ».downward S hS _ Finset.sdiff_subset

end BundleCoordinates

/-- Literal projective-fiber/base cone product.  The condition `J≠P`
means exactly that `J` is a proper cone of the projective-space fan. -/
theorem cone_union_fiber_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {J D : Finset (Lattice n)}
    (hJP : J ⊆ R.positive) (hDP : Disjoint D R.positive) :
    J ∪ D ∈ «Σ».cones ↔ J ≠ R.positive ∧ D ∈ «Σ».cones := by
  constructor
  · intro hcone
    refine ⟨?_, «Σ».downward _ hcone D Finset.subset_union_right⟩
    intro he
    exact R.primitive.2.1
      («Σ».downward _ hcone R.positive (he ▸ Finset.subset_union_left))
  · rintro ⟨hJ, hD⟩
    have hnot : ¬ R.positive ⊆ J := fun h => hJ (Finset.Subset.antisymm hJP h)
    obtain ⟨u, hu, huJ⟩ := Finset.not_subset.mp hnot
    have huD : u ∉ D := fun hud => Finset.disjoint_left.mp hDP hud hu
    have hfill := R.fill_cone_with_positive_except hR hD
      (by rw [hN]; exact Finset.empty_subset _) hu huD
    apply «Σ».downward _ hfill (J ∪ D)
    apply Finset.union_subset_union_left
    intro v hv
    exact Finset.mem_erase.mpr ⟨fun he => huJ (he ▸ hv), hJP hv⟩

namespace BundleCoordinates

variable {R} (c : R.BundleCoordinates)

/-- Complete cone correspondence with the actual quotient fan. -/
theorem cone_iff_fiber_and_base (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {s : Finset (Lattice n)} (hsrays : s ⊆ «Σ».rays) :
    s ∈ «Σ».cones ↔ (s ∩ R.positive ≠ R.positive) ∧
      (s \ R.positive).image c.quotientLattice ∈
        «Σ».quotientStarCones c.basis c.fiberIndices := by
  have hpart : (s ∩ R.positive) ∪ (s \ R.positive) = s := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisjoint : Disjoint (s \ R.positive) R.positive := by
    exact Finset.disjoint_left.mpr (fun v hv hvP => (Finset.mem_sdiff.mp hv).2 hvP)
  rw [← c.nonfiber_cone_iff_projected_cone hR hN
    (Finset.sdiff_subset.trans hsrays) hdisjoint,
    ← R.cone_union_fiber_iff hR hN Finset.inter_subset_right hdisjoint, hpart]

theorem base_ray_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (q : Lattice (n - c.fiberIndices.card)) :
    q ∈ c.baseFan.rays ↔ ∃ v ∈ «Σ».rays \ R.positive, c.quotientLattice v = q := by
  constructor
  · intro hq
    obtain ⟨D, hD, hqD⟩ := (c.baseFan.mem_rays_iff q).mp hq
    obtain ⟨S, hS, hFS, rfl⟩ :=
      («Σ».mem_quotientStarCones c.basis c.fiberIndices D).mp hD
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hqD
    have hvP : v ∉ R.positive := by
      rw [c.over_fiber_sdiff_eq hS hFS] at hv
      exact (Finset.mem_sdiff.mp hv).2
    exact ⟨v, Finset.mem_sdiff.mpr ⟨(«Σ».mem_rays_iff v).mpr
      ⟨S, hS, (Finset.mem_sdiff.mp hv).1⟩, hvP⟩, he⟩
  · rintro ⟨v, hv, rfl⟩
    have hvcone := «Σ».singleton_mem_of_mem_rays (Finset.mem_sdiff.mp hv).1
    have hvdisj : Disjoint ({v} : Finset (Lattice n)) R.positive := by
      simpa only [Finset.disjoint_singleton_left] using (Finset.mem_sdiff.mp hv).2
    have hbasecone := (c.nonfiber_cone_iff_projected_cone hR hN
      (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hv).1) hvdisj).mp hvcone
    exact (c.baseFan.mem_rays_iff _).mpr
      ⟨({v} : Finset (Lattice n)).image c.quotientLattice, hbasecone,
        Finset.mem_image.mpr ⟨v, Finset.mem_singleton_self v, rfl⟩⟩

/-- Projection identifies nonfiber primitive rays with base primitive rays.
Primitivity in the quotient follows from the integral smooth quotient basis. -/
def baseRayEquiv (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅) :
    ↥(«Σ».rays \ R.positive) ≃ ↥c.baseFan.rays :=
  Equiv.ofBijective
    (fun v => ⟨c.quotientLattice v, (c.base_ray_iff hR hN _).mpr ⟨v, v.property, rfl⟩⟩)
    ⟨by
      intro v w he
      apply Subtype.ext
      exact c.quotient_injective_nonfiber hR hN v.property w.property
        (congrArg Subtype.val he), by
      intro q
      obtain ⟨v, hv, he⟩ := (c.base_ray_iff hR hN q).mp q.property
      exact ⟨⟨v, hv⟩, Subtype.ext he⟩⟩

@[simp] theorem baseRayEquiv_apply (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (v : ↥(«Σ».rays \ R.positive)) :
    (c.baseRayEquiv hR hN v : Lattice (n - c.fiberIndices.card)) =
      c.quotientLattice v := rfl

/-- The unique actual nonfiber ray above a base ray, extended by zero away
from the base fan's rays solely to obtain a total coefficient function. -/
def baseRayLift (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (q : Lattice (n - c.fiberIndices.card)) : Lattice n :=
  if hq : q ∈ c.baseFan.rays then
    ((c.baseRayEquiv hR hN).symm ⟨q, hq⟩ : Lattice n) else 0

theorem baseRayLift_mem (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    {q : Lattice (n - c.fiberIndices.card)} (hq : q ∈ c.baseFan.rays) :
    c.baseRayLift hR hN q ∈ «Σ».rays \ R.positive := by
  simp only [baseRayLift, dif_pos hq]
  exact ((c.baseRayEquiv hR hN).symm ⟨q, hq⟩).property

theorem quotient_baseRayLift (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    {q : Lattice (n - c.fiberIndices.card)} (hq : q ∈ c.baseFan.rays) :
    c.quotientLattice (c.baseRayLift hR hN q) = q := by
  simp only [baseRayLift, dif_pos hq]
  have h := congrArg Subtype.val ((c.baseRayEquiv hR hN).apply_symm_apply ⟨q, hq⟩)
  exact h

theorem baseRayLift_quotient (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    {v : Lattice n} (hv : v ∈ «Σ».rays \ R.positive) :
    c.baseRayLift hR hN (c.quotientLattice v) = v := by
  have hq := (c.base_ray_iff hR hN _).mpr ⟨v, hv, rfl⟩
  apply c.quotient_injective_nonfiber hR hN (c.baseRayLift_mem hR hN hq) hv
  exact c.quotient_baseRayLift hR hN hq

end BundleCoordinates

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
