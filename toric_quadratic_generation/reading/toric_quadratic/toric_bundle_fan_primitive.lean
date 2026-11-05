module

public import PaperVerification.ToricBundleFan


@[expose] public section
/-!
# Other primitive collections in a projective bundle fan

The exact fiber/base cone correspondence forces every primitive collection
other than the fiber simplex to be disjoint from that simplex.  Projection
therefore bounds its cardinality by the base dimension plus one.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation

open scoped BigOperators Classical

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

theorem other_primitive_disjoint_fiber (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {S : Finset (Lattice n)}
    (hS : «Σ».IsPrimitiveCollection S) (hne : S ≠ R.positive) :
    Disjoint S R.positive := by
  have hPnot : ¬ R.positive ⊆ S := by
    intro hPS
    have hproper : R.positive ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hPS, Ne.symm hne⟩
    exact R.primitive.2.1 (hS.2.2 R.positive hproper)
  have hJ : S ∩ R.positive ≠ R.positive := by
    intro he
    exact hPnot (he ▸ Finset.inter_subset_left)
  have hdisj : Disjoint (S \ R.positive) R.positive :=
    Finset.disjoint_left.mpr (fun v hv hvP => (Finset.mem_sdiff.mp hv).2 hvP)
  by_contra hnot
  have hproper : S \ R.positive ⊂ S := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
    intro he
    exact hnot (he ▸ hdisj)
  have hD := hS.2.2 (S \ R.positive) hproper
  have hcone := (R.cone_union_fiber_iff hR hN Finset.inter_subset_right hdisj).mpr
    ⟨hJ, hD⟩
  have hpart : (S ∩ R.positive) ∪ (S \ R.positive) = S := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  exact hS.2.1 (hpart ▸ hcone)

namespace BundleCoordinates

variable {R} (c : R.BundleCoordinates)

theorem other_primitive_card_le (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {S : Finset (Lattice n)}
    (hS : «Σ».IsPrimitiveCollection S) (hne : S ≠ R.positive) :
    S.card ≤ (n - c.fiberIndices.card) + 1 := by
  have hdisj := R.other_primitive_disjoint_fiber hR hN hS hne
  obtain ⟨v, hv⟩ := «Σ».primitiveCollection_nonempty hS
  have hproper : S.erase v ⊂ S := Finset.erase_ssubset hv
  have hcone := hS.2.2 (S.erase v) hproper
  have hdrays : S.erase v ⊆ «Σ».rays := (Finset.erase_subset v S).trans hS.1
  have hdP : Disjoint (S.erase v) R.positive := hdisj.mono_left (Finset.erase_subset v S)
  have hbase := (c.nonfiber_cone_iff_projected_cone hR hN hdrays hdP).mp hcone
  have hsize := c.baseFan.card_cone_le hbase
  have hinj : Set.InjOn c.quotientLattice (S.erase v : Set (Lattice n)) := by
    intro x hx y hy hxy
    exact c.quotient_injective_nonfiber hR hN
      (Finset.mem_sdiff.mpr ⟨hdrays hx, fun hxP => Finset.disjoint_left.mp hdP hx hxP⟩)
      (Finset.mem_sdiff.mpr ⟨hdrays hy, fun hyP => Finset.disjoint_left.mp hdP hy hyP⟩) hxy
  rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hv] at hsize
  have hnonempty : 0 < S.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

end BundleCoordinates

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation
