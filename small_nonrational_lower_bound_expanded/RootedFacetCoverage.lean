module

public import FacePlacementGeometry

@[expose] public section

/-!
# Complete rooted-universe coverage from compressed literal certificates

The finite obligations concern normalized pairs of proper faces and the
reduced placement codes. Compatibility is tested as equality of edge sets,
so relabeling need not preserve the literal order of a template's edges.
-/

noncomputable section
namespace Papers.RationalityTen.RootedFacetCoverage

open Finset Set
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport
open LiteralMaskGeometry RawFacetEmbeddingSemantics
open FacePlacementCodes FacePlacementGeometry

structure Bounds (C : ConcreteGrowth.Cell) : Prop where
  vertices : C.vertices < 1024
  edges : ∀ e ∈ C.edges, e < 1024
  ridges : ∀ q ∈ C.ridgeMasks, q < 1024

theorem bounds_of_wellFormed (C : ConcreteGrowth.Cell) (h : WellFormed C) : Bounds C :=
  ⟨h.vertices_bound, h.edges_bound, h.ridges_bound⟩

theorem mapMask_bound (m : Nat) (f : Nat → Nat) (hf : ∀ i, i < m → f i < 10)
    (mask : Nat) : RawFacetEmbedding.mapMask m f mask < 1024 := by
  change RawFacetEmbedding.mapMask m f mask < 2 ^ 10
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  cases hbit : (RawFacetEmbedding.mapMask m f mask).testBit i with
  | false => rfl
  | true =>
    obtain ⟨j, hj, _, hji⟩ := (RawFacetEmbedding.mapMask_bit m f mask i).mp hbit
    have := hf j hj
    omega

theorem mapCell_bounds (m : Nat) (f : Nat → Nat) (hf : ∀ i, i < m → f i < 10)
    (C : ConcreteGrowth.Cell) : Bounds (RawFacetEmbedding.mapCell m f C) := by
  refine ⟨mapMask_bound m f hf _, ?_, ?_⟩
  · intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
    exact mapMask_bound m f hf a
  · intro q hq
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hq
    exact mapMask_bound m f hf a

theorem proper_of_face (C : ConcreteGrowth.Cell) (hC : Bounds C)
    {m : Nat} (hm : m < 1024) (h : maskSet m ∈ (decodeCell C).properFaces) :
    ConcreteGrowth.proper C m = true := by
  simp only [Cell.properFaces, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_image, decodeCell] at h
  simp only [ConcreteGrowth.proper, Bool.or_eq_true, decide_eq_true_eq]
  rcases h with ((hempty | hsingle) | hedge) | hridge
  · apply Or.inl; apply Or.inl
    apply (small_mask_iff ⟨m, hm⟩).mpr
    rw [hempty]
    decide
  · obtain ⟨v, _, hv⟩ := hsingle
    apply Or.inl; apply Or.inl
    apply (small_mask_iff ⟨m, hm⟩).mpr
    simpa only [← hv, Finset.card_singleton] using (Nat.le_refl 1)
  · apply Or.inl; apply Or.inr
    apply (hasMask_true _ _).mpr
    apply (mask_mem_image_iff C.edges hC.edges hm).mp
    exact Finset.mem_image.mpr hedge
  · apply Or.inr
    apply (hasMask_true _ _).mpr
    apply (mask_mem_image_iff C.ridgeMasks hC.ridges hm).mp
    exact Finset.mem_image.mpr hridge

/-- Genuine compatibility passes the order-independent raw test. -/
theorem compatible_of_geometry (A B : ConcreteGrowth.Cell) (hA : Bounds A) (hB : Bounds B)
    (h : (decodeCell A).Compatible (decodeCell B)) : RawFacePlacement.compatible A B = true := by
  let common := Nat.land A.vertices B.vertices
  have hc : common < 1024 := Nat.lt_of_le_of_lt Nat.and_le_left hA.vertices
  have heq : maskSet common = (decodeCell A).vertices ∩ (decodeCell B).vertices :=
    maskSet_inter _ _
  have hpA := proper_of_face A hA hc (heq.symm ▸ h.1)
  have hpB := proper_of_face B hB hc (heq.symm ▸ h.2.1)
  have hedges : ∀ e,
      e ∈ A.edges.filter (fun e => decide (Nat.land e common = e)) ↔
        e ∈ B.edges.filter (fun e => decide (Nat.land e common = e)) := by
    intro e
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨heA, hec⟩
      have hsub : maskSet e ⊆ (decodeCell A).vertices ∩ (decodeCell B).vertices := by
        rw [← heq]
        exact (maskSet_subset_iff (hA.edges e heA)).mpr hec
      have hegeom := (h.2.2 (maskSet e) hsub).mp
        ((mask_mem_image_iff A.edges hA.edges (hA.edges e heA)).mpr heA)
      exact ⟨(mask_mem_image_iff B.edges hB.edges (hA.edges e heA)).mp hegeom, hec⟩
    · rintro ⟨heB, hec⟩
      have hsub : maskSet e ⊆ (decodeCell A).vertices ∩ (decodeCell B).vertices := by
        rw [← heq]
        exact (maskSet_subset_iff (hB.edges e heB)).mpr hec
      have hegeom := (h.2.2 (maskSet e) hsub).mpr
        ((mask_mem_image_iff B.edges hB.edges (hB.edges e heB)).mpr heB)
      exact ⟨(mask_mem_image_iff A.edges hA.edges (hB.edges e heB)).mp hegeom, hec⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨hpA, hpB⟩,
      (RawFacetEmbedding.sameMembers_iff _ _).mpr hedges⟩

structure Representation {m : Nat} (B : Block m) (raw : RawFacePlacement.Block) : Prop where
  shared : raw.shared = B.shared
  outside : raw.outside = B.outside
  source_inverse : ∀ i : Fin m,
    RawFacePlacement.digit raw.sourceInverse i.val = (B.source.symm i).val
  target_forward : ∀ i : Fin 10,
    RawFacePlacement.digit raw.targetForward i.val = (B.target i).val

theorem label_eq_decoded {m : Nat} (B : Block m) (raw : RawFacePlacement.Block)
    (H : Representation B raw) (inner outer : Nat) (i : Fin m) :
    RawFacePlacement.label m raw inner outer i.val = (B.decoded inner outer i).val := by
  unfold RawFacePlacement.label Block.decoded
  rw [H.source_inverse, H.shared, H.outside]
  dsimp only
  by_cases h : (B.source.symm i).val < B.shared
  · rw [if_pos h, dif_pos h]
    rw [decode_eq_fin (Nat.le_refl B.shared) inner ⟨(B.source.symm i).val, h⟩]
    exact H.target_forward
      ⟨(FiniteCycleCandidates.decodeInjection B.shared B.shared (Nat.le_refl _) inner
        ⟨(B.source.symm i).val, h⟩).val,
        lt_of_lt_of_le (Fin.isLt _)
          ((Nat.le_add_right B.shared B.outside).trans B.target_le)⟩
  · rw [if_neg h, dif_neg h]
    have hi : (B.source.symm i).val - B.shared < m - B.shared := by
      have := (B.source.symm i).isLt
      omega
    rw [decode_eq_fin B.remaining_le outer ⟨(B.source.symm i).val - B.shared, hi⟩]
    exact H.target_forward
      ⟨B.shared + (FiniteCycleCandidates.decodeInjection B.outside (m - B.shared)
        B.remaining_le outer ⟨(B.source.symm i).val - B.shared, hi⟩).val,
        lt_of_lt_of_le (Nat.add_lt_add_left (Fin.isLt _) _) B.target_le⟩

theorem check_of_interval {m n : Nat} (raw : RawFacePlacement.Block)
    (template root : ConcreteGrowth.Cell) (cells : Fin n → ConcreteGrowth.Cell)
    (witness : Nat → Fin n)
    (h : FiniteChecks.Interval (RawFacePlacement.intervalCheck m raw template root cells witness)
      0 (RawFacePlacement.count raw.shared raw.shared *
        RawFacePlacement.count raw.outside (m - raw.shared)))
    (inner outer : Nat) (hi : inner < RawFacePlacement.count raw.shared raw.shared)
    (ho : outer < RawFacePlacement.count raw.outside (m - raw.shared)) :
    RawFacePlacement.check m raw template root cells inner outer
      (witness (outer + RawFacePlacement.count raw.outside (m - raw.shared) * inner)) = true := by
  let width := RawFacePlacement.count raw.outside (m - raw.shared)
  have hwidth : 0 < width := Nat.zero_lt_of_lt ho
  have hcode : outer + width * inner <
      RawFacePlacement.count raw.shared raw.shared * width := by
    calc
      _ < width + width * inner := Nat.add_lt_add_right ho _
      _ = (inner + 1) * width := by
        simp only [Nat.add_mul, Nat.one_mul, Nat.mul_comm, Nat.add_comm]
      _ ≤ _ := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hi)
  have hc := h (outer + width * inner) (Nat.zero_le _) hcode
  simpa only [RawFacePlacement.intervalCheck, width,
    Nat.add_mul_div_left _ _ hwidth, Nat.div_eq_of_lt ho, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ho] using hc

/-- The endpoint covers every compatible injection of the full local
template. All finite checks may be split into independent Boolean intervals. -/
theorem covers_of_checks {m b n : Nat} (template root : ConcreteGrowth.Cell)
    (C : Cell m) (htemplate : decodeTemplate m template = C)
    (hvertices : C.vertices = Finset.univ) (hroot : WellFormed root)
    (cells : Fin n → ConcreteGrowth.Cell) (blocks : Fin b → Block m)
    (raw : Fin b → RawFacePlacement.Block)
    (H : ∀ i, Representation (blocks i) (raw i))
    (hblocks : CompleteBlocks C (decodeCell root) blocks)
    (witness : Fin b → Nat → Fin n)
    (hchecks : ∀ i, FiniteChecks.Interval
      (RawFacePlacement.intervalCheck m (raw i) template root cells (witness i))
      0 (RawFacePlacement.count (raw i).shared (raw i).shared *
        RawFacePlacement.count (raw i).outside (m - (raw i).shared))) :
    ∀ f : Fin m ↪ Fin 10, (mapCell f C).Compatible (decodeCell root) →
      ∃ j, decodeCell (cells j) = mapCell f C := by
  intro f hf
  obtain ⟨i, inner, hi, outer, ho, hdecode⟩ :=
    exists_block_and_codes C (decodeCell root) hvertices blocks hblocks f hf
  have hfg (j : Fin m) : RawFacePlacement.label m (raw i) inner outer j.val = (f j).val := by
    rw [label_eq_decoded _ _ (H i), hdecode]
  let placed := RawFacetEmbedding.mapCell m (RawFacePlacement.label m (raw i) inner outer) template
  have hplaced : decodeCell placed = mapCell f C := by
    rw [decode_mapCell _ f hfg template, htemplate]
    rfl
  have hbound : Bounds placed := mapCell_bounds m _ (fun j hj => by
    rw [hfg ⟨j, hj⟩]
    exact (f ⟨j, hj⟩).isLt) template
  have hc : RawFacePlacement.compatible placed root = true :=
    compatible_of_geometry placed root hbound (bounds_of_wellFormed root hroot)
      (hplaced.symm ▸ hf)
  have hi' : inner < RawFacePlacement.count (raw i).shared (raw i).shared := by
    simpa only [(H i).shared, count_eq] using hi
  have ho' : outer < RawFacePlacement.count (raw i).outside (m - (raw i).shared) := by
    simpa only [(H i).shared, (H i).outside, count_eq] using ho
  have hcheck := check_of_interval (raw i) template root cells (witness i)
    (hchecks i) inner outer hi' ho'
  unfold RawFacePlacement.check at hcheck
  change (!RawFacePlacement.compatible placed root || _) = true at hcheck
  rw [hc, Bool.not_true, Bool.false_or] at hcheck
  exact ⟨_, (sameGeometry_decoded hcheck).trans hplaced⟩

end Papers.RationalityTen.RootedFacetCoverage
