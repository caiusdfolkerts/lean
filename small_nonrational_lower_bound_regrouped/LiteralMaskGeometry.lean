module

public import CellRelabelGeometry
public import ConcreteGrowth
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Sort

@[expose] public section

/-!
# Exact semantics of the ten-label bit masks

Literal masks are decoded to ordinary finite vertex sets. Bounds ensure
that decoding loses no high bits. Strictly sorted edge lists ensure that
the executable list-equality test is exactly equality of induced edges.
These are small, checkable data invariants, not assumptions on a polytope.
-/

namespace Papers.RationalityTen.LiteralMaskGeometry

open Finset Set
open MatroidChecked.FacetBoundaryEncoding
open GrowthDAG SparseGrowthDAG GrowthPruning

/-- The subset of the ten vertex labels represented by an integer mask. -/
def maskSet (m : ℕ) : Finset (Fin 10) := Finset.univ.filter fun i => m.testBit i.val = true

@[simp] theorem mem_maskSet (m : ℕ) (i : Fin 10) :
    i ∈ maskSet m ↔ m.testBit i.val = true := by
  simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem maskSet_inter (a b : ℕ) :
    maskSet (Nat.land a b) = maskSet a ∩ maskSet b := by
  ext i
  simp only [mem_maskSet, Finset.mem_inter]
  change (a &&& b).testBit i.val = true ↔
    a.testBit i.val = true ∧ b.testBit i.val = true
  rw [Nat.testBit_and, Bool.and_eq_true]

/-- A bounded mask is determined by precisely the ten decoded bits. -/
theorem maskSet_injective {a b : ℕ} (ha : a < 1024) (hb : b < 1024)
    (h : maskSet a = maskSet b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10
  · apply Bool.eq_iff_iff.mpr
    change a.testBit (⟨i, hi⟩ : Fin 10).val = true ↔
      b.testBit (⟨i, hi⟩ : Fin 10).val = true
    rw [← mem_maskSet, ← mem_maskSet, h]
  · have hpow : 1024 ≤ 2 ^ i := by
      change 2 ^ 10 ≤ 2 ^ i
      exact Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hpow),
      Nat.testBit_lt_two_pow (hb.trans_le hpow)]

noncomputable def maskEquiv : Fin 1024 ≃ Finset (Fin 10) :=
  Equiv.ofBijective (fun m => maskSet m.val)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun a b h =>
      Fin.ext (maskSet_injective a.isLt b.isLt h), by
        simpa only [Fintype.card_fin, Fintype.card_finset] using
          (show 1024 = 2 ^ 10 by decide)⟩)

@[simp] theorem maskEquiv_apply (m : Fin 1024) : maskEquiv m = maskSet m.val := rfl

theorem maskSet_subset_iff {a b : ℕ} (ha : a < 1024) :
    maskSet a ⊆ maskSet b ↔ Nat.land a b = a := by
  constructor
  · intro h
    apply maskSet_injective (Nat.lt_of_le_of_lt Nat.and_le_left ha) ha
    change maskSet (Nat.land a b) = maskSet a
    rw [maskSet_inter, Finset.inter_eq_left.mpr h]
  · intro h
    have heq := congrArg maskSet h
    rw [maskSet_inter] at heq
    exact Finset.inter_eq_left.mp heq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The executable small-mask test means empty or one vertex. The lemma
checks all 1,024 possible masks, independently of any cell universe. -/
theorem small_mask_iff : ∀ m : Fin 1024,
    Nat.land m.val (m.val - 1) = 0 ↔ (maskSet m.val).card ≤ 1 := by
  decide +kernel

/-- Decode every face record, retaining full edge and ridge information. -/
def decodeCell (C : ConcreteGrowth.Cell) : Cell 10 where
  vertices := maskSet C.vertices
  edges := C.edges.toFinset.image maskSet
  ridges := C.ridgeMasks.toFinset.image maskSet

/-- The finite producer's records are checked for lossless decoding and
canonical edge-list order. -/
structure WellFormed (C : ConcreteGrowth.Cell) : Prop where
  vertices_bound : C.vertices < 1024
  edges_bound : ∀ e ∈ C.edges, e < 1024
  ridges_bound : ∀ q ∈ C.ridgeMasks, q < 1024
  edges_sorted : C.edges.Pairwise (· < ·)

instance (C : ConcreteGrowth.Cell) : Decidable (WellFormed C) :=
  decidable_of_iff (C.vertices < 1024 ∧ (∀ e ∈ C.edges, e < 1024) ∧
    (∀ q ∈ C.ridgeMasks, q < 1024) ∧ C.edges.Pairwise (· < ·))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
      fun h => ⟨h.vertices_bound, h.edges_bound, h.ridges_bound, h.edges_sorted⟩⟩

@[simp] theorem hasMask_true (L : List ℕ) (m : ℕ) :
    ConcreteGrowth.hasMask L m = true ↔ m ∈ L := by
  simp only [ConcreteGrowth.hasMask, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hm
    exact ⟨m, hm, rfl⟩

/-- Mask equality in a bounded literal face list is equivalent to equality
of the represented vertex sets. -/
theorem mask_mem_image_iff (L : List ℕ) (hL : ∀ e ∈ L, e < 1024)
    {m : ℕ} (hm : m < 1024) :
    maskSet m ∈ L.toFinset.image maskSet ↔ m ∈ L := by
  constructor
  · intro h
    obtain ⟨a, ha, ham⟩ := Finset.mem_image.mp h
    have haL := List.mem_toFinset.mp ha
    exact (maskSet_injective (hL a haL) hm ham) ▸ haL
  · intro h
    exact Finset.mem_image.mpr ⟨m, List.mem_toFinset.mpr h, rfl⟩

theorem proper_of_mem_properFaces (C : ConcreteGrowth.Cell) (hC : WellFormed C)
    {m : ℕ} (hm : m < 1024) (h : maskSet m ∈ (decodeCell C).properFaces) :
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
    apply (mask_mem_image_iff C.edges hC.edges_bound hm).mp
    exact Finset.mem_image.mpr hedge
  · apply Or.inr
    apply (hasMask_true _ _).mpr
    apply (mask_mem_image_iff C.ridgeMasks hC.ridges_bound hm).mp
    exact Finset.mem_image.mpr hridge

/-- Actual compatible cells pass the exact literal compatibility test.
In particular, shared polygon masks cannot hide conflicting edge cycles. -/
theorem literal_compatible_of_compatible (A B : ConcreteGrowth.Cell)
    (hA : WellFormed A) (hB : WellFormed B)
    (h : (decodeCell A).Compatible (decodeCell B)) :
    ConcreteGrowth.compatible A B = true := by
  let common := Nat.land A.vertices B.vertices
  have hcommon : common < 1024 :=
    Nat.lt_of_le_of_lt Nat.and_le_left hA.vertices_bound
  have heq : maskSet common = (decodeCell A).vertices ∩ (decodeCell B).vertices :=
    maskSet_inter _ _
  have hpA : ConcreteGrowth.proper A common = true :=
    proper_of_mem_properFaces A hA hcommon (heq.symm ▸ h.1)
  have hpB : ConcreteGrowth.proper B common = true :=
    proper_of_mem_properFaces B hB hcommon (heq.symm ▸ h.2.1)
  have hedge : (A.edges.filter fun e => decide (Nat.land e common = e)) =
      (B.edges.filter fun e => decide (Nat.land e common = e)) := by
    apply List.Pairwise.eq_of_mem_iff (hA.edges_sorted.filter _)
      (hB.edges_sorted.filter _)
    intro e
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨heA, hecommon⟩
      have hsub : maskSet e ⊆ (decodeCell A).vertices ∩ (decodeCell B).vertices := by
        rw [← heq]
        exact (maskSet_subset_iff (hA.edges_bound e heA)).mpr hecommon
      have hegeomA : maskSet e ∈ (decodeCell A).edges :=
        (mask_mem_image_iff A.edges hA.edges_bound (hA.edges_bound e heA)).mpr heA
      have hegeomB := (h.2.2 (maskSet e) hsub).mp hegeomA
      exact ⟨(mask_mem_image_iff B.edges hB.edges_bound (hA.edges_bound e heA)).mp hegeomB,
        hecommon⟩
    · rintro ⟨heB, hecommon⟩
      have hsub : maskSet e ⊆ (decodeCell A).vertices ∩ (decodeCell B).vertices := by
        rw [← heq]
        exact (maskSet_subset_iff (hB.edges_bound e heB)).mpr hecommon
      have hegeomB : maskSet e ∈ (decodeCell B).edges :=
        (mask_mem_image_iff B.edges hB.edges_bound (hB.edges_bound e heB)).mpr heB
      have hegeomA := (h.2.2 (maskSet e) hsub).mpr hegeomB
      exact ⟨(mask_mem_image_iff A.edges hA.edges_bound (hB.edges_bound e heB)).mp hegeomA,
        hecommon⟩
  simp only [ConcreteGrowth.compatible, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hpA, hpB⟩, hedge⟩

theorem ridge_list_semantics {c : ℕ} (cells : Fin c → ConcreteGrowth.Cell)
    (hcell : ∀ a, WellFormed (cells a)) (a : Fin c) (q : Fin 1024) :
    has (ConcreteGrowth.ridgeList cells a) q = true ↔
      maskSet q.val ∈ (decodeCell (cells a)).ridges := by
  rw [has_true]
  change q ∈ (cells a).ridgeMasks.map (Fin.ofNat 1024) ↔
    maskSet q.val ∈ (cells a).ridgeMasks.toFinset.image maskSet
  rw [mask_mem_image_iff (cells a).ridgeMasks (hcell a).ridges_bound q.isLt]
  constructor
  · intro h
    obtain ⟨m, hm, hmq⟩ := List.mem_map.mp h
    have hval := congrArg (fun q : Fin 1024 => q.val) hmq
    change m % 1024 = q.val at hval
    rw [Nat.mod_eq_of_lt ((hcell a).ridges_bound m hm)] at hval
    exact hval ▸ hm
  · intro h
    refine List.mem_map.mpr ⟨q.val, h, ?_⟩
    apply Fin.ext
    exact Nat.mod_eq_of_lt q.isLt

/-- The converse proper-face implication uses that the common mask is
contained in the cell's vertices, as every intersection is. -/
theorem mem_properFaces_of_proper (C : ConcreteGrowth.Cell) (hC : WellFormed C)
    {m : ℕ} (hm : m < 1024) (hsub : maskSet m ⊆ (decodeCell C).vertices)
    (h : ConcreteGrowth.proper C m = true) :
    maskSet m ∈ (decodeCell C).properFaces := by
  simp only [ConcreteGrowth.proper, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [Cell.properFaces, Finset.mem_union, Finset.mem_singleton]
  rcases h with (hsmall | hedge) | hridge
  · have hcard := (small_mask_iff ⟨m, hm⟩).mp hsmall
    change (maskSet m).card ≤ 1 at hcard
    by_cases hz : (maskSet m).card = 0
    · exact Or.inl (Or.inl (Or.inl (Finset.card_eq_zero.mp hz)))
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (by omega : (maskSet m).card = 1)
      have hvm : v ∈ maskSet m := by rw [hv]; exact Finset.mem_singleton_self v
      exact Or.inl (Or.inl (Or.inr (Finset.mem_image.mpr ⟨v, hsub hvm, hv.symm⟩)))
  · apply Or.inl; apply Or.inr
    exact (mask_mem_image_iff C.edges hC.edges_bound hm).mpr ((hasMask_true _ _).mp hedge)
  · apply Or.inr
    exact (mask_mem_image_iff C.ridgeMasks hC.ridges_bound hm).mpr ((hasMask_true _ _).mp hridge)

/-- Literal compatibility has exactly the complete finite-set meaning. -/
theorem compatible_of_literal_compatible (A B : ConcreteGrowth.Cell)
    (hA : WellFormed A) (hB : WellFormed B)
    (h : ConcreteGrowth.compatible A B = true) :
    (decodeCell A).Compatible (decodeCell B) := by
  let common := Nat.land A.vertices B.vertices
  have hcommon : common < 1024 :=
    Nat.lt_of_le_of_lt Nat.and_le_left hA.vertices_bound
  have heq : maskSet common = (decodeCell A).vertices ∩ (decodeCell B).vertices :=
    maskSet_inter _ _
  obtain ⟨⟨hpA, hpB⟩, hedge⟩ :=
    (show (ConcreteGrowth.proper A common = true ∧ ConcreteGrowth.proper B common = true) ∧
      (A.edges.filter fun e => decide (Nat.land e common = e)) =
        (B.edges.filter fun e => decide (Nat.land e common = e)) from by
          simpa only [ConcreteGrowth.compatible, Bool.and_eq_true, decide_eq_true_eq] using h)
  refine ⟨?_, ?_, ?_⟩
  · rw [← heq]
    exact mem_properFaces_of_proper A hA hcommon
      (by rw [heq]; exact Finset.inter_subset_left) hpA
  · rw [← heq]
    exact mem_properFaces_of_proper B hB hcommon
      (by rw [heq]; exact Finset.inter_subset_right) hpB
  · intro e hesub
    let q := maskEquiv.symm e
    have hq : maskSet q.val = e := maskEquiv.apply_symm_apply e
    have hland : Nat.land q.val common = q.val := by
      apply (maskSet_subset_iff q.isLt).mp
      rw [hq, heq]
      exact hesub
    rw [← hq]
    change maskSet q.val ∈ A.edges.toFinset.image maskSet ↔
      maskSet q.val ∈ B.edges.toFinset.image maskSet
    rw [mask_mem_image_iff A.edges hA.edges_bound q.isLt,
      mask_mem_image_iff B.edges hB.edges_bound q.isLt]
    constructor
    · intro hAq
      have hqmem : q.val ∈ A.edges.filter (fun e => decide (Nat.land e common = e)) :=
        List.mem_filter.mpr ⟨hAq, decide_eq_true hland⟩
      rw [hedge] at hqmem
      exact (List.mem_filter.mp hqmem).1
    · intro hBq
      have hqmem : q.val ∈ B.edges.filter (fun e => decide (Nat.land e common = e)) :=
        List.mem_filter.mpr ⟨hBq, decide_eq_true hland⟩
      rw [← hedge] at hqmem
      exact (List.mem_filter.mp hqmem).1

theorem literal_compatible_iff (A B : ConcreteGrowth.Cell)
    (hA : WellFormed A) (hB : WellFormed B) :
    ConcreteGrowth.compatible A B = true ↔ (decodeCell A).Compatible (decodeCell B) :=
  ⟨compatible_of_literal_compatible A B hA hB,
    literal_compatible_of_compatible A B hA hB⟩

/-- A checked exact cell-map witness proves invariance of the literal
compatibility function for all pairs, without a pairwise truth table. -/
theorem literal_compatibility_relabel {c : ℕ}
    (cells : Fin c → ConcreteGrowth.Cell) (hcell : ∀ a, WellFormed (cells a))
    (σ : Equiv.Perm (Fin 10)) (cellMap : Fin c → Fin c)
    (hmap : ∀ a, decodeCell (cells (cellMap a)) =
      ActualFacetCatalogueTransport.mapCell σ.toEmbedding (decodeCell (cells a)))
    (a b : Fin c) :
    ConcreteGrowth.compatible (cells (cellMap a)) (cells (cellMap b)) =
      ConcreteGrowth.compatible (cells a) (cells b) := by
  apply Bool.eq_iff_iff.mpr
  rw [literal_compatible_iff _ _ (hcell _) (hcell _),
    literal_compatible_iff _ _ (hcell _) (hcell _), hmap a, hmap b,
    CellRelabelGeometry.compatible_mapCell_iff]

/-- The same vertex relabeling preserves every literal ridge incidence. -/
theorem literal_ridges_relabel {c : ℕ}
    (cells : Fin c → ConcreteGrowth.Cell) (hcell : ∀ a, WellFormed (cells a))
    (σ : Equiv.Perm (Fin 10)) (cellMap : Fin c → Fin c) (ridgeMap : Fin 1024 → Fin 1024)
    (hmap : ∀ a, decodeCell (cells (cellMap a)) =
      ActualFacetCatalogueTransport.mapCell σ.toEmbedding (decodeCell (cells a)))
    (hridge : ∀ q, maskSet (ridgeMap q).val = (maskSet q.val).image σ)
    (a : Fin c) (q : Fin 1024) :
    has (ConcreteGrowth.ridgeList cells (cellMap a)) (ridgeMap q) =
      has (ConcreteGrowth.ridgeList cells a) q := by
  apply Bool.eq_iff_iff.mpr
  rw [ridge_list_semantics cells hcell, ridge_list_semantics cells hcell,
    hmap, hridge]
  change (maskSet q.val).image σ ∈ (decodeCell (cells a)).ridges.image
    (fun R => R.image σ) ↔ maskSet q.val ∈ (decodeCell (cells a)).ridges
  exact CellRelabelGeometry.mem_image_family_iff σ _ _

end Papers.RationalityTen.LiteralMaskGeometry
