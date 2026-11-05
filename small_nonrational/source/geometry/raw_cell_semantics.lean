module

public import LiteralMaskGeometry
public import FiniteInjectionCodes
public import Mathlib.Data.Finset.Sort
public import RawFacetEmbedding
public import RawSmallCellMetadata

/-!
# Exact raw-cell semantics

This canonical module contains the complete five-stage semantic bridge.
The former stage module names remain public import aliases. Each source
stage retains its original scopes and declarations, with explicit EOF
closures; no proof body has been omitted or changed by this refactor.
-/

section BundlePart0
/- Source: LiteralCellEncoding.lean -/






@[expose] public section

/-!
# Computable exact encoding of complete facet templates

The encoder is defined by bitwise union and canonical sorted lists. Its
decoding theorem preserves the whole vertex, edge, and ridge families. This
lets a finite certificate enumerate injections of a local template, while
the mathematical coverage theorem quantifies over every injective labeling.
-/

namespace Papers.RationalityTen.LiteralCellEncoding

open Finset
open MatroidChecked.FacetBoundaryEncoding
open ActualFacetCatalogueTransport LiteralMaskGeometry
open FiniteCycleCandidates

/-- Bitwise union avoids any dependence on duplicate-freeness in the input. -/
def encodeList : List (Fin 10) → ℕ
  | [] => 0
  | v :: vs => Nat.lor (2 ^ v.val) (encodeList vs)

theorem encodeList_lt (vs : List (Fin 10)) : encodeList vs < 1024 := by
  induction vs with
  | nil => decide
  | cons v vs ih =>
    apply Nat.or_lt_two_pow (n := 10) _ ih
    exact Nat.pow_lt_pow_right (by decide) v.isLt

theorem testBit_encodeList (vs : List (Fin 10)) (v : Fin 10) :
    (encodeList vs).testBit v.val = true ↔ v ∈ vs := by
  induction vs with
  | nil => simp [encodeList]
  | cons w ws ih =>
    change ((2 ^ w.val ||| encodeList ws).testBit v.val = true) ↔ v ∈ w :: ws
    simp only [Nat.testBit_or, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr ⟨fun h => Fin.ext h.symm, fun h => congrArg Fin.val h.symm⟩ Iff.rfl

def encodeSet (S : Finset (Fin 10)) : ℕ := encodeList S.sort

theorem encodeSet_lt (S : Finset (Fin 10)) : encodeSet S < 1024 :=
  encodeList_lt _

@[simp] theorem maskSet_encodeSet (S : Finset (Fin 10)) :
    maskSet (encodeSet S) = S := by
  ext v
  simp only [mem_maskSet, encodeSet, testBit_encodeList, Finset.mem_sort]

theorem encodeSet_injective : Function.Injective encodeSet := by
  intro S T h
  simpa only [maskSet_encodeSet] using congrArg maskSet h

/-- A canonical literal record for an arbitrary complete finite cell. The
kind tag is deliberately separate from its geometric data. -/
def encodeCell (C : Cell 10) : ConcreteGrowth.Cell where
  kind := 0
  vertices := encodeSet C.vertices
  edges := (C.edges.image encodeSet).sort
  ridgeMasks := (C.ridges.image encodeSet).sort

theorem encodeCell_wellFormed (C : Cell 10) : WellFormed (encodeCell C) := by
  refine ⟨encodeSet_lt _, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp ((Finset.mem_sort _).mp he)
    exact encodeSet_lt _
  · intro e he
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp ((Finset.mem_sort _).mp he)
    exact encodeSet_lt _
  · exact (Finset.sortedLT_sort _).pairwise

@[simp] theorem decode_encodeCell (C : Cell 10) : decodeCell (encodeCell C) = C := by
  apply cell_ext
  · exact maskSet_encodeSet _
  · change ((C.edges.image encodeSet).sort.toFinset).image maskSet = C.edges
    rw [Finset.sort_toFinset, Finset.image_image]
    simpa only [Function.comp_def, maskSet_encodeSet, Finset.image_id']
  · change ((C.ridges.image encodeSet).sort.toFinset).image maskSet = C.ridges
    rw [Finset.sort_toFinset, Finset.image_image]
    simpa only [Function.comp_def, maskSet_encodeSet, Finset.image_id']

/-- The fieldwise mapping is computable even for a noninjective function;
its use as a genuine template embedding is justified by a separate proof. -/
def mapCellFunction {m : ℕ} (f : Fin m → Fin 10) (C : Cell m) : Cell 10 where
  vertices := C.vertices.image f
  edges := C.edges.image (fun S => S.image f)
  ridges := C.ridges.image (fun S => S.image f)

def encodeMappedCell {m : ℕ} (f : Fin m → Fin 10) (C : Cell m) :
    ConcreteGrowth.Cell := encodeCell (mapCellFunction f C)

@[simp] theorem decode_encodeMappedCell {m : ℕ} (f : Fin m ↪ Fin 10) (C : Cell m) :
    decodeCell (encodeMappedCell f C) = mapCell f C := decode_encodeCell _

theorem encodeMappedCell_wellFormed {m : ℕ} (f : Fin m → Fin 10) (C : Cell m) :
    WellFormed (encodeMappedCell f C) := encodeCell_wellFormed _

/-- Exact equality of all geometric record fields; kind metadata have no
role in identifying a complete cell. -/
def SameGeometry (A B : ConcreteGrowth.Cell) : Prop :=
  A.vertices = B.vertices ∧ A.edges = B.edges ∧ A.ridgeMasks = B.ridgeMasks

instance (A B : ConcreteGrowth.Cell) : Decidable (SameGeometry A B) := by
  unfold SameGeometry
  infer_instance

theorem decode_eq_of_sameGeometry {A B : ConcreteGrowth.Cell}
    (h : SameGeometry A B) : decodeCell A = decodeCell B := by
  apply cell_ext <;> simp only [decodeCell, h.1, h.2.1, h.2.2]

/-- The executable completeness obligation for one compact injection code.
The distinguished root itself and every cell compatible with it are covered. -/
def embeddingCheck {m c : ℕ} (localCell : Cell m)
    (cells : Fin c → ConcreteGrowth.Cell) (root : Fin c)
    (f : Fin m → Fin 10) (witness : Fin c) : Bool :=
  decide ((SameGeometry (encodeMappedCell f localCell) (cells root) ∨
      ConcreteGrowth.compatible (encodeMappedCell f localCell) (cells root) = true) →
    SameGeometry (cells witness) (encodeMappedCell f localCell))

/-- Literal witness replay covers every embedding whose complete cell is
compatible with the normalized root. The full mathematical injection domain
is retained by `exists_injection_code`. -/
theorem embedding_coverage_of_checks {m c : ℕ} (hm : m ≤ 10)
    (localCell : Cell m) (cells : Fin c → ConcreteGrowth.Cell) (root : Fin c)
    (hroot : WellFormed (cells root)) (witness : ℕ → Fin c)
    (h : CodeInterval (fun code => embeddingCheck localCell cells root
      (decodeInjection 10 m hm code) (witness code)) 0 (injectionCount 10 m)) :
    ∀ f : Fin m ↪ Fin 10,
      (mapCell f localCell).Compatible (decodeCell (cells root)) →
        ∃ i, decodeCell (cells i) = mapCell f localCell := by
  intro f hf
  obtain ⟨code, hcode, hdecode⟩ := exists_injection_code hm f f.injective
  have hcheck := of_decide_eq_true (h code (Nat.zero_le _) hcode)
  change (SameGeometry (encodeMappedCell (decodeInjection 10 m hm code) localCell) (cells root) ∨
      ConcreteGrowth.compatible (encodeMappedCell (decodeInjection 10 m hm code) localCell)
        (cells root) = true) → _ at hcheck
  rw [hdecode] at hcheck
  have hcompatible : ConcreteGrowth.compatible (encodeMappedCell f localCell) (cells root) = true :=
    literal_compatible_of_compatible _ _ (encodeMappedCell_wellFormed _ _) hroot
      (by simpa only [decode_encodeMappedCell] using hf)
  refine ⟨witness code, ?_⟩
  exact (decode_eq_of_sameGeometry (hcheck (Or.inr hcompatible))).trans
    (decode_encodeMappedCell f localCell)

/-- Unconditional coverage for a universe containing every embedded cell,
without a distinguished root or a compatibility restriction. -/
def fullEmbeddingCheck {m c : ℕ} (localCell : Cell m)
    (cells : Fin c → ConcreteGrowth.Cell) (f : Fin m → Fin 10) (witness : Fin c) : Bool :=
  decide (SameGeometry (cells witness) (encodeMappedCell f localCell))

theorem full_embedding_coverage_of_checks {m c : ℕ} (hm : m ≤ 10)
    (localCell : Cell m) (cells : Fin c → ConcreteGrowth.Cell) (witness : ℕ → Fin c)
    (h : CodeInterval (fun code => fullEmbeddingCheck localCell cells
      (decodeInjection 10 m hm code) (witness code)) 0 (injectionCount 10 m)) :
    ∀ f : Fin m ↪ Fin 10, ∃ i, decodeCell (cells i) = mapCell f localCell := by
  intro f
  obtain ⟨code, hcode, hdecode⟩ := exists_injection_code hm f f.injective
  have hcheck := of_decide_eq_true (h code (Nat.zero_le _) hcode)
  change SameGeometry (cells (witness code))
    (encodeMappedCell (decodeInjection 10 m hm code) localCell) at hcheck
  rw [hdecode] at hcheck
  exact ⟨witness code, (decode_eq_of_sameGeometry hcheck).trans
    (decode_encodeMappedCell f localCell)⟩

end Papers.RationalityTen.LiteralCellEncoding

end
end BundlePart0

section BundlePart1
/- Source: LiteralEmbeddingRecords.lean -/




@[expose] public section

/-!
# Structural facts behind literal embedding certificates

Every falling-factorial code decodes to an injection. A literal record
checked equal to the canonical encoder is therefore a complete embedded
cell; its mask bounds and sorted edges need no independent geometric test.
-/

namespace Papers.RationalityTen.FiniteCycleCandidates

theorem decodeInjection_injective {n k : ℕ} (hk : k ≤ n) (code : ℕ) :
    Function.Injective (decodeInjection n k hk code) := by
  induction k generalizing n code with
  | zero =>
    intro i
    exact i.elim0
  | succ k ih =>
    cases n with
    | zero => exact (Nat.not_succ_le_zero k hk).elim
    | succ n =>
      let a : Fin (n + 1) := ⟨code % (n + 1), Nat.mod_lt _ (Nat.zero_lt_succ n)⟩
      change Function.Injective (Fin.cons a (fun i =>
        a.succAbove (decodeInjection n k (Nat.le_of_succ_le_succ hk)
          (code / (n + 1)) i)))
      apply Fin.cons_injective_of_injective
      · rintro ⟨i, hi⟩
        exact a.succAbove_ne _ hi
      · exact Fin.succAbove_right_injective.comp
          (ih (Nat.le_of_succ_le_succ hk) (code / (n + 1)))

def decodeEmbedding {n k : ℕ} (hk : k ≤ n) (code : ℕ) : Fin k ↪ Fin n :=
  ⟨decodeInjection n k hk code, decodeInjection_injective hk code⟩

end Papers.RationalityTen.FiniteCycleCandidates

namespace Papers.RationalityTen.LiteralCellEncoding

open LiteralMaskGeometry MatroidChecked.FacetBoundaryEncoding

theorem wellFormed_of_sameGeometry {A B : ConcreteGrowth.Cell}
    (h : SameGeometry A B) (hB : WellFormed B) : WellFormed A := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [h.1] using hB.vertices_bound
  · simpa only [h.2.1] using hB.edges_bound
  · simpa only [h.2.2] using hB.ridges_bound
  · simpa only [h.2.1] using hB.edges_sorted

theorem wellFormed_of_fullEmbeddingCheck {m c : ℕ} (localCell : Cell m)
    (cells : Fin c → ConcreteGrowth.Cell) (f : Fin m → Fin 10) (i : Fin c)
    (h : fullEmbeddingCheck localCell cells f i = true) : WellFormed (cells i) :=
  wellFormed_of_sameGeometry (of_decide_eq_true h) (encodeMappedCell_wellFormed f localCell)

end Papers.RationalityTen.LiteralCellEncoding

end
end BundlePart1

section BundlePart2
/- Source: CellFacetInvariantsBase.lean -/




@[expose] public section
namespace Papers.RationalityTen.CellFacetInvariants
open Finset Set
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport
variable {n c : ℕ}

def cellExcess (C : Cell n) : ℤ := 3 * (C.vertices.card : ℤ) - C.edges.card - 6

theorem mapCell_vertex_card {m : ℕ} (f : Fin m ↪ Fin n) (C : Cell m) :
    (mapCell f C).vertices.card = C.vertices.card :=
  Finset.card_image_of_injective _ f.injective

theorem mapCell_edge_card {m : ℕ} (f : Fin m ↪ Fin n) (C : Cell m) :
    (mapCell f C).edges.card = C.edges.card :=
  Finset.card_image_of_injective _ (Finset.image_injective f.injective)

theorem mapCell_excess {m : ℕ} (f : Fin m ↪ Fin n) (C : Cell m) :
    cellExcess (mapCell f C) = cellExcess C := by
  simp only [cellExcess, mapCell_vertex_card, mapCell_edge_card]

def cellRidgeSizeCount (C : Cell n) (k : ℕ) : ℕ :=
  (C.ridges.filter fun S => S.card = k).card

theorem mapCell_ridge_size_count {m : ℕ} (f : Fin m ↪ Fin n) (C : Cell m)
    (k : ℕ) : cellRidgeSizeCount (mapCell f C) k = cellRidgeSizeCount C k := by
  unfold cellRidgeSizeCount
  change ((C.ridges.image fun S => S.image f).filter fun S => S.card = k).card = _
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (Finset.image_injective f.injective)]
  simp only [Finset.card_image_of_injective _ f.injective]

/-- The local integer kind specification is fully decidable on a literal
candidate cell. It identifies the root separately from other bipyramids. -/
def KindCheck (cells : Fin c → ConcreteGrowth.Cell) (root i : Fin c) : Prop :=
  (cells i).kind = if i = root then 0 else
    if 4 < (LiteralMaskGeometry.decodeCell (cells i)).vertices.card then
      if cellExcess (LiteralMaskGeometry.decodeCell (cells i)) = 1 then 3 else 2
    else 1

instance (cells : Fin c → ConcreteGrowth.Cell) (root i : Fin c) :
    Decidable (KindCheck cells root i) := by
  unfold KindCheck
  infer_instance

/-- The full universe uses the same three facet kinds without reserving
kind zero for a selected root. -/
def UnrootedKindCheck (cells : Fin c → ConcreteGrowth.Cell) (i : Fin c) : Prop :=
  (cells i).kind =
    if 4 < (LiteralMaskGeometry.decodeCell (cells i)).vertices.card then
      if cellExcess (LiteralMaskGeometry.decodeCell (cells i)) = 1 then 3 else 2
    else 1

instance (cells : Fin c → ConcreteGrowth.Cell) (i : Fin c) :
    Decidable (UnrootedKindCheck cells i) := by
  unfold UnrootedKindCheck
  infer_instance

end Papers.RationalityTen.CellFacetInvariants

end
end BundlePart2

section BundlePart3
/- Source: RawFacetEmbeddingSemantics.lean -/





@[expose] public section

/-!
# Exact finite-set semantics of the pure embedding checker

The large certificate files import only the pure checker. This bridge proves
once that its natural-coordinate decoding enumerates every injection and
that its mask operations preserve every vertex, edge, and ridge.
-/

namespace Papers.RationalityTen.RawFacetEmbeddingSemantics

open Finset Set
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport
open LiteralMaskGeometry LiteralCellEncoding FiniteCycleCandidates

def localMaskSet (m mask : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => mask.testBit i.val = true

@[simp] theorem mem_localMaskSet (m mask : ℕ) (i : Fin m) :
    i ∈ localMaskSet m mask ↔ mask.testBit i.val = true := by
  simp only [localMaskSet, Finset.mem_filter, Finset.mem_univ, true_and]

def decodeTemplate (m : ℕ) (cell : ConcreteGrowth.Cell) : Cell m where
  vertices := localMaskSet m cell.vertices
  edges := cell.edges.toFinset.image (localMaskSet m)
  ridges := cell.ridgeMasks.toFinset.image (localMaskSet m)

theorem mapMask_set {m : ℕ} (f : ℕ → ℕ) (g : Fin m → Fin 10)
    (hfg : ∀ i : Fin m, f i.val = (g i).val) (mask : ℕ) :
    maskSet (RawFacetEmbedding.mapMask m f mask) = (localMaskSet m mask).image g := by
  ext v
  rw [mem_maskSet, RawFacetEmbedding.mapMask_bit]
  constructor
  · rintro ⟨j, hj, hbit, hvalue⟩
    refine Finset.mem_image.mpr ⟨⟨j, hj⟩, (mem_localMaskSet _ _ _).mpr hbit, ?_⟩
    exact Fin.ext ((hfg ⟨j, hj⟩).symm.trans hvalue)
  · intro h
    obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp h
    exact ⟨j.val, j.isLt, (mem_localMaskSet _ _ _).mp hj,
      (hfg j).trans (congrArg Fin.val hjv)⟩

theorem decode_mapCell {m : ℕ} (f : ℕ → ℕ) (g : Fin m → Fin 10)
    (hfg : ∀ i : Fin m, f i.val = (g i).val) (cell : ConcreteGrowth.Cell) :
    decodeCell (RawFacetEmbedding.mapCell m f cell) =
      mapCellFunction g (decodeTemplate m cell) := by
  have map_toFinset (l : List ℕ) (f : ℕ → ℕ) :
      (l.map f).toFinset = l.toFinset.image f := by
    ext x
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  apply cell_ext
  · exact mapMask_set f g hfg cell.vertices
  · change ((cell.edges.map (RawFacetEmbedding.mapMask m f)).toFinset).image maskSet =
      (cell.edges.toFinset.image (localMaskSet m)).image (fun S => S.image g)
    rw [map_toFinset, Finset.image_image, Finset.image_image]
    exact Finset.image_congr (fun mask _ => mapMask_set f g hfg mask)
  · change ((cell.ridgeMasks.map (RawFacetEmbedding.mapMask m f)).toFinset).image maskSet =
      (cell.ridgeMasks.toFinset.image (localMaskSet m)).image (fun S => S.image g)
    rw [map_toFinset, Finset.image_image, Finset.image_image]
    exact Finset.image_congr (fun mask _ => mapMask_set f g hfg mask)

theorem sameGeometry_decoded {left right : ConcreteGrowth.Cell}
    (h : RawFacetEmbedding.sameGeometry left right = true) :
    decodeCell left = decodeCell right := by
  obtain ⟨hvertices, hedges, hridges⟩ := RawFacetEmbedding.sameGeometry_sound h
  have he : left.edges.toFinset = right.edges.toFinset := by
    ext i
    simpa only [List.mem_toFinset] using hedges i
  have hr : left.ridgeMasks.toFinset = right.ridgeMasks.toFinset := by
    ext i
    simpa only [List.mem_toFinset] using hridges i
  apply cell_ext <;> simp only [decodeCell, hvertices, he, hr]

theorem wellFormed_of_check (cell : ConcreteGrowth.Cell)
    (h : RawFacetEmbedding.wellFormedCheck cell = true) : WellFormed cell := by
  obtain ⟨hv, he, hr, hs⟩ := RawFacetEmbedding.wellFormedCheck_sound cell h
  exact ⟨hv, he, hr, hs⟩

/-- The pure decoder is exactly the falling-factorial decoder already
proved to cover every mathematical injection. -/
theorem decode_eq_fin {n k : ℕ} (hk : k ≤ n) (code : ℕ) (i : Fin k) :
    RawFacetEmbedding.decode n k code i.val = (decodeInjection n k hk code i).val := by
  induction k generalizing n code with
  | zero => exact i.elim0
  | succ k ih =>
    cases n with
    | zero => exact (Nat.not_succ_le_zero k hk).elim
    | succ n =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [RawFacetEmbedding.decode, decodeInjection]
      · simp only [RawFacetEmbedding.decode, Fin.val_succ, Nat.succ_ne_zero, ite_false,
          Nat.add_sub_cancel, Nat.succ_sub_one, decodeInjection, Fin.cons_succ]
        rw [ih (Nat.le_of_succ_le_succ hk)]
        simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_mk]
        split_ifs <;> rfl

/-- Kernel-checked natural-code intervals imply complete template coverage.
The endpoint quantifies every injection of the full local vertex set. -/
theorem full_coverage_of_checks {m c : ℕ} (hm : m ≤ 10)
    (template : ConcreteGrowth.Cell) (localCell : Cell m)
    (htemplate : decodeTemplate m template = localCell)
    (cells : Fin c → ConcreteGrowth.Cell) (witness : ℕ → Fin c)
    (h : FiniteChecks.Interval (fun code => RawFacetEmbedding.embeddingCheck m template
      cells code (witness code)) 0 (injectionCount 10 m)) :
    ∀ f : Fin m ↪ Fin 10, ∃ i, decodeCell (cells i) = mapCell f localCell := by
  intro f
  obtain ⟨code, hcode, hdecode⟩ := exists_injection_code hm f f.injective
  have hfg (i : Fin m) : RawFacetEmbedding.decode 10 m code i.val = (f i).val := by
    rw [decode_eq_fin hm, hdecode]
  have hcheck := h code (Nat.zero_le _) hcode
  change RawFacetEmbedding.sameGeometry (cells (witness code))
    (RawFacetEmbedding.mapCell m (RawFacetEmbedding.decode 10 m code) template) = true at hcheck
  refine ⟨witness code, ?_⟩
  calc
    _ = decodeCell (RawFacetEmbedding.mapCell m
        (RawFacetEmbedding.decode 10 m code) template) := sameGeometry_decoded hcheck
    _ = mapCellFunction f (decodeTemplate m template) := decode_mapCell _ f hfg template
    _ = mapCell f localCell := by rw [htemplate]; rfl

end Papers.RationalityTen.RawFacetEmbeddingSemantics

end
end BundlePart3

section BundlePart4
/- Source: RawSmallCellMetadataSemantics.lean -/






@[expose] public section

/-!
# Cardinality semantics of pure small-cell metadata

The pure record checks count set bits and sorted edge-list entries. These
are exactly the vertex and edge cardinalities in the decoded finite cell.
-/

namespace Papers.RationalityTen.RawSmallCellMetadata

open Finset
open LiteralMaskGeometry CellFacetInvariants

theorem vertexCount_eq (cell : ConcreteGrowth.Cell) :
    vertexCount cell = (decodeCell cell).vertices.card := by
  have hset : (FiniteMaskSets.elements 10 cell.vertices).toFinset = maskSet cell.vertices := by
    ext i
    simp only [List.mem_toFinset, FiniteMaskSets.mem_elements, mem_maskSet]
  change (FiniteMaskSets.elements 10 cell.vertices).length = (maskSet cell.vertices).card
  rw [← hset, List.toFinset_card_of_nodup (FiniteMaskSets.elements_nodup _ _)]

theorem edgeCount_eq (cell : ConcreteGrowth.Cell) (hcell : WellFormed cell) :
    cell.edges.length = (decodeCell cell).edges.card := by
  have hnodup : cell.edges.Nodup :=
    hcell.edges_sorted.imp (fun {_ _} h => Nat.ne_of_lt h)
  have hinj : Set.InjOn maskSet cell.edges.toFinset := by
    intro a ha b hb hab
    exact maskSet_injective (hcell.edges_bound a (List.mem_toFinset.mp ha))
      (hcell.edges_bound b (List.mem_toFinset.mp hb)) hab
  change cell.edges.length = (cell.edges.toFinset.image maskSet).card
  rw [Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup hnodup]

theorem excess_eq (cell : ConcreteGrowth.Cell) (hcell : WellFormed cell) :
    excess cell = cellExcess (decodeCell cell) := by
  simp only [excess, cellExcess, vertexCount_eq, edgeCount_eq cell hcell]

theorem check_sound {c : ℕ} (cells : Fin c → ConcreteGrowth.Cell) (i : Fin c)
    (h : check (cells i) = true) :
    WellFormed (cells i) ∧ UnrootedKindCheck cells i ∧
      (decodeCell (cells i)).vertices.card ≤ 5 := by
  obtain ⟨hfirst, hsize⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hwell, hkind⟩ := Bool.and_eq_true_iff.mp hfirst
  have hw := RawFacetEmbeddingSemantics.wellFormed_of_check (cells i) hwell
  refine ⟨hw, ?_, ?_⟩
  · have hk := of_decide_eq_true hkind
    simpa only [kind, vertexCount_eq, excess_eq (cells i) hw, UnrootedKindCheck] using hk
  · simpa only [vertexCount_eq] using of_decide_eq_true hsize

end Papers.RationalityTen.RawSmallCellMetadata

end
end BundlePart4
