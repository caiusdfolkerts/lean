module
prelude
public import GraphFacetClique
public import SequentialCounter

@[expose] public section

/-!
# Sound clauses for a finite facet boundary

These are logical consequences of facet compatibility, exact kind counts,
and the fact that every ridge is in exactly two facets.  A SAT producer may
choose any subset of these consequences.  The resulting refutation is an
ordinary Lean proof; the producer and its search heuristics are untrusted.
-/

namespace Papers.RationalityTen.FacetSat

open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning
open GraphFacetClique GraphCandidateCoverage SharedGraphCellPool PackedGraphCertificate

variable {n N r : Nat}

structure Boundary (kind : Fin n → Nat) (relation : Fin n → Fin n → Bool)
    (ridges : Fin n → Fin r → Bool) (quota : Nat → Nat) (S : List (Fin n)) : Prop where
  nodup : S.Nodup
  pairwise : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → relation a b = true
  exactQuota : ∀ j, kindCount kind S j = quota j
  mates : ∀ q a, a ∈ S → ridges a q = true →
    ∃ b, b ∈ S ∧ ridges b q = true ∧ b ≠ a
  no_three : ∀ q a b c, a ∈ S → b ∈ S → c ∈ S →
    ridges a q = true → ridges b q = true → ridges c q = true →
    a = b ∨ a = c ∨ b = c

namespace Boundary

variable {kind : Fin n → Nat} {relation : Fin n → Fin n → Bool}
  {ridges : Fin n → Fin r → Bool} {quota : Nat → Nat} {S : List (Fin n)}

theorem incompatible (H : Boundary kind relation ridges quota S)
    (a b : Fin n) (hne : a ≠ b) (hbad : relation a b = false) :
    a ∈ S → b ∈ S → False := by
  intro ha hb
  exact Bool.noConfusion ((H.pairwise a ha b hb hne).symm.trans hbad)

theorem three (H : Boundary kind relation ridges quota S)
    (q : Fin r) (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haq : ridges a q = true) (hbq : ridges b q = true) (hcq : ridges c q = true) :
    a ∈ S → b ∈ S → c ∈ S → False := by
  intro ha hb hc
  rcases H.no_three q a b c ha hb hc haq hbq hcq with h | h | h
  · exact hab h
  · exact hac h
  · exact hbc h

/-- A checked owner list may contain extra facets.  It must contain every
other candidate incident with the selected ridge. -/
def ownersCheck (ridges : Fin n → Fin r → Bool) (q : Fin r) (a : Fin n)
    (owners : List (Fin n)) : Bool :=
  ridges a q && (List.finRange n).all fun b =>
    !ridges b q || decide (b = a) || decide (b ∈ owners)

theorem mate (H : Boundary kind relation ridges quota S)
    (q : Fin r) (a : Fin n) (owners : List (Fin n))
    (hcheck : ownersCheck ridges q a owners = true) :
    a ∈ S → (∀ b ∈ owners, b ∈ S → False) → False := by
  intro ha hn
  obtain ⟨haq, howners⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨b, hb, hbq, hba⟩ := H.mates q a ha haq
  have hc := List.all_eq_true.mp howners b (List.mem_finRange b)
  have hm : b ∈ owners := by
    simpa only [hbq, hba, Bool.not_true, decide_false, Bool.false_or,
      decide_eq_true_eq] using hc
  exact hn b hm hb

/-- An actual ridge mate must also be compatible with its first owner.  This
stronger initial clause removes irrelevant literals before the SAT proof. -/
def compatibleOwnersCheck (relation : Fin n → Fin n → Bool)
    (ridges : Fin n → Fin r → Bool) (q : Fin r) (a : Fin n)
    (owners : List (Fin n)) : Bool :=
  ridges a q && (List.finRange n).all fun b =>
    !ridges b q || decide (b = a) || !relation a b || decide (b ∈ owners)

theorem compatible_mate (H : Boundary kind relation ridges quota S)
    (q : Fin r) (a : Fin n) (owners : List (Fin n))
    (hcheck : compatibleOwnersCheck relation ridges q a owners = true) :
    a ∈ S → (∀ b ∈ owners, b ∈ S → False) → False := by
  intro ha hn
  obtain ⟨haq, howners⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨b, hb, hbq, hba⟩ := H.mates q a ha haq
  have hc := List.all_eq_true.mp howners b (List.mem_finRange b)
  have hab := H.pairwise a ha b hb hba.symm
  have hm : b ∈ owners := by
    simpa only [hbq, hba, hab, Bool.not_true, decide_false, Bool.false_or,
      decide_eq_true_eq] using hc
  exact hn b hm hb

def cachedOwnersCheck (relation : Fin n → Fin n → Bool)
    (cache : Fin n → Fin r → Bool) (q : Fin r) (a : Fin n)
    (owners : List (Fin n)) : Bool :=
  (List.finRange n).all fun b =>
    !cache b q || decide (b = a) || !relation a b || decide (b ∈ owners)

theorem cached_mate (H : Boundary kind relation ridges quota S)
    (cache : Fin n → Fin r → Bool)
    (hcache : ∀ c q, ridges c q = true → cache c q = true)
    (q : Fin r) (a : Fin n) (owners : List (Fin n))
    (haq : ridges a q = true)
    (hcheck : cachedOwnersCheck relation cache q a owners = true) :
    a ∈ S → (∀ b ∈ owners, b ∈ S → False) → False := by
  intro ha hn
  obtain ⟨b, hb, hbq, hba⟩ := H.mates q a ha haq
  have hc := List.all_eq_true.mp hcheck b (List.mem_finRange b)
  have hab := H.pairwise a ha b hb hba.symm
  have hcached := hcache b q hbq
  have hm : b ∈ owners := by
    simpa only [hcached, hba, hab, Bool.not_true, decide_false, Bool.false_or,
      decide_eq_true_eq] using hc
  exact hn b hm hb

/-- A bit-parallel coverage check replaces a fresh scan of every candidate
for each ridge clause.  Only the short omitted list needs compatibility tests. -/
def packedOwnersCheck (relation : Fin n → Fin n → Bool) (row : Nat) (a : Fin n)
    (owners dropped : List (Fin n)) : Bool :=
  decide (Nat.land row (GrowthBitsets.ofList (a :: (owners ++ dropped))) = row) &&
    dropped.all fun b => !relation a b

theorem packed_mate (H : Boundary kind relation ridges quota S)
    (rows : Fin r → Nat)
    (hrows : ∀ q c, (rows q).testBit c.val = ridges c q)
    (q : Fin r) (a : Fin n) (owners dropped : List (Fin n))
    (haq : ridges a q = true)
    (hcheck : packedOwnersCheck relation (rows q) a owners dropped = true) :
    a ∈ S → (∀ b ∈ owners, b ∈ S → False) → False := by
  intro ha hn
  obtain ⟨b, hb, hbq, hba⟩ := H.mates q a ha haq
  obtain ⟨hcover, hdropped⟩ := Bool.and_eq_true_iff.mp hcheck
  have hbit := congrArg (fun mask : Nat => mask.testBit b.val) (of_decide_eq_true hcover)
  have hrow : (rows q).testBit b.val = true := (hrows q b).trans hbq
  rw [FiniteMaskSets.testBit_land, hrow, Bool.true_and] at hbit
  have hm : b ∈ a :: (owners ++ dropped) :=
    (GrowthBitsets.bitAt_ofList _ _).mp
      ((GrowthBitsets.bitAt_eq_testBit _ _).trans hbit)
  rcases List.mem_cons.mp hm with heq | hm
  · exact hba heq
  · rcases List.mem_append.mp hm with hm | hm
    · exact hn b hm hb
    · have hbad := List.all_eq_true.mp hdropped b hm
      have hgood := H.pairwise a ha b hb hba.symm
      rw [hgood] at hbad
      exact Bool.noConfusion hbad

def kindListCheck (kind : Fin n → Nat) (key : Nat) (vertices : List (Fin n)) : Bool :=
  decide vertices.Nodup && (List.finRange n).all fun c =>
    decide ((c ∈ vertices) ↔ kind c = key)

/-- Sequential-counter atoms count membership in the actual boundary along
a complete, duplicate-free list of candidates of one kind. -/
theorem quota_count (H : Boundary kind relation ridges quota S)
    (key : Nat) (vertices : List (Fin n))
    (hcheck : kindListCheck kind key vertices = true) :
    SequentialCounter.selectedCount (fun c => c ∈ S) vertices = quota key := by
  obtain ⟨hnodup, hmembers⟩ := Bool.and_eq_true_iff.mp hcheck
  have hn : vertices.Nodup := of_decide_eq_true hnodup
  have hm (c : Fin n) : c ∈ vertices ↔ kind c = key :=
    of_decide_eq_true (List.all_eq_true.mp hmembers c (List.mem_finRange c))
  have hp : (vertices.filter fun c => decide (c ∈ S)).Perm
      (S.filter fun c => decide (kind c = key)) := by
    apply (List.perm_ext_iff_of_nodup
      (List.Pairwise.filter _ hn) (List.Pairwise.filter _ H.nodup)).mpr
    intro c
    simp only [List.mem_filter, decide_eq_true_eq, hm, and_comm]
  exact hp.length_eq.trans (H.exactQuota key)

end Boundary

/-- Building a finite collection of falsity hypotheses takes only ordinary
implication introduction, without evaluating a large logical formula. -/
theorem not_mem_nil (P : Fin n → Prop) : ∀ c ∈ ([] : List (Fin n)), P c → False := by
  intro c hc
  exact False.elim (List.not_mem_nil hc)

theorem not_mem_cons (P : Fin n → Prop) (a : Fin n) (tail : List (Fin n))
    (ha : P a → False) (ht : ∀ c ∈ tail, P c → False) :
    ∀ c ∈ a :: tail, P c → False := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ha
  · exact ht c hc

/-- Exact cell codes are needed only for the ridge clauses.  Compatibility
continues to use the smaller checked vertex/proper-face projection. -/
structure Data extends GraphFacetClique.Data where
  cellCodes : Fields
  ridgeMatrix : Nat

namespace Data

variable [NeZero N]

def cells (D : Data) (c : Fin D.count) : Cell := PackedGraphData.cell (D.cellCodes.get c.val)

def ridges (D : Data) (c : Fin D.count) (q : Fin 1024) : Bool :=
  has (ridgeList D.cells c) q

def ridgeRows (D : Data) (q : Fin 1024) : Nat :=
  PackedIncidenceMatrix.row D.count D.ridgeMatrix q.val

theorem ridgeRows_exact (D : Data)
    (hmatrix : D.ridgeMatrix = PackedIncidenceMatrix.code (ridgeList D.cells))
    (q : Fin 1024) (c : Fin D.count) :
    (D.ridgeRows q).testBit c.val = D.ridges c q := by
  have h := PackedIncidenceMatrix.rows_exact_of_code (ridgeList D.cells)
    D.ridgeMatrix hmatrix q c
  simpa only [ridgeRows, ridges, GrowthBitsets.bitAt_eq_testBit] using h

def ridgeCache (D : Data) (c : Fin D.count) (q : Fin 1024) : Bool :=
  (D.faces.get c.val).testBit q.val

def ridgeCacheCheck (D : Data) : Bool :=
  (List.finRange D.count).all fun c => (D.cells c).ridgeMasks.all fun q =>
    decide (q < 1024) && (D.faces.get c.val).testBit q

theorem ridgeCache_necessary (D : Data) (h : D.ridgeCacheCheck = true)
    (c : Fin D.count) (q : Fin 1024) (hq : D.ridges c q = true) :
    D.ridgeCache c q = true := by
  obtain ⟨mask, hm, heq⟩ := List.mem_map.mp ((has_true (ridgeList D.cells c) q).mp hq)
  have hc := List.all_eq_true.mp
    (List.all_eq_true.mp h c (List.mem_finRange c)) mask hm
  obtain ⟨hlt, hbit⟩ := Bool.and_eq_true_iff.mp hc
  have hlt : mask < 1024 := of_decide_eq_true hlt
  have hv := congrArg Fin.val heq
  change mask % 1024 = q.val at hv
  rw [Nat.mod_eq_of_lt hlt] at hv
  change (D.faces.get c.val).testBit q.val = true
  exact hv ▸ hbit

def alignmentCheck (D : Data) (pool : Fin N → Entry) : Bool :=
  D.toData.alignmentCheck pool &&
    (List.finRange D.count).all fun c =>
      decide (D.cellCodes.get c.val = (pool (D.toData.embed c)).cellCode)

theorem cells_exact (D : Data) (pool : Fin N → Entry)
    (cells : Fin N → Cell) (within : Nat → Nat)
    (hpool : ∀ c, (pool c).Facts (cells c) within)
    (h : D.alignmentCheck pool = true) (c : Fin D.count) :
    D.cells c = cells (D.toData.embed c) := by
  have hc := of_decide_eq_true
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 c (List.mem_finRange c))
  exact (congrArg PackedGraphData.cell hc).trans (hpool _).cell_eq

end Data

/-- Transfer a complete globally encoded boundary to its small local indices.
The map is required to be injective and to cover all selected global facets. -/
theorem boundary_pullback (cells : Fin N → Cell) (rows : IncidenceRows N 10 45)
    (quota : Nat → Nat) (complement : Nat) (B : List (Fin N))
    (H : Realization cells rows quota complement B)
    (embedding : Fin n → Fin N)
    (hinjective : ∀ a b, embedding a = embedding b → a = b)
    (localCells : Fin n → Cell) (kind : Fin n → Nat)
    (relation : Fin n → Fin n → Bool)
    (hcells : ∀ c, localCells c = cells (embedding c))
    (hkind : ∀ c, kind c = (cells (embedding c)).kind)
    (hrelation : ∀ a b, ConcreteGrowth.compatible (cells (embedding a))
      (cells (embedding b)) = true → relation a b = true)
    (hcomplete : ∀ c ∈ B, ∃ a, embedding a = c) :
    ∃ S : List (Fin n), Boundary kind relation
      (fun c => has (ridgeList localCells c)) quota S := by
  have hclique : CliqueExclusion.Clique
      (fun a b => ConcreteGrowth.compatible (cells a) (cells b)) B :=
    ⟨H.nodup, fun a ha b hb hab => H.boundary.pairwise a b ha hb hab⟩
  obtain ⟨S, hmap, _, hS⟩ := CliqueExclusion.clique_pullback
    embedding hinjective _ relation B hcomplete hclique hrelation
  have hmem (a : Fin n) : a ∈ S ↔ embedding a ∈ B := by
    rw [← hmap, List.mem_map]
    constructor
    · intro ha
      exact ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, hab⟩
      exact hinjective b a hab ▸ hb
  have hridge (a : Fin n) (q : Fin 1024) :
      has (ridgeList localCells a) q = has (ridgeList cells (embedding a)) q := by
    change has ((localCells a).ridgeMasks.map (Fin.ofNat 1024)) q = _
    rw [hcells]
    rfl
  refine ⟨S, hS.1, hS.2, ?_, ?_, ?_⟩
  · intro j
    have hm := congrArg
      (fun L => (L.filter fun c => decide ((cells c).kind = j)).length) hmap
    simp only [List.filter_map, List.length_map, Function.comp_def, ← hkind] at hm
    exact hm.trans (H.exactQuota j)
  · intro q a ha haq
    have hga : Incident (fun c => has (ridgeList cells c)) (family B) q (embedding a) :=
      ⟨(has_true B _).mpr ((hmem a).mp ha), (hridge a q).symm.trans haq⟩
    obtain ⟨gb, hgb, hne⟩ := H.boundary.mates q (embedding a) hga
    obtain ⟨b, hb, hemb⟩ := List.mem_map.mp (hmap.symm ▸ (has_true B gb).mp hgb.1)
    refine ⟨b, hb, ?_, ?_⟩
    · exact (hridge b q).trans (hemb ▸ hgb.2)
    · intro heq
      exact hne (hemb.symm.trans (congrArg embedding heq))
  · intro q a b c ha hb hc haq hbq hcq
    have hinc (x : Fin n) (hx : x ∈ S) (hxq : has (ridgeList localCells x) q = true) :
        Incident (fun c => has (ridgeList cells c)) (family B) q (embedding x) :=
      ⟨(has_true B _).mpr ((hmem x).mp hx), (hridge x q).symm.trans hxq⟩
    rcases H.boundary.no_three q (embedding a) (embedding b) (embedding c)
      (hinc a ha haq) (hinc b hb hbq) (hinc c hc hcq) with h | h | h
    · exact Or.inl (hinjective a b h)
    · exact Or.inr (Or.inl (hinjective a c h))
    · exact Or.inr (Or.inr (hinjective b c h))

theorem selected_kind_positive (cells : Fin N → Cell) (rows : IncidenceRows N 10 45)
    (quota : Nat → Nat) (complement : Nat) (B : List (Fin N))
    (H : Realization cells rows quota complement B) (c : Fin N) (hc : c ∈ B) :
    0 < quota (cells c).kind := by
  rw [← H.exactQuota]
  apply List.length_pos_of_mem
  exact List.mem_filter.mpr ⟨hc, decide_eq_true rfl⟩

namespace Data

variable [NeZero N]

/-- The Boolean clauses need only the complete candidate universe and exact
cell alignment.  No growth nodes or symmetry frames are needed. -/
theorem excluded (D : Data) (pool : Fin N → Entry)
    (cells : Fin N → Cell) (rows : IncidenceRows N 10 45)
    (within : Nat → Nat) (hpool : ∀ c, (pool c).Facts (cells c) within)
    (quota : Nat → Nat) (allowed complement : Nat)
    (haligned : D.alignmentCheck pool = true)
    (hnodup : (D.toData.embeddingList (N := N)).Nodup)
    (hmask : eligibleMask rows allowed complement =
      GrowthBitsets.ofList (D.toData.embeddingList (N := N)))
    (hallowed : ∀ c, allowed.testBit c.val = true ↔ 0 < quota (cells c).kind)
    (hedges : ∀ c q, (rows.edges c).testBit q.val = true →
      (rows.vertices c).testBit (rows.first q).val = true ∧
      (rows.vertices c).testBit (rows.second q).val = true)
    (hunsat : ∀ S, Boundary D.toData.kind D.toData.relation D.ridges quota S → False) :
    GraphFacetClique.Excluded cells rows quota complement := by
  intro B HB
  have ha := (Bool.and_eq_true_iff.mp haligned).1
  have hcovered (c : Fin N) (hc : c ∈ B) : ∃ a, D.toData.embed a = c := by
    have hm := (mem_embedding_iff rows allowed complement D.toData.embeddingList
      hmask c (hedges c)).mpr
      ⟨(hallowed c).mpr (selected_kind_positive cells rows quota complement B HB c hc),
        HB.induced c hc⟩
    simpa only [GraphFacetClique.Data.embeddingList, List.mem_map,
      List.mem_finRange, true_and] using hm
  obtain ⟨S, HS⟩ := boundary_pullback cells rows quota complement B HB D.toData.embed
    (D.toData.embed_injective hnodup) D.cells D.toData.kind D.toData.relation
    (D.cells_exact pool cells within hpool haligned)
    (D.toData.kind_exact pool cells within hpool ha)
    (D.toData.relation_necessary pool cells within hpool ha) hcovered
  exact hunsat S HS

end Data


end Papers.RationalityTen.FacetSat
