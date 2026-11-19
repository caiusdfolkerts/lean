module
prelude
public import CliqueExclusion
public import GraphCandidateCoverage
public import SharedGraphCellPool

@[expose] public section

/-!
# Facet incompatibility obstructions for an induced graph

An actual boundary must be a family of distinct, pairwise compatible facets
with the specified kind counts.  A coloring of the compatibility graph can
therefore reject a graph before any boundary-growth replay is needed.  The
global incidence rows still certify the complete candidate universe.

The small local record stores only a global embedding and the vertex, face,
and kind fields used by the clique checker.  Its fields are aligned with the
already checked global cell pool; no new geometric assumption is introduced.
The realization interface retains ridge mates, uniqueness, and connectedness
so stronger obstructions can also use these necessary boundary conditions.
-/

namespace Papers.RationalityTen.GraphFacetClique

open ConcreteGrowth GraphCandidateCoverage GrowthPruning GrowthRenaming
open SharedGraphCellPool PackedGraphCertificate GrowthBitsets

variable {N n : Nat}

/-- All necessary boundary conditions used by structural exclusions. -/
structure Realization (cells : Fin N → Cell) (rows : IncidenceRows N 10 45)
    (quota : Nat → Nat) (complement : Nat) (B : List (Fin N)) : Prop where
  nodup : B.Nodup
  boundary : GrowthRenaming.Target (fun c => SparseGrowthDAG.has (ridgeList cells c))
    (fun a b => ConcreteGrowth.compatible (cells a) (cells b))
    (fun c => (cells c).kind) quota B
  exactQuota : ∀ j, kindCount (fun c => (cells c).kind) B j = quota j
  induced : ∀ c ∈ B, Induced rows complement c

/-- A structural impossibility proof can replace a complete growth replay. -/
def Excluded (cells : Fin N → Cell) (rows : IncidenceRows N 10 45)
    (quota : Nat → Nat) (complement : Nat) : Prop :=
  ∀ B, Realization cells rows quota complement B → False

/-- Select the requested kinds without needing an ambient kind bound. -/
def selected (cells : Fin N → Cell) (kinds : List Nat) (B : List (Fin N)) :
    List (Fin N) :=
  kinds.flatMap fun j => B.filter fun c => decide ((cells c).kind = j)

theorem mem_selected (cells : Fin N → Cell) (kinds : List Nat)
    (B : List (Fin N)) (c : Fin N) :
    c ∈ selected cells kinds B ↔ c ∈ B ∧ (cells c).kind ∈ kinds := by
  simp only [selected, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hc, heq⟩
    exact ⟨hc, heq ▸ hj⟩
  · rintro ⟨hc, hj⟩
    exact ⟨(cells c).kind, hj, hc, rfl⟩

theorem selected_nodup (cells : Fin N → Cell) (kinds : List Nat)
    (B : List (Fin N)) (hkinds : kinds.Nodup) (hB : B.Nodup) :
    (selected cells kinds B).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun _ _ => List.Pairwise.filter _ hB, ?_⟩
  apply hkinds.imp
  intro j k hjk a ha b hb hab
  have haj := of_decide_eq_true (List.mem_filter.mp ha).2
  have hbk := of_decide_eq_true (List.mem_filter.mp hb).2
  subst b
  exact hjk (haj.symm.trans hbk)

theorem selected_length (cells : Fin N → Cell) (kinds : List Nat)
    (B : List (Fin N)) (quota : Nat → Nat)
    (hquota : ∀ j, kindCount (fun c => (cells c).kind) B j = quota j) :
    (selected cells kinds B).length = (kinds.map quota).sum := by
  simp only [selected, List.length_flatMap]
  change (kinds.map (fun j => kindCount (fun c => (cells c).kind) B j)).sum = _
  simp only [hquota]

/-- A locally indexed compatibility bound excludes the chosen kind quotas.
Completeness is one-sided: extra candidates only weaken the obstruction. -/
theorem excluded_of_clique (cells : Fin N → Cell) (rows : IncidenceRows N 10 45)
    (quota : Nat → Nat) (complement : Nat) (kinds : List Nat)
    (hkinds : kinds.Nodup) (embedding : Fin n → Fin N)
    (hinjective : ∀ a b, embedding a = embedding b → a = b)
    (relation : Fin n → Fin n → Bool)
    (hcomplete : ∀ c, (cells c).kind ∈ kinds → Induced rows complement c →
      ∃ a, embedding a = c)
    (hrelation : ∀ a b, ConcreteGrowth.compatible (cells (embedding a))
        (cells (embedding b)) = true → relation a b = true)
    (certificate : CliqueExclusion.Certificate n)
    (hcheck : CliqueExclusion.check relation (List.finRange n)
      (kinds.map quota).sum certificate = true) :
    Excluded cells rows quota complement := by
  intro B hB
  let S := selected cells kinds B
  have hclique : CliqueExclusion.Clique
      (fun a b => ConcreteGrowth.compatible (cells a) (cells b)) S := by
    refine ⟨selected_nodup cells kinds B hkinds hB.nodup, ?_⟩
    intro a ha b hb hab
    exact hB.boundary.pairwise a b
      ((mem_selected cells kinds B a).mp ha).1
      ((mem_selected cells kinds B b).mp hb).1 hab
  have hcovered : ∀ c ∈ S, ∃ a, embedding a = c := by
    intro c hc
    obtain ⟨hcB, hck⟩ := (mem_selected cells kinds B c).mp hc
    exact hcomplete c hck (hB.induced c hcB)
  obtain ⟨localVertices, _, hlength, hlocal⟩ := CliqueExclusion.clique_pullback
    embedding hinjective _ relation S hcovered hclique hrelation
  have hbound := CliqueExclusion.check_sound relation (List.finRange n)
    (kinds.map quota).sum certificate hcheck localVertices hlocal
    (fun _ _ => List.mem_finRange _)
  have hsize := selected_length cells kinds B quota hB.exactQuota
  have hsame : localVertices.length = (kinds.map quota).sum := hlength.trans hsize
  rw [hsame] at hbound
  exact Nat.lt_irrefl _ hbound

/-- Quotas for a selected collection of kinds; all other kinds are ignored. -/
def restrictedQuota (kinds : List Nat) (quota : Nat → Nat) (key : Nat) : Nat :=
  if key ∈ kinds then quota key else 0

/-- Quota-aware clique branching can combine several facet kinds without
discarding their separate exact counts. -/
theorem excluded_of_quotas (cells : Fin N → Cell) (rows : IncidenceRows N 10 45)
    (quota : Nat → Nat) (complement : Nat) (kinds : List Nat)
    (embedding : Fin n → Fin N)
    (hinjective : ∀ a b, embedding a = embedding b → a = b)
    (relation : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (hkind : ∀ c, kind c = (cells (embedding c)).kind)
    (hcomplete : ∀ c, (cells c).kind ∈ kinds → Induced rows complement c →
      ∃ a, embedding a = c)
    (hrelation : ∀ a b, ConcreteGrowth.compatible (cells (embedding a))
        (cells (embedding b)) = true → relation a b = true)
    (certificate : CliqueExclusion.QuotaCertificate n)
    (hcheck : CliqueExclusion.checkQuotas relation kind (List.finRange n)
      (restrictedQuota kinds quota) certificate = true) :
    Excluded cells rows quota complement := by
  intro B hB
  let S := B.filter fun c => decide ((cells c).kind ∈ kinds)
  have hclique : CliqueExclusion.Clique
      (fun a b => ConcreteGrowth.compatible (cells a) (cells b)) S := by
    refine ⟨List.Pairwise.filter _ hB.nodup, ?_⟩
    intro a ha b hb hab
    exact hB.boundary.pairwise a b (List.mem_filter.mp ha).1
      (List.mem_filter.mp hb).1 hab
  have hcovered : ∀ c ∈ S, ∃ a, embedding a = c := by
    intro c hc
    obtain ⟨hcB, hck⟩ := List.mem_filter.mp hc
    exact hcomplete c (of_decide_eq_true hck) (hB.induced c hcB)
  obtain ⟨localVertices, hmap, _, hlocal⟩ := CliqueExclusion.clique_pullback
    embedding hinjective _ relation S hcovered hclique hrelation
  apply CliqueExclusion.checkQuotas_sound relation kind (List.finRange n)
    (restrictedQuota kinds quota) certificate hcheck localVertices hlocal
    (fun _ _ => List.mem_finRange _)
  intro j
  by_cases hj : j ∈ kinds
  · have hfiltered : (CliqueExclusion.ofKind kind j localVertices).map embedding =
        B.filter (fun c => decide ((cells c).kind = j)) := by
      have hm := congrArg (fun L => L.filter fun c => decide ((cells c).kind = j)) hmap
      simp only [List.filter_map] at hm
      rw [show S.filter (fun c => decide ((cells c).kind = j)) =
          B.filter (fun c => decide ((cells c).kind = j)) from by
        simp only [S, List.filter_filter]
        apply congrArg (fun p : Fin N → Bool => B.filter p)
        funext c
        by_cases hc : (cells c).kind = j
        · simp only [hc, hj, decide_true, Bool.true_and]
        · simp only [hc, decide_false, Bool.false_and]] at hm
      simpa only [CliqueExclusion.ofKind, Function.comp_def, hkind] using hm
    have hlength := congrArg List.length hfiltered
    simp only [List.length_map] at hlength
    rw [restrictedQuota, ite_eq_left hj]
    exact Nat.le_of_eq (hlength.trans (hB.exactQuota j)).symm
  · simp only [restrictedQuota, ite_eq_right hj, Nat.zero_le]

/-- Only fields actually read by the structural checker are duplicated. -/
structure Data where
  count : Nat
  embedding : Fields
  vertices : Fields
  faces : Fields
  kinds : Fields

namespace Data

variable [NeZero N]

def embed (D : Data) (c : Fin D.count) : Fin N :=
  Fin.ofNat N (D.embedding.get c.val)

def embeddingList (D : Data) : List (Fin N) :=
  (List.finRange D.count).map (D.embed (N := N))

def relation (D : Data) (a b : Fin D.count) : Bool :=
  let common := Nat.land (D.vertices.get a.val) (D.vertices.get b.val)
  FaceOnlyCompatibility.proper (D.faces.get a.val) common &&
    FaceOnlyCompatibility.proper (D.faces.get b.val) common

def kind (D : Data) (c : Fin D.count) : Nat := D.kinds.get c.val

def alignmentCheck (D : Data) (pool : Fin N → Entry) : Bool :=
  (List.finRange D.count).all fun c =>
    let E := pool (D.embed c)
    decide (D.embedding.get c.val < N) &&
    (decide (D.vertices.get c.val = E.cell.vertices) &&
    (decide (D.faces.get c.val = E.faces) &&
      decide (D.kinds.get c.val = E.cell.kind)))

theorem alignment (D : Data) (pool : Fin N → Entry)
    (h : D.alignmentCheck pool = true) (c : Fin D.count) :
    D.embedding.get c.val < N ∧
    D.vertices.get c.val = (pool (D.embed c)).cell.vertices ∧
    D.faces.get c.val = (pool (D.embed c)).faces ∧
    D.kinds.get c.val = (pool (D.embed c)).cell.kind := by
  have hc := List.all_eq_true.mp h c (List.mem_finRange c)
  simpa only [alignmentCheck, Bool.and_eq_true_iff, decide_eq_true_eq] using hc

theorem embed_injective (D : Data) (h : (D.embeddingList (N := N)).Nodup) :
    ∀ a b, D.embed (N := N) a = D.embed b → a = b := by
  intro a b hab
  apply Fin.ext
  apply h.eq_of_getElem_eq
    (i := a.val) (j := b.val) (by simp [embeddingList])
    (by simp [embeddingList])
  simpa only [embeddingList, List.getElem_map, List.getElem_finRange, Fin.cast] using hab

theorem relation_necessary (D : Data) (pool : Fin N → Entry)
    (cells : Fin N → Cell) (within : Nat → Nat)
    (hpool : ∀ c, (pool c).Facts (cells c) within)
    (h : D.alignmentCheck pool = true) (a b : Fin D.count)
    (hab : ConcreteGrowth.compatible (cells (D.embed a)) (cells (D.embed b)) = true) :
    D.relation a b = true := by
  have ha := D.alignment pool h a
  have hb := D.alignment pool h b
  have hface := FaceOnlyCompatibility.necessary
    (pool (D.embed a)).cell (pool (D.embed b)).cell
    (pool (D.embed a)).faces (pool (D.embed b)).faces
    (hpool _).faces_checked (hpool _).faces_checked
    (by simpa only [(hpool _).cell_eq] using hab)
  simpa only [relation, FaceOnlyCompatibility.compatible,
    ha.2.1, hb.2.1, ha.2.2.1, hb.2.2.1] using hface

theorem kind_exact (D : Data) (pool : Fin N → Entry)
    (cells : Fin N → Cell) (within : Nat → Nat)
    (hpool : ∀ c, (pool c).Facts (cells c) within)
    (h : D.alignmentCheck pool = true) (c : Fin D.count) :
    D.kind c = (cells (D.embed c)).kind :=
  (D.alignment pool h c).2.2.2.trans (congrArg Cell.kind (hpool _).cell_eq)

theorem complete (D : Data) (cells : Fin N → Cell)
    (rows : IncidenceRows N 10 45) (allowed complement : Nat) (kinds : List Nat)
    (hallowed : ∀ c, allowed.testBit c.val = true ↔ (cells c).kind ∈ kinds)
    (hedges : ∀ c q, (rows.edges c).testBit q.val = true →
      (rows.vertices c).testBit (rows.first q).val = true ∧
      (rows.vertices c).testBit (rows.second q).val = true)
    (hmask : eligibleMask rows allowed complement = ofList (D.embeddingList (N := N)))
    (c : Fin N) (hkind : (cells c).kind ∈ kinds) (hinduced : Induced rows complement c) :
    ∃ a, D.embed a = c := by
  have hm := (mem_embedding_iff rows allowed complement D.embeddingList hmask c
    (hedges c)).mpr ⟨(hallowed c).mpr hkind, hinduced⟩
  simpa only [embeddingList, List.mem_map, List.mem_finRange, true_and] using hm

end Data

#print axioms excluded_of_clique
#print axioms Data.relation_necessary

end Papers.RationalityTen.GraphFacetClique
