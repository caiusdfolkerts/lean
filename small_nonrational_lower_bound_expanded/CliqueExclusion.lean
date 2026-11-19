module
prelude
public import Init

@[expose] public section

/-!
# Small, independently checked clique obstructions

A family of mutually compatible facets gives a clique in any Boolean relation
which contains facet compatibility.  A proper coloring, or a short branching
tree ending in colorings, can exclude the required number of facets without
replaying the much larger boundary-growth certificate.

The producer supplies only branching choices and color labels.  This module
checks the relation itself, the coverage of every branch, and every coloring.
The soundness theorem does not assume symmetry, irreflexivity, or distinctness
of the candidate list.  It applies to distinct selected vertices whose relation
holds in both directions.
-/

namespace Papers.RationalityTen.CliqueExclusion

/-- The selected vertices are distinct and every ordered pair of different
vertices satisfies the relation. -/
def Clique {n : Nat} (relation : Fin n → Fin n → Bool) (vertices : List (Fin n)) : Prop :=
  vertices.Nodup ∧
    ∀ a ∈ vertices, ∀ b ∈ vertices, a ≠ b → relation a b = true

theorem Clique.sublist {n : Nat} {relation : Fin n → Fin n → Bool}
    {vertices smaller : List (Fin n)} (h : Clique relation vertices)
    (hs : smaller.Sublist vertices) : Clique relation smaller :=
  ⟨h.1.sublist hs, fun a ha b hb hab => h.2 a (hs.subset ha) b (hs.subset hb) hab⟩

/-- Transfer a clique to a complete, injectively enumerated local candidate
universe.  The local relation may be a larger, cheaper relation. -/
theorem clique_pullback {n total : Nat}
    (embedding : Fin n → Fin total)
    (hinjective : ∀ a b, embedding a = embedding b → a = b)
    (globalRelation : Fin total → Fin total → Bool)
    (localRelation : Fin n → Fin n → Bool)
    (vertices : List (Fin total))
    (hcomplete : ∀ vertex ∈ vertices, ∃ a, embedding a = vertex)
    (hclique : Clique globalRelation vertices)
    (hrelation : ∀ a b, globalRelation (embedding a) (embedding b) = true →
      localRelation a b = true) :
    ∃ localVertices : List (Fin n),
      localVertices.map embedding = vertices ∧
      localVertices.length = vertices.length ∧ Clique localRelation localVertices := by
  have hexists : ∃ localVertices : List (Fin n), localVertices.map embedding = vertices := by
    induction vertices with
    | nil => exact ⟨[], rfl⟩
    | cons vertex tail ih =>
        obtain ⟨a, ha⟩ := hcomplete vertex (List.mem_cons_self ..)
        have htail : ∀ vertex ∈ tail, ∃ a, embedding a = vertex :=
          fun vertex hv => hcomplete vertex (List.mem_cons_of_mem _ hv)
        obtain ⟨localTail, ht⟩ := ih htail
          (hclique.sublist (List.Sublist.cons _ (List.Sublist.refl _)))
        exact ⟨a :: localTail, by simp only [List.map, ha, ht]⟩
  obtain ⟨localVertices, hmap⟩ := hexists
  refine ⟨localVertices, hmap, ?_, ?_⟩
  · rw [← hmap, List.length_map]
  · constructor
    · have hmapNodup : (localVertices.map embedding).Nodup := hmap ▸ hclique.1
      exact List.Pairwise.of_map embedding
        (fun a b hne hab => hne (congrArg embedding hab)) hmapNodup
    · intro a ha b hb hab
      have hma : embedding a ∈ vertices := hmap ▸ List.mem_map_of_mem ha
      have hmb : embedding b ∈ vertices := hmap ▸ List.mem_map_of_mem hb
      exact hrelation a b
        (hclique.2 (embedding a) hma (embedding b) hmb
          (fun heq => hab (hinjective a b heq)))

/-- Check a proposed proper coloring only on the current candidates. -/
def coloringCheck {n : Nat} (relation : Fin n → Fin n → Bool)
    (candidates : List (Fin n)) (color : Fin n → Nat) (count : Nat) : Bool :=
  candidates.all fun a =>
    decide (color a < count) &&
      candidates.all fun b =>
        decide (a = b) || decide (color a ≠ color b) || !(relation a b)

theorem coloringCheck_bound {n : Nat} (relation : Fin n → Fin n → Bool)
    (candidates : List (Fin n)) (color : Fin n → Nat) (count : Nat)
    (hcheck : coloringCheck relation candidates color count = true)
    (vertices : List (Fin n)) (hclique : Clique relation vertices)
    (hsub : vertices ⊆ candidates) : vertices.length ≤ count := by
  have hchecked := List.all_eq_true.mp hcheck
  have hdifferent : ∀ a ∈ vertices, ∀ b ∈ vertices, a ≠ b → color a ≠ color b := by
    intro a ha b hb hab
    have hc := (Bool.and_eq_true_iff.mp (hchecked a (hsub ha))).2
    have hp := List.all_eq_true.mp hc b (hsub hb)
    have hr := hclique.2 a ha b hb hab
    simpa only [hab, decide_false, Bool.false_or, hr, Bool.not_true, Bool.or_false,
      decide_eq_true_eq] using hp
  have hnodup : (vertices.map color).Nodup := by
    apply List.pairwise_map.mpr
    exact hclique.1.imp_of_mem (fun ha hb hab => hdifferent _ ha _ hb hab)
  have hcolors : vertices.map color ⊆ List.range count := by
    intro value hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    apply List.mem_range.mpr
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (hchecked a (hsub ha))).1
  have hlength := hnodup.length_le_of_subset hcolors
  simpa only [List.length_map, List.length_range] using hlength

/-- Check one independent color class.  A mask may contain unused vertices;
only current candidates need to be checked. -/
def independentCheck {n : Nat} (relation : Fin n → Fin n → Bool)
    (candidates : List (Fin n)) (mask : Nat) : Bool :=
  let members := candidates.filter fun vertex => mask.testBit vertex.val
  members.all fun a => members.all fun b => decide (a = b) || !(relation a b)

theorem independentCheck_bound {n : Nat} (relation : Fin n → Fin n → Bool)
    (candidates : List (Fin n)) (mask : Nat)
    (hcheck : independentCheck relation candidates mask = true)
    (vertices : List (Fin n)) (hclique : Clique relation vertices)
    (hsub : vertices ⊆ candidates)
    (hmask : ∀ vertex ∈ vertices, mask.testBit vertex.val = true) : vertices.length ≤ 1 := by
  cases vertices with
  | nil => simp
  | cons first tail =>
      have hfirst : first ∈ first :: tail := List.mem_cons_self
      have hmembers : ∀ vertex ∈ first :: tail,
          vertex ∈ candidates.filter (fun c => mask.testBit c.val) :=
        fun vertex hv => List.mem_filter.mpr ⟨hsub hv, hmask vertex hv⟩
      have hsingle : first :: tail ⊆ [first] := by
        intro vertex hv
        have heq : vertex = first := by
          by_cases heq : vertex = first
          · exact heq
          · have hc := List.all_eq_true.mp
              (List.all_eq_true.mp hcheck first (hmembers first hfirst))
              vertex (hmembers vertex hv)
            have hr := hclique.2 first hfirst vertex hv (Ne.symm heq)
            simp only [Ne.symm heq, decide_false, Bool.false_or, hr, Bool.not_true,
              Bool.false_eq_true] at hc
        simp only [List.mem_singleton, heq]
      exact hclique.1.length_le_of_subset hsingle

/-- Explicit masks avoid decoding a color number for every candidate pair.
Coverage costs candidates × colors, and incompatibility checks are confined
to pairs within each class.  Classes may overlap. -/
def classesCheck {n : Nat} (relation : Fin n → Fin n → Bool)
    (candidates : List (Fin n)) (classes : List Nat) : Bool :=
  candidates.all (fun vertex => classes.any (fun mask => mask.testBit vertex.val)) &&
    classes.all (independentCheck relation candidates)

private theorem length_filter_partition {α : Type} (predicate : α → Bool)
    (vertices : List α) :
    (vertices.filter predicate).length +
      (vertices.filter fun vertex => !(predicate vertex)).length = vertices.length := by
  induction vertices with
  | nil => rfl
  | cons vertex tail ih =>
      cases hp : predicate vertex <;> simp [hp] at * <;> omega

private theorem classes_bound {n : Nat} (relation : Fin n → Fin n → Bool)
    (candidates : List (Fin n)) (classes : List Nat)
    (hclasses : classes.all (independentCheck relation candidates) = true)
    (vertices : List (Fin n)) (hclique : Clique relation vertices)
    (hsub : vertices ⊆ candidates)
    (hcover : ∀ vertex ∈ vertices, classes.any (fun mask => mask.testBit vertex.val) = true) :
    vertices.length ≤ classes.length := by
  induction classes generalizing vertices with
  | nil =>
      cases vertices with
      | nil => simp
      | cons vertex tail =>
          have hc := hcover vertex (List.mem_cons_self ..)
          contradiction
  | cons mask rest ih =>
      obtain ⟨hmask, hrest⟩ := Bool.and_eq_true_iff.mp hclasses
      let inside := vertices.filter fun vertex => mask.testBit vertex.val
      let outside := vertices.filter fun vertex => !(mask.testBit vertex.val)
      have hinside : inside.length ≤ 1 :=
        independentCheck_bound relation candidates mask hmask inside
          (hclique.sublist List.filter_sublist)
          (fun _ hv => hsub (List.mem_filter.mp hv).1)
          (fun _ hv => (List.mem_filter.mp hv).2)
      have hremaining : ∀ vertex ∈ outside,
          rest.any (fun mask => mask.testBit vertex.val) = true := by
        intro vertex hv
        obtain ⟨hmem, hnot⟩ := List.mem_filter.mp hv
        have hfalse : mask.testBit vertex.val = false := by
          cases hb : mask.testBit vertex.val <;> simp_all
        have hc := hcover vertex hmem
        simpa only [List.any_cons, hfalse, Bool.false_or] using hc
      have houtside : outside.length ≤ rest.length :=
        ih hrest outside (hclique.sublist List.filter_sublist)
          (fun _ hv => hsub (List.mem_filter.mp hv).1) hremaining
      have hpartition : inside.length + outside.length = vertices.length :=
        length_filter_partition (fun vertex => mask.testBit vertex.val) vertices
      simp only [List.length_cons]
      omega

theorem classesCheck_bound {n : Nat} (relation : Fin n → Fin n → Bool)
    (candidates : List (Fin n)) (classes : List Nat)
    (hcheck : classesCheck relation candidates classes = true)
    (vertices : List (Fin n)) (hclique : Clique relation vertices)
    (hsub : vertices ⊆ candidates) : vertices.length ≤ classes.length := by
  obtain ⟨hcover, hclasses⟩ := Bool.and_eq_true_iff.mp hcheck
  exact classes_bound relation candidates classes hclasses vertices hclique hsub
    (fun vertex hv => List.all_eq_true.mp hcover vertex (hsub hv))

/-- Color labels are packed into fixed-width natural-number fields.  No bound
on the width or payload is trusted: `coloringCheck` checks every used label. -/
def packedColor {n : Nat} (width payload : Nat) (vertex : Fin n) : Nat :=
  Nat.land (Nat.shiftRight payload (width * vertex.val)) (Nat.shiftLeft 1 width - 1)

/-- A certificate can stop at a cardinality or coloring bound, or split on
whether a particular vertex occurs in the clique. -/
inductive Certificate (n : Nat) where
  | size : Certificate n
  | color (count width payload : Nat) : Certificate n
  | classes (masks : List Nat) : Certificate n
  | split (pivot : Fin n) (without withPivot : Certificate n) : Certificate n
  deriving Repr

def without {n : Nat} (candidates : List (Fin n)) (pivot : Fin n) : List (Fin n) :=
  candidates.filter fun vertex => decide (vertex ≠ pivot)

def neighbors {n : Nat} (relation : Fin n → Fin n → Bool)
    (candidates : List (Fin n)) (pivot : Fin n) : List (Fin n) :=
  candidates.filter fun vertex => decide (vertex ≠ pivot) && relation pivot vertex

/-- `check relation candidates target certificate` excludes cliques of at
least `target` vertices.  Recursion follows the certificate, so malformed
certificates also terminate and have no special trusted interpretation. -/
def check {n : Nat} (relation : Fin n → Fin n → Bool)
    (candidates : List (Fin n)) (target : Nat) : Certificate n → Bool
  | .size => decide (candidates.length < target)
  | .color count width payload =>
      decide (count < target) &&
        coloringCheck relation candidates (packedColor width payload) count
  | .classes masks =>
      decide (masks.length < target) && classesCheck relation candidates masks
  | .split pivot left right =>
      check relation (without candidates pivot) target left &&
        check relation (neighbors relation candidates pivot) (target - 1) right

theorem check_sound {n : Nat} (relation : Fin n → Fin n → Bool)
    (candidates : List (Fin n)) (target : Nat) (certificate : Certificate n)
    (hcheck : check relation candidates target certificate = true)
    (vertices : List (Fin n)) (hclique : Clique relation vertices)
    (hsub : vertices ⊆ candidates) : vertices.length < target := by
  induction certificate generalizing candidates target vertices with
  | size =>
      have hbound : candidates.length < target := of_decide_eq_true hcheck
      exact Nat.lt_of_le_of_lt (hclique.1.length_le_of_subset hsub) hbound
  | color count width payload =>
      obtain ⟨hcount, hcolors⟩ := Bool.and_eq_true_iff.mp hcheck
      exact Nat.lt_of_le_of_lt
        (coloringCheck_bound relation candidates (packedColor width payload) count
          hcolors vertices hclique hsub)
        (of_decide_eq_true hcount)
  | classes masks =>
      obtain ⟨hcount, hclasses⟩ := Bool.and_eq_true_iff.mp hcheck
      exact Nat.lt_of_le_of_lt
        (classesCheck_bound relation candidates masks hclasses vertices hclique hsub)
        (of_decide_eq_true hcount)
  | split pivot left right ihleft ihright =>
      obtain ⟨hleft, hright⟩ := Bool.and_eq_true_iff.mp hcheck
      by_cases hpivot : pivot ∈ vertices
      · have herased : Clique relation (vertices.erase pivot) :=
          hclique.sublist List.erase_sublist
        have hneighbors : vertices.erase pivot ⊆ neighbors relation candidates pivot := by
          intro vertex hv
          have hmem : vertex ∈ vertices := List.mem_of_mem_erase hv
          have hne : vertex ≠ pivot := by
            intro heq
            subst vertex
            exact hclique.1.not_mem_erase hv
          apply List.mem_filter.mpr
          exact ⟨hsub hmem, Bool.and_eq_true_iff.mpr
            ⟨decide_eq_true hne, hclique.2 pivot hpivot vertex hmem hne.symm⟩⟩
        have hbound := ihright _ _ hright _ herased hneighbors
        have hlength := List.length_erase_of_mem hpivot
        have hpositive := List.length_pos_of_mem hpivot
        omega
      · have hwithout : vertices ⊆ without candidates pivot := by
          intro vertex hv
          apply List.mem_filter.mpr
          refine ⟨hsub hv, decide_eq_true ?_⟩
          intro heq
          exact hpivot (heq ▸ hv)
        exact ihleft _ _ hleft _ hclique hwithout

/-- Vertices of one prescribed facet kind. -/
def ofKind {n : Nat} (kind : Fin n → Nat) (key : Nat)
    (vertices : List (Fin n)) : List (Fin n) :=
  vertices.filter fun vertex => decide (kind vertex = key)

theorem ofKind_erase_length {n : Nat} (kind : Fin n → Nat) (key : Nat)
    (vertices : List (Fin n)) (pivot : Fin n) (hmem : pivot ∈ vertices) :
    (ofKind kind key (vertices.erase pivot)).length =
      (ofKind kind key vertices).length - (if kind pivot = key then 1 else 0) := by
  unfold ofKind
  rw [← List.erase_filter, List.length_erase]
  simp only [List.mem_filter, hmem, true_and, decide_eq_true_eq]
  split <;> simp_all

/-- Including a vertex consumes one unit of its kind, without changing the
requirements for other kinds. -/
def remainingQuota {n : Nat} (kind : Fin n → Nat) (quota : Nat → Nat)
    (pivot : Fin n) (key : Nat) : Nat :=
  quota key - (if kind pivot = key then 1 else 0)

/-- A quota-aware obstruction can bound any required kind at each leaf.  The
same tree can therefore condition a bipyramid coloring on earlier choices of
square pyramids, tetrahedra, or other required facet kinds. -/
inductive QuotaCertificate (n : Nat) where
  | size (key : Nat) : QuotaCertificate n
  | color (key count width payload : Nat) : QuotaCertificate n
  | classes (key : Nat) (masks : List Nat) : QuotaCertificate n
  | split (pivot : Fin n) (without withPivot : QuotaCertificate n) : QuotaCertificate n
  deriving Repr

def checkQuotas {n : Nat} (relation : Fin n → Fin n → Bool)
    (kind : Fin n → Nat) (candidates : List (Fin n)) (quota : Nat → Nat) :
    QuotaCertificate n → Bool
  | .size key => decide ((ofKind kind key candidates).length < quota key)
  | .color key count width payload =>
      decide (count < quota key) &&
        coloringCheck relation (ofKind kind key candidates) (packedColor width payload) count
  | .classes key masks =>
      decide (masks.length < quota key) &&
        classesCheck relation (ofKind kind key candidates) masks
  | .split pivot left right =>
      checkQuotas relation kind (without candidates pivot) quota left &&
        checkQuotas relation kind (neighbors relation candidates pivot)
          (remainingQuota kind quota pivot) right

/-- Every successful quota certificate excludes a clique meeting all its
kind quotas.  All quotas are lower bounds, so the theorem also applies when a
problem permits additional facets beyond the prescribed ones. -/
theorem checkQuotas_sound {n : Nat} (relation : Fin n → Fin n → Bool)
    (kind : Fin n → Nat) (candidates : List (Fin n)) (quota : Nat → Nat)
    (certificate : QuotaCertificate n)
    (hcheck : checkQuotas relation kind candidates quota certificate = true)
    (vertices : List (Fin n)) (hclique : Clique relation vertices)
    (hsub : vertices ⊆ candidates)
    (hquota : ∀ key, quota key ≤ (ofKind kind key vertices).length) : False := by
  induction certificate generalizing candidates quota vertices with
  | size key =>
      have hsmall : (ofKind kind key candidates).length < quota key :=
        of_decide_eq_true hcheck
      have hfilter : ofKind kind key vertices ⊆ ofKind kind key candidates := by
        intro vertex hv
        obtain ⟨hmem, hk⟩ := List.mem_filter.mp hv
        exact List.mem_filter.mpr ⟨hsub hmem, hk⟩
      have hbound : (ofKind kind key vertices).length ≤
          (ofKind kind key candidates).length :=
        (hclique.1.sublist List.filter_sublist).length_le_of_subset hfilter
      have hlarge := hquota key
      omega
  | color key count width payload =>
      obtain ⟨hcount, hcolors⟩ := Bool.and_eq_true_iff.mp hcheck
      have hsmall : count < quota key := of_decide_eq_true hcount
      have hfilter : ofKind kind key vertices ⊆ ofKind kind key candidates := by
        intro vertex hv
        obtain ⟨hmem, hk⟩ := List.mem_filter.mp hv
        exact List.mem_filter.mpr ⟨hsub hmem, hk⟩
      have hbound := coloringCheck_bound relation (ofKind kind key candidates)
        (packedColor width payload) count hcolors (ofKind kind key vertices)
        (hclique.sublist List.filter_sublist) hfilter
      have hlarge := hquota key
      omega
  | classes key masks =>
      obtain ⟨hcount, hclasses⟩ := Bool.and_eq_true_iff.mp hcheck
      have hsmall : masks.length < quota key := of_decide_eq_true hcount
      have hfilter : ofKind kind key vertices ⊆ ofKind kind key candidates := by
        intro vertex hv
        obtain ⟨hmem, hk⟩ := List.mem_filter.mp hv
        exact List.mem_filter.mpr ⟨hsub hmem, hk⟩
      have hbound := classesCheck_bound relation (ofKind kind key candidates) masks
        hclasses (ofKind kind key vertices) (hclique.sublist List.filter_sublist) hfilter
      have hlarge := hquota key
      omega
  | split pivot left right ihleft ihright =>
      obtain ⟨hleft, hright⟩ := Bool.and_eq_true_iff.mp hcheck
      by_cases hpivot : pivot ∈ vertices
      · have herased : Clique relation (vertices.erase pivot) :=
          hclique.sublist List.erase_sublist
        have hneighbors : vertices.erase pivot ⊆ neighbors relation candidates pivot := by
          intro vertex hv
          have hmem : vertex ∈ vertices := List.mem_of_mem_erase hv
          have hne : vertex ≠ pivot := by
            intro heq
            subst vertex
            exact hclique.1.not_mem_erase hv
          exact List.mem_filter.mpr ⟨hsub hmem, Bool.and_eq_true_iff.mpr
            ⟨decide_eq_true hne, hclique.2 pivot hpivot vertex hmem hne.symm⟩⟩
        have hremaining : ∀ key, remainingQuota kind quota pivot key ≤
            (ofKind kind key (vertices.erase pivot)).length := by
          intro key
          rw [ofKind_erase_length kind key vertices pivot hpivot]
          exact Nat.sub_le_sub_right (hquota key) _
        exact ihright _ _ hright _ herased hneighbors hremaining
      · have hwithout : vertices ⊆ without candidates pivot := by
          intro vertex hv
          refine List.mem_filter.mpr ⟨hsub hv, decide_eq_true ?_⟩
          intro heq
          exact hpivot (heq ▸ hv)
        exact ihleft _ _ hleft _ hclique hwithout hquota


end Papers.RationalityTen.CliqueExclusion
