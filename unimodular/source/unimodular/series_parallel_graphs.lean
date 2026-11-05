module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The graph dependency in the series--parallel characterization

The graph is an ordinary finite simple graph. A long induced cycle is described
by an injective open path and its closing vertex; a domino is described by its
exact six-vertex induced adjacency matrix. Neither forbidden configuration is
identified with series--parallelness by definition.
-/

namespace Unimodular.SeriesParallel

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- An injectively embedded induced path with `length` edges. -/
structure InducedPath where
  length : ℕ
  vertex : Fin (length + 1) → V
  injective : Function.Injective vertex
  adjacent : ∀ i j, G.Adj (vertex i) (vertex j) ↔
    i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- The forbidden long cycle is precisely an induced cycle on at least six
vertices: an induced path on at least five vertices and one closing vertex. -/
def HasLongInducedCycle : Prop :=
  ∃ p : InducedPath G, 4 ≤ p.length ∧
    ∃ z : V, (∀ i, z ≠ p.vertex i) ∧
      ∀ i, G.Adj z (p.vertex i) ↔ i.val = 0 ∨ i.val = p.length

/-- The biadjacency matrix of two squares sharing one edge. -/
def dominoCross (i j : Fin 3) : Prop :=
  ¬(i = 0 ∧ j = 2) ∧ ¬(i = 2 ∧ j = 0)

/-- An induced domino, with every edge and nonedge specified. -/
structure InducedDomino where
  left : Fin 3 → V
  right : Fin 3 → V
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  disjoint : ∀ i j, left i ≠ right j
  left_nonadjacent : ∀ i j, ¬G.Adj (left i) (left j)
  right_nonadjacent : ∀ i j, ¬G.Adj (right i) (right j)
  cross : ∀ i j, G.Adj (left i) (right j) ↔ dominoCross i j

/-- An isolated vertex, an ordinary pendant vertex, or two distinct vertices
with identical full open neighborhoods. -/
def HasReduction : Prop :=
  (∃ v, ∀ w, ¬G.Adj v w) ∨
  (∃ v w, ∀ z, G.Adj v z ↔ z = w) ∨
  (∃ v w, v ≠ w ∧ ∀ z, G.Adj v z ↔ G.Adj w z)

/-- Breadth-first layers, stated without assuming any graph elimination fact. -/
structure Layering where
  root : V
  level : V → ℕ
  zero_iff : ∀ v, level v = 0 ↔ v = root
  adjacent : ∀ {v w}, G.Adj v w →
    level v + 1 = level w ∨ level w + 1 = level v
  predecessor : ∀ v, level v ≠ 0 →
    ∃ w, G.Adj w v ∧ level w + 1 = level v

namespace Layering

variable {G} (L : Layering G)

def predecessors (v : V) : Set V :=
  {w | G.Adj w v ∧ L.level w + 1 = L.level v}

def upper (i : ℕ) : Set V := {v | i ≤ L.level v}

lemma not_adj_of_level_eq {v w : V} (h : L.level v = L.level w) :
    ¬G.Adj v w := by
  intro hvw
  rcases L.adjacent hvw with h' | h' <;> omega

lemma not_adj_of_level_gap {v w : V} (h : L.level v + 1 < L.level w) :
    ¬G.Adj v w := by
  intro hvw
  rcases L.adjacent hvw with h' | h' <;> omega

lemma predecessors_nonempty {v : V} (h : L.level v ≠ 0) :
    (L.predecessors v).Nonempty := L.predecessor v h

end Layering

/-- The elementary finite laminar-family argument behind the last-layer
reduction. It gives equal incidences, not merely equal neighborhood sizes. -/
theorem minimal_laminar_family {A B : Type*} [Fintype B] [Nonempty B]
    [DecidableEq A] (N : B → Finset A)
    (hne : ∀ b, (N b).Nonempty)
    (hlam : ∀ b c, Disjoint (N b) (N c) ∨ N b ⊆ N c ∨ N c ⊆ N b) :
    ∃ b, (N b).card = 1 ∨
      ∃ a ∈ N b, ∃ a' ∈ N b, a ≠ a' ∧
        ∀ c, a ∈ N c ↔ a' ∈ N c := by
  classical
  obtain ⟨b, _, hb⟩ := Finset.univ.exists_min_image
    (fun b => (N b).card) Finset.univ_nonempty
  refine ⟨b, ?_⟩
  by_cases hcard : (N b).card = 1
  · exact Or.inl hcard
  right
  have hpos := Finset.card_pos.mpr (hne b)
  obtain ⟨a, ha, a', ha', hne'⟩ := Finset.one_lt_card.mp (by omega : 1 < (N b).card)
  refine ⟨a, ha, a', ha', hne', ?_⟩
  have hcontain : ∀ c, ∀ x ∈ N b, x ∈ N c → N b ⊆ N c := by
    intro c x hxb hxc
    rcases hlam b c with hd | hbc | hcb
    · exact False.elim (Finset.disjoint_left.mp hd hxb hxc)
    · exact hbc
    · have hcard' := hb c (Finset.mem_univ c)
      have heq : N c = N b := Finset.eq_of_subset_of_card_le hcb hcard'
      exact heq ▸ Finset.Subset.refl _
  intro c
  exact ⟨fun h => hcontain c a ha h ha', fun h => hcontain c a' ha' h ha⟩

/-- A common neighbor turns two overlapping, incomparable neighborhoods into
an actual induced domino. The supplied coloring excludes all within-side edges. -/
theorem domino_of_overlap (c : G.Coloring Bool)
    (a₀ a₁ a₂ b₀ b₁ z : V)
    (ha : c a₀ = c a₁ ∧ c a₀ = c a₂)
    (hb : c b₀ = c b₁ ∧ c b₀ = c z)
    (hza₀ : G.Adj z a₀) (hza₁ : G.Adj z a₁) (hza₂ : G.Adj z a₂)
    (h₀₀ : G.Adj a₀ b₀) (h₀₁ : G.Adj a₀ b₁)
    (h₁₀ : G.Adj a₁ b₀) (hn₁₁ : ¬G.Adj a₁ b₁)
    (hn₂₀ : ¬G.Adj a₂ b₀) (h₂₁ : G.Adj a₂ b₁) :
    Nonempty (InducedDomino G) := by
  have haa₀₁ : a₀ ≠ a₁ := by intro h; subst a₁; exact hn₁₁ h₀₁
  have haa₀₂ : a₀ ≠ a₂ := by intro h; subst a₂; exact hn₂₀ h₀₀
  have haa₁₂ : a₁ ≠ a₂ := by intro h; subst a₂; exact hn₂₀ h₁₀
  have hbb : b₀ ≠ b₁ := by intro h; subst b₁; exact hn₁₁ h₁₀
  have hbz₀ : b₀ ≠ z := by intro h; subst b₀; exact hn₂₀ hza₂.symm
  have hbz₁ : b₁ ≠ z := by intro h; subst b₁; exact hn₁₁ hza₁.symm
  have hc : c a₀ ≠ c b₀ := c.valid h₀₀
  have hacol : ∀ i : Fin 3, c (![a₁, a₀, a₂] i) = c a₀ := by
    intro i
    fin_cases i
    · exact ha.1.symm
    · rfl
    · exact ha.2.symm
  have hbcol : ∀ i : Fin 3, c (![b₀, z, b₁] i) = c b₀ := by
    intro i
    fin_cases i
    · rfl
    · exact hb.2.symm
    · exact hb.1.symm
  refine ⟨⟨![a₁, a₀, a₂], ![b₀, z, b₁], ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j hij
    exact hc ((hacol i).symm.trans ((congrArg c hij).trans (hbcol j)))
  · intro i j hij
    exact c.valid hij ((hacol i).trans (hacol j).symm)
  · intro i j hij
    exact c.valid hij ((hbcol i).trans (hbcol j).symm)
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [dominoCross, G.adj_comm]

/-- All upper neighborhoods in a same-color set with a common lower neighbor
are laminar when the graph has no induced domino. -/
theorem laminar_of_no_domino [DecidableEq V] (c : G.Coloring Bool)
    (hdomino : ¬Nonempty (InducedDomino G))
    (A : Finset V) (B : Set V) (z : V)
    (hA : ∀ a ∈ A, G.Adj z a)
    (hB : ∀ b ∈ B, c b = c z)
    (N : B → Finset V)
    (hN : ∀ b a, a ∈ N b ↔ a ∈ A ∧ G.Adj a b.val) :
    ∀ b b', Disjoint (N b) (N b') ∨ N b ⊆ N b' ∨ N b' ⊆ N b := by
  classical
  intro b b'
  by_contra h
  have hd : ¬Disjoint (N b) (N b') := fun hd => h (Or.inl hd)
  have hbc : ¬N b ⊆ N b' := fun hh => h (Or.inr (Or.inl hh))
  have hcb : ¬N b' ⊆ N b := fun hh => h (Or.inr (Or.inr hh))
  obtain ⟨a₀, ha₀, ha₀'⟩ := Finset.not_disjoint_iff.mp hd
  obtain ⟨a₁, ha₁, ha₁'⟩ := Finset.not_subset.mp hbc
  obtain ⟨a₂, ha₂, ha₂'⟩ := Finset.not_subset.mp hcb
  have ha₀A := (hN b a₀).mp ha₀
  have ha₁A := (hN b a₁).mp ha₁
  have ha₂A := (hN b' a₂).mp ha₂
  have ha₀b' := (hN b' a₀).mp ha₀'
  have hn₁ : ¬G.Adj a₁ b'.val := fun hh => ha₁' ((hN b' a₁).mpr ⟨ha₁A.1, hh⟩)
  have hn₂ : ¬G.Adj a₂ b.val := fun hh => ha₂' ((hN b a₂).mpr ⟨ha₂A.1, hh⟩)
  have hc₀ := c.valid (hA a₀ ha₀A.1)
  have hc₁ := c.valid (hA a₁ ha₁A.1)
  have hc₂ := c.valid (hA a₂ ha₂A.1)
  have hcolors : c a₀ = c a₁ ∧ c a₀ = c a₂ := by
    cases hza : c z <;> cases hca₀ : c a₀ <;>
      cases hca₁ : c a₁ <;> cases hca₂ : c a₂ <;> simp_all
  apply hdomino
  exact domino_of_overlap G c a₀ a₁ a₂ b.val b'.val z hcolors
    ⟨(hB b.val b.property).trans (hB b'.val b'.property).symm,
      hB b.val b.property⟩
    (hA a₀ ha₀A.1) (hA a₁ ha₁A.1) (hA a₂ ha₂A.1)
    ha₀A.2 ha₀b'.2 ha₁A.2 hn₁ hn₂ ha₂A.2

/-! ## SeriesParallelPaths -/

namespace InducedPath

variable {G}

/-- A shortest walk is induced: a chord would give a strictly shorter walk. -/
noncomputable def ofShortest {u v : V} (p : G.Walk u v)
    (hmin : ∀ q : G.Walk u v, p.length ≤ q.length) : InducedPath G where
  length := p.length
  vertex i := p.getVert i.val
  injective := by
    obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
    have hp : p.length = G.dist u v := le_antisymm (hq ▸ hmin q) (G.dist_le p)
    have hpath := p.isPath_of_length_eq_dist hp
    intro i j hij
    exact Fin.ext (hpath.getVert_injOn (Nat.le_of_lt_succ i.isLt)
      (Nat.le_of_lt_succ j.isLt) hij)
  adjacent := by
    intro i j
    constructor
    · intro hij
      have hne : i.val ≠ j.val := by
        intro heq
        apply hij.ne
        exact congrArg p.getVert heq
      rcases lt_or_gt_of_ne hne with hij' | hji'
      · have hshort := hmin ((p.take i.val).append ((p.drop j.val).cons hij))
        simp only [Walk.length_append, Walk.take_length, Walk.length_cons,
          Walk.drop_length, Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)] at hshort
        omega
      · have hshort := hmin ((p.take j.val).append ((p.drop i.val).cons hij.symm))
        simp only [Walk.length_append, Walk.take_length, Walk.length_cons,
          Walk.drop_length, Nat.min_eq_left (Nat.le_of_lt_succ j.isLt)] at hshort
        omega
    · rintro (hij | hji)
      · simpa only [← hij] using p.adj_getVert_succ (show i.val < p.length by omega)
      · have hh := p.adj_getVert_succ (show j.val < p.length by omega)
        simpa only [← hji] using hh.symm

/-- Reversing an induced path preserves its exact induced adjacency relation. -/
def reverse (p : InducedPath G) : InducedPath G where
  length := p.length
  vertex i := p.vertex i.rev
  injective := p.injective.comp Fin.rev_injective
  adjacent := by
    intro i j
    rw [p.adjacent]
    simp only [Fin.val_rev]
    omega

/-- Attach a new initial vertex whose only neighbor on the old path is its
initial vertex. -/
def prepend (p : InducedPath G) (z : V)
    (hne : ∀ i, z ≠ p.vertex i)
    (hadj : ∀ i, G.Adj z (p.vertex i) ↔ i.val = 0) : InducedPath G where
  length := p.length + 1
  vertex := Fin.cases z p.vertex
  injective := by
    intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · rfl
    · simp only [Fin.cases_zero, Fin.cases_succ] at hij
      exact False.elim (hne _ hij)
    · simp only [Fin.cases_zero, Fin.cases_succ] at hij
      exact False.elim (hne _ hij.symm)
    · simp only [Fin.cases_succ] at hij
      exact congrArg Fin.succ (p.injective hij)
  adjacent := by
    intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp
    · simp only [Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ]
      rw [hadj]
      omega
    · simp only [Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ]
      rw [G.adj_comm, hadj]
      omega
    · simp only [Fin.cases_succ, Fin.val_succ]
      rw [p.adjacent]
      omega

/-- Attach a final vertex under the corresponding exact adjacency condition. -/
def append (p : InducedPath G) (z : V)
    (hne : ∀ i, z ≠ p.vertex i)
    (hadj : ∀ i, G.Adj z (p.vertex i) ↔ i.val = p.length) : InducedPath G :=
  (p.reverse.prepend z (fun i => hne i.rev) (by
    intro i
    change Fin (p.length + 1) at i
    change G.Adj z (p.vertex i.rev) ↔ i.val = 0
    rw [hadj]
    simp only [Fin.val_rev]
    omega)).reverse

end InducedPath

/-- Breadth-first distance layers exist for every connected bipartite graph. -/
noncomputable def Layering.ofConnectedBipartite (hconn : G.Connected)
    (c : G.Coloring Bool) (r : V) : Layering G where
  root := r
  level := G.dist r
  zero_iff := by
    intro v
    rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable]
    simp only [hconn r v, not_true_eq_false, or_false]
    exact eq_comm
  adjacent := by
    intro v w hvw
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist r v
    obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist r w
    have hv := c.even_length_iff_congr p
    have hw := c.even_length_iff_congr q
    have hne : G.dist r v ≠ G.dist r w := by
      intro heq
      have hc : c v = c w := by
        rw [hp, heq] at hv
        rw [hq] at hw
        cases hcr : c r <;> cases hcv : c v <;> cases hcw : c w <;> simp_all
      exact c.valid hvw hc
    rcases hvw.diff_dist_adj (u := r) with h | h | h
    · exact False.elim (hne h.symm)
    · exact Or.inl h.symm
    · right
      have hwv := hvw.symm.diff_dist_adj (u := r)
      rcases hwv with h' | h' | h'
      · exact False.elim (hne h')
      · exact h'.symm
      · omega
  predecessor := by
    intro v hv
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist r v
    have hn : 0 < p.length := by omega
    let w := p.getVert (p.length - 1)
    have hwp : G.Adj w v := by
      have h := p.adj_getVert_succ (show p.length - 1 < p.length by omega)
      simpa [w, Nat.sub_add_cancel hn] using h
    have hdist : G.dist r w ≤ p.length - 1 := by
      have h := G.dist_le (p.take (p.length - 1))
      simpa [w, Walk.take_length, Nat.min_eq_left (Nat.sub_le _ _)] using h
    have htriangle := hconn.dist_triangle (u := r) (v := w) (w := v)
    have hdistwv : G.dist w v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwp
    exact ⟨w, hwp, by omega⟩

/-! ## SeriesParallelLayers -/

namespace Layering

variable {G} (L : Layering G)

/-- Connectivity inside the actual induced subgraph on levels at least `i`,
expressed by an ordinary walk all of whose vertices lie there. -/
def UpperConnected (i : ℕ) (x y : V) : Prop :=
  ∃ p : G.Walk x y, ∀ v ∈ p.support, i ≤ L.level v

lemma upperConnected_refl {i : ℕ} {x : V} (hx : i ≤ L.level x) :
    L.UpperConnected i x x := by
  refine ⟨Walk.nil, ?_⟩
  simpa using hx

lemma UpperConnected.symm {L : Layering G} {i : ℕ} {x y : V} (h : L.UpperConnected i x y) :
    L.UpperConnected i y x := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

lemma UpperConnected.trans {L : Layering G} {i : ℕ} {x y z : V}
    (h : L.UpperConnected i x y) (h' : L.UpperConnected i y z) :
    L.UpperConnected i x z := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  refine ⟨p.append q, ?_⟩
  intro v hv
  rcases (Walk.mem_support_append_iff p q).mp hv with hv | hv
  · exact hp v hv
  · exact hq v hv

lemma upperConnected_of_adj {i : ℕ} {x y : V}
    (h : G.Adj x y) (hx : i ≤ L.level x) (hy : i ≤ L.level y) :
    L.UpperConnected i x y := by
  refine ⟨h.toWalk, ?_⟩
  intro v hv
  simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> assumption

/-- Vertices at the same level in one upper component have the same full
predecessor set. This is a proved intermediate property, never a definition of
the forbidden-subgraph condition. -/
def UniformPredecessors : Prop :=
  ∀ i x y, L.level x = i → L.level y = i → L.UpperConnected i x y →
    L.predecessors x = L.predecessors y

/-- Adjacent levels have opposite parity, giving the usual bipartition. -/
def parityColor : G.Coloring Bool :=
  Coloring.mk (fun v => L.level v % 2 = 0) (by
    intro v w hvw
    rcases L.adjacent hvw with h | h <;>
      simp only [ne_eq, decide_eq_decide] <;> omega)

/-- The last-layer argument is completely finite. Once predecessor equality
has been proved, excluding the exact six-vertex domino gives a pendant vertex
or twins; the rank-zero case gives an isolated vertex. -/
theorem hasReduction_of_uniformPredecessors [Fintype V]
    (hpred : L.UniformPredecessors)
    (hdomino : ¬Nonempty (InducedDomino G)) : HasReduction G := by
  classical
  haveI : Nonempty V := ⟨L.root⟩
  obtain ⟨x, _, hx⟩ := Finset.univ.exists_max_image L.level Finset.univ_nonempty
  let k := L.level x
  have hmax : ∀ v, L.level v ≤ k := fun v => hx v (Finset.mem_univ v)
  by_cases hk0 : k = 0
  · left
    refine ⟨x, ?_⟩
    intro v hv
    have hx' := hmax x
    have hv' := hmax v
    rcases L.adjacent hv with h | h <;> omega
  by_cases hk1 : k = 1
  · right; left
    refine ⟨x, L.root, ?_⟩
    intro v
    constructor
    · intro hv
      have hx' := hmax x
      have hv' := hmax v
      have hlev : L.level v = 0 := by
        rcases L.adjacent hv with h | h <;> omega
      exact (L.zero_iff v).mp hlev
    · rintro rfl
      obtain ⟨w, hwx, hw⟩ := L.predecessor x (by exact hk0)
      have hwr : w = L.root := (L.zero_iff w).mp (by omega)
      simpa [hwr] using hwx.symm
  have hk2 : 2 ≤ k := by omega
  let C : Set V := {v | L.UpperConnected (k - 1) x v}
  let A : Finset V := Finset.univ.filter (fun v => L.level v = k - 1 ∧ v ∈ C)
  let B : Set V := {v | L.level v = k ∧ v ∈ C}
  have hxC : x ∈ C := L.upperConnected_refl (by omega)
  haveI : Nonempty B := ⟨⟨x, rfl, hxC⟩⟩
  haveI : Fintype B := Fintype.ofFinite B
  let N : B → Finset V := fun b => A.filter (fun a => G.Adj a b.val)
  have hN : ∀ b a, a ∈ N b ↔ a ∈ A ∧ G.Adj a b.val := by
    intro b a
    exact Finset.mem_filter
  have hAnonempty : A.Nonempty := by
    obtain ⟨a, hax, ha⟩ := L.predecessor x hk0
    have haL : L.level a = k - 1 := by omega
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, haL, ?_⟩⟩
    exact hxC.trans (L.upperConnected_of_adj hax.symm (by omega) (by omega))
  have hNnonempty : ∀ b, (N b).Nonempty := by
    intro b
    obtain ⟨a, hab, ha⟩ := L.predecessor b.val (by have := b.property.1; omega)
    have haL : L.level a = k - 1 := by have := b.property.1; omega
    have haC : a ∈ C := b.property.2.trans
      (L.upperConnected_of_adj hab.symm (by have := b.property.1; omega) (by omega))
    exact ⟨a, (hN b a).mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ a, haL, haC⟩, hab⟩⟩
  obtain ⟨a₀, ha₀⟩ := hAnonempty
  have ha₀' := (Finset.mem_filter.mp ha₀).2
  obtain ⟨z, hza₀, hz⟩ := L.predecessor a₀ (by omega)
  have hzL : L.level z = k - 2 := by omega
  have hA : ∀ a ∈ A, G.Adj z a := by
    intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    have hc : L.UpperConnected (k - 1) a₀ a :=
      (ha₀'.2.symm).trans ha'.2
    have heq := hpred (k - 1) a₀ a ha₀'.1 ha'.1 hc
    have hmem : z ∈ L.predecessors a₀ := ⟨hza₀, hz⟩
    exact ((Set.ext_iff.mp heq z).mp hmem).1
  have hB : ∀ b ∈ B, L.parityColor b = L.parityColor z := by
    intro b hb
    change decide (L.level b % 2 = 0) = decide (L.level z % 2 = 0)
    rw [hb.1, hzL]
    simp only [decide_eq_decide]
    omega
  have hlam := laminar_of_no_domino G L.parityColor hdomino A B z hA hB N hN
  obtain ⟨b, hsingle | ⟨a, ha, a', ha', hne, hsame⟩⟩ :=
    minimal_laminar_family N hNnonempty hlam
  · right; left
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hsingle
    refine ⟨b.val, w, ?_⟩
    intro v
    have hfull : G.Adj b.val v ↔ v ∈ N b := by
      constructor
      · intro hbv
        have hvL : L.level v = k - 1 := by
          have htop := b.property.1
          have hvmax := hmax v
          rcases L.adjacent hbv with h | h <;> omega
        have hvC : v ∈ C := b.property.2.trans
          (L.upperConnected_of_adj hbv (by have := b.property.1; omega) (by omega))
        exact (hN b v).mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ v, hvL, hvC⟩, hbv.symm⟩
      · exact fun hv => ((hN b v).mp hv).2.symm
    rw [hfull, hw, Finset.mem_singleton]
  · right; right
    have haA := (hN b a).mp ha
    have ha'A := (hN b a').mp ha'
    have hal := (Finset.mem_filter.mp haA.1).2
    have ha'l := (Finset.mem_filter.mp ha'A.1).2
    have heq := hpred (k - 1) a a' hal.1 ha'l.1
      ((hal.2.symm).trans ha'l.2)
    refine ⟨a, a', hne, ?_⟩
    have transfer : ∀ u v, u ∈ A → v ∈ A →
        L.predecessors u = L.predecessors v →
        (∀ b' : B, u ∈ N b' ↔ v ∈ N b') →
        ∀ t, G.Adj u t → G.Adj v t := by
      intro u v hu hv hp hs t hut
      have hu' := (Finset.mem_filter.mp hu).2
      have hv' := (Finset.mem_filter.mp hv).2
      rcases L.adjacent hut with h | h
      · have htL : L.level t = k := by omega
        have htC : t ∈ C := hu'.2.trans
          (L.upperConnected_of_adj hut (by omega) (by omega))
        let t' : B := ⟨t, htL, htC⟩
        have huN : u ∈ N t' := (hN t' u).mpr ⟨hu, hut⟩
        exact ((hN t' v).mp ((hs t').mp huN)).2
      · have hmem : t ∈ L.predecessors u := ⟨hut.symm, h⟩
        exact (((Set.ext_iff.mp hp t).mp hmem).1).symm
    intro t
    exact ⟨transfer a a' haA.1 ha'A.1 heq hsame t,
      transfer a' a ha'A.1 haA.1 heq.symm (fun b' => (hsame b').symm) t⟩

end Layering

/-! ## SeriesParallelCycles -/

namespace InducedPath

variable {G}

private lemma boundary_cases {n : ℕ} (i : Fin (n + 3)) :
    i = 0 ∨ i = Fin.last (n + 2) ∨
      ∃ j : Fin (n + 1), i = j.castSucc.succ := by
  cases i using Fin.cases
  · exact Or.inl rfl
  · rename_i i
    cases i using Fin.lastCases
    · exact Or.inr (Or.inl rfl)
    · rename_i i
      exact Or.inr (Or.inr ⟨i, rfl⟩)

def sandwichVertex (p : InducedPath G) (u w : V) :
    Fin (p.length + 3) → V := Fin.cases u (Fin.lastCases w p.vertex)

@[simp] private lemma sandwichVertex_zero (p : InducedPath G) (u w : V) :
    sandwichVertex p u w 0 = u := rfl

@[simp] private lemma sandwichVertex_last (p : InducedPath G) (u w : V) :
    sandwichVertex p u w (Fin.last (p.length + 2)) = w := by
  change Fin.lastCases w p.vertex (Fin.last (p.length + 1)) = w
  exact Fin.lastCases_last

@[simp] private lemma sandwichVertex_middle (p : InducedPath G) (u w : V)
    (i : Fin (p.length + 1)) : sandwichVertex p u w i.castSucc.succ = p.vertex i := by
  simp [sandwichVertex]

/-- Put one new vertex at each end of an induced path. -/
def sandwich (p : InducedPath G) (u w : V)
    (huw : u ≠ w)
    (hu : ∀ i, u ≠ p.vertex i) (hw : ∀ i, w ≠ p.vertex i)
    (huadj : ∀ i, G.Adj u (p.vertex i) ↔ i.val = 0)
    (hwadj : ∀ i, G.Adj w (p.vertex i) ↔ i.val = p.length)
    (hunw : ¬G.Adj u w) : InducedPath G where
  length := p.length + 2
  vertex := sandwichVertex p u w
  injective := by
    intro i j hij
    rcases boundary_cases i with rfl | rfl | ⟨i, rfl⟩ <;>
      rcases boundary_cases j with rfl | rfl | ⟨j, rfl⟩ <;>
      simp only [sandwichVertex_zero, sandwichVertex_last, sandwichVertex_middle] at hij
    · rfl
    · exact False.elim (huw hij)
    · exact False.elim (hu _ hij)
    · exact False.elim (huw hij.symm)
    · rfl
    · exact False.elim (hw _ hij)
    · exact False.elim (hu _ hij.symm)
    · exact False.elim (hw _ hij.symm)
    · exact congrArg (fun i : Fin (p.length + 1) => i.castSucc.succ) (p.injective hij)
  adjacent := by
    intro i j
    rcases boundary_cases i with rfl | rfl | ⟨i, rfl⟩ <;>
      rcases boundary_cases j with rfl | rfl | ⟨j, rfl⟩ <;>
      simp only [sandwichVertex_zero, sandwichVertex_last, sandwichVertex_middle,
        Fin.val_zero, Fin.val_last, Fin.val_succ, Fin.val_castSucc]
    · simp
    · change G.Adj u w ↔ 0 + 1 = p.length + 2 ∨ p.length + 2 + 1 = 0
      simp only [hunw, false_iff]
      omega
    · change G.Adj u (p.vertex j) ↔ 0 + 1 = j.val + 1 ∨ j.val + 1 + 1 = 0
      rw [huadj]
      omega
    · change G.Adj w u ↔ p.length + 2 + 1 = 0 ∨ 0 + 1 = p.length + 2
      rw [G.adj_comm]
      simp only [hunw, false_iff]
      omega
    · simp
    · change G.Adj w (p.vertex j) ↔ p.length + 2 + 1 = j.val + 1 ∨
        j.val + 1 + 1 = p.length + 2
      rw [hwadj]
      omega
    · change G.Adj (p.vertex i) u ↔ i.val + 1 + 1 = 0 ∨ 0 + 1 = i.val + 1
      rw [G.adj_comm, huadj]
      omega
    · change G.Adj (p.vertex i) w ↔ i.val + 1 + 1 = p.length + 2 ∨
        p.length + 2 + 1 = i.val + 1
      rw [G.adj_comm, hwadj]
      omega
    · change G.Adj (p.vertex i) (p.vertex j) ↔
        i.val + 1 + 1 = j.val + 1 ∨ j.val + 1 + 1 = i.val + 1
      rw [p.adjacent]
      omega

/-- A four-edge closure of an induced path gives a genuine induced long cycle.
This is the closure used when two predecessor neighborhoods are incomparable. -/
theorem longCycle_of_three_vertex_closure (p : InducedPath G)
    (hlen : 2 ≤ p.length) (u w z : V)
    (huw : u ≠ w)
    (hu : ∀ i, u ≠ p.vertex i) (hw : ∀ i, w ≠ p.vertex i)
    (huadj : ∀ i, G.Adj u (p.vertex i) ↔ i.val = 0)
    (hwadj : ∀ i, G.Adj w (p.vertex i) ↔ i.val = p.length)
    (hunw : ¬G.Adj u w)
    (hzu : G.Adj z u) (hzw : G.Adj z w)
    (hz : ∀ i, z ≠ p.vertex i)
    (hznadj : ∀ i, ¬G.Adj z (p.vertex i)) : HasLongInducedCycle G := by
  let q := p.sandwich u w huw hu hw huadj hwadj hunw
  refine ⟨q, by change 4 ≤ p.length + 2; omega, z, ?_, ?_⟩
  · intro i
    rcases boundary_cases i with rfl | rfl | ⟨i, rfl⟩
    · simpa only [q, sandwich, sandwichVertex_zero] using hzu.ne
    · simpa only [q, sandwich, sandwichVertex_last] using hzw.ne
    · simpa only [q, sandwich, sandwichVertex_middle] using hz i
  · intro i
    rcases boundary_cases i with rfl | rfl | ⟨i, rfl⟩ <;>
      simp only [q, sandwich, sandwichVertex_zero, sandwichVertex_last,
        sandwichVertex_middle, Fin.val_zero, Fin.val_last, Fin.val_succ, Fin.val_castSucc]
    · simp only [hzu, true_iff, true_or]
    · simp only [hzw, true_iff, or_true]
    · change G.Adj z (p.vertex i) ↔ i.val + 1 = 0 ∨ i.val + 1 = p.length + 2
      simp only [hznadj, false_iff]
      omega

end InducedPath

/-! ## SeriesParallelPredecessors -/

namespace Layering

variable {G} (L : Layering G)

/-- The local obstruction in the breadth-first argument. All interior path
vertices are strictly above its endpoint layer. Distinct predecessor sets then
force an induced long cycle or an induced domino. -/
private theorem strict_excursion_contradiction
    (hcycle : ¬HasLongInducedCycle G) (hdomino : ¬Nonempty (InducedDomino G))
    (p : InducedPath G) (hlen : 2 ≤ p.length) (heven : Even p.length)
    (n : ℕ) (hx : L.level (p.vertex 0) = n)
    (hy : L.level (p.vertex (Fin.last p.length)) = n)
    (hint : ∀ i, 0 < i.val → i.val < p.length → n < L.level (p.vertex i))
    (u w z : V) (huL : L.level u + 1 = n) (hwL : L.level w + 1 = n)
    (hzL : L.level z + 2 = n)
    (hux : G.Adj u (p.vertex 0))
    (hwy : G.Adj w (p.vertex (Fin.last p.length)))
    (huny : ¬G.Adj u (p.vertex (Fin.last p.length)))
    (hzu : G.Adj z u) (hzw : G.Adj z w) : False := by
  have hlevels : ∀ i, n ≤ L.level (p.vertex i) := by
    intro i
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      simpa [hi, hx]
    by_cases hil : i.val = p.length
    · have hi : i = Fin.last p.length := Fin.ext hil
      simpa [hi, hy]
    exact (hint i (by omega) (by omega)).le
  have hu : ∀ i, u ≠ p.vertex i := by
    intro i hi
    have hl := hlevels i
    rw [← hi] at hl
    omega
  have hw : ∀ i, w ≠ p.vertex i := by
    intro i hi
    have hl := hlevels i
    rw [← hi] at hl
    omega
  have hz : ∀ i, z ≠ p.vertex i := by
    intro i hi
    have hl := hlevels i
    rw [← hi] at hl
    omega
  have hznadj : ∀ i, ¬G.Adj z (p.vertex i) := by
    intro i
    exact L.not_adj_of_level_gap (by have := hlevels i; omega)
  have huadj : ∀ i, G.Adj u (p.vertex i) ↔ i.val = 0 := by
    intro i
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      simp [hi, hux]
    by_cases hil : i.val = p.length
    · have hi : i = Fin.last p.length := Fin.ext hil
      simp [hi, huny, show p.length ≠ 0 by omega]
    have hn := L.not_adj_of_level_gap
      (show L.level u + 1 < L.level (p.vertex i) by
        have := hint i (by omega) (by omega); omega)
    simp [hn, hi0]
  have huw : u ≠ w := by
    intro heq
    subst w
    exact huny hwy
  have hunw : ¬G.Adj u w := L.not_adj_of_level_eq (by omega)
  by_cases hwx : G.Adj w (p.vertex 0)
  · have hwends : ∀ i, G.Adj w (p.vertex i) ↔ i.val = 0 ∨ i.val = p.length := by
      intro i
      by_cases hi0 : i.val = 0
      · have hi : i = 0 := Fin.ext hi0
        simp [hi, hwx]
      by_cases hil : i.val = p.length
      · have hi : i = Fin.last p.length := Fin.ext hil
        simp [hi, hwy]
      have hn := L.not_adj_of_level_gap
        (show L.level w + 1 < L.level (p.vertex i) by
          have := hint i (by omega) (by omega); omega)
      simp [hn, hi0, hil]
    by_cases hl4 : 4 ≤ p.length
    · exact hcycle ⟨p, hl4, w, hw, hwends⟩
    have hp2 : p.length = 2 := by
      obtain ⟨d, hd⟩ := heven
      omega
    let t := p.vertex ⟨1, by omega⟩
    have hxt : G.Adj (p.vertex 0) t := (p.adjacent _ _).mpr (Or.inl rfl)
    have hyt : G.Adj (p.vertex (Fin.last p.length)) t := by
      apply (p.adjacent _ _).mpr
      right
      simpa using hp2.symm
    have htL : L.level t = n + 1 := by
      have hint' := hint ⟨1, by omega⟩ (by change 0 < 1; omega)
        (by change 1 < p.length; omega)
      rcases L.adjacent hxt with h | h <;> dsimp [t] at * <;> omega
    have ha : L.parityColor (p.vertex 0) = L.parityColor z ∧
        L.parityColor (p.vertex 0) = L.parityColor (p.vertex (Fin.last p.length)) := by
      change decide (L.level (p.vertex 0) % 2 = 0) = decide (L.level z % 2 = 0) ∧
        decide (L.level (p.vertex 0) % 2 = 0) =
          decide (L.level (p.vertex (Fin.last p.length)) % 2 = 0)
      simp only [decide_eq_decide]
      constructor <;> omega
    have hb : L.parityColor u = L.parityColor t ∧
        L.parityColor u = L.parityColor w := by
      change decide (L.level u % 2 = 0) = decide (L.level t % 2 = 0) ∧
        decide (L.level u % 2 = 0) = decide (L.level w % 2 = 0)
      simp only [decide_eq_decide]
      constructor <;> omega
    apply hdomino
    exact domino_of_overlap G L.parityColor (p.vertex 0) z
      (p.vertex (Fin.last p.length)) u t w ha hb
      hwx hzw.symm hwy hux.symm hxt hzu
      (L.not_adj_of_level_gap (by omega))
      (fun h => huny h.symm) hyt
  · have hwadj : ∀ i, G.Adj w (p.vertex i) ↔ i.val = p.length := by
      intro i
      by_cases hi0 : i.val = 0
      · have hi : i = 0 := Fin.ext hi0
        simp [hi, hwx, show 0 ≠ p.length by omega]
      by_cases hil : i.val = p.length
      · have hi : i = Fin.last p.length := Fin.ext hil
        simp [hi, hwy]
      have hn := L.not_adj_of_level_gap
        (show L.level w + 1 < L.level (p.vertex i) by
          have := hint i (by omega) (by omega); omega)
      simp [hn, hil]
    exact hcycle (p.longCycle_of_three_vertex_closure hlen u w z huw hu hw
      huadj hwadj hunw hzu hzw hz hznadj)

end Layering

namespace Layering

variable {G} (L : Layering G)

/-- One layer of the predecessor-equality induction. A shortest counterexample
walk has no internal vertex on its endpoint level, so the preceding local
obstruction applies. -/
private theorem predecessors_subset_of_lower
    (hcycle : ¬HasLongInducedCycle G) (hdomino : ¬Nonempty (InducedDomino G))
    (n : ℕ) (hn : 0 < n)
    (hprev : ∀ u w, L.level u + 1 = n → L.level w + 1 = n →
      L.UpperConnected (n - 1) u w → L.predecessors u = L.predecessors w)
    (x y : V) (hx : L.level x = n) (hy : L.level y = n)
    (hxy : L.UpperConnected n x y) : L.predecessors x ⊆ L.predecessors y := by
  classical
  intro u hup
  by_contra hnu
  let U := L.upper n
  let H := G.induce U
  let Bad : ℕ → Prop := fun m =>
    ∃ (x y : U) (u : V), L.level x.val = n ∧ L.level y.val = n ∧
      u ∈ L.predecessors x.val ∧ u ∉ L.predecessors y.val ∧
      ∃ p : H.Walk x y, p.length = m
  have hbad : ∃ m, Bad m := by
    obtain ⟨p, hp⟩ := hxy
    let q := p.induce U hp
    refine ⟨q.length, ⟨x, hp _ p.start_mem_support⟩,
      ⟨y, hp _ p.end_mem_support⟩, u, hx, hy, hup, hnu, q, rfl⟩
  obtain ⟨x, y, u, hx, hy, hup, hnu, p, hp⟩ := Nat.find_spec hbad
  have hmin (x' y' : U) (u' : V)
      (hx' : L.level x'.val = n) (hy' : L.level y'.val = n)
      (hup' : u' ∈ L.predecessors x'.val) (hnu' : u' ∉ L.predecessors y'.val)
      (q : H.Walk x' y') : p.length ≤ q.length := by
    rw [hp]
    exact Nat.find_min' hbad ⟨x', y', u', hx', hy', hup', hnu', q, rfl⟩
  let p₀ := InducedPath.ofShortest p (hmin x y u hx hy hup hnu)
  let P : InducedPath G :=
    { length := p₀.length
      vertex := fun i => (p₀.vertex i).val
      injective := by
        intro i j hij
        exact p₀.injective (Subtype.ext hij)
      adjacent := p₀.adjacent }
  have hxP : L.level (P.vertex 0) = n := by
    change L.level (p.getVert 0).val = n
    simpa using hx
  have hyP : L.level (P.vertex (Fin.last P.length)) = n := by
    change L.level (p.getVert p.length).val = n
    simpa using hy
  have hint : ∀ i : Fin (P.length + 1), 0 < i.val → i.val < P.length →
      n < L.level (P.vertex i) := by
    intro i hi0 hil
    change n < L.level (p.getVert i.val).val
    have hge : n ≤ L.level (p.getVert i.val).val := (p.getVert i.val).property
    by_contra hgt
    have hieq : L.level (p.getVert i.val).val = n := by omega
    by_cases hui : u ∈ L.predecessors (p.getVert i.val).val
    · have hh := hmin (p.getVert i.val) y u hieq hy hui hnu (p.drop i.val)
      rw [Walk.drop_length] at hh
      change i.val < p.length at hil
      omega
    · have hh := hmin x (p.getVert i.val) u hx hieq hup hui (p.take i.val)
      rw [Walk.take_length] at hh
      change i.val < p.length at hil
      omega
  have hxne : x ≠ y := by
    intro h
    subst y
    exact hnu hup
  have hp0 : p.length ≠ 0 := fun h => hxne (p.eq_of_length_eq_zero h)
  have hp1 : p.length ≠ 1 := by
    intro h
    exact L.not_adj_of_level_eq (hx.trans hy.symm) (p.adj_of_length_eq_one h)
  have hlen : 2 ≤ P.length := by
    change 2 ≤ p.length
    omega
  let q := p.map (SimpleGraph.Embedding.induce U).toHom
  have heven : Even P.length := by
    have hcol : L.parityColor x.val = L.parityColor y.val := by
      change decide (L.level x.val % 2 = 0) = decide (L.level y.val % 2 = 0)
      rw [hx, hy]
    have hh := (L.parityColor.even_length_iff_congr q).mpr (by
      change (L.parityColor x.val = true ↔ L.parityColor y.val = true)
      rw [hcol])
    change Even p.length
    simpa only [q, Walk.length_map] using hh
  obtain ⟨w, hwy, hwL⟩ := L.predecessor y.val (by omega)
  have huny : ¬G.Adj u y.val := fun h => hnu ⟨h, hup.2.trans (hx.trans hy.symm)⟩
  have huw : u ≠ w := by
    intro h
    subst w
    exact huny hwy
  have hu0 : L.level u ≠ 0 := by
    intro hu0
    have hw0 : L.level w = 0 := by have := hup.2; omega
    exact huw ((L.zero_iff u).mp hu0 |>.trans ((L.zero_iff w).mp hw0).symm)
  have hxy' : L.UpperConnected (n - 1) x.val y.val := by
    refine ⟨q, ?_⟩
    intro v hv
    change v ∈ (p.map (SimpleGraph.Embedding.induce U).toHom).support at hv
    rw [Walk.support_map] at hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    have ha : n ≤ L.level a.val := a.property
    change n - 1 ≤ L.level a.val
    omega
  have hux' : L.UpperConnected (n - 1) u x.val :=
    L.upperConnected_of_adj hup.1 (by have := hup.2; omega) (by omega)
  have hyw' : L.UpperConnected (n - 1) y.val w :=
    L.upperConnected_of_adj hwy.symm (by omega) (by omega)
  have hpred := hprev u w (hup.2.trans hx) (hwL.trans hy)
    (hux'.trans (hxy'.trans hyw'))
  obtain ⟨z, hzu, hzL⟩ := L.predecessor u hu0
  have hzw : G.Adj z w := ((Set.ext_iff.mp hpred z).mp ⟨hzu, hzL⟩).1
  exact L.strict_excursion_contradiction hcycle hdomino P hlen heven n hxP hyP
    hint u w z (hup.2.trans hx) (hwL.trans hy)
    (by have := hup.2; omega) (by change G.Adj u (p.getVert 0).val; simpa using hup.1)
    (by change G.Adj w (p.getVert p.length).val; simpa using hwy)
    (by change ¬G.Adj u (p.getVert p.length).val; simpa using huny) hzu hzw

/-- No induced cycle of length at least six and no induced domino force
predecessor equality in every breadth-first layer. -/
theorem uniformPredecessors_of_forbidden
    (hcycle : ¬HasLongInducedCycle G) (hdomino : ¬Nonempty (InducedDomino G)) :
    L.UniformPredecessors := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro x y hx hy hxy
    by_cases hn : n = 0
    · have hxr := (L.zero_iff x).mp (hx.trans hn)
      have hyr := (L.zero_iff y).mp (hy.trans hn)
      rw [hxr, hyr]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hprev : ∀ u w, L.level u + 1 = n → L.level w + 1 = n →
        L.UpperConnected (n - 1) u w → L.predecessors u = L.predecessors w := by
      intro u w hu hw hconn
      exact ih (n - 1) (by omega) u w (by omega) (by omega) hconn
    exact Set.Subset.antisymm
      (L.predecessors_subset_of_lower hcycle hdomino n hnpos hprev x y hx hy hxy)
      (L.predecessors_subset_of_lower hcycle hdomino n hnpos hprev y x hy hx hxy.symm)

/-- The graph elimination theorem used by the integral fundamental-matrix
argument. Its hypotheses are exactly the two explicitly described forbidden
induced subgraphs. -/
theorem hasReduction_of_forbidden (L : Layering G) [Fintype V]
    (hcycle : ¬HasLongInducedCycle G) (hdomino : ¬Nonempty (InducedDomino G)) :
    HasReduction G :=
  L.hasReduction_of_uniformPredecessors
    (L.uniformPredecessors_of_forbidden hcycle hdomino) hdomino

end Layering

/-! ## SeriesParallelPruning -/

namespace InducedPath

variable {G} {W : Type*} {H : SimpleGraph W}

/-- Transport along an induced graph embedding preserves all path nonedges. -/
def map (p : InducedPath G) (f : G ↪g H) : InducedPath H where
  length := p.length
  vertex := f ∘ p.vertex
  injective := f.injective.comp p.injective
  adjacent := fun i j => f.map_adj_iff.trans (p.adjacent i j)

end InducedPath

namespace InducedDomino

variable {G} {W : Type*} {H : SimpleGraph W}

/-- Transport along an induced embedding preserves the full domino matrix. -/
def map (d : InducedDomino G) (f : G ↪g H) : InducedDomino H where
  left := f ∘ d.left
  right := f ∘ d.right
  left_injective := f.injective.comp d.left_injective
  right_injective := f.injective.comp d.right_injective
  disjoint := fun i j h => d.disjoint i j (f.injective h)
  left_nonadjacent := fun i j h => d.left_nonadjacent i j (f.map_adj_iff.mp h)
  right_nonadjacent := fun i j h => d.right_nonadjacent i j (f.map_adj_iff.mp h)
  cross := fun i j => f.map_adj_iff.trans (d.cross i j)

end InducedDomino

lemma HasLongInducedCycle.map {G : SimpleGraph V} {W : Type*} {H : SimpleGraph W}
    (h : HasLongInducedCycle G) (f : G ↪g H) : HasLongInducedCycle H := by
  obtain ⟨p, hp, z, hz, hadj⟩ := h
  exact ⟨p.map f, hp, f z, fun i h => hz i (f.injective h),
    fun i => f.map_adj_iff.trans (hadj i)⟩

/-- The finite bipartite graph elimination theorem, including disconnected
graphs. The proof reduces to one genuine connected component. -/
theorem hasReduction_of_forbidden [Fintype V] [Nonempty V]
    (c : G.Coloring Bool)
    (hcycle : ¬HasLongInducedCycle G) (hdomino : ¬Nonempty (InducedDomino G)) :
    HasReduction G := by
  classical
  let C := G.connectedComponentMk (Classical.choice (inferInstance : Nonempty V))
  let H := C.toSimpleGraph
  let f : H ↪g G := SimpleGraph.Embedding.induce C.supp
  let c' : H.Coloring Bool := c.comp C.toSimpleGraph_hom
  let r : C := ⟨C.out, C.out_eq⟩
  let L := Layering.ofConnectedBipartite H C.connected_toSimpleGraph c' r
  have hcycle' : ¬HasLongInducedCycle H := fun h => hcycle (h.map f)
  have hdomino' : ¬Nonempty (InducedDomino H) := fun ⟨d⟩ => hdomino ⟨d.map f⟩
  have hr := L.hasReduction_of_forbidden hcycle' hdomino'
  rcases hr with ⟨v, hv⟩ | ⟨v, w, hv⟩ | ⟨v, w, hvw, hv⟩
  · left
    refine ⟨v.val, ?_⟩
    intro z hz
    have hzC := C.mem_supp_of_adj_mem_supp v.property hz
    exact hv ⟨z, hzC⟩ hz
  · right; left
    refine ⟨v.val, w.val, ?_⟩
    intro z
    constructor
    · intro hz
      have hzC := C.mem_supp_of_adj_mem_supp v.property hz
      exact congrArg Subtype.val ((hv ⟨z, hzC⟩).mp hz)
    · rintro rfl
      exact (hv w).mpr rfl
  · right; right
    refine ⟨v.val, w.val, fun h => hvw (Subtype.ext h), ?_⟩
    intro z
    constructor
    · intro hz
      have hzC := C.mem_supp_of_adj_mem_supp v.property hz
      exact (hv ⟨z, hzC⟩).mp hz
    · intro hz
      have hzC := C.mem_supp_of_adj_mem_supp w.property hz
      exact (hv ⟨z, hzC⟩).mpr hz

/-- The three permitted vertex-deletion steps, relative to an actual finite
induced subgraph. -/
def Removable (S : Finset V) (v : V) : Prop :=
  (∀ z ∈ S, ¬G.Adj v z) ∨
  (∃ w ∈ S, ∀ z ∈ S, G.Adj v z ↔ z = w) ∨
  (∃ w ∈ S, v ≠ w ∧ ∀ z ∈ S, G.Adj v z ↔ G.Adj w z)

/-- A complete pruning certificate, built solely from isolated-vertex,
pendant-vertex, and twin-vertex deletions. -/
inductive Prunable [DecidableEq V] : Finset V → Prop
  | empty : Prunable ∅
  | step {S : Finset V} (v : V) (hv : v ∈ S) (hr : Removable G S v)
      (smaller : Prunable (S.erase v)) : Prunable S

/-- Every finite induced subgraph has a complete pruning certificate. This is
an unbounded induction over its number of vertices. -/
theorem prunable_of_forbidden [DecidableEq V]
    (c : G.Coloring Bool)
    (hcycle : ¬HasLongInducedCycle G) (hdomino : ¬Nonempty (InducedDomino G))
    (S : Finset V) : Prunable G S := by
  classical
  suffices ∀ n : ℕ, ∀ S : Finset V, S.card = n → Prunable G S from this S.card S rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro S hcard
    by_cases hs : S = ∅
    · subst S
      exact Prunable.empty
    have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    let H := G.induce (S : Set V)
    let f : H ↪g G := SimpleGraph.Embedding.induce (S : Set V)
    haveI : Nonempty (S : Set V) := ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
    let c' : H.Coloring Bool := c.comp f.toHom
    have hcy : ¬HasLongInducedCycle H := fun h => hcycle (h.map f)
    have hdom : ¬Nonempty (InducedDomino H) := fun ⟨d⟩ => hdomino ⟨d.map f⟩
    have hred := hasReduction_of_forbidden H c' hcy hdom
    have hrem : ∃ v ∈ S, Removable G S v := by
      rcases hred with ⟨v, hv⟩ | ⟨v, w, hv⟩ | ⟨v, w, hvw, hv⟩
      · exact ⟨v.val, v.property, Or.inl (fun z hz => hv ⟨z, hz⟩)⟩
      · refine ⟨v.val, v.property, Or.inr (Or.inl ⟨w.val, w.property, ?_⟩)⟩
        intro z hz
        exact (hv ⟨z, hz⟩).trans ⟨fun h => congrArg Subtype.val h,
          fun h => Subtype.ext h⟩
      · exact ⟨v.val, v.property, Or.inr (Or.inr ⟨w.val, w.property,
          fun h => hvw (Subtype.ext h), fun z hz => hv ⟨z, hz⟩⟩)⟩
    obtain ⟨v, hv, hr⟩ := hrem
    refine Prunable.step v hv hr (ih (S.erase v).card ?_ (S.erase v) rfl)
    rw [← hcard]
    exact Finset.card_erase_lt_of_mem hv

#print axioms Unimodular.SeriesParallel.Layering.uniformPredecessors_of_forbidden
#print axioms Unimodular.SeriesParallel.hasReduction_of_forbidden
#print axioms Unimodular.SeriesParallel.prunable_of_forbidden

end Unimodular.SeriesParallel
