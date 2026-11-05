module
public import graph_foundation.part008
public import shared_results.part004

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.SymbolicTheory -/
section

section




set_option autoImplicit false
noncomputable section

namespace FourPapers.Sublattice

open Classical Finset

variable {V : Type*} [DecidableEq V]

/-- Closure under precisely the implications satisfied by all members of F. -/
def cutImplicationClosed (F : Finset (Finset V)) (W : Finset V) : Prop :=
  ∀ u v, (∀ A ∈ F, u ∈ A → v ∈ A) → u ∈ W → v ∈ W

lemma exists_cut_separator (F : Finset (Finset V)) (W : Finset V)
    (hW : cutImplicationClosed F W) {u v : V} (hu : u ∈ W) (hv : v ∉ W) :
    ∃ A ∈ F, u ∈ A ∧ v ∉ A := by
  by_contra h
  have himp : ∀ A ∈ F, u ∈ A → v ∈ A := by
    intro A hA huA
    by_contra hvA
    exact h ⟨A,hA,huA,hvA⟩
  exact hv (hW u v himp hu)

/-- A finite lattice of cuts is determined by its binary implications.
The nonempty and proper hypotheses are exactly the source/sink conditions
in the network application; no unproved representation theorem is used. -/
theorem mem_cutFamily_of_implications
    (F : Finset (Finset V))
    (hunion : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ∩ B ∈ F)
    (W : Finset V) (hne : W.Nonempty) (hproper : ∃ t, t ∉ W)
    (hW : cutImplicationClosed F W) : W ∈ F := by
  obtain ⟨t,ht⟩ := hproper
  have hpart : ∀ u ∈ W, ∃ A ∈ F, u ∈ A ∧ A ⊆ W := by
    intro u hu
    let T := F.filter (fun A => u ∈ A)
    have hT : T.Nonempty := by
      obtain ⟨A,hA,huA,_⟩ := exists_cut_separator F W hW hu ht
      exact ⟨A,Finset.mem_filter.mpr ⟨hA,huA⟩⟩
    let A := T.inf' hT id
    have hAF : A ∈ F := by
      apply Finset.inf'_mem (F : Set (Finset V)) hinter T hT id
      intro B hB
      exact (Finset.mem_filter.mp hB).1
    have huA : u ∈ A := by
      apply (Finset.mem_inf' hT).mpr
      intro B hB
      exact (Finset.mem_filter.mp hB).2
    have hAW : A ⊆ W := by
      intro v hv
      by_contra hvW
      obtain ⟨B,hB,huB,hvB⟩ := exists_cut_separator F W hW hu hvW
      have hAB : A ⊆ B :=
        Finset.inf'_le id (Finset.mem_filter.mpr ⟨hB,huB⟩)
      exact hvB (hAB hv)
    exact ⟨A,hAF,huA,hAW⟩
  let A (u : {u // u ∈ W}) : Finset V := (hpart u.val u.property).choose
  have hA (u : {u // u ∈ W}) :
      A u ∈ F ∧ u.val ∈ A u ∧ A u ⊆ W :=
    (hpart u.val u.property).choose_spec
  have hatt : W.attach.Nonempty := by
    obtain ⟨u,hu⟩ := hne
    exact ⟨⟨u,hu⟩,by simp⟩
  let U := W.attach.sup' hatt A
  have hUF : U ∈ F := by
    apply Finset.sup'_mem (F : Set (Finset V)) hunion W.attach hatt A
    intro u _
    exact (hA u).1
  have hUW : U ⊆ W := Finset.sup'_le hatt A (fun u _ => (hA u).2.2)
  have hWU : W ⊆ U := by
    intro u hu
    have ha : A ⟨u,hu⟩ ⊆ U := Finset.le_sup' A (by simp)
    exact ha (hA ⟨u,hu⟩).2.1
  have heq : U = W := Finset.Subset.antisymm hUW hWU
  simpa only [heq] using hUF

theorem mem_cutFamily_iff_implications
    (F : Finset (Finset V))
    (hunion : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ∩ B ∈ F)
    (W : Finset V) (hne : W.Nonempty) (hproper : ∃ t, t ∉ W) :
    W ∈ F ↔ cutImplicationClosed F W := by
  constructor
  · intro h u v huv hu
    exact huv W h hu
  · exact mem_cutFamily_of_implications F hunion hinter W hne hproper

end FourPapers.Sublattice

end
end

section








set_option autoImplicit false
noncomputable section

namespace FourPapers.Sublattice

open Classical Finset
universe u v
variable {V : Type u} {E : Type v} [DecidableEq V]

/-- A finite directed walk, with its initial vertex fixed and its actual
terminal vertex retained in the type. -/
inductive CostWalk (src dst : E → V) (s : V) : V → Type (max u v)
  | nil : CostWalk src dst s s
  | snoc {w : V} (p : CostWalk src dst s w) (e : E) (he : src e = w) :
      CostWalk src dst s (dst e)

namespace CostWalk
variable {src dst : E → V} {s : V}

def cost (c : E → ℕ) : {w : V} → CostWalk src dst s w → ℕ
  | _, .nil => 0
  | _, .snoc p e _ => cost c p + c e

@[simp] lemma cost_nil (c : E → ℕ) : cost c (nil (src := src) (dst := dst) (s := s)) = 0 := rfl
@[simp] lemma cost_snoc (c : E → ℕ) {w : V} (p : CostWalk src dst s w)
    (e : E) (he : src e = w) : cost c (p.snoc e he) = cost c p + c e := rfl

/-- Every walk leaving a set crosses one of its directed boundary edges. -/
lemma exists_crossing (W : Finset V) (hs : s ∈ W) {w : V}
    (p : CostWalk src dst s w) (hw : w ∉ W) :
    ∃ e : E, src e ∈ W ∧ dst e ∉ W := by
  induction p with
  | nil => exact (hw hs).elim
  | @snoc w p e he ih =>
    by_cases hw' : w ∈ W
    · exact ⟨e,by simpa only [he] using hw',hw⟩
    · exact ih hw'

end CostWalk

section Shortest
variable (src dst : E → V) (s : V) (c : E → ℕ)
variable (reachable : ∀ w, Nonempty (CostWalk src dst s w))
include reachable

lemma exists_walkCost (w : V) : ∃ a : ℕ, ∃ p : CostWalk src dst s w, p.cost c = a := by
  obtain ⟨p⟩ := reachable w
  exact ⟨p.cost c,p,rfl⟩

def shortestCost (w : V) : ℕ := Nat.find (exists_walkCost src dst s c reachable w)

lemma exists_shortestWalk (w : V) :
    ∃ p : CostWalk src dst s w, p.cost c = shortestCost src dst s c reachable w :=
  Nat.find_spec (exists_walkCost src dst s c reachable w)

lemma shortestCost_le {w : V} (p : CostWalk src dst s w) :
    shortestCost src dst s c reachable w ≤ p.cost c :=
  Nat.find_min' (exists_walkCost src dst s c reachable w) ⟨p,rfl⟩

@[simp] lemma shortestCost_source :
    shortestCost src dst s c reachable s = 0 :=
  Nat.le_zero.mp (shortestCost_le src dst s c reachable CostWalk.nil)

lemma shortestCost_arc (e : E) :
    shortestCost src dst s c reachable (dst e) ≤
      shortestCost src dst s c reachable (src e) + c e := by
  obtain ⟨p,hp⟩ := exists_shortestWalk src dst s c reachable (src e)
  have h := shortestCost_le src dst s c reachable (p.snoc e rfl)
  simpa only [CostWalk.cost_snoc,hp] using h

lemma le_shortestCost (t : V) (m : ℕ)
    (h : ∀ p : CostWalk src dst s t, m ≤ p.cost c) :
    m ≤ shortestCost src dst s c reachable t := by
  obtain ⟨p,hp⟩ := exists_shortestWalk src dst s c reachable t
  simpa only [hp] using h p

end Shortest

section Packing
variable [Fintype V]
variable (src dst : E → V) (s t : V) (c : E → ℕ)
variable (reachable : ∀ w, Nonempty (CostWalk src dst s w))
include reachable

def distanceCut (r : ℕ) : Finset V :=
  Finset.univ.filter (fun w => shortestCost src dst s c reachable w < r)

@[simp] lemma mem_distanceCut (r : ℕ) (w : V) :
    w ∈ distanceCut src dst s c reachable r ↔
      shortestCost src dst s c reachable w < r := by simp [distanceCut]

/-- The distance-level cuts satisfy every implication represented by a
zero-cost arc, hence belong to the exact original finite lattice of cuts. -/
theorem distanceCut_mem
    (F : Finset (Finset V))
    (hunion : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ∩ B ∈ F)
    (himp : ∀ u v, (∀ A ∈ F, u ∈ A → v ∈ A) →
      ∃ e, src e = u ∧ dst e = v ∧ c e = 0)
    (m : ℕ) (hpath : ∀ p : CostWalk src dst s t, m ≤ p.cost c)
    (r : Fin m) :
    distanceCut src dst s c reachable (r.val+1) ∈ F := by
  have ht := le_shortestCost src dst s c reachable t m hpath
  apply mem_cutFamily_of_implications F hunion hinter
  · exact ⟨s,by simp⟩
  · refine ⟨t,?_⟩
    rw [mem_distanceCut]
    have hr := r.isLt
    omega
  · intro u v huv hu
    obtain ⟨e,he₁,he₂,he₀⟩ := himp u v huv
    have hd := shortestCost_arc src dst s c reachable e
    rw [he₁,he₂,he₀,add_zero] at hd
    rw [mem_distanceCut] at hu ⊢
    exact lt_of_le_of_lt hd hu

/-- Each edge crosses at most as many distance-level cuts as its integral
capacity. This is an exact finite counting statement, not a fractional bound. -/
theorem distanceCut_crossing_card (m : ℕ) (e : E) :
    (Finset.univ.filter (fun r : Fin m =>
      src e ∈ distanceCut src dst s c reachable (r.val+1) ∧
      dst e ∉ distanceCut src dst s c reachable (r.val+1))).card ≤ c e := by
  let D := shortestCost src dst s c reachable
  let R : Finset (Fin m) := Finset.univ.filter (fun r =>
    src e ∈ distanceCut src dst s c reachable (r.val+1) ∧
    dst e ∉ distanceCut src dst s c reachable (r.val+1))
  have bounds (r : {r // r ∈ R}) : D (src e) ≤ r.val.val ∧ r.val.val < D (dst e) := by
    have h := (Finset.mem_filter.mp r.property).2
    simp only [mem_distanceCut] at h
    change D (src e) < r.val.val+1 ∧ ¬D (dst e) < r.val.val+1 at h
    exact ⟨by omega,by omega⟩
  have hedge : D (dst e) ≤ D (src e)+c e :=
    shortestCost_arc src dst s c reachable e
  let f : {r // r ∈ R} → Fin (c e) := fun r =>
    ⟨r.val.val-D (src e),by
      have hr := bounds r
      omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    have h := congrArg Fin.val hab
    change a.val.val-D (src e) = b.val.val-D (src e) at h
    have ha := bounds a
    have hb := bounds b
    omega
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fin] using hc

/-- Integral cut packing from shortest paths, with the prescribed finite
cut family retained exactly. -/
theorem cutPacking_of_walkBound
    (F : Finset (Finset V))
    (hunion : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ∩ B ∈ F)
    (himp : ∀ u v, (∀ A ∈ F, u ∈ A → v ∈ A) →
      ∃ e, src e = u ∧ dst e = v ∧ c e = 0)
    (m : ℕ) (hpath : ∀ p : CostWalk src dst s t, m ≤ p.cost c) :
    ∃ a : Fin m → {A // A ∈ F}, ∀ e,
      (Finset.univ.filter (fun r : Fin m => src e ∈ (a r).val ∧ dst e ∉ (a r).val)).card ≤ c e := by
  let a (r : Fin m) : {A // A ∈ F} :=
    ⟨distanceCut src dst s c reachable (r.val+1),
      distanceCut_mem src dst s t c reachable F hunion hinter himp m hpath r⟩
  exact ⟨a,fun e => distanceCut_crossing_card src dst s c reachable m e⟩

end Packing
end FourPapers.Sublattice

end
end

section





set_option autoImplicit false
noncomputable section

namespace FourPapers.Sublattice.CostWalk

open Classical Finset
universe u v w
variable {V : Type u} {E : Type v} {L : Type w} [DecidableEq L]
variable {src dst : E → V} {s : V}

/-- The set of actual variable labels encountered by a walk.  Zero arcs
carry no variable label, and repeated variables are counted only once. -/
def labels (lab : E → Option L) :
    {v : V} → CostWalk src dst s v → Finset L
  | _, .nil => ∅
  | _, .snoc p e _ =>
    match lab e with
    | none => labels lab p
    | some l => insert l (labels lab p)

@[simp] lemma labels_nil (lab : E → Option L) :
    labels lab (nil (src := src) (dst := dst) (s := s)) = ∅ := rfl

lemma labels_subset_snoc (lab : E → Option L) {v : V}
    (p : CostWalk src dst s v) (e : E) (he : src e = v) :
    p.labels lab ⊆ (p.snoc e he).labels lab := by
  cases h : lab e with
  | none => simp only [labels,h]; exact Subset.rfl
  | some l => simp only [labels,h]; exact subset_insert _ _

/-- If crossing a cut forces a labelled edge with property P, then an
actual label of the walk has P. -/
lemma exists_label_crossing (lab : E → Option L)
    (W : Finset V) (hs : s ∈ W) (P : L → Prop)
    (hcross : ∀ e, src e ∈ W → dst e ∉ W →
      ∃ l, lab e = some l ∧ P l)
    {v : V} (p : CostWalk src dst s v) (hv : v ∉ W) :
    ∃ l ∈ p.labels lab, P l := by
  induction p with
  | nil => exact (hv hs).elim
  | @snoc v p e he ih =>
    by_cases hv' : v ∈ W
    · obtain ⟨l,hl,hP⟩ := hcross e (by simpa only [he] using hv') hv
      exact ⟨l,by simp [labels,hl],hP⟩
    · obtain ⟨l,hl,hP⟩ := ih hv'
      exact ⟨l,labels_subset_snoc lab p e he hl,hP⟩

/-- The weight of the distinct variable labels on a walk is bounded by
its integral cost.  Repeated use of an edge can only increase that cost. -/
lemma sum_labels_le_cost (lab : E → Option L) (a : L → ℕ) (c : E → ℕ)
    (hlab : ∀ e l, lab e = some l → a l ≤ c e)
    {v : V} (p : CostWalk src dst s v) :
    ∑ l ∈ p.labels lab, a l ≤ p.cost c := by
  induction p with
  | nil => simp [labels,cost]
  | @snoc v p e he ih =>
    cases hl : lab e with
    | none =>
      simp only [labels,hl,cost_snoc]
      exact ih.trans (Nat.le_add_right _ _)
    | some l =>
      have hc := hlab e l hl
      simp only [labels,hl,cost_snoc]
      by_cases hm : l ∈ p.labels lab
      · rw [Finset.insert_eq_of_mem hm]
        exact ih.trans (Nat.le_add_right _ _)
      · rw [Finset.sum_insert hm]
        exact (add_le_add hc ih).trans_eq (Nat.add_comm _ _)

end FourPapers.Sublattice.CostWalk

end
end

section







set_option autoImplicit false
noncomputable section

namespace FourPapers.Sublattice.RowCutNetwork

open Classical Finset
universe u
variable {ι : Type u} [Fintype ι] (n : ι → ℕ)
local instance : DecidableEq ι := Classical.decEq ι

abbrev Tuple := ∀ i, Fin (n i)
abbrev Label := Σ i, Fin (n i)
abbrev Node := Option (Option (Σ i, Fin (n i + 1)))

abbrev source : Node n := none
abbrev sink : Node n := some none
abbrev atNode (i : ι) (j : Fin (n i + 1)) : Node n := some (some ⟨i,j⟩)

def cut (a : Tuple n) : Finset (Node n) :=
  Finset.univ.filter fun v =>
    match v with
    | none => True
    | some none => False
    | some (some ⟨i,j⟩) => j.val ≤ (a i).val

@[simp] lemma source_mem_cut (a : Tuple n) : source n ∈ cut n a := by
  simp [source,cut]

@[simp] lemma sink_not_mem_cut (a : Tuple n) : sink n ∉ cut n a := by
  simp [sink,cut]

@[simp] lemma atNode_mem_cut (a : Tuple n) (i : ι) (j : Fin (n i + 1)) :
    atNode n i j ∈ cut n a ↔ j.val ≤ (a i).val := by
  simp [atNode,cut]

lemma cut_injective : Function.Injective (cut n) := by
  intro a b h
  funext i
  apply Fin.ext
  apply Nat.le_antisymm
  · have hm : atNode n i (a i).castSucc ∈ cut n a := by simp
    rw [h] at hm
    exact (atNode_mem_cut n b i _).mp hm
  · have hm : atNode n i (b i).castSucc ∈ cut n b := by simp
    rw [← h] at hm
    exact (atNode_mem_cut n a i _).mp hm

lemma cut_inf (a b : Tuple n) : cut n (a ⊓ b) = cut n a ∩ cut n b := by
  ext v
  rcases v with _ | (_ | ⟨i,j⟩)
  · simp
  · simp
  · simp only [Finset.mem_inter,atNode_mem_cut]
    change j.val ≤ min (a i).val (b i).val ↔
      j.val ≤ (a i).val ∧ j.val ≤ (b i).val
    exact le_min_iff

lemma cut_sup (a b : Tuple n) : cut n (a ⊔ b) = cut n a ∪ cut n b := by
  ext v
  rcases v with _ | (_ | ⟨i,j⟩)
  · simp
  · simp
  · simp only [Finset.mem_union,atNode_mem_cut]
    change j.val ≤ max (a i).val (b i).val ↔
      j.val ≤ (a i).val ∨ j.val ≤ (b i).val
    exact le_max_iff

def family (E : Finset (Tuple n)) : Finset (Finset (Node n)) := E.image (cut n)

lemma mem_family {E : Finset (Tuple n)} {W : Finset (Node n)} :
    W ∈ family n E ↔ ∃ a ∈ E, cut n a = W := Finset.mem_image

lemma family_union_closed (E : Finset (Tuple n))
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E) :
    ∀ A ∈ family n E, ∀ B ∈ family n E, A ∪ B ∈ family n E := by
  intro A hA B hB
  obtain ⟨a,ha,rfl⟩ := (mem_family n).mp hA
  obtain ⟨b,hb,rfl⟩ := (mem_family n).mp hB
  exact Finset.mem_image.mpr ⟨a ⊔ b,hsup a ha b hb,cut_sup n a b⟩

lemma family_inter_closed (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E) :
    ∀ A ∈ family n E, ∀ B ∈ family n E, A ∩ B ∈ family n E := by
  intro A hA B hB
  obtain ⟨a,ha,rfl⟩ := (mem_family n).mp hA
  obtain ⟨b,hb,rfl⟩ := (mem_family n).mp hB
  exact Finset.mem_image.mpr ⟨a ⊓ b,hinf a ha b hb,cut_inf n a b⟩

def Implication (E : Finset (Tuple n)) :=
  {uv : Node n × Node n // ∀ a ∈ E, uv.1 ∈ cut n a → uv.2 ∈ cut n a}

def Edge (E : Finset (Tuple n)) := Label n ⊕ Implication n E

def edgeSrc {E : Finset (Tuple n)} : Edge n E → Node n
  | .inl ⟨i,j⟩ => atNode n i j.castSucc
  | .inr h => h.val.1

def edgeDst {E : Finset (Tuple n)} : Edge n E → Node n
  | .inl ⟨i,j⟩ => atNode n i j.succ
  | .inr h => h.val.2

def edgeCost {E : Finset (Tuple n)} (α : Label n → ℕ) : Edge n E → ℕ
  | .inl x => α x
  | .inr _ => 0

def edgeLabel {E : Finset (Tuple n)} : Edge n E → Option (Label n)
  | .inl x => some x
  | .inr _ => none

lemma variable_crossing_iff {E : Finset (Tuple n)}
    (a : Tuple n) (i : ι) (j : Fin (n i)) :
    edgeSrc n (.inl ⟨i,j⟩ : Edge n E) ∈ cut n a ∧
    edgeDst n (.inl ⟨i,j⟩ : Edge n E) ∉ cut n a ↔ a i = j := by
  simp only [edgeSrc,edgeDst,atNode_mem_cut,Fin.val_castSucc,Fin.val_succ]
  constructor
  · intro h
    apply Fin.ext
    omega
  · intro h
    subst j
    omega

lemma implication_arc (E : Finset (Tuple n)) (α : Label n → ℕ)
    (u v : Node n) (h : ∀ A ∈ family n E, u ∈ A → v ∈ A) :
    ∃ e : Edge n E, edgeSrc n e = u ∧ edgeDst n e = v ∧ edgeCost n α e = 0 := by
  let e : Edge n E := .inr ⟨(u,v),fun a ha => h (cut n a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)⟩
  exact ⟨e,rfl,rfl,rfl⟩

lemma row_reachable (E : Finset (Tuple n)) (i : ι) (j : Fin (n i + 1)) :
    Nonempty (CostWalk (edgeSrc n (E := E)) (edgeDst n) (source n) (atNode n i j)) := by
  have aux : ∀ r (hr : r < n i + 1),
      Nonempty (CostWalk (edgeSrc n (E := E)) (edgeDst n) (source n)
        (atNode n i ⟨r,hr⟩)) := by
    intro r
    induction r with
    | zero =>
      intro hr
      let e : Edge n E := .inr ⟨(source n,atNode n i ⟨0,hr⟩),by
        intro a ha hs
        simp⟩
      exact ⟨CostWalk.nil.snoc e rfl⟩
    | succ r ih =>
      intro hr
      obtain ⟨p⟩ := ih (by omega)
      let e : Edge n E := .inl ⟨i,⟨r,by omega⟩⟩
      exact ⟨p.snoc e rfl⟩
  exact aux j.val j.isLt

lemma all_reachable [Nonempty ι] (E : Finset (Tuple n)) :
    ∀ v : Node n, Nonempty (CostWalk (edgeSrc n (E := E)) (edgeDst n) (source n) v) := by
  intro v
  rcases v with _ | (_ | ⟨i,j⟩)
  · exact ⟨CostWalk.nil⟩
  · let i : ι := Classical.choice inferInstance
    obtain ⟨p⟩ := row_reachable n E i (Fin.last (n i))
    let e : Edge n E := .inr ⟨(atNode n i (Fin.last (n i)),sink n),by
      intro a ha h
      have hh := (atNode_mem_cut n a i _).mp h
      have hlt := (a i).isLt
      simp only [Fin.val_last] at hh
      omega⟩
    exact ⟨p.snoc e rfl⟩
  · exact row_reachable n E i j

/-- Every source-to-sink walk supplies an actual vertex cover of the
original row-monomial family, even when the walk repeats vertices. -/
lemma walk_labels_cover (E : Finset (Tuple n))
    (p : CostWalk (edgeSrc n (E := E)) (edgeDst n) (source n) (sink n)) :
    ∀ a ∈ E, ∃ i, (⟨i,a i⟩ : Label n) ∈ p.labels (edgeLabel n) := by
  intro a ha
  obtain ⟨l,hl,hP⟩ := p.exists_label_crossing (edgeLabel n) (cut n a)
    (source_mem_cut n a) (fun l : Label n => a l.1 = l.2) (by
      intro e hs ht
      cases e with
      | inl l =>
        exact ⟨l,rfl,(variable_crossing_iff n a l.1 l.2).mp ⟨hs,ht⟩⟩
      | inr h => exact (ht (h.property a ha hs)).elim) (sink_not_mem_cut n a)
  exact ⟨l.1,by simpa only [hP] using hl⟩

lemma walk_cost_of_covers (E : Finset (Tuple n)) (α : Label n → ℕ) (m : ℕ)
    (hcover : ∀ C : Finset (Label n),
      (∀ a ∈ E, ∃ i, (⟨i,a i⟩ : Label n) ∈ C) → m ≤ ∑ x ∈ C, α x)
    (p : CostWalk (edgeSrc n (E := E)) (edgeDst n) (source n) (sink n)) :
    m ≤ p.cost (edgeCost n α) := by
  apply (hcover (p.labels (edgeLabel n)) (walk_labels_cover n E p)).trans
  apply p.sum_labels_le_cost
  intro e l hl
  cases e with
  | inl x =>
    have h : x = l := Option.some.inj hl
    subst l
    exact le_rfl
  | inr h => cases hl

/-- Exact integral packing for an arbitrary finite sublattice of a
product of finite chains.  Every row and every integral capacity is retained. -/
theorem sublattice_packing_nonempty [Nonempty ι] (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
    (α : Label n → ℕ) (m : ℕ)
    (hcover : ∀ C : Finset (Label n),
      (∀ a ∈ E, ∃ i, (⟨i,a i⟩ : Label n) ∈ C) → m ≤ ∑ x ∈ C, α x) :
    ∃ a : Fin m → {a // a ∈ E}, ∀ i j,
      (Finset.univ.filter (fun r : Fin m => (a r).val i = j)).card ≤ α ⟨i,j⟩ := by
  obtain ⟨A,hA⟩ := cutPacking_of_walkBound (edgeSrc n (E := E)) (edgeDst n)
    (source n) (sink n) (edgeCost n α) (all_reachable n E)
    (family n E) (family_union_closed n E hsup) (family_inter_closed n E hinf)
    (implication_arc n E α) m (walk_cost_of_covers n E α m hcover)
  have hx (r : Fin m) : ∃ a ∈ E, cut n a = (A r).val :=
    (mem_family n).mp (A r).property
  let a (r : Fin m) : {a // a ∈ E} := ⟨(hx r).choose,(hx r).choose_spec.1⟩
  have heq (r : Fin m) : cut n (a r).val = (A r).val := (hx r).choose_spec.2
  refine ⟨a,?_⟩
  intro i j
  have hc := hA (.inl ⟨i,j⟩)
  have hf : (Finset.univ.filter (fun r : Fin m =>
      edgeSrc n (.inl ⟨i,j⟩ : Edge n E) ∈ (A r).val ∧
      edgeDst n (.inl ⟨i,j⟩ : Edge n E) ∉ (A r).val)) =
      Finset.univ.filter (fun r : Fin m => (a r).val i = j) := by
    apply Finset.filter_congr
    intro r hr
    rw [← heq r]
    exact variable_crossing_iff n (a r).val i j
  simpa only [hf,edgeCost] using hc

/-- The integral packing statement also includes an empty row index and
an empty sublattice, with their literal empty-product conventions. -/
theorem sublattice_packing (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
    (α : Label n → ℕ) (m : ℕ)
    (hcover : ∀ C : Finset (Label n),
      (∀ a ∈ E, ∃ i, (⟨i,a i⟩ : Label n) ∈ C) → m ≤ ∑ x ∈ C, α x) :
    ∃ a : Fin m → {a // a ∈ E}, ∀ i j,
      (Finset.univ.filter (fun r : Fin m => (a r).val i = j)).card ≤ α ⟨i,j⟩ := by
  cases isEmpty_or_nonempty ι with
  | inr h => exact sublattice_packing_nonempty n E hinf hsup α m hcover
  | inl h =>
    by_cases hE : E.Nonempty
    · obtain ⟨a,ha⟩ := hE
      exact ⟨fun _ => ⟨a,ha⟩,fun i => isEmptyElim i⟩
    · have hE0 : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
      have hm := hcover ∅ (by simp [hE0])
      have hm0 : m = 0 := by simpa using hm
      subst m
      exact ⟨Fin.elim0,fun i => isEmptyElim i⟩

end FourPapers.Sublattice.RowCutNetwork

end
end

section







set_option autoImplicit false
noncomputable section

namespace FourPapers.Sublattice.RowCutNetwork

open Classical Finset MvPolynomial
universe u v
variable {ι : Type u} [Fintype ι] (n : ι → ℕ)
local instance : DecidableEq ι := Classical.decEq ι

def exponent (a : Tuple n) : Label n →₀ ℕ :=
  ∑ i, Finsupp.single ⟨i,a i⟩ 1

def monomialIdeal (k : Type v) [CommSemiring k] (E : Finset (Tuple n)) :
    Ideal (MvPolynomial (Label n) k) :=
  Ideal.span ((fun a => monomial (exponent n a) (1 : k)) '' (E : Set (Tuple n)))

lemma exponent_apply (a : Tuple n) (i : ι) (j : Fin (n i)) :
    exponent n a ⟨i,j⟩ = if a i = j then 1 else 0 := by
  classical
  rw [exponent,Finsupp.finsetSum_apply,Finset.sum_eq_single i]
  · by_cases h : a i = j
    · subst j
      simp
    · have hh : (⟨i,a i⟩ : Label n) ≠ ⟨i,j⟩ := by
        intro hh
        exact h (Fin.ext (congrArg (fun x : Label n => x.2.val) hh))
      simp [Finsupp.single_apply,h,hh]
  · intro r hr hri
    have hh : (⟨r,a r⟩ : Label n) ≠ ⟨i,j⟩ := by
      intro h
      exact hri (congrArg Sigma.fst h)
    simp [Finsupp.single_apply,hh]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

lemma sum_exponent_apply {m : ℕ} (a : Fin m → Tuple n)
    (i : ι) (j : Fin (n i)) :
    (∑ r, exponent n (a r)) ⟨i,j⟩ =
      (Finset.univ.filter (fun r : Fin m => a r i = j)).card := by
  classical
  simp only [Finsupp.finsetSum_apply,exponent_apply,Finset.sum_boole,Nat.cast_id]

lemma product_monomials {k : Type v} [CommSemiring k] {A : Type*}
    (S : Finset A) (β : A → Label n →₀ ℕ) :
    ∏ a ∈ S, monomial (β a) (1 : k) = monomial (∑ a ∈ S, β a) 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha,ih,monomial_mul_monomial,one_mul]

lemma monomial_sum_mem_power {k : Type v} [CommSemiring k]
    (E : Finset (Tuple n)) {m : ℕ} (a : Fin m → {a // a ∈ E}) :
    monomial (∑ r, exponent n (a r).val) (1 : k) ∈ (monomialIdeal n k E)^m := by
  classical
  have h := Ideal.prod_mem_prod (I := fun _ : Fin m => monomialIdeal n k E)
    (s := Finset.univ) (x := fun r => monomial (exponent n (a r).val) (1 : k))
    (fun r _ => Ideal.subset_span ⟨(a r).val,(a r).property,rfl⟩)
  rw [product_monomials] at h
  simpa using h

/-- The cover inequalities force membership in the actual ordinary power,
over every commutative coefficient semiring. -/
theorem monomial_mem_power_of_covers
    {k : Type v} [CommSemiring k]
    (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
    (α : Label n →₀ ℕ) (m : ℕ)
    (hcover : ∀ C : Finset (Label n),
      (∀ a ∈ E, ∃ i, (⟨i,a i⟩ : Label n) ∈ C) → m ≤ ∑ x ∈ C, α x) :
    monomial α (1 : k) ∈ (monomialIdeal n k E)^m := by
  classical
  obtain ⟨a,ha⟩ := sublattice_packing n E hinf hsup α m hcover
  let β := ∑ r, exponent n (a r).val
  have hβα : β ≤ α := by
    intro x
    rcases x with ⟨i,j⟩
    change (∑ r, exponent n (a r).val) ⟨i,j⟩ ≤ α ⟨i,j⟩
    rw [sum_exponent_apply]
    exact ha i j
  have hmem : monomial β (1 : k) ∈ (monomialIdeal n k E)^m :=
    monomial_sum_mem_power n E a
  have hm := ((monomialIdeal n k E)^m).mul_mem_left (monomial (α-β) 1) hmem
  simpa only [monomial_mul_monomial,one_mul,tsub_add_cancel_of_le hβα] using hm

end FourPapers.Sublattice.RowCutNetwork

end
end

section






set_option autoImplicit false
noncomputable section

namespace FourPapers.DividedTaylor

open Classical MvPolynomial Finset
universe u v
variable {V : Type u} {k : Type v} [CommSemiring k]

def diagonal : MvPolynomial V k →ₐ[k] MvPolynomial (V ⊕ V) k :=
  aeval (fun x => X (Sum.inl x) + X (Sum.inr x))

def taylor : MvPolynomial V k →ₐ[k] MvPolynomial V (MvPolynomial V k) :=
  (sumAlgEquiv k V V).toAlgHom.comp diagonal

def derivative (ν : V →₀ ℕ) (f : MvPolynomial V k) : MvPolynomial V k :=
  (taylor f).coeff ν

def joinExponent (ν μ : V →₀ ℕ) : V ⊕ V →₀ ℕ :=
  Finsupp.sumFinsuppAddEquivProdFinsupp.symm (ν,μ)

@[simp] lemma joinExponent_inl (ν μ : V →₀ ℕ) (x : V) :
    joinExponent ν μ (Sum.inl x) = ν x := rfl
@[simp] lemma joinExponent_inr (ν μ : V →₀ ℕ) (x : V) :
    joinExponent ν μ (Sum.inr x) = μ x := rfl

lemma coeff_sumAlgEquiv (p : MvPolynomial (V ⊕ V) k) (ν μ : V →₀ ℕ) :
    ((sumAlgEquiv k V V p).coeff ν).coeff μ = p.coeff (joinExponent ν μ) := by
  change (AddMonoidAlgebra.domCongr k k
    Finsupp.sumFinsuppAddEquivProdFinsupp p).coeff (ν,μ) = _
  exact AddMonoidAlgebra.coeff_domCongr (R := k) (A := k)
    Finsupp.sumFinsuppAddEquivProdFinsupp p (ν,μ)

lemma coeff_derivative (f : MvPolynomial V k) (ν μ : V →₀ ℕ) :
    (derivative ν f).coeff μ = (diagonal f).coeff (joinExponent ν μ) :=
  coeff_sumAlgEquiv (diagonal f) ν μ

@[simp] lemma diagonal_C (c : k) : diagonal (C c : MvPolynomial V k) = C c := by simp [diagonal]
@[simp] lemma diagonal_X (x : V) :
    diagonal (X x : MvPolynomial V k) = X (Sum.inl x) + X (Sum.inr x) := by
  simp [diagonal]
@[simp] lemma taylor_C (c : k) : taylor (C c : MvPolynomial V k) = C (C c) := by simp [taylor]
@[simp] lemma taylor_X (x : V) :
    taylor (X x : MvPolynomial V k) = X x + C (X x) := by simp [taylor]

def totalWeight : V ⊕ V → V →₀ ℕ
  | .inl x => Finsupp.single x 1
  | .inr x => Finsupp.single x 1

section Finite
variable [Fintype V] [DecidableEq V]

lemma weight_joinExponent (ν μ : V →₀ ℕ) :
    Finsupp.weight totalWeight (joinExponent ν μ) = ν + μ := by
  ext x
  simp [Finsupp.weight_eq_sum,Fintype.sum_sum_type,totalWeight,
    Finsupp.finsetSum_apply,Finsupp.smul_apply,Finsupp.single_apply]

lemma sum_single_weights (α : V →₀ ℕ) :
    ∑ x, α x • (Finsupp.single x 1 : V →₀ ℕ) = α := by
  ext x
  simp [Finsupp.finsetSum_apply,Finsupp.smul_apply,Finsupp.single_apply]

lemma diagonal_monomial_homogeneous (α : V →₀ ℕ) (c : k) :
    IsWeightedHomogeneous totalWeight (diagonal (monomial α c)) α := by
  have hx (x : V) : IsWeightedHomogeneous totalWeight
      (X (Sum.inl x) + X (Sum.inr x) : MvPolynomial (V ⊕ V) k)
      (Finsupp.single x 1) :=
    (isWeightedHomogeneous_X k totalWeight (.inl x)).add
      (isWeightedHomogeneous_X k totalWeight (.inr x))
  have hp := IsWeightedHomogeneous.prod Finset.univ
    (fun x => (X (Sum.inl x) + X (Sum.inr x) : MvPolynomial (V ⊕ V) k) ^ α x)
    (fun x => α x • (Finsupp.single x 1 : V →₀ ℕ)) (fun x _ => (hx x).pow (α x))
  rw [sum_single_weights] at hp
  change IsWeightedHomogeneous totalWeight
    ((aeval fun x => X (Sum.inl x) + X (Sum.inr x)) (monomial α c)) α
  rw [aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (by intro x; simp)]
  exact hp.C_mul c

lemma diagonal_monomial_coeff_zero (α ν μ : V →₀ ℕ) (c : k)
    (h : ν + μ ≠ α) :
    (diagonal (monomial α c)).coeff (joinExponent ν μ) = 0 :=
  (diagonal_monomial_homogeneous α c).coeff_eq_zero (joinExponent ν μ)
    (by simpa only [weight_joinExponent] using h)

lemma diagonal_monomial_coeff_scalar (α : V →₀ ℕ) (c : k)
    (δ : V ⊕ V →₀ ℕ) :
    (diagonal (monomial α c)).coeff δ =
      c * (diagonal (monomial α (1 : k))).coeff δ := by
  have hm : (monomial α c : MvPolynomial V k) = C c * monomial α 1 := by rw [C_mul_monomial,mul_one]
  rw [hm,map_mul,diagonal_C]
  simp

/-- A Taylor coefficient in bidegree (ν,μ) depends only on the original
coefficient in degree ν+μ. No division or characteristic assumption occurs. -/
lemma diagonal_coeff_factor (f : MvPolynomial V k) (ν μ : V →₀ ℕ) :
    (diagonal f).coeff (joinExponent ν μ) =
      f.coeff (ν+μ) * (diagonal (monomial (ν+μ) (1 : k))).coeff (joinExponent ν μ) := by
  classical
  conv_lhs => rw [f.as_sum]
  simp only [map_sum,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single (ν+μ)]
  · exact diagonal_monomial_coeff_scalar (ν+μ) (f.coeff (ν+μ)) (joinExponent ν μ)
  · intro α hα hne
    exact diagonal_monomial_coeff_zero α ν μ (f.coeff α) (Ne.symm hne)
  · intro hnot
    have hcoeff : f.coeff (ν+μ) = 0 := by
      simpa only [mem_support_iff,not_not] using hnot
    simp [hcoeff]

lemma derivative_coeff_ne_zero (f : MvPolynomial V k) (ν μ : V →₀ ℕ)
    (h : (derivative ν f).coeff μ ≠ 0) : f.coeff (ν+μ) ≠ 0 := by
  rw [coeff_derivative,diagonal_coeff_factor] at h
  exact left_ne_zero_of_mul h


def corner (C : Finset V) (x : V) : V ⊕ V := if x ∈ C then .inl x else .inr x

lemma corner_leftInverse (C : Finset V) :
    Function.LeftInverse (Sum.elim id id) (corner C) := by
  intro x
  by_cases hx : x ∈ C <;> simp [corner,hx]

lemma corner_injective (C : Finset V) : Function.Injective (corner C) :=
  (corner_leftInverse C).injective

lemma inl_not_range_corner (C : Finset V) {x : V} (hx : x ∉ C) :
    Sum.inl x ∉ Set.range (corner C) := by
  rintro ⟨y,hy⟩
  have hyx : y = x := by
    have h := congrArg (Sum.elim id id) hy
    simpa only [corner_leftInverse C y,Sum.elim_inl,Sum.elim_inr,id_eq] using h
  subst y
  simp [corner,hx] at hy

lemma inr_not_range_corner (C : Finset V) {x : V} (hx : x ∈ C) :
    Sum.inr x ∉ Set.range (corner C) := by
  rintro ⟨y,hy⟩
  have hyx : y = x := by
    have h := congrArg (Sum.elim id id) hy
    simpa only [corner_leftInverse C y,Sum.elim_inl,Sum.elim_inr,id_eq] using h
  subst y
  simp [corner,hx] at hy

lemma corner_mapDomain (C : Finset V) (α : V →₀ ℕ) :
    α.mapDomain (corner C) =
      joinExponent (α.filter (· ∈ C)) (α.filter (· ∉ C)) := by
  ext x
  cases x with
  | inl x =>
    rw [joinExponent_inl,Finsupp.filter_apply]
    by_cases hx : x ∈ C
    · rw [if_pos hx]
      simpa only [corner,if_pos hx] using
        Finsupp.mapDomain_apply_of_injective (corner_injective C) α x
    · rw [if_neg hx]
      exact Finsupp.mapDomain_of_notMem_range α _ (inl_not_range_corner C hx)
  | inr x =>
    rw [joinExponent_inr,Finsupp.filter_apply]
    by_cases hx : x ∈ C
    · rw [if_neg (not_not.mpr hx)]
      exact Finsupp.mapDomain_of_notMem_range α _ (inr_not_range_corner C hx)
    · rw [if_pos hx]
      simpa only [corner,if_neg hx] using
        Finsupp.mapDomain_apply_of_injective (corner_injective C) α x

lemma kill_diagonal (C : Finset V) :
    (killCompl (R := k) (corner_injective C)).comp diagonal = AlgHom.id k (MvPolynomial V k) := by
  apply MvPolynomial.algHom_ext
  intro x
  change killCompl (corner_injective C) (diagonal (X x : MvPolynomial V k)) = X x
  rw [diagonal_X,map_add]
  have hi := killCompl_rename_app (R := k) (corner_injective C) (X x)
  simp only [rename_X] at hi
  by_cases hx : x ∈ C
  · have hz : killCompl (R := k) (corner_injective C) (X (.inr x)) = 0 := by
      rw [killCompl,aeval_X,dif_neg (inr_not_range_corner C hx)]
    simpa only [corner,if_pos hx,hz,add_zero] using hi
  · have hz : killCompl (R := k) (corner_injective C) (X (.inl x)) = 0 := by
      rw [killCompl,aeval_X,dif_neg (inl_not_range_corner C hx)]
    simpa only [corner,if_neg hx,hz,zero_add] using hi

/-- Differentiating by the whole exponent in the chosen variables has
coefficient one at the complementary exponent, in every characteristic. -/
lemma derivative_corner_coeff (C : Finset V) (f : MvPolynomial V k) (α : V →₀ ℕ) :
    (derivative (α.filter (· ∈ C)) f).coeff (α.filter (· ∉ C)) = f.coeff α := by
  rw [coeff_derivative,← corner_mapDomain]
  have h := coeff_killCompl (corner_injective C) (p := diagonal f) (s := α)
  rw [show killCompl (corner_injective C) (diagonal f) = f from
    DFunLike.congr_fun (kill_diagonal (k := k) C) f] at h
  exact h.symm


lemma filter_add_complement (C : Finset V) (α : V →₀ ℕ) :
    α.filter (· ∈ C) + α.filter (· ∉ C) = α := by
  ext x
  by_cases hx : x ∈ C <;> simp [Finsupp.filter_apply,hx]

lemma derivative_corner_ne_zero (m : MonomialOrder V) (C : Finset V)
    (f : MvPolynomial V k) (hf : f ≠ 0) :
    derivative ((m.degree f).filter (· ∈ C)) f ≠ 0 := by
  intro hz
  have hc := derivative_corner_coeff C f (m.degree f)
  rw [hz] at hc
  exact (m.coeff_degree_ne_zero_iff.mpr hf) (by simpa using hc.symm)

/-- The leading exponent is reduced by exactly the prescribed corner
exponent for every monomial order; no degree compatibility is assumed. -/
lemma derivative_corner_degree (m : MonomialOrder V) (C : Finset V)
    (f : MvPolynomial V k) (hf : f ≠ 0) :
    m.degree (derivative ((m.degree f).filter (· ∈ C)) f) =
      (m.degree f).filter (· ∉ C) := by
  let α := m.degree f
  let ν := α.filter (· ∈ C)
  let μ := α.filter (· ∉ C)
  have hs : ν+μ=α := filter_add_complement C α
  have hlow : m.toSyn μ ≤ m.toSyn (m.degree (derivative ν f)) := by
    apply m.le_degree
    rw [mem_support_iff]
    change (derivative (α.filter (· ∈ C)) f).coeff (α.filter (· ∉ C)) ≠ 0
    rw [derivative_corner_coeff]
    exact m.coeff_degree_ne_zero_iff.mpr hf
  have hupp : m.toSyn (m.degree (derivative ν f)) ≤ m.toSyn μ := by
    apply m.degree_le_iff.mpr
    intro β hβ
    have hco := derivative_coeff_ne_zero f ν β (mem_support_iff.mp hβ)
    have h := m.le_degree (mem_support_iff.mpr hco)
    change m.toSyn (ν+β) ≤ m.toSyn α at h
    rw [← hs,map_add,map_add] at h
    exact le_of_add_le_add_left h
  exact m.toSyn.injective (le_antisymm hupp hlow)

lemma derivative_corner_leadingCoeff (m : MonomialOrder V) (C : Finset V)
    (f : MvPolynomial V k) (hf : f ≠ 0) :
    m.leadingCoeff (derivative ((m.degree f).filter (· ∈ C)) f) = m.leadingCoeff f := by
  unfold MonomialOrder.leadingCoeff
  rw [derivative_corner_degree m C f hf,derivative_corner_coeff]


@[simp] lemma derivative_zero (f : MvPolynomial V k) : derivative 0 f = f := by
  ext α
  have h0 : α.filter (· ∈ (∅ : Finset V)) = 0 := by
    ext x
    simp [Finsupp.filter_apply]
  have h1 : α.filter (· ∉ (∅ : Finset V)) = α := by
    ext x
    simp [Finsupp.filter_apply]
  simpa only [h0,h1] using derivative_corner_coeff (∅ : Finset V) f α


end Finite
end FourPapers.DividedTaylor

end
end

section






set_option autoImplicit false
noncomputable section

namespace FourPapers.DividedTaylor

open Classical MvPolynomial
universe u v
variable {V : Type u} {k : Type v} [Fintype V] [DecidableEq V] [CommRing k]

def quotientTaylor (J : Ideal (MvPolynomial V k)) :
    MvPolynomial V k →+* MvPolynomial V (MvPolynomial V k ⧸ J) :=
  (MvPolynomial.map (Ideal.Quotient.mk J)).comp taylor.toRingHom

lemma quotientTaylor_coeff (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (ν : V →₀ ℕ) :
    (quotientTaylor J f).coeff ν = Ideal.Quotient.mk J (derivative ν f) := by
  exact coeff_map (Ideal.Quotient.mk J) (taylor f) ν

lemma quotientTaylor_mem_vars (J : Ideal (MvPolynomial V k)) (f : MvPolynomial V k)
    (hf : f ∈ J) :
    quotientTaylor J f ∈ idealOfVars V (MvPolynomial V k ⧸ J) := by
  rw [← pow_one (idealOfVars V (MvPolynomial V k ⧸ J)),
    mem_pow_idealOfVars_iff']
  intro ν hν
  have hzero : ν = 0 := (Finsupp.degree_eq_zero_iff ν).mp (by omega)
  subst ν
  rw [quotientTaylor_coeff,derivative_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hf

lemma quotientTaylor_map_le (J : Ideal (MvPolynomial V k)) :
    Ideal.map (quotientTaylor J) J ≤ idealOfVars V (MvPolynomial V k ⧸ J) := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  exact quotientTaylor_mem_vars J f hf

lemma quotientTaylor_mem_vars_power (J : Ideal (MvPolynomial V k)) (m : ℕ)
    (f : MvPolynomial V k) (hf : f ∈ J^m) :
    quotientTaylor J f ∈ (idealOfVars V (MvPolynomial V k ⧸ J))^m := by
  have h := Ideal.mem_map_of_mem (quotientTaylor J) hf
  rw [Ideal.map_pow] at h
  exact Ideal.pow_right_mono (quotientTaylor_map_le J) m h

/-- Every divided partial derivative of total order less than m sends
the actual ordinary power J^m into J, without characteristic restrictions. -/
theorem derivative_mem_of_power (J : Ideal (MvPolynomial V k)) (m : ℕ)
    (f : MvPolynomial V k) (hf : f ∈ J^m)
    (ν : V →₀ ℕ) (hν : Finsupp.degree ν < m) : derivative ν f ∈ J := by
  have h := (mem_pow_idealOfVars_iff' m (quotientTaylor J f)).mp
    (quotientTaylor_mem_vars_power J m f hf) ν hν
  rw [quotientTaylor_coeff] at h
  exact Ideal.Quotient.eq_zero_iff_mem.mp h

/-- Coefficient estimate adapted from TauCeti's ideal-of-variables lemma.
Source: TauCetiProject/TauCeti, commit
5ce4390a0a9a3277d048f680244409f42e9faeda,
TauCeti/RingTheory/MvPolynomial/Ideal.lean. -/
lemma coeff_mul_degree_bound {R : Type*} [CommSemiring R]
    (p : MvPolynomial V R) {s : ℕ} (hp : p ∈ idealOfVars V R ^ s)
    (q : MvPolynomial V R) {e : V →₀ ℕ} (he : Finsupp.degree e ≤ s) :
    (p*q).coeff e = p.coeff e * constantCoeff q := by
  classical
  rw [coeff_mul,Finset.sum_eq_single (e,0),constantCoeff_eq]
  · rintro ⟨a,b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    have hb : Finsupp.degree b ≠ 0 := by
      rw [Ne,Finsupp.degree_eq_zero_iff]
      rintro rfl
      exact hne (by simp_all)
    have hdeg : Finsupp.degree a + Finsupp.degree b = Finsupp.degree e := by
      rw [← map_add,hab]
    rw [(mem_pow_idealOfVars_iff' s p).mp hp a (by omega),zero_mul]
  · exact fun h => absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero e)) h

/-- Cancellation modulo a power of the variable ideal uses the actual
nonzero constant coefficient. The quotient ring is allowed to have any
characteristic. -/
theorem vars_power_cancel {R : Type*} [CommRing R] [IsDomain R]
    {p q : MvPolynomial V R} (hq : constantCoeff q ≠ 0) (s : ℕ)
    (hpq : p*q ∈ idealOfVars V R ^ s) : p ∈ idealOfVars V R ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hps : p ∈ idealOfVars V R ^ s :=
      ih (Ideal.pow_le_pow_right (Nat.le_succ s) hpq)
    rw [mem_pow_idealOfVars_iff']
    intro e he
    have hz := (mem_pow_idealOfVars_iff' (s+1) (p*q)).mp hpq e he
    rw [coeff_mul_degree_bound p hps q (Nat.lt_succ_iff.mp he)] at hz
    exact (mul_eq_zero.mp hz).resolve_right hq

/-- The necessary divided-derivative condition for the actual symbolic
power denominator criterion at an arbitrary prime. -/
theorem derivative_mem_of_prime_denominator
    (P : Ideal (MvPolynomial V k)) [P.IsPrime] (m : ℕ)
    (f g : MvPolynomial V k) (hg : g ∉ P) (hgf : g*f ∈ P^m)
    (ν : V →₀ ℕ) (hν : Finsupp.degree ν < m) :
    derivative ν f ∈ P := by
  have hqg : constantCoeff (quotientTaylor P g) ≠ 0 := by
    rw [constantCoeff_eq,quotientTaylor_coeff,derivative_zero]
    exact fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hprod : quotientTaylor P f * quotientTaylor P g ∈
      idealOfVars V (MvPolynomial V k ⧸ P)^m := by
    rw [← map_mul]
    apply quotientTaylor_mem_vars_power
    simpa only [mul_comm] using hgf
  have hmem := vars_power_cancel hqg m hprod
  have hcoeff := (mem_pow_idealOfVars_iff' m (quotientTaylor P f)).mp hmem ν hν
  rw [quotientTaylor_coeff] at hcoeff
  exact Ideal.Quotient.eq_zero_iff_mem.mp hcoeff


end FourPapers.DividedTaylor

end
end

section




set_option autoImplicit false
noncomputable section

namespace FourPapers

open Classical MvPolynomial
variable {V k : Type*} [CommRing k]

/-- The actual ideal generated by leading terms. -/
def initialIdeal (m : MonomialOrder V) (J : Ideal (MvPolynomial V k)) :
    Ideal (MvPolynomial V k) := Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial V k)))

lemma leadingTerm_mem_initial (m : MonomialOrder V) {J : Ideal (MvPolynomial V k)}
    {f : MvPolynomial V k} (hf : f ∈ J) : m.leadingTerm f ∈ initialIdeal m J :=
  Ideal.subset_span ⟨f,hf,rfl⟩

lemma initialIdeal_mono (m : MonomialOrder V) {J K : Ideal (MvPolynomial V k)} (h : J ≤ K) :
    initialIdeal m J ≤ initialIdeal m K := Ideal.span_mono (Set.image_mono h)

@[simp] lemma initialIdeal_top (m : MonomialOrder V) :
    initialIdeal m (⊤ : Ideal (MvPolynomial V k)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h := leadingTerm_mem_initial m (J := ⊤) (f := (1 : MvPolynomial V k)) (by trivial)
  simpa using h

lemma initialIdeal_mul_le [NoZeroDivisors k] (m : MonomialOrder V)
    (J K : Ideal (MvPolynomial V k)) :
    initialIdeal m J * initialIdeal m K ≤ initialIdeal m (J*K) := by
  rw [initialIdeal,initialIdeal,Ideal.span_mul_span]
  apply Ideal.span_le.mpr
  rintro f ⟨p,⟨a,ha,rfl⟩,q,⟨b,hb,rfl⟩,rfl⟩
  change m.leadingTerm a * m.leadingTerm b ∈ initialIdeal m (J*K)
  rw [← m.leadingTerm_mul]
  exact leadingTerm_mem_initial m (Ideal.mul_mem_mul ha hb)

lemma initialIdeal_pow_le [NoZeroDivisors k] (m : MonomialOrder V)
    (J : Ideal (MvPolynomial V k)) (s : ℕ) :
    (initialIdeal m J)^s ≤ initialIdeal m (J^s) := by
  induction s with
  | zero => simp [Ideal.one_eq_top]
  | succ s ih =>
    rw [pow_succ,pow_succ]
    exact (mul_le_mul' ih le_rfl).trans (initialIdeal_mul_le m (J^s) J)

/-- Initial ideals fix actual monomial ideals, for every monomial order. -/
theorem initialIdeal_monomialSpan (m : MonomialOrder V) (S : Set (V →₀ ℕ)) :
    initialIdeal m (Ideal.span ((fun a => monomial a (1:k)) '' S)) =
      Ideal.span ((fun a => monomial a (1:k)) '' S) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,rfl⟩
    change m.leadingTerm f ∈ Ideal.span ((fun a => monomial a (1:k)) '' S)
    by_cases hz : f = 0
    · subst f
      simp
    · obtain ⟨a,ha,had⟩ := mem_ideal_span_monomial_image.mp hf _ (m.degree_mem_support hz)
      have hm : monomial (m.degree f) (1:k) ∈
          Ideal.span ((fun a => monomial a (1:k)) '' S) := by
        have hh := (Ideal.span ((fun a => monomial a (1:k)) '' S)).mul_mem_left
          (monomial (m.degree f-a) 1) (Ideal.subset_span ⟨a,ha,rfl⟩)
        simpa only [monomial_mul_monomial,one_mul,tsub_add_cancel_of_le had] using hh
      have hh := (Ideal.span ((fun a => monomial a (1:k)) '' S)).mul_mem_left
        (C (m.leadingCoeff f)) hm
      simpa only [MonomialOrder.C_mul_leadingCoeff_monomial_degree] using hh
  · apply Ideal.span_le.mpr
    rintro g ⟨a,ha,rfl⟩
    have hh := leadingTerm_mem_initial m (J:=Ideal.span ((fun a => monomial a (1:k)) '' S))
      (Ideal.subset_span (Set.mem_image_of_mem _ ha))
    change monomial a (1:k) ∈ initialIdeal m _
    simpa only [MonomialOrder.leadingTerm_monomial] using hh

end FourPapers

end
end

section






set_option autoImplicit false
noncomputable section

namespace FourPapers.Sublattice.RowCutNetwork

open Classical MvPolynomial Finset
universe u v
variable {ι : Type u} [Fintype ι] (n : ι → ℕ)
local instance : DecidableEq ι := Classical.decEq ι
variable {k : Type v} [Field k]

lemma monomialIdeal_span_image (E : Finset (Tuple n)) :
    monomialIdeal n k E =
      Ideal.span ((fun a => monomial a (1 : k)) '' (exponent n '' (E : Set (Tuple n)))) := by
  unfold monomialIdeal
  rw [Set.image_image]

lemma exponent_le_degree_of_mem (m : MonomialOrder (Label n))
    (J : Ideal (MvPolynomial (Label n) k)) (E : Finset (Tuple n))
    (hinit : initialIdeal m J = monomialIdeal n k E)
    (f : MvPolynomial (Label n) k) (hf : f ∈ J) (hne : f ≠ 0) :
    ∃ a ∈ E, exponent n a ≤ m.degree f := by
  have hlt : m.leadingTerm f ∈ monomialIdeal n k E := by
    rw [← hinit]
    exact leadingTerm_mem_initial m hf
  rw [monomialIdeal_span_image] at hlt
  have hs : m.degree f ∈ (m.leadingTerm f).support := by
    rw [mem_support_iff]
    simpa [MonomialOrder.leadingTerm,coeff_monomial] using m.leadingCoeff_ne_zero_iff.mpr hne
  obtain ⟨a,⟨b,hb,rfl⟩,ha⟩ := mem_ideal_span_monomial_image.mp hlt _ hs
  exact ⟨b,hb,ha⟩

lemma degree_filter_cover (C : Finset (Label n)) (α : Label n →₀ ℕ) :
    Finsupp.degree (α.filter (· ∈ C)) = ∑ x ∈ C, α x := by
  rw [Finsupp.degree_eq_sum]
  simp only [Finsupp.filter_apply]
  rw [← Finset.sum_filter]
  simp

/-- The leading monomial of every polynomial satisfying the divided-derivative condition belongs to the s-th
ordinary power of its sublattice initial ideal. -/
theorem leading_monomial_mem_power_of_derivatives
    (m : MonomialOrder (Label n)) (J : Ideal (MvPolynomial (Label n) k))
    (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
    (hinit : initialIdeal m J = monomialIdeal n k E)
    (s : ℕ) (f : MvPolynomial (Label n) k)
    (hderiv : ∀ ν : Label n →₀ ℕ, Finsupp.degree ν < s →
      DividedTaylor.derivative ν f ∈ J) (hne : f ≠ 0) :
    monomial (m.degree f) (1 : k) ∈ (monomialIdeal n k E)^s := by
  apply monomial_mem_power_of_covers n E hinf hsup (m.degree f) s
  intro C hC
  by_contra hbound
  have horder : Finsupp.degree ((m.degree f).filter (· ∈ C)) < s := by
    rw [degree_filter_cover]
    omega
  let D := DividedTaylor.derivative ((m.degree f).filter (· ∈ C)) f
  have hDJ : D ∈ J := hderiv _ horder
  have hDne : D ≠ 0 := DividedTaylor.derivative_corner_ne_zero m C f hne
  obtain ⟨a,ha,hadeg⟩ := exponent_le_degree_of_mem n m J E hinit D hDJ hDne
  obtain ⟨i,hi⟩ := hC a ha
  have h := hadeg ⟨i,a i⟩
  have hd : m.degree D = (m.degree f).filter (· ∉ C) :=
    DividedTaylor.derivative_corner_degree m C f hne
  rw [hd,exponent_apply,Finsupp.filter_apply] at h
  simp only [ite_true,not_true_eq_false,hi,ite_false] at h
  omega

/-- The ordinary-power case of the derivative criterion. -/
theorem leading_monomial_mem_power
    (m : MonomialOrder (Label n)) (J : Ideal (MvPolynomial (Label n) k))
    (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
    (hinit : initialIdeal m J = monomialIdeal n k E)
    (s : ℕ) (f : MvPolynomial (Label n) k) (hf : f ∈ J^s) (hne : f ≠ 0) :
    monomial (m.degree f) (1 : k) ∈ (monomialIdeal n k E)^s :=
  leading_monomial_mem_power_of_derivatives n m J E hinf hsup hinit s f
    (fun ν hν => DividedTaylor.derivative_mem_of_power J s f hf ν hν) hne

/-- Commutation of initial ideals with every ordinary power, for an
arbitrary finite sublattice and every field. -/
theorem initialIdeal_power_eq
    (m : MonomialOrder (Label n)) (J : Ideal (MvPolynomial (Label n) k))
    (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
    (hinit : initialIdeal m J = monomialIdeal n k E)
    (s : ℕ) :
    initialIdeal m (J^s) = (monomialIdeal n k E)^s := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,rfl⟩
    by_cases hzero : f = 0
    · subst f
      simp
    · have hm := leading_monomial_mem_power n m J E hinf hsup hinit s f hf hzero
      have hh := ((monomialIdeal n k E)^s).mul_mem_left (C (m.leadingCoeff f)) hm
      change m.leadingTerm f ∈ (monomialIdeal n k E)^s
      simpa only [MonomialOrder.C_mul_leadingCoeff_monomial_degree] using hh
  · rw [← hinit]
    exact initialIdeal_pow_le m J s

end FourPapers.Sublattice.RowCutNetwork

end
end

namespace MonomialOrder
open MvPolynomial
theorem ideal_eq_of_le_of_initial_le {σ R : Type*} [CommRing R]
    (m : MonomialOrder σ) {J K : Ideal (MvPolynomial σ R)} (hJK : J ≤ K)
    (hinit : Ideal.span (m.leadingTerm '' (K : Set (MvPolynomial σ R))) ≤
      Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial σ R)))) : K = J := by
  have h : m.IsGroebnerBasis (J : Set (MvPolynomial σ R)) K :=
    ⟨hJK, le_antisymm hinit (Ideal.span_mono (Set.image_mono hJK))⟩
  simpa using h.ideal_eq_span

theorem radical_of_squarefree_initial {σ k : Type*} [Field k]
    (m : MonomialOrder σ) (J : Ideal (MvPolynomial σ k))
    (S : Set (σ →₀ ℕ)) (hsq : ∀ a ∈ S, ∀ i, a i ≤ 1)
    (hinit : Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial σ k))) =
      Ideal.span ((fun a => monomial a (1:k)) '' S)) : J.IsRadical := by
  classical
  intro f hf
  obtain ⟨r,hr⟩ := exists_isRemainder (m:=m) (B:=(J:Set _))
    (fun b _ hb => m.isUnit_leadingCoeff.mpr hb) f
  apply ((m.isGroebnerBasis_self J).remainder_eq_zero_iff_mem hr).mp
  by_contra hne
  have hdiff : f-r ∈ J := by simpa using hr.sub_mem_span
  have hrJ : r ∈ J.radical := by
    have h := J.radical.sub_mem hf (Ideal.le_radical hdiff)
    simpa using h
  obtain ⟨s,hs⟩ := hrJ
  have hlt : m.leadingTerm (r^s) ∈ Ideal.span ((fun a => monomial a (1:k)) '' S) := by
    rw [←hinit]
    exact Ideal.subset_span ⟨r^s,hs,rfl⟩
  obtain ⟨a,ha,had⟩ := mem_ideal_span_monomial_image.mp hlt
    (m.degree (r^s)) (by rw [m.support_leadingTerm' (pow_ne_zero s hne)]; simp)
  have had' : a ≤ m.degree r := by
    intro i
    have hi := had i
    rw [m.degree_pow] at hi
    have hsqi := hsq a ha i
    simp only [Finsupp.smul_apply,smul_eq_mul] at hi
    by_cases hz : m.degree r i = 0
    · simp only [hz,mul_zero] at hi
      omega
    · omega
  have hmon : monomial (m.degree r) (1:k) ∈
      Ideal.span ((fun a => monomial a (1:k)) '' S) := by
    have hh := (Ideal.span ((fun a => monomial a (1:k)) '' S)).mul_mem_left
      (monomial (m.degree r-a) 1) (Ideal.subset_span ⟨a,ha,rfl⟩)
    simpa only [monomial_mul_monomial,one_mul,tsub_add_cancel_of_le had'] using hh
  rw [←hinit] at hmon
  obtain ⟨b,hb,hb0,hbr⟩ := exists_degree_le_of_mem_span_leadingTerm (m:=m) hmon
    (by simp : m.degree r ∈ (monomial (m.degree r) (1:k)).support)
  exact hr.not_degree_le (m.degree_mem_support hne) hb hb0 hbr
end MonomialOrder






namespace FourPapers
noncomputable section
variable {R : Type*} [CommRing R]
def primeSymbolicPower (P : Ideal R) [P.IsPrime] (s : ℕ) : Ideal R :=
  ((P^s).map (algebraMap R (Localization.AtPrime P))).comap
    (algebraMap R (Localization.AtPrime P))

lemma mem_primeSymbolicPower_iff (P : Ideal R) [P.IsPrime] (s : ℕ) (f : R) :
    f ∈ primeSymbolicPower P s ↔ ∃ g ∉ P, g*f ∈ P^s := by
  unfold primeSymbolicPower
  rw [Ideal.mem_comap,IsLocalization.algebraMap_mem_map_algebraMap_iff
    P.primeCompl (Localization.AtPrime P)]
  rfl

def radicalSymbolicPower (J : Ideal R) (s : ℕ) : Ideal R :=
  ⨅ P : J.minimalPrimes, @primeSymbolicPower R _ P.val P.property.isPrime s

lemma mem_radicalSymbolicPower_iff (J : Ideal R) (s : ℕ) (f : R) :
    f ∈ radicalSymbolicPower J s ↔
      ∀ P ∈ J.minimalPrimes, ∃ g ∉ P, g*f ∈ P^s := by
  simp only [radicalSymbolicPower,Submodule.mem_iInf]
  constructor
  · intro hf P hP
    letI : P.IsPrime := hP.isPrime
    exact (mem_primeSymbolicPower_iff P s f).mp (hf ⟨P,hP⟩)
  · intro hf P
    letI : P.val.IsPrime := P.property.isPrime
    exact (mem_primeSymbolicPower_iff P.val s f).mpr (hf P.val P.property)
/-- Symbolic power defined by contraction of the ordinary power from all
localizations at minimal primes. -/
def symbolicPower (J : Ideal R) (s : ℕ) : Ideal R :=
  ⨅ P : J.minimalPrimes, by
    letI : P.val.IsPrime := P.property.isPrime
    exact ((J^s).map (algebraMap R (Localization.AtPrime P.val))).comap
      (algebraMap R (Localization.AtPrime P.val))

lemma pow_le_symbolicPower (J : Ideal R) (s : ℕ) :
    J^s ≤ symbolicPower J s := by
  apply le_iInf
  intro P
  exact Ideal.le_comap_map

lemma symbolicPower_eq_radicalSymbolicPower (J : Ideal R) (hJ : J.IsRadical) (s : ℕ) :
    symbolicPower J s = radicalSymbolicPower J s := by
  apply iInf_congr
  intro P
  letI : P.val.IsPrime := P.property.isPrime
  have heq : J.map (algebraMap R (Localization.AtPrime P.val)) =
      P.val.map (algebraMap R (Localization.AtPrime P.val)) := by
    calc
      _ = (J.map (algebraMap R (Localization.AtPrime P.val))).radical := by
        rw [←IsLocalization.map_radical P.val.primeCompl, hJ.radical]
      _ = _ := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime P.val) P.val J P.property
  change ((J^s).map _).comap _ = ((P.val^s).map _).comap _
  rw [Ideal.map_pow,Ideal.map_pow,heq]

lemma mem_symbolicPower_iff (J : Ideal R) (hJ : J.IsRadical) (s : ℕ) (f : R) :
    f ∈ symbolicPower J s ↔ ∀ P ∈ J.minimalPrimes, ∃ g ∉ P, g*f ∈ P^s := by
  rw [symbolicPower_eq_radicalSymbolicPower J hJ,mem_radicalSymbolicPower_iff]

end
end FourPapers






namespace FourPapers
noncomputable section
open MvPolynomial Finset
universe u v
variable {V : Type u} [DecidableEq V] {k : Type v} [CommSemiring k]

def coordinateIdeal (C : Finset V) : Ideal (MvPolynomial V k) :=
  Ideal.span (X '' (C : Set V))

def coverWeight (C : Finset V) (a : V →₀ ℕ) : ℕ := ∑ x ∈ C, a x

lemma coverWeight_add (C : Finset V) (a b : V →₀ ℕ) :
    coverWeight C (a+b) = coverWeight C a + coverWeight C b := by
  simp [coverWeight,Finset.sum_add_distrib]

lemma coverWeight_mono (C : Finset V) {a b : V →₀ ℕ} (h : a ≤ b) :
    coverWeight C a ≤ coverWeight C b :=
  Finset.sum_le_sum (fun i _ => h i)

def coverWeightIdeal (C : Finset V) (s : ℕ) : Ideal (MvPolynomial V k) :=
  restrictSupportIdeal k {a | s ≤ coverWeight C a} (fun _ _ hab ha => ha.trans (coverWeight_mono C hab))

lemma mem_coverWeightIdeal (C : Finset V) (s : ℕ) (f : MvPolynomial V k) :
    f ∈ coverWeightIdeal C s ↔ ∀ a ∈ f.support, s ≤ coverWeight C a := Iff.rfl

lemma coordinateIdeal_le_coverWeightIdeal (C : Finset V) :
    coordinateIdeal (k:=k) C ≤ coverWeightIdeal C 1 := by
  apply Ideal.span_le.mpr
  rintro p ⟨i,hi,rfl⟩
  change X i ∈ coverWeightIdeal (k:=k) C 1
  rw [mem_coverWeightIdeal]
  intro a ha
  change i ∈ C at hi
  have ha' : a = Finsupp.single i 1 := Finset.mem_singleton.mp (support_monomial_subset ha)
  subst a
  simp [coverWeight,Finsupp.single_apply,hi]

lemma coverWeightIdeal_mul_le (C : Finset V) (s t : ℕ) :
    coverWeightIdeal (k:=k) C s * coverWeightIdeal C t ≤ coverWeightIdeal C (s+t) := by
  apply Ideal.mul_le.mpr
  intro f hf g hg
  rw [mem_coverWeightIdeal]
  intro a ha
  have hn := mem_support_iff.mp ha
  rw [coeff_mul] at hn
  obtain ⟨⟨b,c⟩,hbc,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hb := hf (mem_support_iff.mpr (left_ne_zero_of_mul hne))
  have hc := hg (mem_support_iff.mpr (right_ne_zero_of_mul hne))
  have heq : b+c = a := Finset.HasAntidiagonal.mem_antidiagonal.mp hbc
  change s ≤ coverWeight C b at hb
  change t ≤ coverWeight C c at hc
  rw [←heq,coverWeight_add]
  omega

theorem coordinateIdeal_power_le (C : Finset V) (s : ℕ) :
    coordinateIdeal (k:=k) C ^ s ≤ coverWeightIdeal C s := by
  induction s with
  | zero =>
    intro f hf
    rw [mem_coverWeightIdeal]
    exact fun _ _ => Nat.zero_le _
  | succ s ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (coordinateIdeal_le_coverWeightIdeal C)).trans
      (coverWeightIdeal_mul_le C s 1)
end
end FourPapers


section




set_option autoImplicit false
noncomputable section
namespace FourPapers.DividedTaylor
open MvPolynomial
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V] {k : Type v} [CommRing k]

theorem derivative_mem_of_symbolicPower
    (J : Ideal (MvPolynomial V k)) (hJ : J.IsRadical) (s : ℕ)
    (f : MvPolynomial V k) (hf : f ∈ FourPapers.symbolicPower J s)
    (ν : V →₀ ℕ) (hν : Finsupp.degree ν < s) :
    derivative ν f ∈ J := by
  apply hJ
  rw [←Ideal.sInf_minimalPrimes,Ideal.mem_sInf]
  intro P hP
  letI : P.IsPrime := hP.isPrime
  obtain ⟨g,hg,hgf⟩ := (FourPapers.mem_symbolicPower_iff J hJ s f).mp hf P hP
  exact derivative_mem_of_prime_denominator P s f g hg hgf ν hν
end FourPapers.DividedTaylor

end
end

section





set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice.RowCutNetwork
open Classical MvPolynomial Finset
universe u v
variable {ι : Type u} [Fintype ι] (n : ι → ℕ)
local instance : DecidableEq ι := Classical.decEq ι
variable {k : Type v} [Field k]

theorem radical_of_sublattice_initial
    (m : MonomialOrder (Label n)) (J : Ideal (MvPolynomial (Label n) k))
    (E : Finset (Tuple n)) (hinit : initialIdeal m J = monomialIdeal n k E) :
    J.IsRadical := by
  apply m.radical_of_squarefree_initial J (exponent n '' (E : Set (Tuple n)))
  · rintro a ⟨b,hb,rfl⟩ ⟨i,j⟩
    rw [exponent_apply]
    split_ifs <;> omega
  · exact hinit.trans (monomialIdeal_span_image n E)

theorem initialIdeal_symbolicPower_le
    (m : MonomialOrder (Label n)) (J : Ideal (MvPolynomial (Label n) k))
    (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
    (hinit : initialIdeal m J = monomialIdeal n k E) (s : ℕ) :
    initialIdeal m (FourPapers.symbolicPower J s) ≤ (monomialIdeal n k E)^s := by
  apply Ideal.span_le.mpr
  rintro g ⟨f,hf,rfl⟩
  by_cases hzero : f = 0
  · subst f
    simp
  · have hm := leading_monomial_mem_power_of_derivatives n m J E hinf hsup hinit s f
      (fun ν hν => DividedTaylor.derivative_mem_of_symbolicPower J
        (radical_of_sublattice_initial n m J E hinit) s f hf ν hν) hzero
    have hh := ((monomialIdeal n k E)^s).mul_mem_left (C (m.leadingCoeff f)) hm
    change m.leadingTerm f ∈ (monomialIdeal n k E)^s
    simpa only [MonomialOrder.C_mul_leadingCoeff_monomial_degree] using hh

/-- Equality of every symbolic power (defined by localization at the minimal
primes) with the ordinary power. This applies to every ideal with a finite
sublattice initial ideal, over every field. -/
theorem symbolicPower_eq_power
    (m : MonomialOrder (Label n)) (J : Ideal (MvPolynomial (Label n) k))
    (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
    (hinit : initialIdeal m J = monomialIdeal n k E) (s : ℕ) :
    FourPapers.symbolicPower J s = J^s := by
  apply m.ideal_eq_of_le_of_initial_le (FourPapers.pow_le_symbolicPower J s)
  change initialIdeal m (FourPapers.symbolicPower J s) ≤ initialIdeal m (J^s)
  rw [initialIdeal_power_eq n m J E hinf hsup hinit s]
  exact initialIdeal_symbolicPower_le n m J E hinf hsup hinit s

end FourPapers.Sublattice.RowCutNetwork

end
end

section




set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice.RowCutNetwork
open Classical MvPolynomial Finset
universe u v
variable {ι : Type u} [Fintype ι] (n : ι → ℕ)
local instance : DecidableEq ι := Classical.decEq ι

def IsCover (E : Finset (Tuple n)) (C : Finset (Label n)) : Prop :=
  ∀ a ∈ E, ∃ i, (⟨i,a i⟩ : Label n) ∈ C

def IsMinimalCover (E : Finset (Tuple n)) (C : Finset (Label n)) : Prop :=
  IsCover n E C ∧ ∀ D, D ⊆ C → IsCover n E D → C ⊆ D

lemma exists_minimalCover (E : Finset (Tuple n)) (C : Finset (Label n))
    (hC : IsCover n E C) :
    ∃ D, D ⊆ C ∧ IsMinimalCover n E D := by
  let hex : ∃ r : ℕ, ∃ D : Finset (Label n), D ⊆ C ∧ IsCover n E D ∧ D.card = r :=
    ⟨C.card,C,Finset.Subset.refl C,hC,rfl⟩
  obtain ⟨D,hDC,hD,hr⟩ := Nat.find_spec hex
  refine ⟨D,hDC,hD,?_⟩
  intro B hBD hB
  have hcard : D.card ≤ B.card := by
    rw [hr]
    exact Nat.find_min' hex ⟨B,hBD.trans hDC,hB,rfl⟩
  exact (Finset.eq_of_subset_of_card_le hBD hcard).symm.subset

lemma monomialIdeal_le_coordinateIdeal {k : Type v} [CommSemiring k]
    (E : Finset (Tuple n)) (C : Finset (Label n)) (hC : IsCover n E C) :
    monomialIdeal n k E ≤ coordinateIdeal C := by
  apply Ideal.span_le.mpr
  rintro p ⟨a,ha,rfl⟩
  obtain ⟨i,hi⟩ := hC a ha
  have hle : Finsupp.single (⟨i,a i⟩ : Label n) 1 ≤ exponent n a := by
    intro x
    by_cases hx : x = (⟨i,a i⟩ : Label n)
    · subst x
      simp [exponent_apply]
    · simp [Finsupp.single_apply,Ne.symm hx]
  have hm : X (⟨i,a i⟩ : Label n) ∈ coordinateIdeal (k:=k) C :=
    Ideal.subset_span ⟨⟨i,a i⟩,hi,rfl⟩
  have hh := (coordinateIdeal (k:=k) C).mul_mem_left
    (monomial (exponent n a-Finsupp.single ⟨i,a i⟩ 1) 1) hm
  change monomial _ (1:k) * monomial _ 1 ∈ coordinateIdeal C at hh
  change monomial (exponent n a) (1:k) ∈ coordinateIdeal C
  simpa only [monomial_mul_monomial,one_mul,tsub_add_cancel_of_le hle] using hh

/-- The exact intersection over minimal vertex covers in Theorem 4.1,
with ordinary powers of the literal variable-generated coordinate ideals.
The equality holds over every commutative coefficient semiring. -/
theorem power_eq_iInf_minimalCover {k : Type v} [CommSemiring k]
    (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E) (s : ℕ) :
    (monomialIdeal n k E)^s =
      ⨅ C : {C : Finset (Label n) // IsMinimalCover n E C},
        coordinateIdeal C.val ^ s := by
  apply le_antisymm
  · apply le_iInf
    intro C
    exact Ideal.pow_right_mono (monomialIdeal_le_coordinateIdeal n E C.val C.property.1) s
  · intro f hf
    have hmon (a : Label n →₀ ℕ) (ha : a ∈ f.support) :
        monomial a (1:k) ∈ (monomialIdeal n k E)^s := by
      apply monomial_mem_power_of_covers n E hinf hsup a s
      intro C hC
      obtain ⟨D,hDC,hD⟩ := exists_minimalCover n E C hC
      have hfD : f ∈ coordinateIdeal (k:=k) D ^ s := by
        have hall := (Submodule.mem_iInf _).mp hf
        exact hall ⟨D,hD⟩
      have hweight := (mem_coverWeightIdeal D s f).mp
        (coordinateIdeal_power_le D s hfD) a ha
      exact hweight.trans (Finset.sum_le_sum_of_subset_of_nonneg hDC (by
        intro x hx hxD
        exact Nat.zero_le _))
    rw [f.as_sum]
    apply Ideal.sum_mem
    intro a ha
    have hh := ((monomialIdeal n k E)^s).mul_mem_left (C (f.coeff a)) (hmon a ha)
    simpa only [C_mul_monomial,mul_one] using hh

end FourPapers.Sublattice.RowCutNetwork

end
end

section




set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice.RowCutNetwork
open Classical MvPolynomial
universe u v
variable {ι : Type u} [Fintype ι] (n : ι → ℕ)
local instance : DecidableEq ι := Classical.decEq ι
variable {k : Type v} [Field k]

lemma initialIdeal_monomialIdeal (m : MonomialOrder (Label n)) (E : Finset (Tuple n)) :
    initialIdeal m (monomialIdeal n k E) = monomialIdeal n k E := by
  rw [monomialIdeal_span_image]
  exact initialIdeal_monomialSpan m _

/-- The complete ideal identities displayed in Theorem 4.1.
The symbolic-power convention here is exactly the paper's intersection
of contractions of P^s from the minimal-prime localizations. -/
theorem verified_theorem_4_1
    (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E) (s : ℕ) :
    (monomialIdeal n k E)^s = radicalSymbolicPower (monomialIdeal n k E) s ∧
    (monomialIdeal n k E)^s =
      ⨅ C : {C : Finset (Label n) // IsMinimalCover n E C}, coordinateIdeal C.val ^ s := by
  let ord : LinearOrder (Label n) := LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  let wf : @WellFoundedGT (Label n) ord.toLT :=
    @Finite.to_wellFoundedGT (Label n) inferInstance ord.toPreorder
  let m : MonomialOrder (Label n) := @MonomialOrder.lex (Label n) ord wf
  constructor
  · have hinit := initialIdeal_monomialIdeal n (k:=k) m E
    rw [←symbolicPower_eq_radicalSymbolicPower _
      (radical_of_sublattice_initial n m _ E hinit)]
    exact (symbolicPower_eq_power n m _ E hinf hsup hinit s).symm
  · exact power_eq_iInf_minimalCover n E hinf hsup s

/-- The symbolic and initial-ideal conclusions of Theorem 4.3; the Betti
and homology-generation conclusions are separate and not asserted here. -/
theorem verified_theorem_4_3_ideal_identities
    (m : MonomialOrder (Label n)) (J : Ideal (MvPolynomial (Label n) k))
    (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
    (hinit : initialIdeal m J = monomialIdeal n k E) (s : ℕ) :
    radicalSymbolicPower J s = J^s ∧
    initialIdeal m (radicalSymbolicPower J s) = (monomialIdeal n k E)^s ∧
    initialIdeal m (J^s) = (monomialIdeal n k E)^s := by
  have heq : radicalSymbolicPower J s = J^s := by
    rw [←symbolicPower_eq_radicalSymbolicPower J (radical_of_sublattice_initial n m J E hinit)]
    exact symbolicPower_eq_power n m J E hinf hsup hinit s
  exact ⟨heq,by rw [heq]; exact initialIdeal_power_eq n m J E hinf hsup hinit s,
    initialIdeal_power_eq n m J E hinf hsup hinit s⟩
end FourPapers.Sublattice.RowCutNetwork

end
end
#print axioms FourPapers.Sublattice.RowCutNetwork.verified_theorem_4_1
#check FourPapers.Sublattice.RowCutNetwork.verified_theorem_4_1
#print axioms FourPapers.Sublattice.RowCutNetwork.verified_theorem_4_3_ideal_identities

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerUncovered -/
section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
/- SOURCE FourPapers.Sublattice.FirstPowerUncovered -/
section ExtensionSource5

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- The row maximum need not be an edge or a member of the sublattice. Every
different actual generator still gives an explicitly contractible coefficient
block, with a homotopy raising the genuine exterior degree. -/
theorem firstPowerBlock_contractible_of_distinct_maximum
    (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : FiniteTuple n} {b : E}
    (hβ : RowMaximum β a) (hb : finiteRowExponent n b.val≤β) (hne : b.val≠a) :
    ∃H : Module.End k
      (TotalFaceModule (k := k) (quotientKoszulFaces (finitePredecessorFamily n E b.val)
        (β-finiteRowExponent n b.val))),
      quotientTotalDifferential (finitePredecessorFamily n E b.val)
        (β-finiteRowExponent n b.val)*H+
      H*quotientTotalDifferential (finitePredecessorFamily n E b.val)
        (β-finiteRowExponent n b.val)=1 ∧
      ∀i x,x∈totalFacePiece
        (quotientKoszulFaces (finitePredecessorFamily n E b.val)
          (β-finiteRowExponent n b.val)) i →
        H x∈totalFacePiece
        (quotientKoszulFaces (finitePredecessorFamily n E b.val)
          (β-finiteRowExponent n b.val)) (i+1) := by
  obtain ⟨r,hr,hpos⟩ := lower_generator_positive_unused hβ hb hne
  refine ⟨quotientTotalCreation (finitePredecessorFamily n E b.val)
    (β-finiteRowExponent n b.val) ⟨r,ULift.up (a r)⟩,?_,?_⟩
  · exact quotientTotalCreation_contracts_of_contains
      (finiteCoordinatePredecessor_contains_iff hE b.property)
      (coordinatePredecessor_isUnused E b.val r (a r) hr.le) hpos
  · exact quotientTotalCreation_raises_of_contains
      (finiteCoordinatePredecessor_contains_iff hE b.property)
      (coordinatePredecessor_isUnused E b.val r (a r) hr.le) hpos

end FourPapers.Sublattice
end

end
end ExtensionSource5


end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FixedFaceFactor -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- When a variable quotient forces one exterior face, exterior multiplication
by that face is an actual equivalence, over an arbitrary coefficient ring. -/
def fixedFaceIndexEquiv (S : V → Prop) (A : Finset V) (Q : Finset V → Prop)
    (hA : ∀v∈A, S v) (hQ : ∀G, Q G → ∀v∈G, ¬S v) :
    {G // Q G} ≃ {F // splitFacePredicate S (fun F => F=A) Q F} :=
  (show {G // Q G} ≃ ({F : Finset V // F=A} × {G // Q G}) from
    { toFun := fun G => (⟨A,rfl⟩,G)
      invFun := Prod.snd
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨F,hF⟩,G⟩
        subst F
        rfl }).trans
    (splitFaceIndexEquiv S (fun F => F=A) Q (by rintro F rfl; exact hA) hQ)

def fixedFaceFactorEquiv (S : V → Prop) (A : Finset V) (Q : Finset V → Prop)
    (hA : ∀v∈A, S v) (hQ : ∀G, Q G → ∀v∈G, ¬S v) :
    TotalFaceModule (k := k) Q ≃ₗ[k]
      TotalFaceModule (k := k) (splitFacePredicate S (fun F => F=A) Q) :=
  signedBasisEquiv (totalFaceBasis Q)
    (totalFaceBasis (splitFacePredicate S (fun F => F=A) Q))
    (fixedFaceIndexEquiv S A Q hA hQ)
    (fun G => faceWedgeSign A G.val (Finset.disjoint_left.mpr
      (fun v hv hv' => hQ G.val G.property v hv' (hA v hv))))

lemma fixedFaceFactorEquiv_val (S : V → Prop) (A : Finset V) (Q : Finset V → Prop)
    (hA : ∀v∈A, S v) (hQ : ∀G, Q G → ∀v∈G, ¬S v)
    (x : TotalFaceModule (k := k) Q) :
    (fixedFaceFactorEquiv S A Q hA hQ x).val = Simplicial.basis A * x.val := by
  let f : TotalFaceModule (k := k) Q →ₗ[k] Simplicial.Ambient V k :=
    (TotalFaceModule (k := k) (splitFacePredicate S (fun F => F=A) Q)).subtype.comp
      (fixedFaceFactorEquiv S A Q hA hQ).toLinearMap
  let g : TotalFaceModule (k := k) Q →ₗ[k] Simplicial.Ambient V k :=
    (LinearMap.mulLeft k (Simplicial.basis A)).comp (TotalFaceModule (k := k) Q).subtype
  have h : f=g := by
    apply (totalFaceBasis (k := k) Q).ext
    intro G
    change (fixedFaceFactorEquiv (k := k) S A Q hA hQ
      (totalFaceBasis (k := k) Q G)).val =
      Simplicial.basis (k := k) A * (totalFaceBasis (k := k) Q G).val
    rw [fixedFaceFactorEquiv,signedBasisEquiv_basis,totalFaceBasis_val,
      Submodule.coe_smul_of_tower,totalFaceBasis_val]
    exact (faceBasis_mul_of_disjoint (k := k) A G.val _).symm
  exact LinearMap.congr_fun h x

lemma fixedFace_projectedDifferential_zero (A : Finset V) :
    projectedTotalDifferential (k := k) (fun F => F=A) = 0 := by
  apply (totalFaceBasis (k := k) (fun F => F=A)).ext
  rintro ⟨F,hF⟩
  change F = A at hF
  subst F
  apply Subtype.ext
  simp only [LinearMap.zero_apply, projectedTotalDifferential_val,
    totalFaceBasis_val, ZeroMemClass.coe_zero]
  rw [Simplicial.boundary_eq_sum,map_sum]
  apply Finset.sum_eq_zero
  intro v _
  rw [Simplicial.contraction_basis]
  by_cases hv : v∈A
  · rw [if_pos hv,LinearMapClass.map_smul_of_tower (S := k),faceProjection_basis]
    have hne : A.erase v ≠ A := by
      intro h
      have hh : v∈A.erase v := h.symm ▸ hv
      exact Finset.notMem_erase v A hh
    rw [if_neg hne,smul_zero]
  · rw [if_neg hv,map_zero]

/-- The sign is the usual tensor differential sign of the fixed left face. -/
lemma fixedFaceFactorEquiv_differential (S : V → Prop) (A : Finset V)
    (Q : Finset V → Prop) (hA : ∀v∈A, S v) (hQ : ∀G, Q G → ∀v∈G, ¬S v)
    (x : TotalFaceModule (k := k) Q) :
    projectedTotalDifferential (splitFacePredicate S (fun F => F=A) Q)
        (fixedFaceFactorEquiv S A Q hA hQ x) =
      (-1 : k)^A.card • fixedFaceFactorEquiv S A Q hA hQ
        (projectedTotalDifferential Q x) := by
  let a : TotalFaceModule (k := k) (fun F => F=A) := totalFaceBasis _ ⟨A,rfl⟩
  have ha : a.val=Simplicial.basis A := totalFaceBasis_val _ _
  have h := projectedTotalDifferential_mul_separated S (fun F => F=A) Q
    (by rintro F rfl; exact hA) hQ a x
  apply Subtype.ext
  apply_fun (fun z => z.val) at h
  change faceProjection (splitFacePredicate S (fun F => F=A) Q)
      (Simplicial.boundary (a.val*x.val)) =
    (projectedTotalDifferential (fun F => F=A) a).val*x.val +
      CliffordAlgebra.involute a.val*(projectedTotalDifferential Q x).val at h
  have hb : CliffordAlgebra.involute (Simplicial.basis (k := k) A) =
      (-1 : k)^A.card • Simplicial.basis A :=
    TauCeti.ExteriorAlgebra.involute_basis (Pi.basisFun k V) A
  rw [fixedFace_projectedDifferential_zero,LinearMap.zero_apply,
    ZeroMemClass.coe_zero,zero_mul,zero_add,ha,hb] at h
  change faceProjection (splitFacePredicate S (fun F => F=A) Q)
      (Simplicial.boundary ((fixedFaceFactorEquiv S A Q hA hQ x).val)) = _
  rw [fixedFaceFactorEquiv_val,h,smul_mul_assoc]
  rw [Submodule.coe_smul,fixedFaceFactorEquiv_val]

lemma fixedFaceFactorEquiv_cycle_iff (S : V → Prop) (A : Finset V)
    (Q : Finset V → Prop) (hA : ∀v∈A, S v) (hQ : ∀G, Q G → ∀v∈G, ¬S v)
    (x : TotalFaceModule (k := k) Q) :
    projectedTotalDifferential (splitFacePredicate S (fun F => F=A) Q)
      (fixedFaceFactorEquiv S A Q hA hQ x)=0 ↔ projectedTotalDifferential Q x=0 := by
  have hs : IsUnit ((-1 : k)^A.card) := (IsUnit.neg isUnit_one).pow A.card
  rw [fixedFaceFactorEquiv_differential,hs.smul_eq_zero,LinearEquiv.map_eq_zero_iff]

/-- Every cycle in a variable-factor quotient is literally one fixed face
times a cycle in the residual quotient. No field or Künneth hypothesis occurs. -/
theorem fixedFace_cycle_factorization (S : V → Prop) (A : Finset V)
    (Q : Finset V → Prop) (hA : ∀v∈A, S v) (hQ : ∀G, Q G → ∀v∈G, ¬S v)
    (z : TotalFaceModule (k := k) (splitFacePredicate S (fun F => F=A) Q))
    (hz : projectedTotalDifferential _ z=0) :
    ∃ x : TotalFaceModule (k := k) Q,
      projectedTotalDifferential Q x=0 ∧ z.val=Simplicial.basis A*x.val := by
  let e := fixedFaceFactorEquiv (k := k) S A Q hA hQ
  refine ⟨e.symm z,?_,?_⟩
  · apply (fixedFaceFactorEquiv_cycle_iff S A Q hA hQ _).mp
    change projectedTotalDifferential _ (e (e.symm z)) = 0
    simpa only [e.apply_symm_apply] using hz
  · have hval := fixedFaceFactorEquiv_val S A Q hA hQ (e.symm z)
    change (e (e.symm z)).val = _ at hval
    simpa only [e.apply_symm_apply] using hval

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerHomologyDetection -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- The actual maximal-block projection commutes with the ordinary differential. -/
lemma firstPowerBlockProjection_differential (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : ChainTotalModule n E 1 β k) :
    (chainTotalOrdinaryDifferential hE 1 β k x) (firstPowerTarget hβ) =
      quotientTotalDifferential
        (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
        (β-finiteChainShift n (firstPowerTarget hβ).val) (x (firstPowerTarget hβ)) := by
  have h := LinearMap.congr_fun (maximalBlock_projection_lower
    (fun w : AdmissibleChain n E 1 β => totalFaceBasis (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
        (β-finiteChainShift n w.val)))
    (fun w => finiteChainFactorWeight.{u} w.val) (firstPowerTarget hβ)
    (firstPowerTarget_maximalWeight hβ)
    (chainTotalOrdinaryDifferential hE 1 β k-chainTotalSpecialDifferential n E 1 β k)
    (chainTotalDifferential_strictLower hE 1 β k)) x
  change (chainTotalOrdinaryDifferential hE 1 β k x) (firstPowerTarget hβ) -
    quotientTotalDifferential _ _ (x (firstPowerTarget hβ)) = 0 at h
  exact sub_eq_zero.mp h

/-- Every cycle in the kernel of the actual maximal-block projection has an
explicit integral filling. The lower-block contractions and the finite
triangular perturbation have already been constructed from the lattice. -/
lemma firstPowerBlockCycle_boundary (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : ChainTotalModule n E 1 β k)
    (hx : chainTotalOrdinaryDifferential hE 1 β k x = 0)
    (hq : x (firstPowerTarget hβ) = 0) :
    ∃ y : ChainTotalModule n E 1 β k, chainTotalOrdinaryDifferential hE 1 β k y = x := by
  let b := fun w : AdmissibleChain n E 1 β => totalFaceBasis (k := k)
    (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val))
  let rank := fun w : AdmissibleChain n E 1 β => finiteChainFactorWeight.{u} w.val
  let D := chainTotalOrdinaryDifferential hE 1 β k
  let dB := fun w : AdmissibleChain n E 1 β => quotientTotalDifferential (k := k)
    (finiteChainCoefficientFamily n w.val) (β-finiteChainShift n w.val)
  let H := firstPowerLowerHomotopy (k := k) hE hβ
  have hlow : ∀ i j : ChainFaceIndex n E 1 β, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr ((D-blockSpecialDifferential dB) ((DFinsupp.basis b) i)) j = 0 :=
    chainTotalDifferential_strictLower hE 1 β k
  have hqδ : ∀ z, ((D-blockSpecialDifferential dB) z) (firstPowerTarget hβ) = 0 := by
    intro z
    exact LinearMap.congr_fun (maximalBlock_projection_lower b rank (firstPowerTarget hβ)
      (firstPowerTarget_maximalWeight hβ) (D-blockSpecialDifferential dB) hlow) z
  have hcontract := partialPerturbation_contracts (DFinsupp.basis b) (fun i => rank i.1)
    (DFinsupp.lapply (firstPowerTarget hβ)) D (blockSpecialDifferential dB)
    (blockPartialHomotopy (firstPowerTarget hβ) H)
    (chainTotalOrdinaryDifferential_square_zero hE 1 β k)
    (blockSpecialDifferential_square_zero dB (fun w => quotientTotalDifferential_comp _ _))
    hqδ (blockPartialHomotopy_projection (firstPowerTarget hβ) H)
    (blockPartialHomotopy_contracts dB (firstPowerTarget hβ) H
      (firstPowerLowerHomotopy_contracts hE hβ))
    (blockPerturbationLower b rank (firstPowerTarget hβ) D dB H hlow)
  let T := blockKernelHomotopy b rank (firstPowerTarget hβ) D dB H hlow
  refine ⟨T x, ?_⟩
  have hc : D (T x)+T (D x)=x := hcontract.2 x hq
  simpa only [show D x=0 from hx,map_zero,add_zero] using hc

/-- Projection from the actual ideal face complex to the literal predecessor
quotient at its row maximum. Its target is the paper's colon quotient strand. -/
def firstPowerFaceProjection (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val) :
    TotalFaceModule (k := k)
        (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β) →ₗ[k]
      TotalFaceModule (k := k)
        (quotientKoszulFaces (finitePredecessorFamily n E a.val)
          (β-finiteRowExponent n a.val)) :=
  (LinearEquiv.ofEq _ _ (firstPowerSourceModule_eq (k := k) hβ)).symm.toLinearMap.comp
    ((DFinsupp.lapply (firstPowerTarget hβ)).comp (chainTotalEquiv hE 1 β k).symm.toLinearMap)

lemma firstPowerFaceProjection_cast (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β)) :
    firstPowerSourceCast (k := k) hβ (firstPowerFaceProjection hE hβ x) =
      ((chainTotalEquiv hE 1 β k).symm x) (firstPowerTarget hβ) :=
  (LinearEquiv.ofEq _ _ (firstPowerSourceModule_eq (k := k) hβ)).apply_symm_apply _

lemma firstPowerFaceProjection_differential (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β)) :
    firstPowerFaceProjection hE hβ (idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) β) x) =
      quotientTotalDifferential (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val) (firstPowerFaceProjection hE hβ x) := by
  apply (LinearEquiv.ofEq _ _ (firstPowerSourceModule_eq (k := k) hβ)).injective
  change firstPowerSourceCast hβ (firstPowerFaceProjection hE hβ
      (idealTotalDifferential _ x)) =
    firstPowerSourceCast hβ (quotientTotalDifferential _ _ (firstPowerFaceProjection hE hβ x))
  rw [firstPowerFaceProjection_cast,←firstPowerSourceCast_differential,
    firstPowerFaceProjection_cast]
  have h := firstPowerBlockProjection_differential hE hβ ((chainTotalEquiv hE 1 β k).symm x)
  simpa only [chainTotalOrdinaryDifferential,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using h

lemma firstPowerFaceProjection_lift (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val))) :
    firstPowerFaceProjection hE hβ (firstPowerExteriorLift hE hβ x)=x := by
  apply (LinearEquiv.ofEq _ _ (firstPowerSourceModule_eq (k := k) hβ)).injective
  change firstPowerSourceCast hβ (firstPowerFaceProjection hE hβ
      (firstPowerExteriorLift hE hβ x)) = firstPowerSourceCast hβ x
  rw [firstPowerFaceProjection_cast]
  simp only [firstPowerExteriorLift,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun (firstPowerChainSection_is_chain (k := k) hE hβ).1
    (firstPowerSourceCast hβ x)

theorem firstPowerFaceCycle_boundary_of_zero_projection (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β))
    (hx : idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) β) x=0)
    (hq : firstPowerFaceProjection hE hβ x=0) :
    ∃ y, idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) β) y=x := by
  let t := chainTotalEquiv hE 1 β k
  have hc : chainTotalOrdinaryDifferential hE 1 β k (t.symm x)=0 := by
    simp only [chainTotalOrdinaryDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
      t,LinearEquiv.apply_symm_apply,hx,map_zero]
  have hp : (t.symm x) (firstPowerTarget hβ)=0 := by
    rw [←firstPowerFaceProjection_cast hE hβ x,hq,map_zero]
  obtain ⟨z,hz⟩ := firstPowerBlockCycle_boundary hE hβ (t.symm x) hc hp
  refine ⟨t z, ?_⟩
  have h := congrArg t hz
  simpa only [chainTotalOrdinaryDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    t,LinearEquiv.apply_symm_apply] using h

/-- The top predecessor block detects actual boundaries, over every ring. -/
theorem firstPowerFaceCycle_boundary_iff (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β))
    (hx : idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) β) x=0) :
    (∃ y, idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) β) y=x) ↔
    ∃ z, quotientTotalDifferential (finitePredecessorFamily n E a.val)
      (β-finiteRowExponent n a.val) z=firstPowerFaceProjection hE hβ x := by
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨firstPowerFaceProjection hE hβ y,(firstPowerFaceProjection_differential hE hβ y).symm⟩
  · rintro ⟨z,hz⟩
    let D := idealTotalDifferential (k := k)
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) β)
    let y := firstPowerExteriorLift hE hβ z
    have hc : D (x-D y)=0 := by
      rw [map_sub,hx]
      have hD : D (D y)=0 := by
        apply Subtype.ext
        exact Simplicial.boundary_boundary y.val
      rw [hD,sub_zero]
    have hp : firstPowerFaceProjection hE hβ (x-D y)=0 := by
      rw [map_sub,firstPowerFaceProjection_differential,firstPowerFaceProjection_lift,hz,sub_self]
    obtain ⟨b,hb⟩ := firstPowerFaceCycle_boundary_of_zero_projection hE hβ (x-D y) hc hp
    refine ⟨b+y, ?_⟩
    change D (b+y)=x
    rw [map_add,hb,sub_add_cancel]

end FourPapers.Sublattice

namespace FourPapers.Sublattice
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- A boundary-detecting chain map reduces cycle generation to its target.
This is used only after the target spanning statement and the detection
property have been proved for the actual complexes. -/
theorem cycle_spanning_of_boundary_detection
    (D : Module.End R M) (d : Module.End R N) (q : M →ₗ[R] N)
    (hq : ∀ x, q (D x)=d (q x))
    (hdetect : ∀x, D x=0 → (∃ y,d y=q x) → ∃ y,D y=x)
    (G : Set M) (hG : G ⊆ LinearMap.ker D)
    (hspan : LinearMap.ker d ≤ (Submodule.span R G).map q ⊔ LinearMap.range d) :
    LinearMap.ker D ≤ Submodule.span R G ⊔ LinearMap.range D := by
  intro z hz
  have hqz : q z ∈ LinearMap.ker d := by
    change d (q z)=0
    rw [←hq,show D z=0 from hz,map_zero]
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp (hspan hqz)
  obtain ⟨x,hx,hqx⟩ := ha
  have hxclosed : D x=0 := (Submodule.span_le.mpr hG) hx
  have hclosed : D (z-x)=0 := by rw [map_sub,show D z=0 from hz,hxclosed,sub_self]
  have hproj : ∃ y,d y=q (z-x) := by
    obtain ⟨y,hy⟩ := hb
    refine ⟨y, ?_⟩
    rw [map_sub,hqx,←hab,add_sub_cancel_left]
    exact hy
  obtain ⟨y,hy⟩ := hdetect (z-x) hclosed hproj
  exact Submodule.mem_sup.mpr ⟨x,hx,z-x,⟨y,hy⟩,by abel⟩

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- The literal first-power cycle-generation reduction, with the boundary
detector proved from the sublattice rather than supplied as a hypothesis. -/
theorem firstPowerFaceCycle_generated (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (G : Set (TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β)))
    (hG : G ⊆ (LinearMap.ker (idealTotalDifferential (k := k)
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) β)) : Set _))
    (hspan : LinearMap.ker (quotientTotalDifferential (k := k)
        (finitePredecessorFamily n E a.val) (β-finiteRowExponent n a.val)) ≤
      (Submodule.span k G).map (firstPowerFaceProjection hE hβ) ⊔
        LinearMap.range (quotientTotalDifferential (finitePredecessorFamily n E a.val)
          (β-finiteRowExponent n a.val))) :
    LinearMap.ker (idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) β)) ≤
      Submodule.span k G ⊔ LinearMap.range (idealTotalDifferential
        (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) β)) :=
  cycle_spanning_of_boundary_detection
    (idealTotalDifferential (k := k)
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) β))
    (quotientTotalDifferential (k := k) (finitePredecessorFamily n E a.val)
      (β-finiteRowExponent n a.val))
    (firstPowerFaceProjection (k := k) hE hβ)
    (firstPowerFaceProjection_differential (k := k) hE hβ)
    (fun x hx h => (firstPowerFaceCycle_boundary_iff hE hβ x hx).mpr h)
    G hG hspan

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.firstPowerFaceCycle_boundary_iff
#print axioms FourPapers.Sublattice.firstPowerFaceCycle_generated
#print axioms FourPapers.Sublattice.cycle_spanning_of_boundary_detection


end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerProjectionCoordinates -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma firstPowerFaceProjection_val_cast (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β)) :
    (firstPowerFaceProjection hE hβ x).val =
      (((chainTotalEquiv hE 1 β k).symm x) (firstPowerTarget hβ)).val := by
  have h := congrArg Subtype.val (firstPowerFaceProjection_cast hE hβ x)
  simpa only [firstPowerSourceCast_val] using h

/-- The maximal-block map is exactly the basis quotient projection on exterior
coordinates. This identifies the algebraic projection used for homology
with the concrete erasure calculation on rectangle cycles. -/
theorem firstPowerFaceProjection_val (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E} (hβ : RowMaximum β a.val)
    (x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β)) :
    (firstPowerFaceProjection hE hβ x).val =
      quotientFaceProjection (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val) x.val := by
  let t := chainTotalEquiv hE 1 β k
  let Q := quotientKoszulFaces (finitePredecessorFamily n E a.val)
    (β-finiteRowExponent n a.val)
  let M := TotalFaceModule (k := k)
    (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) β)
  let L : ChainTotalModule n E 1 β k →ₗ[k] Simplicial.Ambient (FiniteVariable.{u} n) k :=
    (TotalFaceModule (k := k) Q).subtype.comp ((firstPowerFaceProjection hE hβ).comp t.toLinearMap)
  let R : ChainTotalModule n E 1 β k →ₗ[k] Simplicial.Ambient (FiniteVariable.{u} n) k :=
    (quotientFaceProjection (finitePredecessorFamily n E a.val)
      (β-finiteRowExponent n a.val)).comp (M.subtype.comp t.toLinearMap)
  have hLR : L=R := by
    apply (chainTotalBasis n E 1 β k).ext
    rintro ⟨w,F⟩
    change (firstPowerFaceProjection hE hβ
      (t (chainTotalBasis n E 1 β k ⟨w,F⟩))).val =
      quotientFaceProjection (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val) (t (chainTotalBasis n E 1 β k ⟨w,F⟩)).val
    rw [firstPowerFaceProjection_val_cast,LinearEquiv.symm_apply_apply,
      chainTotalEquiv_basis,totalFaceBasis_val,chainFaceEquiv_val,chainTotalBasis_apply]
    by_cases hw : w=firstPowerTarget hβ
    · subst w
      have hF : Q F.val := by
        simpa only [Q,firstPowerTarget,singletonChain_coefficient,singletonChain_shift]
          using F.property
      change quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val) F.val at hF
      change fullKoszulFaces (β-finiteRowExponent n a.val) F.val ∧
        ¬forbiddenKoszulFaces (finitePredecessorFamily n E a.val)
          (β-finiteRowExponent n a.val) F.val at hF
      simp only [DFinsupp.single_eq_same,totalFaceBasis_val,quotientFaceProjection,
        relativeProjection_basis,if_pos hF]
    · have hn : ¬Q F.val := by
        intro hF
        let G : {G // quotientKoszulFaces
            (finiteChainCoefficientFamily n (firstPowerTarget hβ).val)
            (β-finiteChainShift n (firstPowerTarget hβ).val) G} :=
          ⟨F.val,by simpa only [Q,firstPowerTarget,singletonChain_coefficient,
            singletonChain_shift] using hF⟩
        have he : (⟨w,F⟩ : ChainFaceIndex n E 1 β) = ⟨firstPowerTarget hβ,G⟩ := by
          apply (chainFaceEquiv hE β).injective
          apply Subtype.ext
          rfl
        exact hw (congrArg Sigma.fst he)
      change ¬quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (β-finiteRowExponent n a.val) F.val at hn
      change ¬(fullKoszulFaces (β-finiteRowExponent n a.val) F.val ∧
        ¬forbiddenKoszulFaces (finitePredecessorFamily n E a.val)
          (β-finiteRowExponent n a.val) F.val) at hn
      simp only [DFinsupp.single_eq_of_ne (Ne.symm hw),ZeroMemClass.coe_zero,quotientFaceProjection,
        relativeProjection_basis,if_neg hn]
  have h := LinearMap.congr_fun hLR (t.symm x)
  change (firstPowerFaceProjection hE hβ (t (t.symm x))).val =
    quotientFaceProjection (finitePredecessorFamily n E a.val)
      (β-finiteRowExponent n a.val) (t (t.symm x)).val at h
  simpa only [LinearEquiv.apply_symm_apply] using h

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialDiagonalResolution -/
section

/-!
# The actual polynomial diagonal resolution

The sequence `X i - C (a i)` is obtained from the polynomial variables by a
coefficient-preserving translation automorphism. Its Koszul complex is an
actual free resolution of its quotient, and that quotient is identified with
the coefficient ring by evaluation at `a`. Taking the coefficient ring to be
another polynomial ring gives the universal diagonal complex used in the
construction of a resolution of a polynomial module.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.PolynomialDiagonalResolution

open MvPolynomial CategoryTheory

universe u v
variable {R : Type u} {V : Type v} [CommRing R]

/-- Translation is a genuine algebra automorphism, with the inverse proved
by the universal property of the polynomial ring. -/
def translation (a : V → R) : MvPolynomial V R ≃ₐ[R] MvPolynomial V R where
  toFun := aeval (fun i => X i + C (a i))
  invFun := aeval (fun i => X i - C (a i))
  left_inv f := by
    have he : (aeval (fun i => X i - C (a i))).comp
        (aeval (fun i => X i + C (a i))) =
          AlgHom.id R (MvPolynomial V R) := by
      ext i
      simp
    exact AlgHom.congr_fun he f
  right_inv f := by
    have he : (aeval (fun i => X i + C (a i))).comp
        (aeval (fun i => X i - C (a i))) =
          AlgHom.id R (MvPolynomial V R) := by
      ext i
      simp
    exact AlgHom.congr_fun he f
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' r := by simp

@[simp] theorem translation_X (a : V → R) (i : V) :
    translation a (X i) = X i + C (a i) := by
  change aeval _ (X i) = _
  simp

@[simp] theorem translation_C (a : V → R) (r : R) :
    translation a (C r) = C r := (translation a).commutes r

@[simp] theorem translation_symm_X (a : V → R) (i : V) :
    (translation a).symm (X i) = X i - C (a i) := by
  change aeval _ (X i) = _
  simp

def diagonalIdeal (a : V → R) : Ideal (MvPolynomial V R) :=
  Ideal.span (Set.range (fun i => X i - C (a i)))

theorem translation_diagonalIdeal (a : V → R) :
    (diagonalIdeal a).map (translation a).toRingEquiv.toRingHom =
      MvPolynomial.idealOfVars V R := by
  rw [diagonalIdeal, Ideal.map_span]
  change Ideal.span ((translation a) '' Set.range (fun i => X i - C (a i))) =
    Ideal.span (Set.range (X : V → MvPolynomial V R))
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    simp
  · rintro ⟨i, rfl⟩
    exact ⟨X i - C (a i), ⟨i, rfl⟩, by simp⟩

theorem constantCoeff_translation (a : V → R) (f : MvPolynomial V R) :
    constantCoeff (translation a f) = aeval a f := by
  have he : (aeval (fun _ : V => (0 : R))).comp (translation a).toAlgHom =
      aeval a := by
    ext i
    simp
  simpa using AlgHom.congr_fun he f

/-- The constant-coefficient kernel, allowing independent universes for
variables and coefficients. -/
private theorem constantCoeff_kernel :
    RingHom.ker (constantCoeff : MvPolynomial V R →+* R) = idealOfVars V R := by
  classical
  ext f
  rw [RingHom.mem_ker, constantCoeff_eq]
  change f.coeff 0 = 0 ↔ f ∈ Ideal.span (Set.range (X : V → MvPolynomial V R))
  rw [← Set.image_univ, mem_ideal_span_X_image]
  constructor
  · intro hf a ha
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      exact (MvPolynomial.mem_support_iff.mp ha) hf
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 (Finsupp.ext h)
    exact ⟨i, Set.mem_univ i, hi⟩
  · intro hf
    by_contra h
    obtain ⟨i, _, hi⟩ := hf 0 (MvPolynomial.mem_support_iff.mpr h)
    exact hi rfl

/-- The displayed generators give the literal kernel of evaluation. -/
theorem diagonalIdeal_eq_kernel (a : V → R) :
    diagonalIdeal a = RingHom.ker (aeval a).toRingHom := by
  ext f
  have hm : translation a f ∈
      (diagonalIdeal a).map (translation a).toRingEquiv.toRingHom ↔
        f ∈ diagonalIdeal a := by
    rw [Ideal.mem_map_iff_of_surjective
      (translation a).toRingEquiv.toRingHom (translation a).surjective]
    constructor
    · rintro ⟨g, hg, he⟩
      exact (translation a).injective he ▸ hg
    · intro hf
      exact ⟨f, hf, rfl⟩
  rw [← hm, translation_diagonalIdeal,
    ← constantCoeff_kernel (R := R) (V := V), RingHom.mem_ker,
    constantCoeff_translation, RingHom.mem_ker]
  rfl

set_option maxHeartbeats 200000 in
/-- Evaluation identifies the quotient with the original coefficient ring,
as an algebra over that ring. -/
def diagonalQuotientEquiv (a : V → R) :
    (MvPolynomial V R ⧸ diagonalIdeal a) ≃ₐ[R] R := by
  let e : (MvPolynomial V R ⧸ diagonalIdeal a) ≃ₐ[R]
      (MvPolynomial V R ⧸ RingHom.ker (aeval a : MvPolynomial V R →ₐ[R] R).toRingHom) :=
    Ideal.quotientEquivAlgOfEq R (diagonalIdeal_eq_kernel a)
  let g : (MvPolynomial V R ⧸
      RingHom.ker (aeval a : MvPolynomial V R →ₐ[R] R).toRingHom) ≃ₐ[R] R :=
    Ideal.quotientKerAlgEquivOfRightInverse
      (f := (aeval a : MvPolynomial V R →ₐ[R] R))
      (g := fun r : R => (C r : MvPolynomial V R)) (fun r => by simp)
  exact e.trans g

section Finite

variable [Nontrivial R] (N : ℕ) (a : Fin N → R)

def diagonalList : List (MvPolynomial (Fin N) R) :=
  List.ofFn (fun i => X i - C (a i))

theorem diagonalList_regular :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin N) R) (diagonalList N a) := by
  let e : MvPolynomial (Fin N) R ≃ₐ[R] MvPolynomial (Fin N) R :=
    (translation a).symm
  have he : List.Forall₂
      (fun (f g : MvPolynomial (Fin N) R) =>
        ∀ x : MvPolynomial (Fin N) R, e (f • x) = g • e x)
      (List.ofFn (X : Fin N → MvPolynomial (Fin N) R))
      ((List.ofFn (X : Fin N → MvPolynomial (Fin N) R)).map e) := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro f _ x
    exact e.map_mul f x
  have h := (AddEquiv.isRegular_congr (e := e.toRingEquiv.toAddEquiv) he).mp
    (CommAlg.Koszul.fin_variables_regular (k := R) N)
  have hl : (List.ofFn (X : Fin N → MvPolynomial (Fin N) R)).map e =
      diagonalList N a := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact translation_symm_X a i
  exact hl ▸ h

theorem diagonalList_ideal : Ideal.ofList (diagonalList N a) = diagonalIdeal a := by
  apply congrArg Ideal.span
  ext f
  simp only [diagonalList, List.mem_ofFn, Set.mem_range]
  rfl

/-- The ordinary Koszul complex on the displayed differences, as a genuine
projective resolution in the module category of the polynomial ring. -/
def diagonalResolution : ProjectiveResolution
    (ModuleCat.of (MvPolynomial (Fin N) R)
      (MvPolynomial (Fin N) R ⧸ diagonalIdeal a)) :=
  CommAlg.Koszul.transportResolution
    (CommAlg.Koszul.regularSequenceResolution (diagonalList N a)
      (diagonalList_regular N a))
    (Submodule.quotEquivOfEq _ _ (diagonalList_ideal N a)).toModuleIso

@[simp] theorem diagonalResolution_complex :
    (diagonalResolution N a).complex =
      koszulComplex.ofList (diagonalList N a) := rfl

theorem diagonalComplex_exact_positive (p : ℕ) (hp : p ≠ 0) :
    (koszulComplex.ofList (diagonalList N a)).ExactAt p :=
  koszulComplex.exactAt_of_isRegular _ (diagonalList_regular N a) p hp

end Finite
end FourPapers.PolynomialDiagonalResolution

end
end
end


end
