module
prelude
public import WitnessGrowthDAG

@[expose] public section

/-!
# Renaming finite boundary problems

The renaming contains explicit inverse maps. Its laws concern only incidence,
facet kind, and pair compatibility. They imply preservation of every target
condition used by growth; no completeness or realizability assertion occurs
among the renaming laws. A geometric application additionally identifies these
cell and ridge maps with the recorded permutation of vertex labels.
-/

namespace Papers.RationalityTen.GrowthRenaming

open GrowthDAG SparseGrowthDAG GrowthPruning

structure Bijection (α : Type) where
  forward : α → α
  inverse : α → α
  left_inverse : ∀ a, inverse (forward a) = a
  right_inverse : ∀ a, forward (inverse a) = a

theorem Bijection.injective {α : Type} (p : Bijection α) {a b : α}
    (h : p.forward a = p.forward b) : a = b := by
  have h' := congrArg p.inverse h
  simpa only [p.left_inverse] using h'

variable {n r : Nat}

theorem mem_map_iff (p : Bijection (Fin n)) (B : List (Fin n)) (c : Fin n) :
    p.forward c ∈ B.map p.forward ↔ c ∈ B := by
  constructor
  · intro h
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp h
    exact p.injective heq ▸ ha
  · intro h
    exact List.mem_map.mpr ⟨c, h, rfl⟩

theorem family_map (p : Bijection (Fin n)) (B : List (Fin n)) (c : Fin n) :
    family (B.map p.forward) (p.forward c) = family B c := by
  apply Bool.eq_iff_iff.mpr
  change has (B.map p.forward) (p.forward c) = true ↔ has B c = true
  rw [has_true, has_true]
  exact mem_map_iff p B c

structure Renaming (ridges : Fin n → Fin r → Bool)
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat) where
  cells : Bijection (Fin n)
  ridgeMap : Bijection (Fin r)
  incidence : ∀ c q, ridges (cells.forward c) (ridgeMap.forward q) = ridges c q
  compatibility : ∀ a b, compatible (cells.forward a) (cells.forward b) = compatible a b
  kind_preserved : ∀ c, kind (cells.forward c) = kind c

theorem kindCount_map (ridges : Fin n → Fin r → Bool)
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (p : Renaming ridges compatible kind) (B : List (Fin n)) (k : Nat) :
    kindCount kind (B.map p.cells.forward) k = kindCount kind B k := by
  simp only [kindCount, List.filter_map, Function.comp_def, p.kind_preserved, List.length_map]

theorem hasMate_map (ridges : Fin n → Fin r → Bool)
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (p : Renaming ridges compatible kind) (B : List (Fin n))
    (h : HasMate ridges (family B)) :
    HasMate ridges (family (B.map p.cells.forward)) := by
  intro q a ha
  obtain ⟨x, hx, hxa⟩ := List.mem_map.mp ((has_true _ a).mp ha.1)
  subst a
  have hxq : ridges x (p.ridgeMap.inverse q) = true := by
    rw [← p.incidence, p.ridgeMap.right_inverse]
    exact ha.2
  obtain ⟨y, hy, hne⟩ := h (p.ridgeMap.inverse q) x ⟨(has_true B x).mpr hx, hxq⟩
  refine ⟨p.cells.forward y, ⟨?_, ?_⟩, ?_⟩
  · rw [family_map]
    exact hy.1
  · rw [← p.ridgeMap.right_inverse q, p.incidence]
    exact hy.2
  · exact fun heq => hne (p.cells.injective heq)

theorem noThree_map (ridges : Fin n → Fin r → Bool)
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (p : Renaming ridges compatible kind) (B : List (Fin n))
    (h : NoThree ridges (family B)) :
    NoThree ridges (family (B.map p.cells.forward)) := by
  intro q a b c ha hb hc
  obtain ⟨x, hx, hxa⟩ := List.mem_map.mp ((has_true _ a).mp ha.1)
  obtain ⟨y, hy, hyb⟩ := List.mem_map.mp ((has_true _ b).mp hb.1)
  obtain ⟨z, hz, hzc⟩ := List.mem_map.mp ((has_true _ c).mp hc.1)
  subst a b c
  have hi (u : Fin n) (hu : ridges (p.cells.forward u) q = true) :
      ridges u (p.ridgeMap.inverse q) = true := by
    rw [← p.incidence, p.ridgeMap.right_inverse]
    exact hu
  rcases h (p.ridgeMap.inverse q) x y z
      ⟨(has_true B x).mpr hx, hi x ha.2⟩
      ⟨(has_true B y).mpr hy, hi y hb.2⟩
      ⟨(has_true B z).mpr hz, hi z hc.2⟩ with heq | heq | heq
  · exact Or.inl (congrArg p.cells.forward heq)
  · exact Or.inr (Or.inl (congrArg p.cells.forward heq))
  · exact Or.inr (Or.inr (congrArg p.cells.forward heq))

theorem connected_map (ridges : Fin n → Fin r → Bool)
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (p : Renaming ridges compatible kind) (B : List (Fin n))
    (h : Connected ridges (family B)) :
    Connected ridges (family (B.map p.cells.forward)) := by
  intro S hsub hne hproper
  let T : Family n := fun c => S (p.cells.forward c)
  have hsubT : Included T (family B) := by
    intro c hc
    have hm := hsub (p.cells.forward c) hc
    rw [family_map] at hm
    exact hm
  have hneT : Nonempty T := by
    obtain ⟨a, ha⟩ := hne
    refine ⟨p.cells.inverse a, ?_⟩
    simpa only [T, p.cells.right_inverse] using ha
  have hproperT : ¬Same T (family B) := by
    intro heq
    apply hproper
    intro a
    have hm := family_map p.cells B (p.cells.inverse a)
    rw [p.cells.right_inverse] at hm
    have he := heq (p.cells.inverse a)
    change S (p.cells.forward (p.cells.inverse a)) = family B (p.cells.inverse a) at he
    rw [p.cells.right_inverse] at he
    exact he.trans hm.symm
  obtain ⟨q, a, b, ha, hb, hbS⟩ := h T hsubT hneT hproperT
  refine ⟨p.ridgeMap.forward q, p.cells.forward a, p.cells.forward b, ?_, ?_, hbS⟩
  · exact ⟨ha.1, (p.incidence a q).trans ha.2⟩
  · exact ⟨(family_map p.cells B b).trans hb.1, (p.incidence b q).trans hb.2⟩

structure Target (ridges : Fin n → Fin r → Bool)
    (compatible : Fin n → Fin n → Bool) (kind : Fin n → Nat)
    (quota : Nat → Nat) (B : List (Fin n)) : Prop where
  budget : ∀ k, kindCount kind B k ≤ quota k
  pairwise : ∀ a b, a ∈ B → b ∈ B → a ≠ b → compatible a b = true
  mates : HasMate ridges (family B)
  no_three : NoThree ridges (family B)
  connected : Connected ridges (family B)

theorem Target.rename {ridges : Fin n → Fin r → Bool}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat} {quota : Nat → Nat}
    {B : List (Fin n)} (h : Target ridges compatible kind quota B)
    (p : Renaming ridges compatible kind) :
    Target ridges compatible kind quota (B.map p.cells.forward) := by
  refine ⟨?_, ?_, hasMate_map _ _ _ p B h.mates,
    noThree_map _ _ _ p B h.no_three, connected_map _ _ _ p B h.connected⟩
  · intro k
    rw [kindCount_map]
    exact h.budget k
  · intro a b ha hb hne
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    rw [p.compatibility]
    exact h.pairwise x y hx hy (fun heq => hne (congrArg p.cells.forward heq))

theorem included_map (p : Bijection (Fin n)) (S B : List (Fin n))
    (h : Included (family S) (family B)) :
    Included (family (S.map p.forward)) (family (B.map p.forward)) := by
  intro c hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ((has_true _ c).mp hc)
  rw [family_map]
  exact h a ((has_true S a).mpr ha)

theorem nonempty_map (p : Bijection (Fin n)) (S : List (Fin n))
    (h : Nonempty (family S)) : Nonempty (family (S.map p.forward)) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨p.forward c, (family_map p S c).trans hc⟩

#print axioms Target.rename

end Papers.RationalityTen.GrowthRenaming
