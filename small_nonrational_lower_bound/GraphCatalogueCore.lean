module
prelude
public import FastBatchedGrowth
public import IdentityGrowthRenaming
public import Init.Data.List.Nat.Pairwise

@[expose] public section

/-!
# Exhaustive finite graph catalogues from checked one-edge extensions

The objects are duplicate-free lists of edges.  Incidence with vertices is an
arbitrary finite Boolean relation, and the only restriction is a uniform upper
bound on vertex degrees.  A catalogue step checks every possible new edge.
Renamings carry explicit inverse maps and preserve incidence.

Induction on the number of edges proves completeness.  Canonical labeling is
used only to produce witnesses; no minimality property of a canonical label is
assumed anywhere in the proof.
-/

namespace Papers.RationalityTen.GraphCatalogueCore

open GrowthDAG SparseGrowthDAG GrowthRenaming GrowthBitsets

variable {n v g : Nat}

abbrev IncidenceRenaming (incidence : Fin n → Fin v → Bool) :=
  Renaming incidence (fun _ _ => true) (fun _ => 0)

def degree (incidence : Fin n → Fin v → Bool) (edges : List (Fin n))
    (vertex : Fin v) : Nat :=
  (edges.filter fun edge => incidence edge vertex).length

structure Valid (incidence : Fin n → Fin v → Bool) (bound : Nat)
    (edges : List (Fin n)) : Prop where
  nodup : edges.Nodup
  degree_le : ∀ vertex, degree incidence edges vertex ≤ bound

theorem Valid.perm {incidence : Fin n → Fin v → Bool} {bound : Nat}
    {S T : List (Fin n)} (h : Valid incidence bound S) (hp : S.Perm T) :
    Valid incidence bound T := by
  refine ⟨hp.nodup_iff.mp h.nodup, ?_⟩
  intro vertex
  have heq := (hp.filter (fun edge => incidence edge vertex)).length_eq
  change degree incidence S vertex = degree incidence T vertex at heq
  rw [← heq]
  exact h.degree_le vertex

theorem Valid.subset {incidence : Fin n → Fin v → Bool} {bound : Nat}
    {S T : List (Fin n)} (h : Valid incidence bound T)
    (hnd : S.Nodup) (hsub : S ⊆ T) : Valid incidence bound S := by
  refine ⟨hnd, ?_⟩
  intro vertex
  apply Nat.le_trans ?_ (h.degree_le vertex)
  exact List.Nodup.length_le_of_subset (List.Pairwise.filter _ hnd) (by
    intro edge hedge
    obtain ⟨hmem, hinc⟩ := List.mem_filter.mp hedge
    exact List.mem_filter.mpr ⟨hsub hmem, hinc⟩)

theorem Valid.rename {incidence : Fin n → Fin v → Bool} {bound : Nat}
    {S : List (Fin n)} (h : Valid incidence bound S)
    (p : IncidenceRenaming incidence) :
    Valid incidence bound (S.map p.cells.forward) := by
  refine ⟨List.pairwise_map.mpr (h.nodup.imp fun hne heq =>
    hne (p.cells.injective heq)), ?_⟩
  intro vertex
  have hinc (edge : Fin n) :
      incidence (p.cells.forward edge) vertex =
        incidence edge (p.ridgeMap.inverse vertex) := by
    simpa only [p.ridgeMap.right_inverse] using
      p.incidence edge (p.ridgeMap.inverse vertex)
  simpa only [degree, List.filter_map, Function.comp_def, hinc, List.length_map]
    using h.degree_le (p.ridgeMap.inverse vertex)

theorem Valid.word {incidence : Fin n → Fin v → Bool} {bound : Nat}
    {S : List (Fin n)} (h : Valid incidence bound S)
    (renamings : Fin g → IncidenceRenaming incidence) (word : List (Fin g)) :
    Valid incidence bound (OrbitGrowthDAG.applyWord renamings word S) := by
  induction word generalizing S with
  | nil => exact h
  | cons p rest ih => exact ih (h.rename (renamings p))

variable {incidence : Fin n → Fin v → Bool}

def imageEdge (renamings : Fin g → IncidenceRenaming incidence)
    (word : List (Fin g)) (edge : Fin n) : Fin n :=
  match word with
  | [] => edge
  | p :: rest => imageEdge renamings rest ((renamings p).cells.forward edge)

theorem applyWord_cons (renamings : Fin g → IncidenceRenaming incidence)
    (word : List (Fin g)) (edge : Fin n) (S : List (Fin n)) :
    OrbitGrowthDAG.applyWord renamings word (edge :: S) =
      imageEdge renamings word edge :: OrbitGrowthDAG.applyWord renamings word S := by
  induction word generalizing edge S with
  | nil => rfl
  | cons p rest ih =>
      simpa only [OrbitGrowthDAG.applyWord, List.map_cons, imageEdge] using
        ih ((renamings p).cells.forward edge) (S.map (renamings p).cells.forward)

theorem applyWord_append (renamings : Fin g → IncidenceRenaming incidence)
    (first second : List (Fin g)) (S : List (Fin n)) :
    OrbitGrowthDAG.applyWord renamings (first ++ second) S =
      OrbitGrowthDAG.applyWord renamings second
        (OrbitGrowthDAG.applyWord renamings first S) := by
  induction first generalizing S with
  | nil => rfl
  | cons p rest ih => exact ih (S.map (renamings p).cells.forward)

def Covers (incidence : Fin n → Fin v → Bool) (bound : Nat)
    (renamings : Fin g → IncidenceRenaming incidence)
    {count : Nat} (models : Fin count → List (Fin n)) (size : Nat) : Prop :=
  ∀ edges, Valid incidence bound edges → edges.length = size →
    ∃ model word, (models model).Perm (OrbitGrowthDAG.applyWord renamings word edges)

/-- Completeness passes from one edge count to the next once every admissible
one-edge extension of every catalogue entry has a checked image in the next
catalogue.  The extension may use any explicit incidence-preserving renaming.
-/
theorem covers_step {incidence : Fin n → Fin v → Bool} {bound : Nat}
    (renamings : Fin g → IncidenceRenaming incidence)
    {before after size : Nat}
    (models : Fin before → List (Fin n)) (next : Fin after → List (Fin n))
    (hprevious : Covers incidence bound renamings models size)
    (hextensions : ∀ i edge, edge ∉ models i → Valid incidence bound (edge :: models i) →
      ∃ j frame, (next j).Perm
        ((edge :: models i).map (renamings frame).cells.forward)) :
    Covers incidence bound renamings next (size + 1) := by
  intro edges hvalid hsize
  cases edges with
  | nil => simp only [List.length_nil] at hsize; omega
  | cons edge S =>
      have hS : Valid incidence bound S := hvalid.subset
        (List.nodup_cons.mp hvalid.nodup).2 (fun _ h => List.mem_cons_of_mem _ h)
      have hlength : S.length = size := by simp only [List.length_cons] at hsize; omega
      obtain ⟨i, word, hmodel⟩ := hprevious S hS hlength
      let renamedEdge := imageEdge renamings word edge
      have hcons : (renamedEdge :: models i).Perm
          (OrbitGrowthDAG.applyWord renamings word (edge :: S)) := by
        rw [applyWord_cons]
        exact hmodel.cons renamedEdge
      have hcurrent : Valid incidence bound (renamedEdge :: models i) :=
        (hvalid.word renamings word).perm hcons.symm
      obtain ⟨j, frame, hnext⟩ := hextensions i renamedEdge
        (List.nodup_cons.mp hcurrent.nodup).1 hcurrent
      refine ⟨j, word ++ [frame], ?_⟩
      rw [applyWord_append]
      exact hnext.trans (hcons.map (renamings frame).cells.forward)

theorem covers_zero (incidence : Fin n → Fin v → Bool) (bound : Nat)
    (renamings : Fin g → IncidenceRenaming incidence)
    {count : Nat} (models : Fin count → List (Fin n))
    (root : Fin count) (hroot : models root = []) :
    Covers incidence bound renamings models 0 := by
  intro edges _ hlength
  have hempty : edges = [] := List.length_eq_zero_iff.mp hlength
  exact ⟨root, [], by rw [hroot, hempty]; exact List.Perm.refl []⟩

theorem complete_by_steps (incidence : Fin n → Fin v → Bool) (bound : Nat)
    (renamings : Fin g → IncidenceRenaming incidence) (maxSize : Nat)
    (counts : Nat → Nat) (models : (size : Nat) → Fin (counts size) → List (Fin n))
    (root : Fin (counts 0)) (hroot : models 0 root = [])
    (hextensions : ∀ size, size < maxSize → ∀ i edge,
      edge ∉ models size i → Valid incidence bound (edge :: models size i) →
      ∃ j frame, (models (size + 1) j).Perm
        ((edge :: models size i).map (renamings frame).cells.forward)) :
    ∀ size, size ≤ maxSize → Covers incidence bound renamings (models size) size := by
  intro size
  induction size with
  | zero => intro _; exact covers_zero incidence bound renamings (models 0) root hroot
  | succ size ih =>
      intro hsize
      exact covers_step renamings (models size) (models (size+1))
        (ih (Nat.le_trans (Nat.le_succ size) hsize))
        (hextensions size (Nat.lt_of_lt_of_le (Nat.lt_succ_self size) hsize))

#print axioms complete_by_steps

end Papers.RationalityTen.GraphCatalogueCore
