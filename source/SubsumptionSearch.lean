module
prelude
public import UnsupportedRidgePruning

@[expose] public section

/-!
# Complete search with reuse of earlier subfamilies

A leaf records a selected partial family. Exhaustiveness proves that some leaf
is contained in every target, after an explicit word of checked renamings.
The application must then justify every leaf: a closed leaf equals its connected
target, while a capacity leaf rules out every target extension. This separation
does not assert realizability or rationality of an unchecked leaf.
-/

namespace Papers.RationalityTen.SubsumptionSearch

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth

variable {n r g k t : Nat}

/-- A smaller completed subfamily can replace a larger current family.  Its
strictly smaller proof index prevents circular reuse. -/
def childCheck {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (nodes : Fin t → Node n r g k t) (i : Fin t) (link : Child n g t) : Bool :=
  (decide (link.node.val < i.val) && decide ((nodes link.node).mask ≠ 0)) &&
    decide (Nat.land (nodes link.node).mask
      (ofList ((link.cell :: (nodes i).cells).map (renamings link.frame).cells.forward)) =
        (nodes link.node).mask)

theorem included_of_masks (S T : List (Fin n))
    (h : Nat.land (ofList S) (ofList T) = ofList S) :
    Included (family S) (family T) := by
  intro c hc
  change has S c = true at hc
  have hh := congrArg (fun bits => bitAt bits c.val) h
  rw [bitAt_and, bitAt_ofList_eq_has, bitAt_ofList_eq_has, hc,
    Bool.true_and] at hh
  exact hh

theorem nonempty_of_mask_ne_zero (S : List (Fin n)) (h : ofList S ≠ 0) :
    Nonempty (family S) := by
  cases S with
  | nil => exact False.elim (h rfl)
  | cons c rest => exact ⟨c, (has_true _ _).mpr (List.mem_cons_self)⟩

def nodeBody {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (leaves : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t)
    (exclusions : Fin t → Nat) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal j => decide ((nodes i).mask = ofList (leaves j))
  | .split q a closed children =>
      (decide (Nat.land (nodes i).mask (cache.candidates q) = 2^a.val) &&
        children.all (childCheck renamings nodes i)) &&
      decide (Nat.land (cache.candidates q)
        (Nat.lor (exclusions i) (ofList (children.map Child.cell))) = cache.candidates q)

def nodeCheck {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (leaves : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t)
    (exclusions : Fin t → Nat) (exclusionCheck : Fin t → Bool) (i : Fin t) : Bool :=
  (decide (nodes i).cells.Nodup && decide ((nodes i).mask = ofList (nodes i).cells)) &&
    (exclusionCheck i && nodeBody cache quota renamings leaves nodes exclusions i)

theorem complete_of_checks {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (leaves : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t)
    (exclusions : Fin t → Nat) (exclusionCheck : Fin t → Bool)
    (exclusions_sound : ∀ i B,
      Target (fun c => has (ridgeList c)) compatible kind quota B →
      Included (family (nodes i).cells) (family B) →
      (nodes i).cells.Nodup → exclusionCheck i = true →
      ∀ c, family B c = true → family (nodes i).cells c = false →
        bitAt (exclusions i) c.val = false)
    (hnodes : ∀ i, nodeCheck cache quota renamings leaves nodes exclusions exclusionCheck i = true)
    (B : List (Fin n))
    (hB : Target (fun c => has (ridgeList c)) compatible kind quota B)
    (root : Fin t) (hroot : Included (family (nodes root).cells) (family B))
    (hne : Nonempty (family (nodes root).cells)) :
    ∃ j word, Included (family (leaves j))
      (family (OrbitGrowthDAG.applyWord renamings word B)) ∧ Nonempty (family (leaves j)) := by
  have hmasks : ∀ i, (nodes i).mask = ofList (nodes i).cells := by
    intro i
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (hnodes i)).1).2
  have main : ∀ height : Nat, ∀ i : Fin t, i.val = height →
      ∀ B : List (Fin n), Target (fun c => has (ridgeList c)) compatible kind quota B →
      Included (family (nodes i).cells) (family B) → Nonempty (family (nodes i).cells) →
      ∃ j word, Included (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) ∧ Nonempty (family (leaves j)) := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
      intro i hi B hB hsub hnonempty
      obtain ⟨hstate,hrest⟩ := Bool.and_eq_true_iff.mp (hnodes i)
      obtain ⟨hexclusions,hbody⟩ := Bool.and_eq_true_iff.mp hrest
      have hnd : (nodes i).cells.Nodup :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hstate).1
      cases ha : (nodes i).action with
      | terminal j =>
        have hmask : (nodes i).mask = ofList (leaves j) :=
          of_decide_eq_true (by simpa only [nodeBody,ha] using hbody)
        have hs := sameCheck_sound _ _
          (FastBatchedGrowth.sameCheck_of_masks _ _ ((hmasks i).symm.trans hmask))
        exact ⟨j,[],same_included (fun c => (hs c).symm) hsub,
          same_nonempty (fun c => (hs c).symm) hnonempty⟩
      | split q a closed children =>
        have hh :
            (decide (Nat.land (nodes i).mask (cache.candidates q) = 2^a.val) &&
              children.all (childCheck renamings nodes i)) = true ∧
            decide (Nat.land (cache.candidates q)
              (Nat.lor (exclusions i) (ofList (children.map Child.cell))) =
                cache.candidates q) = true :=
          Bool.and_eq_true_iff.mp (by simpa only [nodeBody,ha] using hbody)
        obtain ⟨hopen,hchildren⟩ := Bool.and_eq_true_iff.mp hh.1
        obtain ⟨c,hcB,hcS,hcr⟩ := missing_cell (fun c => has (ridgeList c))
          (family B) (family (nodes i).cells) q a hsub hB.mates
          (openCheck_sound _ _ _ _
            (FastBatchedGrowth.openCheck_of_mask cache (nodes i).cells (nodes i).mask
              (hmasks i) q a (of_decide_eq_true hopen)))
        change has (nodes i).cells c = false at hcS
        have hcand : bitAt (cache.candidates q) c.val = true :=
          (cache.candidates_exact q c).trans hcr
        have hblocked := exclusions_sound i B hB hsub hnd hexclusions c hcB hcS
        have hcChild := bitAt_cover _ _ _ c.val (of_decide_eq_true hh.2) hcand hblocked
        have hmem : c ∈ children.map Child.cell := (bitAt_ofList _ c).mp hcChild
        obtain ⟨link,hlinkMem,hcell⟩ := List.mem_map.mp hmem
        obtain ⟨hindexNonempty,hmask⟩ := Bool.and_eq_true_iff.mp
          (List.all_eq_true.mp hchildren link hlinkMem)
        obtain ⟨hindex,hchildNonempty⟩ := Bool.and_eq_true_iff.mp hindexNonempty
        have hinc : Included (family (nodes link.node).cells)
            (family ((c :: (nodes i).cells).map (renamings link.frame).cells.forward)) := by
          apply included_of_masks
          rw [← hmasks link.node]
          simpa only [hcell] using of_decide_eq_true hmask
        have hsubCons : Included (family (c :: (nodes i).cells)) (family B) :=
          same_included (family_cons (nodes i).cells c) (add_included hsub hcB)
        have hsubMap := included_map (renamings link.frame).cells _ B hsubCons
        have hsubChild : Included (family (nodes link.node).cells)
            (family (B.map (renamings link.frame).cells.forward)) :=
          fun d hd => hsubMap d (hinc d hd)
        have hneChild : Nonempty (family (nodes link.node).cells) := by
          apply nonempty_of_mask_ne_zero
          rw [← hmasks link.node]
          exact of_decide_eq_true hchildNonempty
        obtain ⟨leaf,word,hresult⟩ := ih link.node.val
          (hi ▸ of_decide_eq_true hindex) link.node rfl
          (B.map (renamings link.frame).cells.forward) (hB.rename (renamings link.frame))
          hsubChild hneChild
        exact ⟨leaf,link.frame :: word,hresult⟩
  exact main root.val root rfl B hB hroot hne

#print axioms complete_of_checks

end Papers.RationalityTen.SubsumptionSearch
