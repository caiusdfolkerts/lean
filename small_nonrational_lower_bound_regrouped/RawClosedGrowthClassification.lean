module
prelude
public import RawNatGrowthCompleteness

@[expose] public section

/-!
# Closed-leaf classification from the full raw certificate

The output retains the exact word of checked cell renamings. Geometric
applications transport the actual labeling by that word before resolving
the selected literal leaf. This theorem does not classify unchecked data.
-/

namespace Papers.RationalityTen.RawClosedGrowthClassification

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth RawNatGrowthSoundness
open RawNatGrowthCompleteness

variable {n r g k t : Nat}

theorem target_applyWord
    {ridges : Fin n → Fin r → Bool}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (budget : Nat → Nat)
    (renamings : Fin g → Renaming ridges compatible kind)
    (word : List (Fin g)) (B : List (Fin n))
    (hB : Target ridges compatible kind budget B) :
    Target ridges compatible kind budget (OrbitGrowthDAG.applyWord renamings word B) := by
  induction word generalizing B with
  | nil => exact hB
  | cons frame rest ih => exact ih _ (hB.rename (renamings frame))

variable [NeZero n] [NeZero r] [NeZero g] [NeZero k] [NeZero t]

theorem complete_of_raw_closed_checks (candidates bad rawKind : Nat → Nat)
    (maps : Nat → Nat → Nat) (rawLeaves : Nat → List Nat)
    (rawNodes : Nat → RawBatchGrowth.Node)
    {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (hcandidates : ∀ q, candidates q.val = cache.candidates q)
    (hbad : ∀ c, bad c.val = cache.incompatible c)
    (hkind : ∀ c, rawKind c.val = kind c)
    (hmaps : ∀ f c, maps f.val c.val = ((renamings f).cells.forward c).val)
    (hleaves : ∀ j : Fin k, listBounds n (rawLeaves j.val) = true)
    (hclosed : ∀ j : Fin k, WitnessGrowthDAG.closedCheck ridgeList
      (decodedLeaves (n := n) rawLeaves j) = true)
    (hnodup : ∀ j : Fin k, (decodedLeaves (n := n) rawLeaves j).Nodup)
    (hbounds : ∀ i : Fin t, nodeBounds n r g k t (rawNodes i.val) = true)
    (hchecks : ∀ i : Fin t,
      RawNatGrowthCheck.nodeCheck candidates bad cache.kinds cache.keys rawKind quota
        maps rawLeaves rawNodes i.val = true)
    (B : List (Fin n))
    (hB : Target (fun c => has (ridgeList c)) compatible kind quota B)
    (root : Fin t)
    (hroot : Included (family (decodedNodes (n := n) (r := r) (g := g)
      (k := k) rawNodes root).cells) (family B))
    (hne : Nonempty (family (decodedNodes (n := n) (r := r) (g := g)
      (k := k) rawNodes root).cells)) :
    ∃ (j : Fin k) (word : List (Fin g)),
      (decodedLeaves (n := n) rawLeaves j).Nodup ∧
      Same (family (decodedLeaves (n := n) rawLeaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  obtain ⟨j, word, hsub, hnonempty⟩ := complete_of_raw_checks candidates bad rawKind
    maps rawLeaves rawNodes cache quota renamings hcandidates hbad hkind hmaps
    hleaves hbounds hchecks B hB root hroot hne
  have transformed := target_applyWord quota renamings word B hB
  exact ⟨j, word, hnodup j, closed_leaf_eq_target ridgeList _ _ hsub hnonempty
    transformed.no_three transformed.connected (hclosed j)⟩

#print axioms complete_of_raw_closed_checks

end Papers.RationalityTen.RawClosedGrowthClassification
