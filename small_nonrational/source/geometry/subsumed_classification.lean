module
prelude
public import SubsumedStreaming
public import RawClosedGrowthClassification
@[expose] public section
set_option maxHeartbeats 0
namespace Papers.RationalityTen.SubsumedClassification
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth RawNatGrowthSoundness
open RawNatGrowthCompleteness RawClosedGrowthClassification
variable {n r g k t : Nat}
variable [NeZero n] [NeZero r] [NeZero g] [NeZero k] [NeZero t]
theorem complete_of_raw_checks (candidates bad rawKind : Nat → Nat)
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
    (hbounds : ∀ i : Fin t, nodeBounds n r g k t (rawNodes i.val) = true)
    (hchecks : ∀ i : Fin t,
      SubsumedRawGrowth.nodeCheck candidates bad cache.kinds cache.keys rawKind quota
        maps rawLeaves rawNodes i.val = true)
    (B : List (Fin n))
    (hB : Target (fun c => has (ridgeList c)) compatible kind quota B)
    (root : Fin t)
    (hroot : Included (family (decodedNodes (n := n) (r := r) (g := g)
      (k := k) rawNodes root).cells) (family B))
    (hne : Nonempty (family (decodedNodes (n := n) (r := r) (g := g)
      (k := k) rawNodes root).cells)) :
    ∃ j word, Included (family (decodedLeaves (n := n) (k := k) rawLeaves j))
      (family (OrbitGrowthDAG.applyWord renamings word B)) ∧
        Nonempty (family (decodedLeaves (n := n) (k := k) rawLeaves j)) := by
  apply SubsumedGrowth.complete_of_checks cache quota renamings
    (decodedLeaves rawLeaves) (decodedNodes rawNodes) ?_ B hB root hroot hne
  intro i
  apply SubsumedRawSoundness.nodeCheck_sound candidates bad rawKind maps
    rawLeaves rawNodes cache quota renamings (decodedLeaves rawLeaves)
    (decodedNodes rawNodes) hcandidates hbad hkind hmaps
  · intro j
    exact (val_decode_list (rawLeaves j.val) (hleaves j)).symm
  · intro j
    exact (erase_decode_node (rawNodes j.val) (hbounds j)).symm
  · exact hchecks i

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
      SubsumedRawGrowth.nodeCheck candidates bad cache.kinds cache.keys rawKind quota
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
end Papers.RationalityTen.SubsumedClassification
