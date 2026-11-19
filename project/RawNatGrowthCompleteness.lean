module
prelude
public import RawNatGrowthSoundness

@[expose] public section

/-!
# Complete exhaustive search from bounded natural-number certificates

This is the application theorem for the proof-independent raw replay.  Every
raw index is checked before decoding, every table must agree with its proved
cache or renaming, and every node is checked by the same exhaustive rule.
Leaves remain separate obligations: this theorem gives a nonempty included
leaf, and a closed-leaf check identifies it with the complete target.
-/

namespace Papers.RationalityTen.RawNatGrowthCompleteness

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth RawNatGrowthSoundness

variable {n r g k t : Nat}
variable [NeZero n] [NeZero r] [NeZero g] [NeZero k] [NeZero t]

def decodedNodes (raw : Nat → RawBatchGrowth.Node) (i : Fin t) : Node n r g k t :=
  RawBatchGrowth.decodeNode (raw i.val)

def decodedLeaves (raw : Nat → List Nat) (j : Fin k) : List (Fin n) :=
  (raw j.val).map (Fin.ofNat n)

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
      RawNatGrowthCheck.nodeCheck candidates bad cache.kinds cache.keys rawKind quota
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
  apply BatchedSearchLeaves.complete_of_checks cache quota renamings
    (decodedLeaves rawLeaves) (decodedNodes rawNodes) ?_ B hB root hroot hne
  intro i
  rw [← PrimitiveBitsetGrowth.nodeCheck_eq]
  apply RawNatGrowthSoundness.nodeCheck_sound candidates bad rawKind maps
    rawLeaves rawNodes cache quota renamings (decodedLeaves rawLeaves)
    (decodedNodes rawNodes) hcandidates hbad hkind hmaps
  · intro j
    exact (val_decode_list (rawLeaves j.val) (hleaves j)).symm
  · intro j
    exact (erase_decode_node (rawNodes j.val) (hbounds j)).symm
  · exact hchecks i

omit [NeZero n] [NeZero r] in
theorem closed_leaf_eq_target
    (ridgeList : Fin n → List (Fin r))
    (B leaf : List (Fin n))
    (hsub : Included (family leaf) (family B))
    (hne : Nonempty (family leaf))
    (hthree : NoThree (fun c => has (ridgeList c)) (family B))
    (hconnected : Connected (fun c => has (ridgeList c)) (family B))
    (hclosed : WitnessGrowthDAG.closedCheck ridgeList leaf = true) :
    Same (family leaf) (family B) :=
  closed_eq_target (fun c => has (ridgeList c)) (family B) (family leaf)
    hsub hne hthree hconnected (WitnessGrowthDAG.closedCheck_sound _ _ hclosed)

#print axioms complete_of_raw_checks
#print axioms closed_leaf_eq_target

end Papers.RationalityTen.RawNatGrowthCompleteness
