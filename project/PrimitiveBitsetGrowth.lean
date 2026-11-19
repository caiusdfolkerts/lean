module
prelude
public import BatchedSearchLeaves

@[expose] public section

/-!
# Arithmetic primitives for fast kernel reduction

The slow division by a recursively computed power of two is replaced by the
kernel's shift and bit-test primitives. The identities below prove that the
resulting checker is exactly the already justified bitset checker.
-/

namespace Papers.RationalityTen.PrimitiveBitsetGrowth

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth

variable {n r g k t : Nat}

def singleton (i : Nat) : Nat := Nat.shiftLeft 1 i

theorem singleton_eq (i : Nat) : singleton i = 2^i := by
  change (1 <<< i) = 2^i
  simpa only [Nat.one_mul] using Nat.shiftLeft_eq 1 i

def mask (S : List (Fin n)) : Nat := unionValues (fun c => singleton c.val) S

theorem mask_eq (S : List (Fin n)) : mask S = ofList S := by
  have hfun : (fun c : Fin n => singleton c.val) = (fun c : Fin n => 2^c.val) :=
    funext (fun c => singleton_eq c.val)
  rw [mask,hfun]
  rfl

def closedCheck {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (selected : Nat) (w : ClosedWitness n r) : Bool :=
  ((decide (w.first ≠ w.second) && selected.testBit w.first.val) &&
      selected.testBit w.second.val) &&
    ((cache.candidates w.ridge).testBit w.first.val &&
      (cache.candidates w.ridge).testBit w.second.val)

theorem closedCheck_eq {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (selected : Nat) (w : ClosedWitness n r) :
    closedCheck cache selected w = closedWitnessCheck cache selected w := by
  simp only [closedCheck,closedWitnessCheck,bitAt_eq_testBit]

def childCheck {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (nodes : Fin t → Node n r g k t) (i : Fin t) (link : Child n g t) : Bool :=
  decide (link.node.val < i.val) &&
    decide ((nodes link.node).mask =
      mask ((link.cell :: (nodes i).cells).map (renamings link.frame).cells.forward))

theorem childCheck_eq {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (nodes : Fin t → Node n r g k t) (i : Fin t) (link : Child n g t) :
    childCheck renamings nodes i link = FastBatchedGrowth.childCheck renamings nodes i link := by
  simp only [childCheck,FastBatchedGrowth.childCheck,mask_eq]

def nodeBody {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (leaves : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t) (i : Fin t) : Bool :=
  match (nodes i).action with
  | .terminal j => decide ((nodes i).mask = mask (leaves j))
  | .split q a closed children =>
      ((decide (Nat.land (nodes i).mask (cache.candidates q) = singleton a.val) &&
        closed.all (closedCheck cache (nodes i).mask)) &&
        children.all (childCheck renamings nodes i)) &&
      decide (Nat.land (cache.candidates q)
        (Nat.lor (blockedMask cache quota (nodes i).cells (nodes i).mask closed)
          (mask (children.map Child.cell))) = cache.candidates q)

def nodeCheck {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (leaves : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t) (i : Fin t) : Bool :=
  (decide (nodes i).cells.Nodup && decide ((nodes i).mask = mask (nodes i).cells)) &&
    nodeBody cache quota renamings leaves nodes i

theorem nodeCheck_eq {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (quota : Nat → Nat)
    (renamings : Fin g → Renaming (fun c => has (ridgeList c)) compatible kind)
    (leaves : Fin k → List (Fin n)) (nodes : Fin t → Node n r g k t) (i : Fin t) :
    nodeCheck cache quota renamings leaves nodes i =
      BatchedSearchLeaves.nodeCheck cache quota renamings leaves nodes i := by
  have hc : closedCheck cache (nodes i).mask = closedWitnessCheck cache (nodes i).mask :=
    funext (closedCheck_eq cache (nodes i).mask)
  have hl : childCheck renamings nodes i = FastBatchedGrowth.childCheck renamings nodes i :=
    funext (childCheck_eq renamings nodes i)
  cases ha : (nodes i).action <;>
    simp only [nodeCheck,BatchedSearchLeaves.nodeCheck,nodeBody,
      BatchedSearchLeaves.nodeBody,ha,mask_eq,singleton_eq,hc,hl]

#print axioms nodeCheck_eq

end Papers.RationalityTen.PrimitiveBitsetGrowth
