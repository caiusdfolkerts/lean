module
prelude
public import FullSmallFacetUniverse
public import GraphProblemCertificate
public import GraphCandidateCoverage
public import FastTenGraphEdges
public import FiniteChecks

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev cellCount : Nat := 6510
noncomputable abbrev cells := FacetUniverses.FullSmall.cells
def fastEdgeMask (q : Fin 45) : Nat :=
  2 ^ (FastTenGraphEdges.first q).val + 2 ^ (FastTenGraphEdges.second q).val

def decodeSupport (code : Nat) : List (Fin cellCount) :=
  (unpackList code).1.map (Fin.ofNat cellCount)

theorem candidate_exact_of_bits
    (ridgeList : Fin cellCount → List (Fin 1024))
    (supports : Fin 1024 → List (Fin cellCount)) (rows : Fin 1024 → Nat)
    (hmasks : ∀ q, rows q = PrimitiveBitsetGrowth.mask (supports q))
    (hcoverage : ∀ c, (ridgeList c).all
      (fun q => (rows q).testBit c.val) = true)
    (hsound : ∀ q, (supports q).all (fun c => has (ridgeList c) q) = true)
    (q : Fin 1024) (c : Fin cellCount) :
    bitAt (rows q) c.val = has (ridgeList c) q := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rw [hmasks, PrimitiveBitsetGrowth.mask_eq, bitAt_ofList] at h
    exact List.all_eq_true.mp (hsound q) c h
  · intro h
    have hh := List.all_eq_true.mp (hcoverage c) q ((has_true _ _).mp h)
    simpa only [bitAt_eq_testBit] using hh
end Papers.RationalityTen.SharedSmallGraph
