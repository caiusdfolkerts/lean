module
prelude
public import RawGrowthCacheCertificate
@[expose] public section
namespace Papers.RationalityTen.FastRawCacheCertificate
open GrowthDAG SparseGrowthDAG GrowthBitsets ConcreteGrowth BatchedGrowthPruning
open RawNatGrowthSoundness RawGrowthCacheCertificate
variable {n : Nat}

/-- The forward incidence check uses a bit lookup. The exact mask certificate
converts it to the original sparse-row membership premise. -/
noncomputable def ofChecks
    (cells : Nat → Cell)
    (candidates bad kinds : Nat → Nat)
    (candidateRows badRows kindRows : Nat → List Nat)
    (keys : List Nat)
    (hridgeBounds : ∀ c : Fin n, listBounds 1024 (cells c.val).ridgeMasks = true)
    (hcandidateMasks : ∀ q : Fin 1024,
      candidates q.val = RawNatGrowthCheck.mask (candidateRows q.val))
    (hcandidateCoverage : ∀ c : Fin n,
      (cells c.val).ridgeMasks.all (fun q => (candidates q).testBit c.val) = true)
    (hcandidateSound : ∀ q : Fin 1024,
      (candidateRows q.val).all (fun c => hasNat (cells c).ridgeMasks q.val) = true)
    (hbadMasks : ∀ c : Fin n, bad c.val = RawNatGrowthCheck.mask (badRows c.val))
    (hbadSound : ∀ a : Fin n,
      (badRows a.val).all (fun c => !(compatible (cells a.val) (cells c))) = true)
    (hkindMasks : ∀ j, j ∈ keys → kinds j = RawNatGrowthCheck.mask (kindRows j))
    (hkindSound : ∀ j, j ∈ keys →
      (kindRows j).all (fun c => decide ((cells c).kind = j)) = true) :
    Cache (ConcreteGrowth.ridgeList (fun c : Fin n => cells c.val))
      (fun a b : Fin n => compatible (cells a.val) (cells b.val))
      (fun c : Fin n => (cells c.val).kind) := by
  apply RawGrowthCacheCertificate.ofChecks cells candidates bad kinds candidateRows badRows
    kindRows keys hridgeBounds hcandidateMasks ?_ hcandidateSound hbadMasks hbadSound
    hkindMasks hkindSound
  intro c
  apply List.all_eq_true.mpr
  intro q hq
  have bound : q < 1024 := of_decide_eq_true (List.all_eq_true.mp (hridgeBounds c) q hq)
  have h := List.all_eq_true.mp (hcandidateCoverage c) q hq
  have hm := hcandidateMasks ⟨q, bound⟩
  change candidates q = RawNatGrowthCheck.mask (candidateRows q) at hm
  rw [hm, RawGrowthCacheCertificate.mask_bit] at h
  exact h

#print axioms ofChecks
end Papers.RationalityTen.FastRawCacheCertificate
