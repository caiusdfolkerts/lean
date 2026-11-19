module
prelude
public import RootedSixBase03GrowthCacheCells000
public import RootedSixBase03GrowthCacheCells001
public import RootedSixBase03GrowthCacheCells002
public import RootedSixBase03GrowthCacheCells003
public import RootedSixBase03GrowthCacheCells004
public import RootedSixBase03GrowthCacheCells005
public import RootedSixBase03GrowthCacheCells006
public import RootedSixBase03GrowthCacheCells007
public import RootedSixBase03GrowthCacheCells008
public import RootedSixBase03GrowthCacheCells009
public import RootedSixBase03GrowthCacheCells010
public import RootedSixBase03GrowthCacheCells011
public import RootedSixBase03GrowthCacheCells012
public import RootedSixBase03GrowthCacheCells013
public import RootedSixBase03GrowthCacheCells014
public import RootedSixBase03GrowthCacheCells015
public import RootedSixBase03GrowthCacheCells016
public import RootedSixBase03GrowthCacheCells017
public import RootedSixBase03GrowthCacheCells018
public import RootedSixBase03GrowthCacheCells019
public import RootedSixBase03GrowthCacheCells020
public import RootedSixBase03GrowthCacheBad000
public import RootedSixBase03GrowthCacheBad001
public import RootedSixBase03GrowthCacheBad002
public import RootedSixBase03GrowthCacheBad003
public import RootedSixBase03GrowthCacheBad004
public import RootedSixBase03GrowthCacheBad005
public import RootedSixBase03GrowthCacheBad006
public import RootedSixBase03GrowthCacheBad007
public import RootedSixBase03GrowthCacheBad008
public import RootedSixBase03GrowthCacheBad009
public import RootedSixBase03GrowthCacheBad010
public import RootedSixBase03GrowthCacheBad011
public import RootedSixBase03GrowthCacheBad012
public import RootedSixBase03GrowthCacheBad013
public import RootedSixBase03GrowthCacheBad014
public import RootedSixBase03GrowthCacheBad015
public import RootedSixBase03GrowthCacheBad016
public import RootedSixBase03GrowthCacheBad017
public import RootedSixBase03GrowthCacheBad018
public import RootedSixBase03GrowthCacheBad019
public import RootedSixBase03GrowthCacheBad020
public import RootedSixBase03GrowthCacheRidges000
public import RootedSixBase03GrowthCacheRidges001
public import RootedSixBase03GrowthCacheRidges002
public import RootedSixBase03GrowthCacheRidges003
public import RootedSixBase03GrowthCacheRidges004
public import RootedSixBase03GrowthCacheRidges005
public import RootedSixBase03GrowthCacheRidges006
public import RootedSixBase03GrowthCacheRidges007
public import RootedSixBase03GrowthCacheKinds000
public import RootedSixBase03GrowthCacheWellFormed000
public import RootedSixBase03GrowthCacheWellFormed001
public import RootedSixBase03GrowthCacheWellFormed002
public import RootedSixBase03GrowthCacheWellFormed003
public import RootedSixBase03GrowthCacheWellFormed004
public import RootedSixBase03GrowthCacheWellFormed005
public import RootedSixBase03GrowthCacheWellFormed006
public import RootedSixBase03GrowthCacheWellFormed007
public import RootedSixBase03GrowthCacheWellFormed008
public import RootedSixBase03GrowthCacheWellFormed009
public import RootedSixBase03GrowthCacheWellFormed010
public import RootedSixBase03GrowthCacheWellFormed011
public import RootedSixBase03GrowthCacheWellFormed012
public import RootedSixBase03GrowthCacheWellFormed013
public import RootedSixBase03GrowthCacheWellFormed014
public import RootedSixBase03GrowthCacheWellFormed015
public import RootedSixBase03GrowthCacheWellFormed016
public import RootedSixBase03GrowthCacheWellFormed017
public import RootedSixBase03GrowthCacheWellFormed018
public import RootedSixBase03GrowthCacheWellFormed019
public import RootedSixBase03GrowthCacheWellFormed020

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
theorem cellTest_complete : Interval cellTest 0 5238 := (interval_append cellTest 0 2560 5238 (interval_append cellTest 0 1280 2560 (interval_append cellTest 0 512 1280 (interval_append cellTest 0 256 512 cellTestInterval0 cellTestInterval256) (interval_append cellTest 512 768 1280 cellTestInterval512 (interval_append cellTest 768 1024 1280 cellTestInterval768 cellTestInterval1024))) (interval_append cellTest 1280 1792 2560 (interval_append cellTest 1280 1536 1792 cellTestInterval1280 cellTestInterval1536) (interval_append cellTest 1792 2048 2560 cellTestInterval1792 (interval_append cellTest 2048 2304 2560 cellTestInterval2048 cellTestInterval2304)))) (interval_append cellTest 2560 3840 5238 (interval_append cellTest 2560 3072 3840 (interval_append cellTest 2560 2816 3072 cellTestInterval2560 cellTestInterval2816) (interval_append cellTest 3072 3328 3840 cellTestInterval3072 (interval_append cellTest 3328 3584 3840 cellTestInterval3328 cellTestInterval3584))) (interval_append cellTest 3840 4608 5238 (interval_append cellTest 3840 4096 4608 cellTestInterval3840 (interval_append cellTest 4096 4352 4608 cellTestInterval4096 cellTestInterval4352)) (interval_append cellTest 4608 4864 5238 cellTestInterval4608 (interval_append cellTest 4864 5120 5238 cellTestInterval4864 cellTestInterval5120)))))
theorem badTest_complete : Interval badTest 0 5238 := (interval_append badTest 0 2560 5238 (interval_append badTest 0 1280 2560 (interval_append badTest 0 512 1280 (interval_append badTest 0 256 512 badTestInterval0 badTestInterval256) (interval_append badTest 512 768 1280 badTestInterval512 (interval_append badTest 768 1024 1280 badTestInterval768 badTestInterval1024))) (interval_append badTest 1280 1792 2560 (interval_append badTest 1280 1536 1792 badTestInterval1280 badTestInterval1536) (interval_append badTest 1792 2048 2560 badTestInterval1792 (interval_append badTest 2048 2304 2560 badTestInterval2048 badTestInterval2304)))) (interval_append badTest 2560 3840 5238 (interval_append badTest 2560 3072 3840 (interval_append badTest 2560 2816 3072 badTestInterval2560 badTestInterval2816) (interval_append badTest 3072 3328 3840 badTestInterval3072 (interval_append badTest 3328 3584 3840 badTestInterval3328 badTestInterval3584))) (interval_append badTest 3840 4608 5238 (interval_append badTest 3840 4096 4608 badTestInterval3840 (interval_append badTest 4096 4352 4608 badTestInterval4096 badTestInterval4352)) (interval_append badTest 4608 4864 5238 badTestInterval4608 (interval_append badTest 4864 5120 5238 badTestInterval4864 badTestInterval5120)))))
theorem ridgeTest_complete : Interval ridgeTest 0 1024 := (interval_append ridgeTest 0 512 1024 (interval_append ridgeTest 0 256 512 (interval_append ridgeTest 0 128 256 ridgeTestInterval0 ridgeTestInterval128) (interval_append ridgeTest 256 384 512 ridgeTestInterval256 ridgeTestInterval384)) (interval_append ridgeTest 512 768 1024 (interval_append ridgeTest 512 640 768 ridgeTestInterval512 ridgeTestInterval640) (interval_append ridgeTest 768 896 1024 ridgeTestInterval768 ridgeTestInterval896)))
theorem kindTest_complete : Interval kindTest 0 11 := kindTestInterval0
theorem wellFormedTest_complete : Interval wellFormedTest 0 5238 := (interval_append wellFormedTest 0 2560 5238 (interval_append wellFormedTest 0 1280 2560 (interval_append wellFormedTest 0 512 1280 (interval_append wellFormedTest 0 256 512 wellFormedTestInterval0 wellFormedTestInterval256) (interval_append wellFormedTest 512 768 1280 wellFormedTestInterval512 (interval_append wellFormedTest 768 1024 1280 wellFormedTestInterval768 wellFormedTestInterval1024))) (interval_append wellFormedTest 1280 1792 2560 (interval_append wellFormedTest 1280 1536 1792 wellFormedTestInterval1280 wellFormedTestInterval1536) (interval_append wellFormedTest 1792 2048 2560 wellFormedTestInterval1792 (interval_append wellFormedTest 2048 2304 2560 wellFormedTestInterval2048 wellFormedTestInterval2304)))) (interval_append wellFormedTest 2560 3840 5238 (interval_append wellFormedTest 2560 3072 3840 (interval_append wellFormedTest 2560 2816 3072 wellFormedTestInterval2560 wellFormedTestInterval2816) (interval_append wellFormedTest 3072 3328 3840 wellFormedTestInterval3072 (interval_append wellFormedTest 3328 3584 3840 wellFormedTestInterval3328 wellFormedTestInterval3584))) (interval_append wellFormedTest 3840 4608 5238 (interval_append wellFormedTest 3840 4096 4608 wellFormedTestInterval3840 (interval_append wellFormedTest 4096 4352 4608 wellFormedTestInterval4096 wellFormedTestInterval4352)) (interval_append wellFormedTest 4608 4864 5238 wellFormedTestInterval4608 (interval_append wellFormedTest 4864 5120 5238 wellFormedTestInterval4864 wellFormedTestInterval5120)))))

theorem cell_facts (a : Fin 5238) : (listBounds 1024 (rawCells a.val).ridgeMasks = true) ∧ ((rawCells a.val).ridgeMasks.all (fun q => (candidateMasks q).testBit a.val) = true) ∧ (decide (rawKind a.val = (rawCells a.val).kind) = true) ∧ (decide ((rawCells a.val).vertices < 1024) = true) ∧ ((List.range 10).all (fun v => decide ((vertexMasks v).testBit a.val = (rawCells a.val).vertices.testBit v)) = true) ∧ ((SignatureCompatibility.faces (rawCells a.val)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 5238) signatureIndex signatureMasks (rawCells a.val) q).testBit a.val) = true) := by
  simpa only [cellTest, Bool.and_eq_true_iff] using cellTest_complete a.val (Nat.zero_le _) a.isLt
theorem ridge_facts (q : Fin 1024) :
    candidateMasks q.val = RawNatGrowthCheck.mask (candidateRows q.val) ∧
    (candidateRows q.val).all (fun c => hasNat (rawCells c).ridgeMasks q.val) = true := by
  obtain ⟨hm, hs⟩ := Bool.and_eq_true_iff.mp (ridgeTest_complete q.val (Nat.zero_le _) q.isLt)
  exact ⟨of_decide_eq_true hm, hs⟩
theorem bad_disjoint (a : Fin 5238) : Nat.land (badMasks a.val)
    (SignatureCompatibility.cover (SignatureCompatibility.allMask 5238) vertexMasks signatureIndex signatureMasks (rawCells a.val)) = 0 := by
  have h := badTest_complete a.val (Nat.zero_le _) a.isLt
  by_cases hz : badMasks a.val = 0
  · rw [hz]; exact Nat.zero_and _
  · exact of_decide_eq_true (by simpa only [badTest, hz, ite_false] using h)
noncomputable def cache : BatchedGrowthPruning.Cache ridgeList literalCompatible kind :=
  SignatureCompatibility.ofChecks rawCells candidateMasks badMasks kindMasks candidateRows kindRows keys
    vertexMasks signatureIndex signatureMasks
    (fun c => (cell_facts c).1)
    (fun q => (ridge_facts q).1)
    (fun c => (cell_facts c).2.1)
    (fun q => (ridge_facts q).2)
    (by
      intro j hj
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp
        (kindTest_complete j (Nat.zero_le _) (List.mem_range.mp hj))).1)
    (by
      intro j hj
      exact (Bool.and_eq_true_iff.mp
        (kindTest_complete j (Nat.zero_le _) (List.mem_range.mp hj))).2)
    (fun c => of_decide_eq_true (cell_facts c).2.2.2.1)
    (by
      intro c v hv
      exact of_decide_eq_true (List.all_eq_true.mp (cell_facts c).2.2.2.2.1 v (List.mem_range.mpr hv)))
    (fun c => (cell_facts c).2.2.2.2.2) bad_disjoint
theorem raw_kind_exact (c : Fin 5238) : rawKind c.val = kind c :=
  of_decide_eq_true (cell_facts c).2.2.1
theorem facts.kindExact (c : Fin 5238) : fastKind c.val = (cells c).kind := raw_kind_exact c
theorem well_formed (c : Fin 5238) : RawFacetEmbedding.wellFormedCheck (cells c) = true :=
  wellFormedTest_complete c.val (Nat.zero_le _) c.isLt
#print axioms cache
#print axioms well_formed

end Papers.RationalityTen.RootedCaches.RootedSixBase03
