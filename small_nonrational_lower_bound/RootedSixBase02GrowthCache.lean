module
prelude
public import BundledChecks.RootedSixBase02GrowthCacheBatch000
public import BundledChecks.RootedSixBase02GrowthCacheBatch001
public import BundledChecks.RootedSixBase02GrowthCacheBatch002
public import BundledChecks.RootedSixBase02GrowthCacheBatch003
public import RootedSixBase02GrowthCacheRidges000
public import RootedSixBase02GrowthCacheRidges001
public import RootedSixBase02GrowthCacheRidges002
public import RootedSixBase02GrowthCacheRidges003
public import RootedSixBase02GrowthCacheRidges004
public import RootedSixBase02GrowthCacheRidges005
public import RootedSixBase02GrowthCacheRidges006
public import RootedSixBase02GrowthCacheRidges007
public import RootedSixBase02GrowthCacheKinds000
public import BundledChecks.RootedSixBase02GrowthCacheBatch004
public import BundledChecks.RootedSixBase02GrowthCacheBatch005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
theorem cellTest_complete : Interval cellTest 0 8084 := (interval_append cellTest 0 4096 8084 (interval_append cellTest 0 2048 4096 (interval_append cellTest 0 1024 2048 (interval_append cellTest 0 512 1024 (interval_append cellTest 0 256 512 cellTestInterval0 cellTestInterval256) (interval_append cellTest 512 768 1024 cellTestInterval512 cellTestInterval768)) (interval_append cellTest 1024 1536 2048 (interval_append cellTest 1024 1280 1536 cellTestInterval1024 cellTestInterval1280) (interval_append cellTest 1536 1792 2048 cellTestInterval1536 cellTestInterval1792))) (interval_append cellTest 2048 3072 4096 (interval_append cellTest 2048 2560 3072 (interval_append cellTest 2048 2304 2560 cellTestInterval2048 cellTestInterval2304) (interval_append cellTest 2560 2816 3072 cellTestInterval2560 cellTestInterval2816)) (interval_append cellTest 3072 3584 4096 (interval_append cellTest 3072 3328 3584 cellTestInterval3072 cellTestInterval3328) (interval_append cellTest 3584 3840 4096 cellTestInterval3584 cellTestInterval3840)))) (interval_append cellTest 4096 6144 8084 (interval_append cellTest 4096 5120 6144 (interval_append cellTest 4096 4608 5120 (interval_append cellTest 4096 4352 4608 cellTestInterval4096 cellTestInterval4352) (interval_append cellTest 4608 4864 5120 cellTestInterval4608 cellTestInterval4864)) (interval_append cellTest 5120 5632 6144 (interval_append cellTest 5120 5376 5632 cellTestInterval5120 cellTestInterval5376) (interval_append cellTest 5632 5888 6144 cellTestInterval5632 cellTestInterval5888))) (interval_append cellTest 6144 7168 8084 (interval_append cellTest 6144 6656 7168 (interval_append cellTest 6144 6400 6656 cellTestInterval6144 cellTestInterval6400) (interval_append cellTest 6656 6912 7168 cellTestInterval6656 cellTestInterval6912)) (interval_append cellTest 7168 7680 8084 (interval_append cellTest 7168 7424 7680 cellTestInterval7168 cellTestInterval7424) (interval_append cellTest 7680 7936 8084 cellTestInterval7680 cellTestInterval7936)))))
theorem badTest_complete : Interval badTest 0 8084 := (interval_append badTest 0 4096 8084 (interval_append badTest 0 2048 4096 (interval_append badTest 0 1024 2048 (interval_append badTest 0 512 1024 (interval_append badTest 0 256 512 badTestInterval0 badTestInterval256) (interval_append badTest 512 768 1024 badTestInterval512 badTestInterval768)) (interval_append badTest 1024 1536 2048 (interval_append badTest 1024 1280 1536 badTestInterval1024 badTestInterval1280) (interval_append badTest 1536 1792 2048 badTestInterval1536 badTestInterval1792))) (interval_append badTest 2048 3072 4096 (interval_append badTest 2048 2560 3072 (interval_append badTest 2048 2304 2560 badTestInterval2048 badTestInterval2304) (interval_append badTest 2560 2816 3072 badTestInterval2560 badTestInterval2816)) (interval_append badTest 3072 3584 4096 (interval_append badTest 3072 3328 3584 badTestInterval3072 badTestInterval3328) (interval_append badTest 3584 3840 4096 badTestInterval3584 badTestInterval3840)))) (interval_append badTest 4096 6144 8084 (interval_append badTest 4096 5120 6144 (interval_append badTest 4096 4608 5120 (interval_append badTest 4096 4352 4608 badTestInterval4096 badTestInterval4352) (interval_append badTest 4608 4864 5120 badTestInterval4608 badTestInterval4864)) (interval_append badTest 5120 5632 6144 (interval_append badTest 5120 5376 5632 badTestInterval5120 badTestInterval5376) (interval_append badTest 5632 5888 6144 badTestInterval5632 badTestInterval5888))) (interval_append badTest 6144 7168 8084 (interval_append badTest 6144 6656 7168 (interval_append badTest 6144 6400 6656 badTestInterval6144 badTestInterval6400) (interval_append badTest 6656 6912 7168 badTestInterval6656 badTestInterval6912)) (interval_append badTest 7168 7680 8084 (interval_append badTest 7168 7424 7680 badTestInterval7168 badTestInterval7424) (interval_append badTest 7680 7936 8084 badTestInterval7680 badTestInterval7936)))))
theorem ridgeTest_complete : Interval ridgeTest 0 1024 := (interval_append ridgeTest 0 512 1024 (interval_append ridgeTest 0 256 512 (interval_append ridgeTest 0 128 256 ridgeTestInterval0 ridgeTestInterval128) (interval_append ridgeTest 256 384 512 ridgeTestInterval256 ridgeTestInterval384)) (interval_append ridgeTest 512 768 1024 (interval_append ridgeTest 512 640 768 ridgeTestInterval512 ridgeTestInterval640) (interval_append ridgeTest 768 896 1024 ridgeTestInterval768 ridgeTestInterval896)))
theorem kindTest_complete : Interval kindTest 0 11 := kindTestInterval0
theorem wellFormedTest_complete : Interval wellFormedTest 0 8084 := (interval_append wellFormedTest 0 4096 8084 (interval_append wellFormedTest 0 2048 4096 (interval_append wellFormedTest 0 1024 2048 (interval_append wellFormedTest 0 512 1024 (interval_append wellFormedTest 0 256 512 wellFormedTestInterval0 wellFormedTestInterval256) (interval_append wellFormedTest 512 768 1024 wellFormedTestInterval512 wellFormedTestInterval768)) (interval_append wellFormedTest 1024 1536 2048 (interval_append wellFormedTest 1024 1280 1536 wellFormedTestInterval1024 wellFormedTestInterval1280) (interval_append wellFormedTest 1536 1792 2048 wellFormedTestInterval1536 wellFormedTestInterval1792))) (interval_append wellFormedTest 2048 3072 4096 (interval_append wellFormedTest 2048 2560 3072 (interval_append wellFormedTest 2048 2304 2560 wellFormedTestInterval2048 wellFormedTestInterval2304) (interval_append wellFormedTest 2560 2816 3072 wellFormedTestInterval2560 wellFormedTestInterval2816)) (interval_append wellFormedTest 3072 3584 4096 (interval_append wellFormedTest 3072 3328 3584 wellFormedTestInterval3072 wellFormedTestInterval3328) (interval_append wellFormedTest 3584 3840 4096 wellFormedTestInterval3584 wellFormedTestInterval3840)))) (interval_append wellFormedTest 4096 6144 8084 (interval_append wellFormedTest 4096 5120 6144 (interval_append wellFormedTest 4096 4608 5120 (interval_append wellFormedTest 4096 4352 4608 wellFormedTestInterval4096 wellFormedTestInterval4352) (interval_append wellFormedTest 4608 4864 5120 wellFormedTestInterval4608 wellFormedTestInterval4864)) (interval_append wellFormedTest 5120 5632 6144 (interval_append wellFormedTest 5120 5376 5632 wellFormedTestInterval5120 wellFormedTestInterval5376) (interval_append wellFormedTest 5632 5888 6144 wellFormedTestInterval5632 wellFormedTestInterval5888))) (interval_append wellFormedTest 6144 7168 8084 (interval_append wellFormedTest 6144 6656 7168 (interval_append wellFormedTest 6144 6400 6656 wellFormedTestInterval6144 wellFormedTestInterval6400) (interval_append wellFormedTest 6656 6912 7168 wellFormedTestInterval6656 wellFormedTestInterval6912)) (interval_append wellFormedTest 7168 7680 8084 (interval_append wellFormedTest 7168 7424 7680 wellFormedTestInterval7168 wellFormedTestInterval7424) (interval_append wellFormedTest 7680 7936 8084 wellFormedTestInterval7680 wellFormedTestInterval7936)))))

theorem cell_facts (a : Fin 8084) : (listBounds 1024 (rawCells a.val).ridgeMasks = true) ∧ ((rawCells a.val).ridgeMasks.all (fun q => (candidateMasks q).testBit a.val) = true) ∧ (decide (rawKind a.val = (rawCells a.val).kind) = true) ∧ (decide ((rawCells a.val).vertices < 1024) = true) ∧ ((List.range 10).all (fun v => decide ((vertexMasks v).testBit a.val = (rawCells a.val).vertices.testBit v)) = true) ∧ ((SignatureCompatibility.faces (rawCells a.val)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 8084) signatureIndex signatureMasks (rawCells a.val) q).testBit a.val) = true) := by
  simpa only [cellTest, Bool.and_eq_true_iff] using cellTest_complete a.val (Nat.zero_le _) a.isLt
theorem ridge_facts (q : Fin 1024) :
    candidateMasks q.val = RawNatGrowthCheck.mask (candidateRows q.val) ∧
    (candidateRows q.val).all (fun c => hasNat (rawCells c).ridgeMasks q.val) = true := by
  obtain ⟨hm, hs⟩ := Bool.and_eq_true_iff.mp (ridgeTest_complete q.val (Nat.zero_le _) q.isLt)
  exact ⟨of_decide_eq_true hm, hs⟩
theorem bad_disjoint (a : Fin 8084) : Nat.land (badMasks a.val)
    (SignatureCompatibility.cover (SignatureCompatibility.allMask 8084) vertexMasks signatureIndex signatureMasks (rawCells a.val)) = 0 := by
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
theorem raw_kind_exact (c : Fin 8084) : rawKind c.val = kind c :=
  of_decide_eq_true (cell_facts c).2.2.1
theorem facts.kindExact (c : Fin 8084) : fastKind c.val = (cells c).kind := raw_kind_exact c
theorem well_formed (c : Fin 8084) : RawFacetEmbedding.wellFormedCheck (cells c) = true :=
  wellFormedTest_complete c.val (Nat.zero_le _) c.isLt
#print axioms cache
#print axioms well_formed

end Papers.RationalityTen.RootedCaches.RootedSixBase02
