module
prelude
public import BundledChecks.RootedSixExtra02GrowthCacheBatch000
public import BundledChecks.RootedSixExtra02GrowthCacheBatch001
public import BundledChecks.RootedSixExtra02GrowthCacheBatch002
public import BundledChecks.RootedSixExtra02GrowthCacheBatch003
public import RootedSixExtra02GrowthCacheRidges000
public import RootedSixExtra02GrowthCacheRidges001
public import RootedSixExtra02GrowthCacheRidges002
public import RootedSixExtra02GrowthCacheRidges003
public import RootedSixExtra02GrowthCacheRidges004
public import RootedSixExtra02GrowthCacheRidges005
public import RootedSixExtra02GrowthCacheRidges006
public import RootedSixExtra02GrowthCacheRidges007
public import RootedSixExtra02GrowthCacheKinds000
public import BundledChecks.RootedSixExtra02GrowthCacheBatch004

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
theorem cellTest_complete : Interval cellTest 0 6620 := (interval_append cellTest 0 3328 6620 (interval_append cellTest 0 1536 3328 (interval_append cellTest 0 768 1536 (interval_append cellTest 0 256 768 cellTestInterval0 (interval_append cellTest 256 512 768 cellTestInterval256 cellTestInterval512)) (interval_append cellTest 768 1024 1536 cellTestInterval768 (interval_append cellTest 1024 1280 1536 cellTestInterval1024 cellTestInterval1280))) (interval_append cellTest 1536 2304 3328 (interval_append cellTest 1536 1792 2304 cellTestInterval1536 (interval_append cellTest 1792 2048 2304 cellTestInterval1792 cellTestInterval2048)) (interval_append cellTest 2304 2816 3328 (interval_append cellTest 2304 2560 2816 cellTestInterval2304 cellTestInterval2560) (interval_append cellTest 2816 3072 3328 cellTestInterval2816 cellTestInterval3072)))) (interval_append cellTest 3328 4864 6620 (interval_append cellTest 3328 4096 4864 (interval_append cellTest 3328 3584 4096 cellTestInterval3328 (interval_append cellTest 3584 3840 4096 cellTestInterval3584 cellTestInterval3840)) (interval_append cellTest 4096 4352 4864 cellTestInterval4096 (interval_append cellTest 4352 4608 4864 cellTestInterval4352 cellTestInterval4608))) (interval_append cellTest 4864 5632 6620 (interval_append cellTest 4864 5120 5632 cellTestInterval4864 (interval_append cellTest 5120 5376 5632 cellTestInterval5120 cellTestInterval5376)) (interval_append cellTest 5632 6144 6620 (interval_append cellTest 5632 5888 6144 cellTestInterval5632 cellTestInterval5888) (interval_append cellTest 6144 6400 6620 cellTestInterval6144 cellTestInterval6400)))))
theorem badTest_complete : Interval badTest 0 6620 := (interval_append badTest 0 3328 6620 (interval_append badTest 0 1536 3328 (interval_append badTest 0 768 1536 (interval_append badTest 0 256 768 badTestInterval0 (interval_append badTest 256 512 768 badTestInterval256 badTestInterval512)) (interval_append badTest 768 1024 1536 badTestInterval768 (interval_append badTest 1024 1280 1536 badTestInterval1024 badTestInterval1280))) (interval_append badTest 1536 2304 3328 (interval_append badTest 1536 1792 2304 badTestInterval1536 (interval_append badTest 1792 2048 2304 badTestInterval1792 badTestInterval2048)) (interval_append badTest 2304 2816 3328 (interval_append badTest 2304 2560 2816 badTestInterval2304 badTestInterval2560) (interval_append badTest 2816 3072 3328 badTestInterval2816 badTestInterval3072)))) (interval_append badTest 3328 4864 6620 (interval_append badTest 3328 4096 4864 (interval_append badTest 3328 3584 4096 badTestInterval3328 (interval_append badTest 3584 3840 4096 badTestInterval3584 badTestInterval3840)) (interval_append badTest 4096 4352 4864 badTestInterval4096 (interval_append badTest 4352 4608 4864 badTestInterval4352 badTestInterval4608))) (interval_append badTest 4864 5632 6620 (interval_append badTest 4864 5120 5632 badTestInterval4864 (interval_append badTest 5120 5376 5632 badTestInterval5120 badTestInterval5376)) (interval_append badTest 5632 6144 6620 (interval_append badTest 5632 5888 6144 badTestInterval5632 badTestInterval5888) (interval_append badTest 6144 6400 6620 badTestInterval6144 badTestInterval6400)))))
theorem ridgeTest_complete : Interval ridgeTest 0 1024 := (interval_append ridgeTest 0 512 1024 (interval_append ridgeTest 0 256 512 (interval_append ridgeTest 0 128 256 ridgeTestInterval0 ridgeTestInterval128) (interval_append ridgeTest 256 384 512 ridgeTestInterval256 ridgeTestInterval384)) (interval_append ridgeTest 512 768 1024 (interval_append ridgeTest 512 640 768 ridgeTestInterval512 ridgeTestInterval640) (interval_append ridgeTest 768 896 1024 ridgeTestInterval768 ridgeTestInterval896)))
theorem kindTest_complete : Interval kindTest 0 11 := kindTestInterval0
theorem wellFormedTest_complete : Interval wellFormedTest 0 6620 := (interval_append wellFormedTest 0 3328 6620 (interval_append wellFormedTest 0 1536 3328 (interval_append wellFormedTest 0 768 1536 (interval_append wellFormedTest 0 256 768 wellFormedTestInterval0 (interval_append wellFormedTest 256 512 768 wellFormedTestInterval256 wellFormedTestInterval512)) (interval_append wellFormedTest 768 1024 1536 wellFormedTestInterval768 (interval_append wellFormedTest 1024 1280 1536 wellFormedTestInterval1024 wellFormedTestInterval1280))) (interval_append wellFormedTest 1536 2304 3328 (interval_append wellFormedTest 1536 1792 2304 wellFormedTestInterval1536 (interval_append wellFormedTest 1792 2048 2304 wellFormedTestInterval1792 wellFormedTestInterval2048)) (interval_append wellFormedTest 2304 2816 3328 (interval_append wellFormedTest 2304 2560 2816 wellFormedTestInterval2304 wellFormedTestInterval2560) (interval_append wellFormedTest 2816 3072 3328 wellFormedTestInterval2816 wellFormedTestInterval3072)))) (interval_append wellFormedTest 3328 4864 6620 (interval_append wellFormedTest 3328 4096 4864 (interval_append wellFormedTest 3328 3584 4096 wellFormedTestInterval3328 (interval_append wellFormedTest 3584 3840 4096 wellFormedTestInterval3584 wellFormedTestInterval3840)) (interval_append wellFormedTest 4096 4352 4864 wellFormedTestInterval4096 (interval_append wellFormedTest 4352 4608 4864 wellFormedTestInterval4352 wellFormedTestInterval4608))) (interval_append wellFormedTest 4864 5632 6620 (interval_append wellFormedTest 4864 5120 5632 wellFormedTestInterval4864 (interval_append wellFormedTest 5120 5376 5632 wellFormedTestInterval5120 wellFormedTestInterval5376)) (interval_append wellFormedTest 5632 6144 6620 (interval_append wellFormedTest 5632 5888 6144 wellFormedTestInterval5632 wellFormedTestInterval5888) (interval_append wellFormedTest 6144 6400 6620 wellFormedTestInterval6144 wellFormedTestInterval6400)))))

theorem cell_facts (a : Fin 6620) : (listBounds 1024 (rawCells a.val).ridgeMasks = true) ∧ ((rawCells a.val).ridgeMasks.all (fun q => (candidateMasks q).testBit a.val) = true) ∧ (decide (rawKind a.val = (rawCells a.val).kind) = true) ∧ (decide ((rawCells a.val).vertices < 1024) = true) ∧ ((List.range 10).all (fun v => decide ((vertexMasks v).testBit a.val = (rawCells a.val).vertices.testBit v)) = true) ∧ ((SignatureCompatibility.faces (rawCells a.val)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 6620) signatureIndex signatureMasks (rawCells a.val) q).testBit a.val) = true) := by
  simpa only [cellTest, Bool.and_eq_true_iff] using cellTest_complete a.val (Nat.zero_le _) a.isLt
theorem ridge_facts (q : Fin 1024) :
    candidateMasks q.val = RawNatGrowthCheck.mask (candidateRows q.val) ∧
    (candidateRows q.val).all (fun c => hasNat (rawCells c).ridgeMasks q.val) = true := by
  obtain ⟨hm, hs⟩ := Bool.and_eq_true_iff.mp (ridgeTest_complete q.val (Nat.zero_le _) q.isLt)
  exact ⟨of_decide_eq_true hm, hs⟩
theorem bad_disjoint (a : Fin 6620) : Nat.land (badMasks a.val)
    (SignatureCompatibility.cover (SignatureCompatibility.allMask 6620) vertexMasks signatureIndex signatureMasks (rawCells a.val)) = 0 := by
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
theorem raw_kind_exact (c : Fin 6620) : rawKind c.val = kind c :=
  of_decide_eq_true (cell_facts c).2.2.1
theorem facts.kindExact (c : Fin 6620) : fastKind c.val = (cells c).kind := raw_kind_exact c
theorem well_formed (c : Fin 6620) : RawFacetEmbedding.wellFormedCheck (cells c) = true :=
  wellFormedTest_complete c.val (Nat.zero_le _) c.isLt
#print axioms cache
#print axioms well_formed

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
