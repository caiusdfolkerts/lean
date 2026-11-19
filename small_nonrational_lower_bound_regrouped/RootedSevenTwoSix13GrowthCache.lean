module
prelude
public import BundledChecks.RootedSevenTwoSix13GrowthCacheBatch000
public import RootedSevenTwoSix13GrowthCacheRidges000
public import BundledChecks.RootedSevenTwoSix13GrowthCacheBatch001
public import RootedSevenTwoSix13GrowthCacheRidges003
public import RootedSevenTwoSix13GrowthCacheRidges005
public import RootedSevenTwoSix13GrowthCacheRidges006
public import RootedSevenTwoSix13GrowthCacheRidges007
public import RootedSevenTwoSix13GrowthCacheKinds000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
theorem cellTest_complete : Interval cellTest 0 2038 := (interval_append cellTest 0 1024 2038 (interval_append cellTest 0 512 1024 (interval_append cellTest 0 256 512 cellTestInterval0 cellTestInterval256) (interval_append cellTest 512 768 1024 cellTestInterval512 cellTestInterval768)) (interval_append cellTest 1024 1536 2038 (interval_append cellTest 1024 1280 1536 cellTestInterval1024 cellTestInterval1280) (interval_append cellTest 1536 1792 2038 cellTestInterval1536 cellTestInterval1792)))
theorem badTest_complete : Interval badTest 0 2038 := (interval_append badTest 0 1024 2038 (interval_append badTest 0 512 1024 (interval_append badTest 0 256 512 badTestInterval0 badTestInterval256) (interval_append badTest 512 768 1024 badTestInterval512 badTestInterval768)) (interval_append badTest 1024 1536 2038 (interval_append badTest 1024 1280 1536 badTestInterval1024 badTestInterval1280) (interval_append badTest 1536 1792 2038 badTestInterval1536 badTestInterval1792)))
theorem ridgeTest_complete : Interval ridgeTest 0 1024 := (interval_append ridgeTest 0 512 1024 (interval_append ridgeTest 0 256 512 (interval_append ridgeTest 0 128 256 ridgeTestInterval0 ridgeTestInterval128) (interval_append ridgeTest 256 384 512 ridgeTestInterval256 ridgeTestInterval384)) (interval_append ridgeTest 512 768 1024 (interval_append ridgeTest 512 640 768 ridgeTestInterval512 ridgeTestInterval640) (interval_append ridgeTest 768 896 1024 ridgeTestInterval768 ridgeTestInterval896)))
theorem kindTest_complete : Interval kindTest 0 5 := kindTestInterval0
theorem wellFormedTest_complete : Interval wellFormedTest 0 2038 := (interval_append wellFormedTest 0 1024 2038 (interval_append wellFormedTest 0 512 1024 (interval_append wellFormedTest 0 256 512 wellFormedTestInterval0 wellFormedTestInterval256) (interval_append wellFormedTest 512 768 1024 wellFormedTestInterval512 wellFormedTestInterval768)) (interval_append wellFormedTest 1024 1536 2038 (interval_append wellFormedTest 1024 1280 1536 wellFormedTestInterval1024 wellFormedTestInterval1280) (interval_append wellFormedTest 1536 1792 2038 wellFormedTestInterval1536 wellFormedTestInterval1792)))

theorem cell_facts (a : Fin 2038) : (listBounds 1024 (rawCells a.val).ridgeMasks = true) ∧ ((rawCells a.val).ridgeMasks.all (fun q => (candidateMasks q).testBit a.val) = true) ∧ (decide (rawKind a.val = (rawCells a.val).kind) = true) ∧ (decide ((rawCells a.val).vertices < 1024) = true) ∧ ((List.range 10).all (fun v => decide ((vertexMasks v).testBit a.val = (rawCells a.val).vertices.testBit v)) = true) ∧ ((SignatureCompatibility.faces (rawCells a.val)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 2038) signatureIndex signatureMasks (rawCells a.val) q).testBit a.val) = true) := by
  simpa only [cellTest, Bool.and_eq_true_iff] using cellTest_complete a.val (Nat.zero_le _) a.isLt
theorem ridge_facts (q : Fin 1024) :
    candidateMasks q.val = RawNatGrowthCheck.mask (candidateRows q.val) ∧
    (candidateRows q.val).all (fun c => hasNat (rawCells c).ridgeMasks q.val) = true := by
  obtain ⟨hm, hs⟩ := Bool.and_eq_true_iff.mp (ridgeTest_complete q.val (Nat.zero_le _) q.isLt)
  exact ⟨of_decide_eq_true hm, hs⟩
theorem bad_disjoint (a : Fin 2038) : Nat.land (badMasks a.val)
    (SignatureCompatibility.cover (SignatureCompatibility.allMask 2038) vertexMasks signatureIndex signatureMasks (rawCells a.val)) = 0 := by
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
theorem raw_kind_exact (c : Fin 2038) : rawKind c.val = kind c :=
  of_decide_eq_true (cell_facts c).2.2.1
theorem facts.kindExact (c : Fin 2038) : fastKind c.val = (cells c).kind := raw_kind_exact c
theorem well_formed (c : Fin 2038) : RawFacetEmbedding.wellFormedCheck (cells c) = true :=
  wellFormedTest_complete c.val (Nat.zero_le _) c.isLt
#print axioms cache
#print axioms well_formed

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
