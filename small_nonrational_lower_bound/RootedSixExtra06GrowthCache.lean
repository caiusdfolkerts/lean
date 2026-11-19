module
prelude
public import RootedSixExtra06GrowthCacheCells000
public import RootedSixExtra06GrowthCacheCells001
public import RootedSixExtra06GrowthCacheCells002
public import RootedSixExtra06GrowthCacheCells003
public import RootedSixExtra06GrowthCacheCells004
public import RootedSixExtra06GrowthCacheCells005
public import RootedSixExtra06GrowthCacheCells006
public import RootedSixExtra06GrowthCacheCells007
public import RootedSixExtra06GrowthCacheCells008
public import RootedSixExtra06GrowthCacheBad000
public import RootedSixExtra06GrowthCacheBad001
public import RootedSixExtra06GrowthCacheBad002
public import RootedSixExtra06GrowthCacheBad003
public import RootedSixExtra06GrowthCacheBad004
public import RootedSixExtra06GrowthCacheBad005
public import RootedSixExtra06GrowthCacheBad006
public import RootedSixExtra06GrowthCacheBad007
public import RootedSixExtra06GrowthCacheBad008
public import RootedSixExtra06GrowthCacheRidges000
public import RootedSixExtra06GrowthCacheRidges001
public import RootedSixExtra06GrowthCacheRidges002
public import RootedSixExtra06GrowthCacheRidges003
public import RootedSixExtra06GrowthCacheRidges004
public import RootedSixExtra06GrowthCacheRidges005
public import RootedSixExtra06GrowthCacheRidges006
public import RootedSixExtra06GrowthCacheRidges007
public import RootedSixExtra06GrowthCacheKinds000
public import RootedSixExtra06GrowthCacheWellFormed000
public import RootedSixExtra06GrowthCacheWellFormed001
public import RootedSixExtra06GrowthCacheWellFormed002
public import RootedSixExtra06GrowthCacheWellFormed003
public import RootedSixExtra06GrowthCacheWellFormed004
public import RootedSixExtra06GrowthCacheWellFormed005
public import RootedSixExtra06GrowthCacheWellFormed006
public import RootedSixExtra06GrowthCacheWellFormed007
public import RootedSixExtra06GrowthCacheWellFormed008

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
theorem cellTest_complete : Interval cellTest 0 2300 := (interval_append cellTest 0 1024 2300 (interval_append cellTest 0 512 1024 (interval_append cellTest 0 256 512 cellTestInterval0 cellTestInterval256) (interval_append cellTest 512 768 1024 cellTestInterval512 cellTestInterval768)) (interval_append cellTest 1024 1536 2300 (interval_append cellTest 1024 1280 1536 cellTestInterval1024 cellTestInterval1280) (interval_append cellTest 1536 1792 2300 cellTestInterval1536 (interval_append cellTest 1792 2048 2300 cellTestInterval1792 cellTestInterval2048))))
theorem badTest_complete : Interval badTest 0 2300 := (interval_append badTest 0 1024 2300 (interval_append badTest 0 512 1024 (interval_append badTest 0 256 512 badTestInterval0 badTestInterval256) (interval_append badTest 512 768 1024 badTestInterval512 badTestInterval768)) (interval_append badTest 1024 1536 2300 (interval_append badTest 1024 1280 1536 badTestInterval1024 badTestInterval1280) (interval_append badTest 1536 1792 2300 badTestInterval1536 (interval_append badTest 1792 2048 2300 badTestInterval1792 badTestInterval2048))))
theorem ridgeTest_complete : Interval ridgeTest 0 1024 := (interval_append ridgeTest 0 512 1024 (interval_append ridgeTest 0 256 512 (interval_append ridgeTest 0 128 256 ridgeTestInterval0 ridgeTestInterval128) (interval_append ridgeTest 256 384 512 ridgeTestInterval256 ridgeTestInterval384)) (interval_append ridgeTest 512 768 1024 (interval_append ridgeTest 512 640 768 ridgeTestInterval512 ridgeTestInterval640) (interval_append ridgeTest 768 896 1024 ridgeTestInterval768 ridgeTestInterval896)))
theorem kindTest_complete : Interval kindTest 0 11 := kindTestInterval0
theorem wellFormedTest_complete : Interval wellFormedTest 0 2300 := (interval_append wellFormedTest 0 1024 2300 (interval_append wellFormedTest 0 512 1024 (interval_append wellFormedTest 0 256 512 wellFormedTestInterval0 wellFormedTestInterval256) (interval_append wellFormedTest 512 768 1024 wellFormedTestInterval512 wellFormedTestInterval768)) (interval_append wellFormedTest 1024 1536 2300 (interval_append wellFormedTest 1024 1280 1536 wellFormedTestInterval1024 wellFormedTestInterval1280) (interval_append wellFormedTest 1536 1792 2300 wellFormedTestInterval1536 (interval_append wellFormedTest 1792 2048 2300 wellFormedTestInterval1792 wellFormedTestInterval2048))))

theorem cell_facts (a : Fin 2300) : (listBounds 1024 (rawCells a.val).ridgeMasks = true) ∧ ((rawCells a.val).ridgeMasks.all (fun q => (candidateMasks q).testBit a.val) = true) ∧ (decide (rawKind a.val = (rawCells a.val).kind) = true) ∧ (decide ((rawCells a.val).vertices < 1024) = true) ∧ ((List.range 10).all (fun v => decide ((vertexMasks v).testBit a.val = (rawCells a.val).vertices.testBit v)) = true) ∧ ((SignatureCompatibility.faces (rawCells a.val)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask 2300) signatureIndex signatureMasks (rawCells a.val) q).testBit a.val) = true) := by
  simpa only [cellTest, Bool.and_eq_true_iff] using cellTest_complete a.val (Nat.zero_le _) a.isLt
theorem ridge_facts (q : Fin 1024) :
    candidateMasks q.val = RawNatGrowthCheck.mask (candidateRows q.val) ∧
    (candidateRows q.val).all (fun c => hasNat (rawCells c).ridgeMasks q.val) = true := by
  obtain ⟨hm, hs⟩ := Bool.and_eq_true_iff.mp (ridgeTest_complete q.val (Nat.zero_le _) q.isLt)
  exact ⟨of_decide_eq_true hm, hs⟩
theorem bad_disjoint (a : Fin 2300) : Nat.land (badMasks a.val)
    (SignatureCompatibility.cover (SignatureCompatibility.allMask 2300) vertexMasks signatureIndex signatureMasks (rawCells a.val)) = 0 := by
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
theorem raw_kind_exact (c : Fin 2300) : rawKind c.val = kind c :=
  of_decide_eq_true (cell_facts c).2.2.1
theorem facts.kindExact (c : Fin 2300) : fastKind c.val = (cells c).kind := raw_kind_exact c
theorem well_formed (c : Fin 2300) : RawFacetEmbedding.wellFormedCheck (cells c) = true :=
  wellFormedTest_complete c.val (Nat.zero_le _) c.isLt
#print axioms cache
#print axioms well_formed

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
