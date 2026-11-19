module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0299Data
public import RawLeafCertificate
public import OldTerminalMatches.M005
public import OldTerminalMatches.M006

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0299
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.quota 2))
 (.branch 2
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0382))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0383))))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0384))
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0385))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0386)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0387))
 (.branch 8
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0388))))
 (.branch 10
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0389))
 (.branch 11
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0390))
 (.leaf (.matching Nonrational.OldTerminalMatches.M006.r0391))))))
cert_disposition_3
cert_dispositionTest_5 00
cert_disposition_at_8 0
cert_disposition_at_9 1 00 005 0382
cert_disposition_at_9 2 00 005 0383
cert_disposition_at_9 3 00 006 0384
cert_disposition_at_9 4 00 006 0385
cert_disposition_at_9 5 00 006 0386
cert_disposition_at_6 6 00 006 0387
cert_disposition_at_8 7
cert_disposition_at_9 8 00 006 0388
cert_disposition_at_9 9 00 006 0389
cert_disposition_at_9 10 00 006 0390
cert_disposition_at_6 11 00 006 0391
cert_disposition_interval_4 0 1
cert_disposition_interval_4 1 2
cert_disposition_interval_4 2 3
cert_disposition_interval_4 3 4
cert_disposition_interval_4 4 5
cert_disposition_interval_4 5 6
cert_disposition_interval_4 6 7
cert_disposition_interval_4 7 8
cert_disposition_interval_4 8 9
cert_disposition_interval_4 9 10
cert_disposition_interval_4 10 11
cert_disposition_interval_4 11 12
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 6 12 (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5))) (interval_append dispositionTest 6 9 12 (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)) (interval_append dispositionTest 9 10 12 disposition_interval_9 (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11))))
cert_disposition_checked_5 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0299
