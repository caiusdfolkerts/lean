module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase01GrowthCache
public import RootedSixBase01FastWords
public import SubsumedClassification
public import RootedSubsumedForest0301Leaves
public import RootedSubsumedForest0301Proof000
public import RootedSubsumedForest0301Proof001
public import RootedSubsumedForest0301Proof002
public import RootedSubsumedForest0301Proof003
public import RootedSubsumedForest0301Proof004
public import RootedSubsumedForest0301Proof005
public import RootedSubsumedForest0301Proof006
public import RootedSubsumedForest0301Proof007
public import RootedSubsumedForest0301Proof008
public import RootedSubsumedForest0301Proof009
public import RootedSubsumedForest0301Proof010
public import RootedSubsumedForest0301Proof011
public import RootedSubsumedForest0301Proof012
public import RootedSubsumedForest0301Proof013
public import RootedSubsumedForest0301Proof014
public import RootedSubsumedForest0301Proof015
public import RootedSubsumedForest0301Proof016
public import RootedSubsumedForest0301Proof017
public import RootedSubsumedForest0301Proof018
public import RootedSubsumedForest0301Proof019
public import RootedSubsumedForest0301Proof020
public import RootedSubsumedForest0301Proof021
public import RootedSubsumedForest0301Proof022
public import RootedSubsumedForest0301Proof023
public import RootedSubsumedForest0301Proof024
public import RootedSubsumedForest0301Proof025
public import RootedSubsumedForest0301Proof026
public import RootedSubsumedForest0301Proof027
public import RootedSubsumedForest0301Proof028
public import RootedSubsumedForest0301Proof029
public import RootedSubsumedForest0301Proof030
public import RootedSubsumedForest0301Proof031
public import RootedSubsumedForest0301Proof032
public import RootedSubsumedForest0301Proof033
public import RootedSubsumedForest0301Proof034
public import RootedSubsumedForest0301Proof035
public import RootedSubsumedForest0301Proof036

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 11520 23092 (interval_append nodeTest 0 5760 11520 (interval_append nodeTest 0 2560 5760 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5760 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)))) (interval_append nodeTest 5760 8320 11520 (interval_append nodeTest 5760 7040 8320 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400) (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680)) (interval_append nodeTest 8320 9600 11520 (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960) (interval_append nodeTest 9600 10240 11520 nodeInterval9600 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880))))) (interval_append nodeTest 11520 17280 23092 (interval_append nodeTest 11520 14080 17280 (interval_append nodeTest 11520 12800 14080 (interval_append nodeTest 11520 12160 12800 nodeInterval11520 nodeInterval12160) (interval_append nodeTest 12800 13440 14080 nodeInterval12800 nodeInterval13440)) (interval_append nodeTest 14080 15360 17280 (interval_append nodeTest 14080 14720 15360 nodeInterval14080 nodeInterval14720) (interval_append nodeTest 15360 16000 17280 nodeInterval15360 (interval_append nodeTest 16000 16640 17280 nodeInterval16000 nodeInterval16640)))) (interval_append nodeTest 17280 20480 23092 (interval_append nodeTest 17280 18560 20480 (interval_append nodeTest 17280 17920 18560 nodeInterval17280 nodeInterval17920) (interval_append nodeTest 18560 19200 20480 nodeInterval18560 (interval_append nodeTest 19200 19840 20480 nodeInterval19200 nodeInterval19840))) (interval_append nodeTest 20480 21760 23092 (interval_append nodeTest 20480 21120 21760 nodeInterval20480 nodeInterval21120) (interval_append nodeTest 21760 22400 23092 nodeInterval21760 (interval_append nodeTest 22400 23040 23092 nodeInterval22400 nodeInterval23040))))))
cert_root_7 23091
cert_nodes_3 48
cert_boundary_classification_5 48 01
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
