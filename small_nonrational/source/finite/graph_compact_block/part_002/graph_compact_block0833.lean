module
prelude
import GraphInputsRow31Part00045Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0833
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 8539607203840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record000_result⟩)
 (.leaf ⟨(31, 8539871379968), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 8539879768064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 8540144009216), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record003_result⟩)
 (.leaf ⟨(31, 8542727766016), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 8543495782400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record005_result⟩)
 (.leaf ⟨(31, 8615704396292), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 8615981219840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 8663225925632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record008_result⟩)
 (.leaf ⟨(31, 8684566478848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(31, 8727373678848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record010_result⟩)
 (.leaf ⟨(31, 8727390650368), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record011_result⟩))
 (.branch 13
 (.leaf ⟨(31, 8727927455744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record012_result⟩)
 (.branch 14
 (.leaf ⟨(31, 8736508739584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record013_result⟩)
 (.leaf ⟨(31, 8744553547776), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(31, 8744578580480), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record015_result⟩)
 (.leaf ⟨(31, 8745107062784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record016_result⟩))
 (.branch 18
 (.leaf ⟨(31, 8753680220160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record017_result⟩)
 (.branch 19
 (.leaf ⟨(31, 8849322950784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record018_result⟩)
 (.leaf ⟨(31, 8910324957184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00045.record019_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25838 + i))) 0 20 :=
  interval_of_check _ 0 20 (by decide +kernel)

public theorem complete : Block 25838 25858 :=
  block_of_table results 25838 20 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0833
