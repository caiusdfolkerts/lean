module
prelude
import GraphInputsRow30Part00014Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0742
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 7533938868224), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 7534178271232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record001_result⟩)
 (.leaf ⟨(30, 7542768173056), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 7550552670464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 7551357813248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record004_result⟩)
 (.leaf ⟨(30, 7551374589952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 7560302199040), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 7560306425856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record007_result⟩)
 (.leaf ⟨(30, 7560417804544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 7560430094336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record009_result⟩)
 (.leaf ⟨(30, 7560562214912), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 7562766320384), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record011_result⟩)
 (.leaf ⟨(30, 7563047337984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(30, 7564846695168), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record013_result⟩)
 (.branch 15
 (.leaf ⟨(30, 7564855148544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record014_result⟩)
 (.leaf ⟨(30, 7565119389696), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(30, 7565127712768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 7572607205376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record017_result⟩)
 (.leaf ⟨(30, 7578002161664), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(30, 7585718616064), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record019_result⟩)
 (.branch 21
 (.leaf ⟨(30, 7593653469440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record020_result⟩)
 (.leaf ⟨(30, 7593657696256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(30, 7593665759232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record022_result⟩)
 (.leaf ⟨(30, 7593905096960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record023_result⟩))
 (.branch 25
 (.leaf ⟨(30, 7597818183936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record024_result⟩)
 (.leaf ⟨(30, 7598065715456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00014.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24004 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 24004 24030 :=
  block_of_table results 24004 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0742
