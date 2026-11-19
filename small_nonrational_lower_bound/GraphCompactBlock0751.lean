module
prelude
import GraphInputsRow30Part00023Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0751
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 12005238899200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record000_result⟩)
 (.leaf ⟨(30, 12008747466880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 12009131507712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record002_result⟩)
 (.leaf ⟨(30, 12013023690880), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 12017318641792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record004_result⟩)
 (.leaf ⟨(30, 12021613625344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 12021882028032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record006_result⟩)
 (.leaf ⟨(30, 12098258080000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(30, 12100338454784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record008_result⟩)
 (.leaf ⟨(30, 12133574119680), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record009_result⟩))
 (.branch 11
 (.leaf ⟨(30, 12134771654656), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record010_result⟩)
 (.leaf ⟨(30, 12135031668992), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(30, 12135040057344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record012_result⟩)
 (.leaf ⟨(30, 12139064524800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record013_result⟩))
 (.branch 15
 (.leaf ⟨(30, 12139332927488), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 12142544191744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record015_result⟩)
 (.leaf ⟨(30, 12142556221440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00023.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24255 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 24255 24272 :=
  block_of_table results 24255 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0751
