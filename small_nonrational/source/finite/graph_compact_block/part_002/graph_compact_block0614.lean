module
prelude
import GraphInputsRow29Part00180Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0614
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 26132057424384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 26139171098688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record001_result⟩)
 (.leaf ⟨(29, 26207890440708), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 26319559723264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 26319576694784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record004_result⟩)
 (.leaf ⟨(29, 26320113500160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 26336739592192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 26391613636672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record007_result⟩)
 (.leaf ⟨(29, 26391811817536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 26393820832000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record009_result⟩)
 (.leaf ⟨(29, 26393952952576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 26398254243904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record011_result⟩)
 (.leaf ⟨(29, 26398287274048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22827 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 22827 22840 :=
  block_of_table results 22827 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0614
