module
prelude
import GraphInputsRow31Part00095Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0883
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 19328632160256), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 19366007701760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record001_result⟩)
 (.leaf ⟨(31, 19469900447744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 19535390310976), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record003_result⟩)
 (.leaf ⟨(31, 19572841250816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 19611625980416), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record005_result⟩)
 (.leaf ⟨(31, 19611628077056), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(31, 19623726612480), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 19624511143936), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record008_result⟩)
 (.leaf ⟨(31, 19641162268672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(31, 19679540297984), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record010_result⟩)
 (.leaf ⟨(31, 19878988759168), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record011_result⟩))
 (.branch 13
 (.leaf ⟨(31, 19947708235840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record012_result⟩)
 (.leaf ⟨(31, 20019514736640), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26294 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 26294 26308 :=
  block_of_table results 26294 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0883
