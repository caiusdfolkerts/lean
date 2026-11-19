module
prelude
import GraphInputsRow31Part00173Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0961
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 34256678092800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 34278134120448), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record001_result⟩)
 (.leaf ⟨(31, 34497177454656), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 34497195163648), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 34498320269312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record004_result⟩)
 (.leaf ⟨(31, 34500532764672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(31, 34531555934208), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 34535848804352), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record007_result⟩)
 (.leaf ⟨(31, 34634633318416), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(31, 34634633580800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record009_result⟩)
 (.leaf ⟨(31, 34634633609472), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record010_result⟩))
 (.branch 12
 (.leaf ⟨(31, 34634666872832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_result⟩)
 (.leaf ⟨(31, 34634667393024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26770 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 26770 26783 :=
  block_of_table results 26770 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0961
