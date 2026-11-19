module
prelude
import GraphInputsRow29Part00068Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0502
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 12147646038272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 12147650265088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record001_result⟩)
 (.leaf ⟨(29, 12147654426624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 12147914473600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record003_result⟩)
 (.leaf ⟨(29, 12151134126208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 12151268327552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record005_result⟩)
 (.leaf ⟨(29, 12165786374400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 12167932809472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record007_result⟩)
 (.leaf ⟨(29, 12170607726592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 12173357154304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record009_result⟩)
 (.leaf ⟨(29, 12173423214592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 12173617168640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record011_result⟩)
 (.leaf ⟨(29, 12173625556992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 12174756446464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record013_result⟩)
 (.leaf ⟨(29, 12174768476160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00068.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21441 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 21441 21456 :=
  block_of_table results 21441 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0502
