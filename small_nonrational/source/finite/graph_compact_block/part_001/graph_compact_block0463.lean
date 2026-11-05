module
prelude
import GraphInputsRow29Part00029Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0463
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 6844835693312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 6851076817664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record001_result⟩)
 (.leaf ⟨(29, 6854969426176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 6854981715968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 6855179896832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record004_result⟩)
 (.leaf ⟨(29, 6857598959616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 6878731964672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 6909937647616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record007_result⟩)
 (.leaf ⟨(29, 6912018022400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 6977465942016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record009_result⟩)
 (.leaf ⟨(29, 6982278905856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 6982287228928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record011_result⟩)
 (.leaf ⟨(29, 6983905247232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20931 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 20931 20944 :=
  block_of_table results 20931 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0463
