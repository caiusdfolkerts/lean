module
prelude
import GraphInputsRow30Part00011Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0739
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 6854969426176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 6854981715968), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record001_result⟩)
 (.leaf ⟨(30, 6855179896832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(30, 6857598959616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record003_result⟩)
 (.leaf ⟨(30, 6909937647616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record004_result⟩))
 (.branch 6
 (.leaf ⟨(30, 6912018022400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record005_result⟩)
 (.leaf ⟨(30, 6977465942016), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(30, 6982278905856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record007_result⟩)
 (.leaf ⟨(30, 6982287228928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record008_result⟩))
 (.branch 10
 (.leaf ⟨(30, 6983905247232), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record009_result⟩)
 (.leaf ⟨(30, 6986166960896), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(30, 6986447978496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record011_result⟩)
 (.leaf ⟨(30, 6988528353280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record012_result⟩))
 (.branch 14
 (.leaf ⟨(30, 6999458709504), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record013_result⟩)
 (.leaf ⟨(30, 7003082653696), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23936 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 23936 23951 :=
  block_of_table results 23936 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0739
