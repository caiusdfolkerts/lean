module
prelude
import GraphInputsRow29Part00111Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0545
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 19330171961600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record000_result⟩)
 (.leaf ⟨(29, 19366280233216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 19366817103872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record002_result⟩)
 (.leaf ⟨(29, 19366825426944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 19426816622592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record004_result⟩)
 (.leaf ⟨(29, 19434865492224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 19435402362880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record006_result⟩)
 (.leaf ⟨(29, 19435410685952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 19435534483456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record008_result⟩)
 (.leaf ⟨(29, 19469762101248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 19469892059904), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record010_result⟩)
 (.leaf ⟨(29, 19503723380736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 19504260186112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record012_result⟩)
 (.leaf ⟨(29, 19512581685248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 19534796849152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record014_result⟩)
 (.leaf ⟨(29, 19564251381760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00111.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22128 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 22128 22144 :=
  block_of_table results 22128 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0545
