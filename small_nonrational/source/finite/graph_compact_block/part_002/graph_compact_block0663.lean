module
prelude
import GraphInputsRow29Part00229Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0663
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 30865254129696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record000_result⟩)
 (.leaf ⟨(29, 30865313792256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 30865322147841), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record002_result⟩)
 (.leaf ⟨(29, 30865325301760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 30865515094272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record004_result⟩)
 (.leaf ⟨(29, 30866327867424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 30866362335233), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record006_result⟩)
 (.leaf ⟨(29, 30866588311808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(29, 30873639518208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record008_result⟩)
 (.leaf ⟨(29, 30881620697120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record009_result⟩))
 (.branch 11
 (.leaf ⟨(29, 30896119939328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record010_result⟩)
 (.leaf ⟨(29, 30896656809984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(29, 30896665133056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record012_result⟩)
 (.leaf ⟨(29, 30898281054464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record013_result⟩))
 (.branch 15
 (.leaf ⟨(29, 30898289442816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record014_result⟩)
 (.branch 16
 (.leaf ⟨(29, 30898549457152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record015_result⟩)
 (.leaf ⟨(29, 30898553683968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23229 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 23229 23246 :=
  block_of_table results 23229 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0663
