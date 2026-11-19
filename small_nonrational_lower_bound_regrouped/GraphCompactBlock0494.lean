module
prelude
import GraphInputsRow29Part00060Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0494
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 11283294326816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 11317654061057), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record001_result⟩)
 (.leaf ⟨(29, 11380325384192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 11384226054144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record003_result⟩)
 (.leaf ⟨(29, 11384618254336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 11398912442496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record005_result⟩)
 (.leaf ⟨(29, 11401129132032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(29, 11401397534720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 11448373772544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record008_result⟩)
 (.leaf ⟨(29, 11448642240512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 11448650563584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record010_result⟩)
 (.leaf ⟨(29, 11448910643200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 11449042763776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record012_result⟩)
 (.leaf ⟨(29, 11452943433728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21346 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 21346 21360 :=
  block_of_table results 21346 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0494
