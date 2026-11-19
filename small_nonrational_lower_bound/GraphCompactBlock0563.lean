module
prelude
import GraphInputsRow29Part00129Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0563
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 21596976726016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00129.record000_result⟩)
 (.leaf ⟨(29, 21599426216192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00129.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 21600196378624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00129.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 21603721167104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00129.record003_result⟩)
 (.leaf ⟨(29, 21659520270592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00129.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 21668110172416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00129.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 21668915315200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00129.record006_result⟩)
 (.leaf ⟨(29, 21672405123328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00129.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 21728642793472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00129.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 21878563553344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00129.record009_result⟩)
 (.leaf ⟨(29, 21921531986176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00129.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22328 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 22328 22339 :=
  block_of_table results 22328 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0563
