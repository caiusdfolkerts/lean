module
prelude
import GraphInputsRow31Part00091Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0879
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 17783995777024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 17784119509248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record001_result⟩)
 (.leaf ⟨(31, 17786265944320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 17818288406528), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 17921558462592), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record004_result⟩)
 (.leaf ⟨(31, 17923704897664), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(31, 17927999864896), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 18143075451008), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record007_result⟩)
 (.leaf ⟨(31, 18152188551232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(31, 18216836432128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record009_result⟩)
 (.branch 11
 (.leaf ⟨(31, 18252273090560), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record010_result⟩)
 (.leaf ⟨(31, 18252281413632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26248 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 26248 26260 :=
  block_of_table results 26248 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0879
