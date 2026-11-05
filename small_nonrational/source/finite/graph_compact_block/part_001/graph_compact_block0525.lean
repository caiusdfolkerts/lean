module
prelude
import GraphInputsRow29Part00091Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0525
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 16128415891456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 16493834699008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record001_result⟩)
 (.leaf ⟨(29, 16493834764288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 16493838340352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 16494977618176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_result⟩)
 (.leaf ⟨(29, 16494977683456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 16494985482256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 16495002257424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record007_result⟩)
 (.leaf ⟨(29, 16495109738752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 16496075997185), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 16496208183296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record010_result⟩)
 (.leaf ⟨(29, 16496468197632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21781 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 21781 21793 :=
  block_of_table results 21781 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0525
