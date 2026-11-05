module
prelude
import GraphInputsRow29Part00135Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0569
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 23177523642624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 23203703488768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record001_result⟩)
 (.leaf ⟨(29, 23204240359424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 23212289229056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 23212826099712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record004_result⟩)
 (.leaf ⟨(29, 23212834422784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 23212958220288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 23218662473984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record007_result⟩)
 (.leaf ⟨(29, 23244925575232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 23246042841344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record009_result⟩)
 (.leaf ⟨(29, 23246051213313), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 23246051229696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record011_result⟩)
 (.leaf ⟨(29, 23246108901632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(29, 23246118330368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record013_result⟩)
 (.branch 15
 (.leaf ⟨(29, 23249329594624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record014_result⟩)
 (.leaf ⟨(29, 23279286878209), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(29, 23281006608640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 23281543479296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record017_result⟩)
 (.leaf ⟨(29, 23281551802368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(29, 23283086983424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record019_result⟩)
 (.branch 21
 (.leaf ⟨(29, 23332552507648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record020_result⟩)
 (.leaf ⟨(29, 23349732376576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(29, 23350269181952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record022_result⟩)
 (.leaf ⟨(29, 23354429931520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record023_result⟩))
 (.branch 25
 (.leaf ⟨(29, 23378178613504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record024_result⟩)
 (.leaf ⟨(29, 23383279419648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00135.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22431 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 22431 22457 :=
  block_of_table results 22431 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0569
