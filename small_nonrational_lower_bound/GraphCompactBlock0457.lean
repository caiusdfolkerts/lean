module
prelude
import GraphInputsRow29Part00023Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0457
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 5899137745152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 5899406213120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record001_result⟩)
 (.leaf ⟨(29, 5899414536192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 5899942887936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record003_result⟩)
 (.leaf ⟨(29, 5899951276032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 6050715599104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record005_result⟩)
 (.leaf ⟨(29, 6051111960832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(29, 6051116122368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 6051116187648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record008_result⟩)
 (.leaf ⟨(29, 6051218854144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 6065781477632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record010_result⟩)
 (.leaf ⟨(29, 6066141233152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 6067324981264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record012_result⟩)
 (.leaf ⟨(29, 6086262849792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(29, 6086531252480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record014_result⟩)
 (.branch 16
 (.leaf ⟨(29, 6086531317760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record015_result⟩)
 (.leaf ⟨(29, 6086534893824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(29, 6087587823872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record017_result⟩)
 (.leaf ⟨(29, 6087587889152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record018_result⟩))
 (.branch 20
 (.leaf ⟨(29, 6099416170496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record019_result⟩)
 (.leaf ⟨(29, 6099537233936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(29, 6100610973697), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record021_result⟩)
 (.branch 23
 (.leaf ⟨(29, 6324502925568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record022_result⟩)
 (.leaf ⟨(29, 6324899287296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(29, 6339585640464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record024_result⟩)
 (.leaf ⟨(29, 6342202888192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record025_result⟩))
 (.branch 27
 (.leaf ⟨(29, 6378844323840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record026_result⟩)
 (.leaf ⟨(29, 6379100340480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00023.record027_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20850 + i))) 0 28 :=
  interval_of_check _ 0 28 (by decide +kernel)

public theorem complete : Block 20850 20878 :=
  block_of_table results 20850 28 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0457
