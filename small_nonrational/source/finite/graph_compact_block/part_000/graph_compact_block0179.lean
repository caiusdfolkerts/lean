module
prelude
import GraphInputsRow24Part00063Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0179
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 22929366581248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 22930901762304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record001_result⟩)
 (.leaf ⟨(24, 22931636813824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 22937679757312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 22937688080384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_result⟩)
 (.leaf ⟨(24, 22943784534272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 22948081631232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 22948354195456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record007_result⟩)
 (.leaf ⟨(24, 22948816617472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 22956132565248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 22956143034368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record010_result⟩)
 (.leaf ⟨(24, 22962582339584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(24, 22970903838720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 22980325343232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_result⟩)
 (.leaf ⟨(24, 22989099827456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(24, 22989368230144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 22989378699264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record016_result⟩)
 (.leaf ⟨(24, 22989618036992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(24, 22993782767616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 22995818004480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record019_result⟩)
 (.leaf ⟨(24, 22995859161344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(24, 23004403744768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 23006797627968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record022_result⟩)
 (.leaf ⟨(24, 23014582403328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record023_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10190 + i))) 0 24 :=
  interval_of_check _ 0 24 (by decide +kernel)

public theorem complete : Block 10190 10214 :=
  block_of_table results 10190 24 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0179
