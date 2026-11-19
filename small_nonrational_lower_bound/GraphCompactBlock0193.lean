module
prelude
import GraphInputsRow24Part00077Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0193
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 24319984943104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24333351129344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record001_result⟩)
 (.leaf ⟨(24, 24333483249920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 24333549310208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 24333753782336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record004_result⟩)
 (.leaf ⟨(24, 24336562979072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 24336569221376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 24336569286656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record007_result⟩)
 (.leaf ⟨(24, 24336972914752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 24338046652480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record009_result⟩)
 (.leaf ⟨(24, 24345152880896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 24345152946176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record011_result⟩)
 (.leaf ⟨(24, 24345154961664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 24345155026944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 24345162293312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record014_result⟩)
 (.leaf ⟨(24, 24345293373504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 24345558655040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record016_result⟩)
 (.leaf ⟨(24, 24366760919296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 24366769307648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record018_result⟩)
 (.leaf ⟨(24, 24367029321984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(24, 24367033548800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record020_result⟩)
 (.branch 22
 (.leaf ⟨(24, 24367039791104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record021_result⟩)
 (.leaf ⟨(24, 24367229583616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(24, 24375082418432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record023_result⟩)
 (.leaf ⟨(24, 24375222927360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record024_result⟩))
 (.branch 26
 (.leaf ⟨(24, 24375619289088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record025_result⟩)
 (.leaf ⟨(24, 24375627612160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00077.record026_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10551 + i))) 0 27 :=
  interval_of_check _ 0 27 (by decide +kernel)

public theorem complete : Block 10551 10578 :=
  block_of_table results 10551 27 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0193
