module
prelude
import GraphInputsRow24Part00166Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0282
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 34086020743424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 34086020808704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record001_result⟩)
 (.leaf ⟨(24, 34086022824192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 34086022889472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 34086222565632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record004_result⟩)
 (.leaf ⟨(24, 34086228336704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 34086228353024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 34087163662592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record007_result⟩)
 (.leaf ⟨(24, 34087163727872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 34087180177664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record009_result⟩)
 (.leaf ⟨(24, 34087180242944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 34087302074432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record011_result⟩)
 (.leaf ⟨(24, 34088253719040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 34088358645824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 34090398023936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record014_result⟩)
 (.leaf ⟨(24, 34090431054080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(24, 34094007193616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 34094023968784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record017_result⟩)
 (.leaf ⟨(24, 34095097708545), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(24, 34119375655168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 34119514067008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record020_result⟩)
 (.leaf ⟨(24, 34123666718976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 34123792123920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record022_result⟩)
 (.leaf ⟨(24, 34123809292289), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 34124794494976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record024_result⟩)
 (.leaf ⟨(24, 34124865863681), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00166.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12035 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 12035 12061 :=
  block_of_table results 12035 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0282
