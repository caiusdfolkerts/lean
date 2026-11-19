module
prelude
import GraphInputsRow24Part00076Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0192
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 24229198266368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24229326160128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record001_result⟩)
 (.leaf ⟨(24, 24229396381952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 24229802156096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record003_result⟩)
 (.leaf ⟨(24, 24230473240832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 24230875893824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record005_result⟩)
 (.leaf ⟨(24, 24233486909696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 24233491071232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 24233491136512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record008_result⟩)
 (.leaf ⟨(24, 24233493152000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 24233625337856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record010_result⟩)
 (.leaf ⟨(24, 24233889513728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 24233889579008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record012_result⟩)
 (.leaf ⟨(24, 24233895804992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(24, 24233962905664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 24234766110976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record015_result⟩)
 (.leaf ⟨(24, 24242211012864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 24262564479008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record017_result⟩)
 (.leaf ⟨(24, 24266859429920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 24267123671072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record019_result⟩)
 (.leaf ⟨(24, 24267127832608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 24276569702656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record021_result⟩)
 (.leaf ⟨(24, 24299595366401), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 24302805074176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record023_result⟩)
 (.leaf ⟨(24, 24319247810816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 24319384158208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record025_result⟩)
 (.leaf ⟨(24, 24319392481280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 24319516278784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record027_result⟩)
 (.leaf ⟨(24, 24319524601856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00076.record028_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10522 + i))) 0 29 :=
  interval_of_check _ 0 29 (by decide +kernel)

public theorem complete : Block 10522 10551 :=
  block_of_table results 10522 29 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0192
