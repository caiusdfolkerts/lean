module
prelude
import GraphInputsRow24Part00036Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0152
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 17082968244224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record000_result⟩)
 (.leaf ⟨(24, 17082976567296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 17086592123136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record002_result⟩)
 (.leaf ⟨(24, 17086864752640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 17087128993792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record004_result⟩)
 (.leaf ⟨(24, 17087137316864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 17089712685312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record006_result⟩)
 (.leaf ⟨(24, 17090480766976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 17102595457280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record008_result⟩)
 (.leaf ⟨(24, 17120033832960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 17120050348032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record010_result⟩)
 (.leaf ⟨(24, 17120293847296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 17120305876992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record012_result⟩)
 (.leaf ⟨(24, 17120545214720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 17121618690816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 17137724817936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record015_result⟩)
 (.leaf ⟨(24, 17146855883008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 17155450011648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record017_result⟩)
 (.leaf ⟨(24, 17155986817024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 17171317063680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record019_result⟩)
 (.leaf ⟨(24, 17172085080064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 17172629815296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record021_result⟩)
 (.leaf ⟨(24, 17184449954048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 17184730386432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record023_result⟩)
 (.leaf ⟨(24, 17186349449472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 17187117531136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record025_result⟩)
 (.leaf ⟨(24, 17189021679617), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 17189023256576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record027_result⟩)
 (.leaf ⟨(24, 17189130473728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(24, 17189742641152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record029_result⟩)
 (.leaf ⟨(24, 17190147325952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record030_result⟩))
 (.branch 32
 (.leaf ⟨(24, 17191278280704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record031_result⟩)
 (.branch 33
 (.leaf ⟨(24, 17197326010384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record032_result⟩)
 (.leaf ⟨(24, 17198192034048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00036.record033_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9363 + i))) 0 34 :=
  interval_of_check _ 0 34 (by decide +kernel)

public theorem complete : Block 9363 9397 :=
  block_of_table results 9363 34 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0152
