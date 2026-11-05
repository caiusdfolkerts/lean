module
prelude
import GraphInputsRow24Part00016Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0132
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 10228265418752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record000_result⟩)
 (.leaf ⟨(24, 10228269580288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 10231897686016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 10232426168320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record003_result⟩)
 (.leaf ⟨(24, 10232430329856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 10243039838336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 10267222114560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record006_result⟩)
 (.leaf ⟨(24, 10276275503232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 10301613441280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 10301617668096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record009_result⟩)
 (.leaf ⟨(24, 10301621829632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(24, 10301625861120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 10301757981696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record012_result⟩)
 (.leaf ⟨(24, 10301881713408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(24, 10302016077952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 10302022222848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_result⟩)
 (.leaf ⟨(24, 10331646624000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(24, 10347133042944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 10349139001344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record018_result⟩)
 (.leaf ⟨(24, 10355972522240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(24, 10370603352064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record020_result⟩)
 (.branch 22
 (.leaf ⟨(24, 10372683726848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record021_result⟩)
 (.leaf ⟨(24, 10372692049920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8630 + i))) 0 23 :=
  interval_of_check _ 0 23 (by decide +kernel)

public theorem complete : Block 8630 8653 :=
  block_of_table results 8630 23 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0132
