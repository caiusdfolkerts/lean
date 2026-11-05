module
prelude
import GraphInputsRow24Part00046Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0162
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 19097976897536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record000_result⟩)
 (.leaf ⟨(24, 19097985220608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 19098513702912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 19099788804352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record003_result⟩)
 (.leaf ⟨(24, 19099925151744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 19099933474816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 19100057272320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record006_result⟩)
 (.leaf ⟨(24, 19100065595392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 19100329836544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 19100525936640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record009_result⟩)
 (.leaf ⟨(24, 19145229926400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(24, 19151931326720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 19158114779136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record012_result⟩)
 (.leaf ⟨(24, 19168508264704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(24, 19168642531328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 19168650854400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record015_result⟩)
 (.leaf ⟨(24, 19169045135360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(24, 19169111195648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 19179382046976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record018_result⟩)
 (.leaf ⟨(24, 19179390435328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(24, 19179514167552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record020_result⟩)
 (.branch 22
 (.leaf ⟨(24, 19179522555904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record021_result⟩)
 (.leaf ⟨(24, 19179782570240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046.record022_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9632 + i))) 0 23 :=
  interval_of_check _ 0 23 (by decide +kernel)

public theorem complete : Block 9632 9655 :=
  block_of_table results 9632 23 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0162
