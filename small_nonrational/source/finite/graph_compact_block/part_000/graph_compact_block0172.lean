module
prelude
import GraphInputsRow24Part00056Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0172
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 20694568075264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 20694638264321), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record001_result⟩)
 (.leaf ⟨(24, 20701849323648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 20701915383936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_result⟩)
 (.leaf ⟨(24, 20710385811456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 20710435356672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record005_result⟩)
 (.leaf ⟨(24, 20711475412992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(24, 20719211986944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record007_result⟩)
 (.leaf ⟨(24, 20719216148480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record008_result⟩))
 (.branch 10
 (.leaf ⟨(24, 20727650781184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record009_result⟩)
 (.leaf ⟨(24, 20727803740160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 20748991333376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record011_result⟩)
 (.leaf ⟨(24, 20756912209920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 20757688092800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record013_result⟩)
 (.leaf ⟨(24, 20758992584704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(24, 20760032772096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 20763349369088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record016_result⟩)
 (.leaf ⟨(24, 20792228249600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(24, 20796634579200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record018_result⟩)
 (.leaf ⟨(24, 20800929268480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record019_result⟩))
 (.branch 21
 (.leaf ⟨(24, 20822087729408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record020_result⟩)
 (.leaf ⟨(24, 20822095825024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 20824291674240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_result⟩)
 (.leaf ⟨(24, 20824440504320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 20826372049024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record024_result⟩)
 (.leaf ⟨(24, 20826586939392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(24, 20830879809536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record026_result⟩)
 (.leaf ⟨(24, 20830927208704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record027_result⟩))
 (.branch 29
 (.leaf ⟨(24, 20833141523200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record028_result⟩)
 (.leaf ⟨(24, 20839250659456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record029_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9942 + i))) 0 30 :=
  interval_of_check _ 0 30 (by decide +kernel)

public theorem complete : Block 9942 9972 :=
  block_of_table results 9942 30 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0172
