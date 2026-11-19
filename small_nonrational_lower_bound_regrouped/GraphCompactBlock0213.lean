module
prelude
import GraphInputsRow24Part00097Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0213
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 25261655457792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record000_result⟩)
 (.leaf ⟨(24, 25292162793728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 25292166955264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 25292167020544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record003_result⟩)
 (.leaf ⟨(24, 25292169036032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 25292301156608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record005_result⟩)
 (.leaf ⟨(24, 25292301221888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 25292401807616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 25292565397760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record008_result⟩)
 (.leaf ⟨(24, 25292565463040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 25292571689024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record010_result⟩)
 (.leaf ⟨(24, 25292672340032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 25294309228800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 25294313390336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record013_result⟩)
 (.leaf ⟨(24, 25294313455616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(24, 25294350061824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 25294441349376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record016_result⟩)
 (.leaf ⟨(24, 25294447591680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(24, 25294447656960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 25294709752064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record019_result⟩)
 (.leaf ⟨(24, 25294709817344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record020_result⟩))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 25294711898112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record021_result⟩)
 (.leaf ⟨(24, 25294716059648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 25294719164480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record023_result⟩)
 (.branch 25
 (.leaf ⟨(24, 25295893565456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record024_result⟩)
 (.leaf ⟨(24, 25298642931968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record025_result⟩))))
 (.branch 28
 (.branch 27
 (.leaf ⟨(24, 25299004702976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_result⟩)
 (.leaf ⟨(24, 25299004768256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_result⟩))
 (.branch 29
 (.leaf ⟨(24, 25299010994240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record028_result⟩)
 (.branch 30
 (.leaf ⟨(24, 25299012034624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_result⟩)
 (.leaf ⟨(24, 25299045584960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record030_result⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨(24, 25300186435600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record031_result⟩)
 (.leaf ⟨(24, 25307228672256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record032_result⟩))
 (.branch 34
 (.leaf ⟨(24, 25307234963520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record033_result⟩)
 (.branch 35
 (.leaf ⟨(24, 25307367084096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record034_result⟩)
 (.leaf ⟨(24, 25307594670080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(24, 25307596734528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 25307597774912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record037_result⟩)
 (.leaf ⟨(24, 25327716352000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(24, 25327717847296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 25327732801792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_result⟩)
 (.leaf ⟨(24, 25327732867072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10861 + i))) 0 42 :=
  interval_of_check _ 0 42 (by decide +kernel)

public theorem complete : Block 10861 10903 :=
  block_of_table results 10861 42 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0213
