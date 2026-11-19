module
prelude
import GraphInputsRow24Part00028Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0144
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 15285897658368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 15286360080384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record001_result⟩)
 (.leaf ⟨(24, 15294399578368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 15294672207872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 15294936449024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record004_result⟩)
 (.leaf ⟨(24, 15294944772096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 15295184175104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 15299237642240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record007_result⟩)
 (.leaf ⟨(24, 15299344924672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 15302968672512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 15307282350336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record010_result⟩)
 (.leaf ⟨(24, 15307666423808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(24, 15307823382528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 15309549404160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record013_result⟩)
 (.leaf ⟨(24, 15320148541440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(24, 15320685346816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 15326611833088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record016_result⟩)
 (.leaf ⟨(24, 15326884462592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(24, 15327148703744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 15327157026816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record019_result⟩)
 (.leaf ⟨(24, 15327396429824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 15333051138304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record021_result⟩)
 (.leaf ⟨(24, 15333588008960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 15333596332032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record023_result⟩)
 (.leaf ⟨(24, 15333637554176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00028.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9118 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 9118 9143 :=
  block_of_table results 9118 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0144
