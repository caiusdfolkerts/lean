module
prelude
import GraphInputsRow24Part00119Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0235
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 28452313121024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 28452323330048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record001_result⟩)
 (.leaf ⟨(24, 28458554245376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 28458564454400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 28484378624000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record004_result⟩)
 (.leaf ⟨(24, 28484508598528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 28484518807552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 28484626024704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record007_result⟩)
 (.leaf ⟨(24, 28488786643200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 28488803287808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record009_result⟩)
 (.leaf ⟨(24, 28492955781120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 28493484130824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record011_result⟩)
 (.leaf ⟨(24, 28521133309952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 28523164139520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 28523213684736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record014_result⟩)
 (.leaf ⟨(24, 28590630551808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(24, 28591097168000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 28597539594368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record017_result⟩)
 (.leaf ⟨(24, 28623965307136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(24, 28623969501312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 28624369532944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record020_result⟩)
 (.leaf ⟨(24, 28626251178112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 28626515968016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record022_result⟩)
 (.leaf ⟨(24, 28631667589376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 28632808427776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record024_result⟩)
 (.leaf ⟨(24, 28636192194688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11371 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 11371 11397 :=
  block_of_table results 11371 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0235
