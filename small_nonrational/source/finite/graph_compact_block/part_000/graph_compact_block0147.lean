module
prelude
import GraphInputsRow24Part00031Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0147
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 16607166398464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 16607174721536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record001_result⟩)
 (.leaf ⟨(24, 16630675693584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 16632403658768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 16632424435968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record004_result⟩)
 (.leaf ⟨(24, 16632556556544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 16636959064320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 16639260102912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record007_result⟩)
 (.leaf ⟨(24, 16639265873984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 16639265890304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 16639266394176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record010_result⟩)
 (.leaf ⟨(24, 16639317772304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(24, 16640348537088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 16640458629120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record013_result⟩)
 (.leaf ⟨(24, 16641532366848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(24, 16643669893376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 16648570437888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record016_result⟩)
 (.leaf ⟨(24, 16648574664704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(24, 16648713011201), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 16648780128256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record019_result⟩)
 (.leaf ⟨(24, 16649853865984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 16657528406016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record021_result⟩)
 (.leaf ⟨(24, 16704272924928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 16705007976448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record023_result⟩)
 (.leaf ⟨(24, 16709168726016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00031.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9238 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 9238 9263 :=
  block_of_table results 9238 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0147
