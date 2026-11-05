module
prelude
import GraphInputsRow30Part00037Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0765
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 23006799724544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record000_result⟩)
 (.leaf ⟨(30, 23014724861952), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 23108580810816), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record002_result⟩)
 (.branch 4
 (.leaf ⟨(30, 23177400950784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record003_result⟩)
 (.leaf ⟨(30, 23177523642624), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(30, 23212834422784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record005_result⟩)
 (.branch 7
 (.leaf ⟨(30, 23212958220288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record006_result⟩)
 (.leaf ⟨(30, 23218662473984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(30, 23419116601344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record008_result⟩)
 (.branch 10
 (.leaf ⟨(30, 23421263036416), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record009_result⟩)
 (.leaf ⟨(30, 23424820855040), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(30, 23474957451264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record011_result⟩)
 (.leaf ⟨(30, 23487836061696), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record012_result⟩))
 (.branch 14
 (.leaf ⟨(30, 23493540380672), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record013_result⟩)
 (.branch 15
 (.leaf ⟨(30, 23495761199104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record014_result⟩)
 (.leaf ⟨(30, 23538704646400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(30, 23543005904896), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 23543542710272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record017_result⟩)
 (.leaf ⟨(30, 23555884515328), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(30, 23556421320704), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record019_result⟩)
 (.branch 21
 (.leaf ⟨(30, 23557964890112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record020_result⟩)
 (.leaf ⟨(30, 23590713950208), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(30, 23692797018112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record022_result⟩)
 (.leaf ⟨(30, 23692920815616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record023_result⟩))
 (.branch 25
 (.leaf ⟨(30, 23932845424640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record024_result⟩)
 (.branch 26
 (.leaf ⟨(30, 23933437886464), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record025_result⟩)
 (.leaf ⟨(30, 23934511104000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(30, 23972091527168), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record027_result⟩)
 (.branch 29
 (.leaf ⟨(30, 24035442556928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record028_result⟩)
 (.leaf ⟨(30, 24055180754944), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(30, 24055717560320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record030_result⟩)
 (.branch 32
 (.leaf ⟨(30, 24058838122496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record031_result⟩)
 (.leaf ⟨(30, 24070139740160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record032_result⟩)))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf ⟨(30, 24070676545536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record033_result⟩)
 (.leaf ⟨(30, 24091033600000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record034_result⟩))
 (.branch 36
 (.leaf ⟨(30, 24103375405056), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record035_result⟩)
 (.branch 37
 (.leaf ⟨(30, 24103912210432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record036_result⟩)
 (.leaf ⟨(30, 24104027815936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record037_result⟩))))
 (.branch 41
 (.branch 39
 (.leaf ⟨(30, 24192647987456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record038_result⟩)
 (.branch 40
 (.leaf ⟨(30, 24199502504000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record039_result⟩)
 (.leaf ⟨(30, 24225916682496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(30, 24242081005568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record041_result⟩)
 (.branch 43
 (.leaf ⟨(30, 24262832824448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record042_result⟩)
 (.leaf ⟨(30, 24276439695360), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00037.record043_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24770 + i))) 0 44 :=
  interval_of_check _ 0 44 (by decide +kernel)

public theorem complete : Block 24770 24814 :=
  block_of_table results 24770 44 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0765
