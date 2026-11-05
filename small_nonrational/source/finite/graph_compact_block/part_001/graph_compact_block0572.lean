module
prelude
import GraphInputsRow29Part00138Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0572
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 23692920815616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record000_result⟩)
 (.leaf ⟨(29, 23695372386560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 23696140468224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record002_result⟩)
 (.leaf ⟨(29, 23699665256704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 23764330938368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record004_result⟩)
 (.leaf ⟨(29, 23795798704128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 23795807027200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 23796302020864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record007_result⟩)
 (.leaf ⟨(29, 23796937981952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 23832773722368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record009_result⟩)
 (.leaf ⟨(29, 23897760071680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 23921626251264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record011_result⟩)
 (.branch 13
 (.leaf ⟨(29, 23925787000832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record012_result⟩)
 (.leaf ⟨(29, 23932700754176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(29, 23932837101568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record014_result⟩)
 (.leaf ⟨(29, 23932845424640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record015_result⟩))
 (.branch 17
 (.leaf ⟨(29, 23932969222144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 23932977545216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record017_result⟩)
 (.leaf ⟨(29, 23933437886464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22494 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 22494 22513 :=
  block_of_table results 22494 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0572
