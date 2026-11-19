module
prelude
import GraphInputsRow24Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0116
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 255764529408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record000_result⟩)
 (.leaf ⟨(24, 256165052672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 256165117952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record002_result⟩)
 (.leaf ⟨(24, 256293011712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 256301400064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record004_result⟩)
 (.leaf ⟨(24, 264354431232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 264354496512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record006_result⟩)
 (.leaf ⟨(24, 264482390272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 264486551808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record008_result⟩)
 (.leaf ⟨(24, 264486617088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 265015034112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record010_result⟩)
 (.leaf ⟨(24, 265019260928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 265027584000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record012_result⟩)
 (.leaf ⟨(24, 268647301376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 476945875200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record014_result⟩)
 (.leaf ⟨(24, 665598361600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 680024702976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record016_result⟩)
 (.leaf ⟨(24, 680553120000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 680557346816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record018_result⟩)
 (.leaf ⟨(24, 680565669888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 736127713280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record020_result⟩)
 (.leaf ⟨(24, 736263995392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 737295794432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record022_result⟩)
 (.leaf ⟨(24, 737304182784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 742368837632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record024_result⟩)
 (.leaf ⟨(24, 742897254656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 742901481472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record026_result⟩)
 (.leaf ⟨(24, 744317091840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(24, 744449147136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record028_result⟩)
 (.leaf ⟨(24, 744977629440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record029_result⟩))
 (.branch 31
 (.leaf ⟨(24, 744981856256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record030_result⟩)
 (.leaf ⟨(24, 744990179328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000.record031_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7786 + i))) 0 32 :=
  interval_of_check _ 0 32 (by decide +kernel)

public theorem complete : Block 7786 7818 :=
  block_of_table results 7786 32 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0116
