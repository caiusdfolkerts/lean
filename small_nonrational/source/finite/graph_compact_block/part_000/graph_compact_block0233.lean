module
prelude
import GraphInputsRow24Part00117Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0233
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 28076499013888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record000_result⟩)
 (.leaf ⟨(24, 28077681869056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 28077690257408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record002_result⟩)
 (.leaf ⟨(24, 28080790323456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 28080790388736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record004_result⟩)
 (.leaf ⟨(24, 28080791884032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 28081054564608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 28081054629888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record007_result⟩)
 (.leaf ⟨(24, 28081056125184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 28081179854864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record009_result⟩)
 (.leaf ⟨(24, 28082253594625), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 28085194391808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record011_result⟩)
 (.leaf ⟨(24, 28090568867840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(24, 28111974498560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record013_result⟩)
 (.leaf ⟨(24, 28111982886912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record014_result⟩))
 (.branch 16
 (.leaf ⟨(24, 28116135248128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 28116143636480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record016_result⟩)
 (.leaf ⟨(24, 28116333428992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(24, 28116539998208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record018_result⟩)
 (.leaf ⟨(24, 28117406646528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record019_result⟩))
 (.branch 21
 (.leaf ⟨(24, 28124861497344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record020_result⟩)
 (.leaf ⟨(24, 28151501619456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 28152046813184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record022_result⟩)
 (.leaf ⟨(24, 28177428648192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 28177692889344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 28177699180608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record025_result⟩)
 (.leaf ⟨(24, 28184138485824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(24, 28193585102849), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record027_result⟩)
 (.leaf ⟨(24, 28247064641792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record028_result⟩))
 (.branch 30
 (.leaf ⟨(24, 28247337271296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record029_result⟩)
 (.branch 31
 (.leaf ⟨(24, 28247601512448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record030_result⟩)
 (.leaf ⟨(24, 28247609835520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(24, 28249145016576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record032_result⟩)
 (.leaf ⟨(24, 28249417646080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record033_result⟩))
 (.branch 35
 (.leaf ⟨(24, 28249681887232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record034_result⟩)
 (.branch 36
 (.leaf ⟨(24, 28249690210304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record035_result⟩)
 (.leaf ⟨(24, 28249880068096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00117.record036_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11300 + i))) 0 37 :=
  interval_of_check _ 0 37 (by decide +kernel)

public theorem complete : Block 11300 11337 :=
  block_of_table results 11300 37 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0233
