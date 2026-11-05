module
prelude
import GraphInputsRow24Part00014Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0130
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 8727927488768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 8727939778560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record001_result⟩)
 (.leaf ⟨(24, 8728179116288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 8729659506944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 8731689550080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record004_result⟩)
 (.leaf ⟨(24, 8732226420736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 8732234743808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 8732474146816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record007_result⟩)
 (.leaf ⟨(24, 8734092886016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 8734629691392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record009_result⟩)
 (.leaf ⟨(24, 8736517128960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 8744572322048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record011_result⟩)
 (.leaf ⟨(24, 8744830371840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 8744956395520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 8745113354240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record014_result⟩)
 (.leaf ⟨(24, 8745358721544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(24, 8746839375872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 8747111940096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record017_result⟩)
 (.leaf ⟨(24, 8748848546048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(24, 8749653688832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 8757975318528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record020_result⟩)
 (.leaf ⟨(24, 8766305140736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 8775163445248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record022_result⟩)
 (.leaf ⟨(24, 8783484944384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 8792334925824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record024_result⟩)
 (.leaf ⟨(24, 8910324990208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record025_result⟩))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf ⟨(24, 8911862169600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record026_result⟩)
 (.branch 28
 (.leaf ⟨(24, 8988768927744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record027_result⟩)
 (.leaf ⟨(24, 9056555122816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(24, 9064601879808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record029_result⟩)
 (.branch 31
 (.leaf ⟨(24, 9065134588160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record030_result⟩)
 (.leaf ⟨(24, 9185404141696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record031_result⟩))))
 (.branch 35
 (.branch 33
 (.leaf ⟨(24, 9202305106176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record032_result⟩)
 (.branch 34
 (.leaf ⟨(24, 9202573541504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record033_result⟩)
 (.leaf ⟨(24, 9202841976832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(24, 9202846138368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record035_result⟩)
 (.leaf ⟨(24, 9249828651136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record036_result⟩))
 (.branch 38
 (.leaf ⟨(24, 9254121521280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record037_result⟩)
 (.leaf ⟨(24, 9256267956352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record038_result⟩)))))
 (.branch 46
 (.branch 42
 (.branch 40
 (.leaf ⟨(24, 9270898753536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 9288480211072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record040_result⟩)
 (.leaf ⟨(24, 9495742840832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(24, 9536517718144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record042_result⟩)
 (.leaf ⟨(24, 9538463924224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record043_result⟩))
 (.branch 45
 (.leaf ⟨(24, 9538732326912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record044_result⟩)
 (.leaf ⟨(24, 9545097183488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record045_result⟩))))
 (.branch 49
 (.branch 47
 (.leaf ⟨(24, 9565710065920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record046_result⟩)
 (.branch 48
 (.leaf ⟨(24, 9659125612672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record047_result⟩)
 (.leaf ⟨(24, 9665366737024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record048_result⟩)))
 (.branch 51
 (.branch 50
 (.leaf ⟨(24, 9666406924416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record049_result⟩)
 (.leaf ⟨(24, 9675902844928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record050_result⟩))
 (.branch 52
 (.leaf ⟨(24, 9676295012480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record051_result⟩)
 (.leaf ⟨(24, 9682267701504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00014.record052_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8544 + i))) 0 53 :=
  interval_of_check _ 0 53 (by decide +kernel)

public theorem complete : Block 8544 8597 :=
  block_of_table results 8544 53 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0130
