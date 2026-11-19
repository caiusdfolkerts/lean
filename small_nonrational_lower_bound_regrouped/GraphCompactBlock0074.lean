module
prelude
import GraphInputsRow19Part00034Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0074
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 32522629029888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 32522860240896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record001_result⟩)
 (.leaf ⟨(19, 32523124482048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 32530141552640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 32531189735680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record004_result⟩)
 (.leaf ⟨(19, 32531198124032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 32531726467616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 32641803157760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record007_result⟩)
 (.leaf ⟨(19, 32641810440448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(19, 32641810505728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record009_result⟩)
 (.leaf ⟨(19, 32642306672896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record010_result⟩))
 (.branch 12
 (.leaf ⟨(19, 32642313752608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record011_result⟩)
 (.leaf ⟨(19, 32642313760768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(19, 32642314012704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record013_result⟩)
 (.branch 15
 (.leaf ⟨(19, 32642331314184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record014_result⟩)
 (.leaf ⟨(19, 32642900822272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(19, 32642900887552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record016_result⟩)
 (.leaf ⟨(19, 32642917532160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record017_result⟩))
 (.branch 19
 (.leaf ⟨(19, 32643371500552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record018_result⟩)
 (.leaf ⟨(19, 32643388276737), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(19, 32658973394976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record020_result⟩)
 (.branch 22
 (.leaf ⟨(19, 32659469763592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record021_result⟩)
 (.leaf ⟨(19, 32710626451472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(19, 32711700390144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record023_result⟩)
 (.leaf ⟨(19, 32712757020688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record024_result⟩))
 (.branch 26
 (.leaf ⟨(19, 32712761182224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record025_result⟩)
 (.leaf ⟨(19, 32713794945280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record026_result⟩))))))
 (.branch 40
 (.branch 33
 (.branch 30
 (.branch 28
 (.leaf ⟨(19, 32715076798496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record027_result⟩)
 (.branch 29
 (.leaf ⟨(19, 32723415080960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record028_result⟩)
 (.leaf ⟨(19, 32724471652352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(19, 32724999995936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record030_result⟩)
 (.branch 32
 (.leaf ⟨(19, 32745990422784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record031_result⟩)
 (.leaf ⟨(19, 32779242078464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record032_result⟩))))
 (.branch 36
 (.branch 34
 (.leaf ⟨(19, 32779242143744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record033_result⟩)
 (.branch 35
 (.leaf ⟨(19, 32779245199616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record034_result⟩)
 (.leaf ⟨(19, 32779245264896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record035_result⟩)))
 (.branch 38
 (.branch 37
 (.leaf ⟨(19, 32779477190912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record036_result⟩)
 (.leaf ⟨(19, 32779484270624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record037_result⟩))
 (.branch 39
 (.leaf ⟨(19, 32779484278784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record038_result⟩)
 (.leaf ⟨(19, 32779501832200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record039_result⟩)))))
 (.branch 47
 (.branch 43
 (.branch 41
 (.leaf ⟨(19, 32780335581440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 32780335646720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record041_result⟩)
 (.leaf ⟨(19, 32780352291328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record042_result⟩)))
 (.branch 45
 (.branch 44
 (.leaf ⟨(19, 32780541102112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record043_result⟩)
 (.leaf ⟨(19, 32780542018568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record044_result⟩))
 (.branch 46
 (.leaf ⟨(19, 32780558794753), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record045_result⟩)
 (.leaf ⟨(19, 32787815074048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record046_result⟩))))
 (.branch 50
 (.branch 48
 (.leaf ⟨(19, 32787822413856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record047_result⟩)
 (.branch 49
 (.leaf ⟨(19, 32788318782472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record048_result⟩)
 (.leaf ⟨(19, 32788335558657), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record049_result⟩)))
 (.branch 52
 (.branch 51
 (.leaf ⟨(19, 32804977119264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record050_result⟩)
 (.leaf ⟨(19, 32804977647616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record051_result⟩))
 (.branch 53
 (.leaf ⟨(19, 32804978557952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record052_result⟩)
 (.leaf ⟨(19, 32805010539040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00034.record053_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5381 + i))) 0 54 :=
  interval_of_check _ 0 54 (by decide +kernel)

public theorem complete : Block 5381 5435 :=
  block_of_table results 5381 54 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0074
