module
prelude
import GraphInputsRow26Part00066Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0382
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 31413957038112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record000_result⟩)
 (.leaf ⟨(26, 31414801203456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 31414809591808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 31415069606144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record003_result⟩)
 (.leaf ⟨(26, 31415081115648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 31415270908160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 31415874420992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record006_result⟩)
 (.leaf ⟨(26, 31416142823680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 31416154853376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 31416344125696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record009_result⟩)
 (.leaf ⟨(26, 31423395332096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 31431376511008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record011_result⟩)
 (.leaf ⟨(26, 31442654527744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 31443191398400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 31443199721472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record014_result⟩)
 (.leaf ⟨(26, 31448895652096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(26, 31449168281600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 31449432522752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record017_result⟩)
 (.leaf ⟨(26, 31449440845824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(26, 31449630703616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record019_result⟩)
 (.branch 21
 (.leaf ⟨(26, 31451248656384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record020_result⟩)
 (.leaf ⟨(26, 31451785461760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 31464965046528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record022_result⟩)
 (.leaf ⟨(26, 31465736249344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 31466075521024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 31466348085248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record025_result⟩)
 (.leaf ⟨(26, 31466810507264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(26, 31478109446400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 31478381547552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record028_result⟩)
 (.leaf ⟨(26, 31480579362816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(26, 31480768635136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 31484872232960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record031_result⟩)
 (.leaf ⟨(26, 31491976364288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record032_result⟩)))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf ⟨(26, 31491980591104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record033_result⟩)
 (.leaf ⟨(26, 31491987873792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record034_result⟩))
 (.branch 36
 (.leaf ⟨(26, 31495801020448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record035_result⟩)
 (.branch 37
 (.leaf ⟨(26, 31511776657408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record036_result⟩)
 (.leaf ⟨(26, 31511784980480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record037_result⟩))))
 (.branch 41
 (.branch 39
 (.leaf ⟨(26, 31513320161536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record038_result⟩)
 (.branch 40
 (.leaf ⟨(26, 31513592791040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record039_result⟩)
 (.leaf ⟨(26, 31513857032192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(26, 31513865355264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record041_result⟩)
 (.branch 43
 (.leaf ⟨(26, 31514055213056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record042_result⟩)
 (.leaf ⟨(26, 31514897219584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00066.record043_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17217 + i))) 0 44 :=
  interval_of_check _ 0 44 (by decide +kernel)

public theorem complete : Block 17217 17261 :=
  block_of_table results 17217 44 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0382
