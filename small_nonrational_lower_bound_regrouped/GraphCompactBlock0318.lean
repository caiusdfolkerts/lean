module
prelude
import GraphInputsRow26Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0318
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 1027103293696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record000_result⟩)
 (.leaf ⟨(26, 1027111682048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 1050736083072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record002_result⟩)
 (.leaf ⟨(26, 1208569921792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 1217163985152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record004_result⟩)
 (.leaf ⟨(26, 1225353428992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 1225481322752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 1225485484288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record007_result⟩)
 (.leaf ⟨(26, 1225485549568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 1225749725440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record009_result⟩)
 (.leaf ⟨(26, 1225749790720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 1226018193408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record011_result⟩)
 (.leaf ⟨(26, 1226026516480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(26, 1229646233856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record013_result⟩)
 (.leaf ⟨(26, 1232832921600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record014_result⟩))
 (.branch 16
 (.leaf ⟨(26, 1294070743296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 1329469620480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record016_result⟩)
 (.leaf ⟨(26, 1329502650624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(26, 1363794886912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record018_result⟩)
 (.leaf ⟨(26, 1363794952192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record019_result⟩))
 (.branch 21
 (.leaf ⟨(26, 1363798918400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record020_result⟩)
 (.leaf ⟨(26, 1422919762176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 1438984995072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record022_result⟩)
 (.leaf ⟨(26, 1458252579072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 1458318639360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 1458351669504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record025_result⟩)
 (.leaf ⟨(26, 1458351734784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(26, 1470157062400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record027_result⟩)
 (.leaf ⟨(26, 1471197249792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record028_result⟩))
 (.branch 30
 (.leaf ⟨(26, 1479773618432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record029_result⟩)
 (.branch 31
 (.leaf ⟨(26, 1481977724936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record030_result⟩)
 (.leaf ⟨(26, 1482109845512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(26, 1482322657536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record032_result⟩)
 (.leaf ⟨(26, 1482374086664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record033_result⟩))
 (.branch 35
 (.leaf ⟨(26, 1502043176960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record034_result⟩)
 (.branch 36
 (.leaf ⟨(26, 1505522516224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record035_result⟩)
 (.leaf ⟨(26, 1506067644416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00002.record036_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14119 + i))) 0 37 :=
  interval_of_check _ 0 37 (by decide +kernel)

public theorem complete : Block 14119 14156 :=
  block_of_table results 14119 37 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0318
