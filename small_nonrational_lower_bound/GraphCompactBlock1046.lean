module
prelude
import GraphInputsSix0Part00081Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1046
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 31596732219904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record000_result⟩)
 (.leaf ⟨(32, 31602369503488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 31604517044224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record002_result⟩)
 (.leaf ⟨(32, 31605053849600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(32, 31622042750976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record004_result⟩)
 (.leaf ⟨(32, 31622099902720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record005_result⟩))
 (.branch 7
 (.leaf ⟨(32, 31655386480640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 31659621613568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record007_result⟩)
 (.leaf ⟨(32, 31689679110144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(32, 31722914775040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record009_result⟩)
 (.leaf ⟨(32, 31722964320256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record010_result⟩))
 (.branch 12
 (.leaf ⟨(32, 31751688716544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record011_result⟩)
 (.leaf ⟨(32, 31751825063936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(32, 31751833387008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record013_result⟩)
 (.leaf ⟨(32, 31752023244800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record014_result⟩))
 (.branch 16
 (.leaf ⟨(32, 31753835151616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 31754103619584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record016_result⟩)
 (.leaf ⟨(32, 31754111942656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(32, 31754573324288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record018_result⟩)
 (.leaf ⟨(32, 31754875339008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record019_result⟩))
 (.branch 21
 (.leaf ⟨(32, 31755646541824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record020_result⟩)
 (.leaf ⟨(32, 31758264369152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(32, 31758272692224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record022_result⟩)
 (.leaf ⟨(32, 31761317765376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record023_result⟩))
 (.branch 25
 (.leaf ⟨(32, 31763465306112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record024_result⟩)
 (.branch 26
 (.leaf ⟨(32, 31763539689472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record025_result⟩)
 (.leaf ⟨(32, 31764002111488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record026_result⟩)))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf ⟨(32, 31778497634304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record027_result⟩)
 (.leaf ⟨(32, 31778564734976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record028_result⟩))
 (.branch 30
 (.leaf ⟨(32, 31784924381440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record029_result⟩)
 (.leaf ⟨(32, 31785060728832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record030_result⟩)))
 (.branch 33
 (.branch 32
 (.leaf ⟨(32, 31785069051904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record031_result⟩)
 (.leaf ⟨(32, 31785308454912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record032_result⟩))
 (.branch 34
 (.leaf ⟨(32, 31787070816512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record033_result⟩)
 (.branch 35
 (.leaf ⟨(32, 31787339284480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record034_result⟩)
 (.leaf ⟨(32, 31787347607552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00081.record035_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34638 + i))) 0 36 :=
  interval_of_check _ 0 36 (by decide +kernel)

public theorem complete : Block 34638 34674 :=
  block_of_table results 34638 36 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1046
