module
prelude
import GraphInputsSix0Part00082Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1047
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 31787388829696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 31787858534400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record001_result⟩)
 (.leaf ⟨(32, 31789200605440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 31790005748224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 31795643031808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record004_result⟩)
 (.leaf ⟨(32, 31812822900736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 31812890001408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 31819283071232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record007_result⟩)
 (.leaf ⟨(32, 31819353358336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(32, 31819361681408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record009_result⟩)
 (.leaf ⟨(32, 31819551539200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record010_result⟩))
 (.branch 12
 (.leaf ⟨(32, 31819559862272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record011_result⟩)
 (.leaf ⟨(32, 31819601084416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(32, 31820070789120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record013_result⟩)
 (.branch 15
 (.leaf ⟨(32, 31825725497600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record014_result⟩)
 (.leaf ⟨(32, 31826262368256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(32, 31826311913472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record016_result⟩)
 (.branch 18
 (.leaf ⟨(32, 31827855286528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record017_result⟩)
 (.leaf ⟨(32, 31828459127296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(32, 31842887671840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record019_result⟩)
 (.branch 21
 (.leaf ⟨(32, 31886971863072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record020_result⟩)
 (.leaf ⟨(32, 31887070953504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(32, 31887205154848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record022_result⟩)
 (.leaf ⟨(32, 31889171693824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record023_result⟩))
 (.branch 25
 (.leaf ⟨(32, 31889369874688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record024_result⟩)
 (.leaf ⟨(32, 31889634115840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record025_result⟩))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf ⟨(32, 31889674997824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record026_result⟩)
 (.branch 28
 (.leaf ⟨(32, 31890426368032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record027_result⟩)
 (.leaf ⟨(32, 31890690609184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(32, 31891386278144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record029_result⟩)
 (.branch 31
 (.leaf ⟨(32, 31891482939424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record030_result⟩)
 (.leaf ⟨(32, 31891751342112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record031_result⟩))))
 (.branch 35
 (.branch 33
 (.leaf ⟨(32, 31896114303040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record032_result⟩)
 (.branch 34
 (.leaf ⟨(32, 31904435802176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record033_result⟩)
 (.leaf ⟨(32, 31922638569728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(32, 31922910662720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record035_result⟩)
 (.leaf ⟨(32, 31923695141120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record036_result⟩))
 (.branch 38
 (.leaf ⟨(32, 31925771239680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record037_result⟩)
 (.leaf ⟨(32, 31926237823232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record038_result⟩)))))
 (.branch 46
 (.branch 42
 (.branch 40
 (.leaf ⟨(32, 31927311040768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record039_result⟩)
 (.branch 41
 (.leaf ⟨(32, 31929349967936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record040_result⟩)
 (.leaf ⟨(32, 31937935708224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(32, 31960530452736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record042_result⟩)
 (.leaf ⟨(32, 31961603670272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record043_result⟩))
 (.branch 45
 (.leaf ⟨(32, 31973012701440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record044_result⟩)
 (.leaf ⟨(32, 31994356498688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record045_result⟩))))
 (.branch 49
 (.branch 47
 (.leaf ⟨(32, 31994629128192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record046_result⟩)
 (.branch 48
 (.leaf ⟨(32, 31994901692416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record047_result⟩)
 (.leaf ⟨(32, 31995091550208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record048_result⟩)))
 (.branch 51
 (.branch 50
 (.leaf ⟨(32, 32011536367616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record049_result⟩)
 (.leaf ⟨(32, 32011808931840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record050_result⟩))
 (.branch 52
 (.leaf ⟨(32, 32012271353856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record051_result⟩)
 (.leaf ⟨(32, 32012337414144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00082.record052_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34674 + i))) 0 53 :=
  interval_of_check _ 0 53 (by decide +kernel)

public theorem complete : Block 34674 34727 :=
  block_of_table results 34674 53 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1047
