module
prelude
import GraphInputsSix0Part00086Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1051
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 32804977516544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record000_result⟩)
 (.leaf ⟨(32, 32805011587072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 32806034087936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record002_result⟩)
 (.branch 4
 (.leaf ⟨(32, 32806101188608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record003_result⟩)
 (.leaf ⟨(32, 32813567213824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(32, 32813835681792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record005_result⟩)
 (.branch 7
 (.leaf ⟨(32, 32813844004864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record006_result⟩)
 (.leaf ⟨(32, 32814355712000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(32, 32822140209408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record008_result⟩)
 (.branch 10
 (.leaf ⟨(32, 32822677080064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record009_result⟩)
 (.leaf ⟨(32, 32822693724672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(32, 32839319945732), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record011_result⟩)
 (.leaf ⟨(32, 32916646404352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record012_result⟩))
 (.branch 14
 (.leaf ⟨(32, 32916713570304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record013_result⟩)
 (.branch 15
 (.leaf ⟨(32, 32916721893376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record014_result⟩)
 (.leaf ⟨(32, 32917183275008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(32, 32917233600512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record016_result⟩)
 (.branch 18
 (.leaf ⟨(32, 32918776973568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record017_result⟩)
 (.leaf ⟨(32, 32919313844224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(32, 32919330488832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record019_result⟩)
 (.branch 21
 (.leaf ⟨(32, 32933809358880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record020_result⟩)
 (.leaf ⟨(32, 32935956709892), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(32, 32986712588320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record022_result⟩)
 (.leaf ⟨(32, 32988877308160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record023_result⟩))
 (.branch 25
 (.leaf ⟨(32, 32991025832192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record024_result⟩)
 (.branch 26
 (.leaf ⟨(32, 33022146003200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record025_result⟩)
 (.leaf ⟨(32, 33023202574592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(32, 33023338807296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record027_result⟩)
 (.branch 29
 (.leaf ⟨(32, 33025419182080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record028_result⟩)
 (.leaf ⟨(32, 33032996659456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(32, 33058653217024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record030_result⟩)
 (.branch 32
 (.leaf ⟨(32, 33059709788416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record031_result⟩)
 (.leaf ⟨(32, 33059777871872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record032_result⟩)))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf ⟨(32, 33063938621440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record033_result⟩)
 (.leaf ⟨(32, 33064135696640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record034_result⟩))
 (.branch 36
 (.leaf ⟨(32, 33065208914176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record035_result⟩)
 (.branch 37
 (.leaf ⟨(32, 33098495492096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record036_result⟩)
 (.leaf ⟨(32, 33099568120576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record037_result⟩))))
 (.branch 41
 (.branch 39
 (.leaf ⟨(32, 33102730625024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record038_result⟩)
 (.branch 40
 (.leaf ⟨(32, 33126320455680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record039_result⟩)
 (.leaf ⟨(32, 33158515933184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(32, 33158557090048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record041_result⟩)
 (.branch 43
 (.leaf ⟨(32, 33167415181888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record042_result⟩)
 (.leaf ⟨(32, 33195132256256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00086.record043_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34889 + i))) 0 44 :=
  interval_of_check _ 0 44 (by decide +kernel)

public theorem complete : Block 34889 34933 :=
  block_of_table results 34889 44 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1051
