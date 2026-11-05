module
prelude
import GraphInputsSix0Part00089Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1054
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 34636092936448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 34637873185024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record001_result⟩)
 (.leaf ⟨(32, 34638009532416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(32, 34638017855488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record003_result⟩)
 (.leaf ⟨(32, 34638240743424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record004_result⟩))
 (.branch 6
 (.leaf ⟨(32, 34639196983552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record005_result⟩)
 (.leaf ⟨(32, 34639205371904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(32, 34639213498624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record007_result⟩)
 (.leaf ⟨(32, 34639716814864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record008_result⟩))
 (.branch 10
 (.leaf ⟨(32, 34640286974720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record009_result⟩)
 (.leaf ⟨(32, 34640790290960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(32, 34641092837632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record011_result⟩)
 (.leaf ⟨(32, 34641864560640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record012_result⟩))
 (.branch 14
 (.leaf ⟨(32, 34643248285712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record013_result⟩)
 (.leaf ⟨(32, 34670085439744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(32, 34673288315136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 34673556783104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record016_result⟩)
 (.leaf ⟨(32, 34673565106176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(32, 34674076553216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record018_result⟩)
 (.leaf ⟨(32, 34674344886528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record019_result⟩))
 (.branch 21
 (.leaf ⟨(32, 34674382536704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record020_result⟩)
 (.leaf ⟨(32, 34674655100928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(32, 34675150029312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record022_result⟩)
 (.leaf ⟨(32, 34675150553088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record023_result⟩))
 (.branch 25
 (.leaf ⟨(32, 34681861050624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record024_result⟩)
 (.leaf ⟨(32, 34681895059456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(32, 34682976600064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record026_result⟩)
 (.leaf ⟨(32, 34683505082368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record027_result⟩))
 (.branch 29
 (.leaf ⟨(32, 34699074863104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record028_result⟩)
 (.leaf ⟨(32, 34703629619200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00089.record029_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (35063 + i))) 0 30 :=
  interval_of_check _ 0 30 (by decide +kernel)

public theorem complete : Block 35063 35093 :=
  block_of_table results 35063 30 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1054
