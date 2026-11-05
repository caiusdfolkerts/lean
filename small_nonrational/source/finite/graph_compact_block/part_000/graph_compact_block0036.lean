module
prelude
import GraphInputsRow16Part00036Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0036
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 31749628305408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record000_result⟩)
 (.leaf ⟨(16, 31752980078592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 31755663319040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record002_result⟩)
 (.branch 4
 (.leaf ⟨(16, 31755664359424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record003_result⟩)
 (.leaf ⟨(16, 31782913515520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(16, 31785044084736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record005_result⟩)
 (.leaf ⟨(16, 31785182447616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record006_result⟩))
 (.branch 8
 (.leaf ⟨(16, 31930457276416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 31942914375936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record008_result⟩)
 (.leaf ⟨(16, 31942925885440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 31962375979264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record010_result⟩)
 (.leaf ⟨(16, 31962644381952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 31962655891456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record012_result⟩)
 (.branch 14
 (.leaf ⟨(16, 31962912849920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record013_result⟩)
 (.leaf ⟨(16, 31962921172992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(16, 31975126630656), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record015_result⟩)
 (.leaf ⟨(16, 31975130857472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record016_result⟩))
 (.branch 18
 (.leaf ⟨(16, 31975138140160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record017_result⟩)
 (.branch 19
 (.leaf ⟨(16, 31977416695808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record018_result⟩)
 (.leaf ⟨(16, 31977979248640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(16, 31978489913344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record020_result⟩)
 (.leaf ⟨(16, 31990150627584), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record021_result⟩))
 (.branch 23
 (.leaf ⟨(16, 31990150692864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record022_result⟩)
 (.branch 24
 (.leaf ⟨(16, 31990546989312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record023_result⟩)
 (.leaf ⟨(16, 31990547054592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(16, 31993522817280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record025_result⟩)
 (.leaf ⟨(16, 31993769828352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record026_result⟩))
 (.branch 28
 (.leaf ⟨(16, 32010442670336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record027_result⟩)
 (.branch 29
 (.leaf ⟨(16, 32010446897152), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record028_result⟩)
 (.leaf ⟨(16, 32010454179840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(16, 32010685390848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record030_result⟩)
 (.leaf ⟨(16, 32010949632000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record031_result⟩))
 (.branch 33
 (.leaf ⟨(16, 32011536498688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record032_result⟩)
 (.branch 34
 (.leaf ⟨(16, 32011741962240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record033_result⟩)
 (.leaf ⟨(16, 32011742872576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(16, 32042152116224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record035_result⟩)
 (.branch 37
 (.leaf ⟨(16, 32164760010752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record036_result⟩)
 (.leaf ⟨(16, 32168400158976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(16, 32168411668480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record038_result⟩)
 (.branch 40
 (.leaf ⟨(16, 32171001135104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record039_result⟩)
 (.leaf ⟨(16, 32196302766336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00036.record040_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1978 + i))) 0 41 :=
  interval_of_check _ 0 41 (by decide +kernel)

public theorem complete : Block 1978 2019 :=
  block_of_table results 1978 41 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0036
