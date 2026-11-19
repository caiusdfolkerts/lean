module
prelude
import GraphInputsRow19Part00036Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0076
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 34121521332480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 34124790792448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record001_result⟩)
 (.leaf ⟨(19, 34126908424192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 34154809401600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 34158185809952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record004_result⟩)
 (.leaf ⟨(19, 34159011569664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 34159242780672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 34190238712064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record007_result⟩)
 (.leaf ⟨(19, 34190255227136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(19, 34194399461632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record009_result⟩)
 (.leaf ⟨(19, 34194436718592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record010_result⟩))
 (.branch 12
 (.leaf ⟨(19, 34194445041664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record011_result⟩)
 (.leaf ⟨(19, 34194667929600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(19, 34194676252672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record013_result⟩)
 (.branch 15
 (.leaf ⟨(19, 34195187699712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record014_result⟩)
 (.leaf ⟨(19, 34195724500992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(19, 34195732824064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record016_result⟩)
 (.branch 18
 (.leaf ⟨(19, 34239530410048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record017_result⟩)
 (.leaf ⟨(19, 34240570466368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(19, 34635776557312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record019_result⟩)
 (.branch 21
 (.leaf ⟨(19, 34635776622592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record020_result⟩)
 (.leaf ⟨(19, 34636919476480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(19, 34636919541760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record022_result⟩)
 (.leaf ⟨(19, 34642443370496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record023_result⟩))
 (.branch 25
 (.leaf ⟨(19, 34642971852800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record024_result⟩)
 (.leaf ⟨(19, 34669131469056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record025_result⟩))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf ⟨(19, 34670106443776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record026_result⟩)
 (.branch 28
 (.leaf ⟨(19, 34670201307392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record027_result⟩)
 (.leaf ⟨(19, 34670205534208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record028_result⟩)))
 (.branch 30
 (.leaf ⟨(19, 34670213337088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record029_result⟩)
 (.branch 31
 (.leaf ⟨(19, 34670217822464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record030_result⟩)
 (.leaf ⟨(19, 34670230112256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record031_result⟩))))
 (.branch 35
 (.branch 33
 (.leaf ⟨(19, 34673547937808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record032_result⟩)
 (.branch 34
 (.leaf ⟨(19, 34673556721920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record033_result⟩)
 (.leaf ⟨(19, 34673565106177), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record034_result⟩)))
 (.branch 37
 (.branch 36
 (.leaf ⟨(19, 34673565110272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record035_result⟩)
 (.leaf ⟨(19, 34673573236992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record036_result⟩))
 (.branch 38
 (.leaf ⟨(19, 34673581885440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record037_result⟩)
 (.leaf ⟨(19, 34674076553232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record038_result⟩)))))
 (.branch 45
 (.branch 42
 (.branch 40
 (.leaf ⟨(19, 34674362056960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record039_result⟩)
 (.branch 41
 (.leaf ⟨(19, 34674399313920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record040_result⟩)
 (.leaf ⟨(19, 34674407636992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(19, 34674630524928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record042_result⟩)
 (.branch 44
 (.leaf ⟨(19, 34674638848000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record043_result⟩)
 (.leaf ⟨(19, 34674646713088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record044_result⟩))))
 (.branch 48
 (.branch 46
 (.leaf ⟨(19, 34674671878144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record045_result⟩)
 (.branch 47
 (.leaf ⟨(19, 34675150029328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record046_result⟩)
 (.leaf ⟨(19, 34675150295040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record047_result⟩)))
 (.branch 50
 (.branch 49
 (.leaf ⟨(19, 34675167330304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record048_result⟩)
 (.leaf ⟨(19, 34681878221056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record049_result⟩))
 (.branch 51
 (.leaf ⟨(19, 34681911836672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record050_result⟩)
 (.leaf ⟨(19, 34681920159744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00036.record051_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5499 + i))) 0 52 :=
  interval_of_check _ 0 52 (by decide +kernel)

public theorem complete : Block 5499 5551 :=
  block_of_table results 5499 52 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0076
