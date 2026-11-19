module
prelude
import GraphInputsRow16Part00019Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0019
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 28
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 22185461694464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 22186229252352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record001_result⟩)
 (.leaf ⟨(16, 22186501881856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 22190158856192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record003_result⟩)
 (.leaf ⟨(16, 22237807673600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 22254578630912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record005_result⟩)
 (.leaf ⟨(16, 22255045214464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(16, 22255115501568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 22255123824640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record008_result⟩)
 (.leaf ⟨(16, 22314310713344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 22323399770368), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record010_result⟩)
 (.leaf ⟨(16, 22327560585216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 22327593615360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record012_result⟩)
 (.leaf ⟨(16, 22362621231104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(16, 22374978191616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 22392153899008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record015_result⟩)
 (.leaf ⟨(16, 22396981477888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(16, 22427045740544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record017_result⟩)
 (.leaf ⟨(16, 22443563450624), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record018_result⟩))
 (.branch 20
 (.leaf ⟨(16, 22602039967744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record019_result⟩)
 (.leaf ⟨(16, 22664412463104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(16, 22664420786176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record021_result⟩)
 (.branch 23
 (.leaf ⟨(16, 22666492837888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record022_result⟩)
 (.leaf ⟨(16, 22666501160960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(16, 22689878180096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record024_result⟩)
 (.leaf ⟨(16, 22689886568448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record025_result⟩))
 (.branch 27
 (.leaf ⟨(16, 22698468081920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record026_result⟩)
 (.leaf ⟨(16, 22698472308736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record027_result⟩))))))
 (.branch 42
 (.branch 35
 (.branch 31
 (.branch 29
 (.leaf ⟨(16, 22698478551040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record028_result⟩)
 (.branch 30
 (.leaf ⟨(16, 22698676731904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record029_result⟩)
 (.leaf ⟨(16, 22717770268928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record030_result⟩)))
 (.branch 33
 (.branch 32
 (.leaf ⟨(16, 22732465192960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record031_result⟩)
 (.leaf ⟨(16, 22735078096896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record032_result⟩))
 (.branch 34
 (.leaf ⟨(16, 22735086419968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record033_result⟩)
 (.leaf ⟨(16, 22749982523648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(16, 22769040424960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record035_result⟩)
 (.branch 37
 (.leaf ⟨(16, 22769300439296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record036_result⟩)
 (.leaf ⟨(16, 22769311948800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(16, 22769874043136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record038_result⟩)
 (.leaf ⟨(16, 22769882431488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record039_result⟩))
 (.branch 41
 (.leaf ⟨(16, 22770080612352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record040_result⟩)
 (.leaf ⟨(16, 22770340626688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record041_result⟩)))))
 (.branch 49
 (.branch 45
 (.branch 43
 (.leaf ⟨(16, 22770344853504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record042_result⟩)
 (.branch 44
 (.leaf ⟨(16, 22770352136192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record043_result⟩)
 (.leaf ⟨(16, 22804405878784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(16, 22826988880128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record045_result⟩)
 (.leaf ⟨(16, 22827317100800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record046_result⟩))
 (.branch 48
 (.leaf ⟨(16, 22827321327616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record047_result⟩)
 (.leaf ⟨(16, 22827327569920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record048_result⟩))))
 (.branch 52
 (.branch 50
 (.leaf ⟨(16, 22827525750784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record049_result⟩)
 (.branch 51
 (.leaf ⟨(16, 22854940786944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record050_result⟩)
 (.leaf ⟨(16, 22855980974336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(16, 22863856828672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record052_result⟩)
 (.leaf ⟨(16, 22863927115776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record053_result⟩))
 (.branch 55
 (.leaf ⟨(16, 22863935438848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record054_result⟩)
 (.leaf ⟨(16, 22864967303168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00019.record055_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1196 + i))) 0 56 :=
  interval_of_check _ 0 56 (by decide +kernel)

public theorem complete : Block 1196 1252 :=
  block_of_table results 1196 56 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0019
