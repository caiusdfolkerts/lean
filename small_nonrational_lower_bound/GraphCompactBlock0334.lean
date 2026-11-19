module
prelude
import GraphInputsRow26Part00018Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0334
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 11958608726144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record000_result⟩)
 (.leaf ⟨(26, 11958819520640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 11958821601408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 11958821634048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record003_result⟩)
 (.leaf ⟨(26, 11960825413633), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 11963945975809), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 11966334124160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record006_result⟩)
 (.leaf ⟨(26, 11966334156800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 11966335717376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 11967198658561), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record009_result⟩)
 (.leaf ⟨(26, 11974475778176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 11974574868608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record011_result⟩)
 (.leaf ⟨(26, 11983045296128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 11984099754112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 11984101867520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record014_result⟩)
 (.leaf ⟨(26, 11984105899008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(26, 11984233824896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 11984304079872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record017_result⟩)
 (.leaf ⟨(26, 11991704174848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(26, 11991704240128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record019_result⟩)
 (.branch 21
 (.leaf ⟨(26, 11991708369024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record020_result⟩)
 (.leaf ⟨(26, 11991712270464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 11991838441472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record022_result⟩)
 (.leaf ⟨(26, 11991840196864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 11991842570368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 11991842603008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record025_result⟩)
 (.leaf ⟨(26, 11991844391040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(26, 11991963928584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 11992108632192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record028_result⟩)
 (.leaf ⟨(26, 11996120615040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(26, 11996124677128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 11996141453313), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_result⟩)
 (.leaf ⟨(26, 12000277170432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(26, 12000277235712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 12000417547272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record034_result⟩)
 (.leaf ⟨(26, 12000681788424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(26, 12000698564609), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 12008867104896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record037_result⟩)
 (.leaf ⟨(26, 12021613593728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(26, 12021617787904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 12021881897476), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record040_result⟩)
 (.leaf ⟨(26, 12098161688704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(26, 12098262368272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 12098425897216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record043_result⟩)
 (.leaf ⟨(26, 12098425929856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15006 + i))) 0 45 :=
  interval_of_check _ 0 45 (by decide +kernel)

public theorem complete : Block 15006 15051 :=
  block_of_table results 15006 45 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0334
