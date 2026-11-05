module
prelude
import GraphInputsRow26Part00017Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0333
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 11410862080000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record000_result⟩)
 (.leaf ⟨(26, 11410996281344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 11411000410240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record002_result⟩)
 (.leaf ⟨(26, 11411066470528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 11413142716416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record004_result⟩)
 (.leaf ⟨(26, 11413146845312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 11417303465984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record006_result⟩)
 (.leaf ⟨(26, 11417307594880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 11422572544000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record008_result⟩)
 (.leaf ⟨(26, 11422576705536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 11431158251648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record010_result⟩)
 (.leaf ⟨(26, 11431162445824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 11431261536256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record012_result⟩)
 (.leaf ⟨(26, 11431358513280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 11435521376256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record014_result⟩)
 (.leaf ⟨(26, 11444097679616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(26, 11444097744896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record016_result⟩)
 (.leaf ⟨(26, 11444101873792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record017_result⟩))
 (.branch 19
 (.leaf ⟨(26, 11444231946240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record018_result⟩)
 (.leaf ⟨(26, 11444236075136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(26, 11444349307136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record020_result⟩)
 (.leaf ⟨(26, 11444353501312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record021_result⟩))
 (.branch 23
 (.leaf ⟨(26, 11444500316288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record022_result⟩)
 (.leaf ⟨(26, 11444500348928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(26, 11446376300544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record024_result⟩)
 (.leaf ⟨(26, 11446378381312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record025_result⟩))
 (.branch 27
 (.leaf ⟨(26, 11446379421696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record026_result⟩)
 (.leaf ⟨(26, 11446382510208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(26, 11446429681920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record028_result⟩)
 (.leaf ⟨(26, 11446433876096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record029_result⟩))
 (.branch 31
 (.leaf ⟨(26, 11446499936384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record030_result⟩)
 (.leaf ⟨(26, 11446646784000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record031_result⟩))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf ⟨(26, 11448650563585), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record032_result⟩)
 (.leaf ⟨(26, 11450939621504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record033_result⟩))
 (.branch 35
 (.leaf ⟨(26, 11450939654144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record034_result⟩)
 (.leaf ⟨(26, 11452943433729), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record035_result⟩)))
 (.branch 38
 (.branch 37
 (.leaf ⟨(26, 11455089868801), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record036_result⟩)
 (.leaf ⟨(26, 11459180365952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record037_result⟩))
 (.branch 39
 (.leaf ⟨(26, 11471924904064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record038_result⟩)
 (.leaf ⟨(26, 11471927017472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record039_result⟩))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf ⟨(26, 11471931048960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record040_result⟩)
 (.leaf ⟨(26, 11472058974848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record041_result⟩))
 (.branch 43
 (.leaf ⟨(26, 11472129229824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record042_result⟩)
 (.leaf ⟨(26, 11478594764928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(26, 11478859006080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record044_result⟩)
 (.leaf ⟨(26, 11548508651536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record045_result⟩))
 (.branch 47
 (.leaf ⟨(26, 11548670132352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record046_result⟩)
 (.leaf ⟨(26, 11554881896464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record047_result⟩)))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf ⟨(26, 11563467636752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record048_result⟩)
 (.leaf ⟨(26, 11583824691216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record049_result⟩))
 (.branch 51
 (.leaf ⟨(26, 11588381802512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record050_result⟩)
 (.leaf ⟨(26, 11684618535040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(26, 11684622204944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record052_result⟩)
 (.leaf ⟨(26, 11709726081152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record053_result⟩))
 (.branch 55
 (.leaf ⟨(26, 11822189084688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record054_result⟩)
 (.leaf ⟨(26, 11846896599168), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record055_result⟩))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf ⟨(26, 11958352904448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record056_result⟩)
 (.leaf ⟨(26, 11958352969728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record057_result⟩))
 (.branch 59
 (.leaf ⟨(26, 11958357098624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record058_result⟩)
 (.leaf ⟨(26, 11958359179392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record059_result⟩)))
 (.branch 62
 (.branch 61
 (.leaf ⟨(26, 11958476605568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record060_result⟩)
 (.leaf ⟨(26, 11958551150592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record061_result⟩))
 (.branch 63
 (.leaf ⟨(26, 11958553231360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record062_result⟩)
 (.leaf ⟨(26, 11958604531968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00017.record063_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14942 + i))) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

public theorem complete : Block 14942 15006 :=
  block_of_table results 14942 64 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0333
