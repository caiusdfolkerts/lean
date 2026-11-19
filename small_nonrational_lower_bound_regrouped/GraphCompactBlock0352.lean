module
prelude
import GraphInputsRow26Part00036Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0352
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 20276751370368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record000_result⟩)
 (.leaf ⟨(26, 20289629980800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 20344763138176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record002_result⟩)
 (.leaf ⟨(26, 20346511130752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 20346910613632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record004_result⟩)
 (.leaf ⟨(26, 20359792345216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 20380182429824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record006_result⟩)
 (.leaf ⟨(26, 20381239001216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 20385397539072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record008_result⟩)
 (.leaf ⟨(26, 20385403781376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 20388624994560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record010_result⟩)
 (.leaf ⟨(26, 20411992080512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 20412126281856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record012_result⟩)
 (.leaf ⟨(26, 20414273757312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 20414542160000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record014_result⟩)
 (.leaf ⟨(26, 20418837110912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(26, 20496999530752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record016_result⟩)
 (.leaf ⟨(26, 20498140369152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record017_result⟩))
 (.branch 19
 (.leaf ⟨(26, 20557403799552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record018_result⟩)
 (.leaf ⟨(26, 20561962991616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(26, 20574304796672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record020_result⟩)
 (.leaf ⟨(26, 20626989388032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record021_result⟩))
 (.branch 23
 (.leaf ⟨(26, 20629978906624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record022_result⟩)
 (.leaf ⟨(26, 20685726449920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(26, 20685726515200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record024_result⟩)
 (.leaf ⟨(26, 20685730644096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record025_result⟩))
 (.branch 27
 (.leaf ⟨(26, 20685732724864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record026_result⟩)
 (.leaf ⟨(26, 20685792575488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(26, 20685796704384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record028_result⟩)
 (.leaf ⟨(26, 20685850151040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record029_result⟩))
 (.branch 31
 (.leaf ⟨(26, 20685924696064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record030_result⟩)
 (.leaf ⟨(26, 20685926776832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record031_result⟩))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf ⟨(26, 20685927817216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record032_result⟩)
 (.leaf ⟨(26, 20686048331904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record033_result⟩))
 (.branch 35
 (.leaf ⟨(26, 20686193066112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record034_result⟩)
 (.leaf ⟨(26, 20686195146880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record035_result⟩)))
 (.branch 38
 (.branch 37
 (.leaf ⟨(26, 20686195179520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record036_result⟩)
 (.leaf ⟨(26, 20689412718720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record037_result⟩))
 (.branch 39
 (.leaf ⟨(26, 20689415872512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record038_result⟩)
 (.leaf ⟨(26, 20693707702272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record039_result⟩))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf ⟨(26, 20693708742656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record040_result⟩)
 (.leaf ⟨(26, 20694568075264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record041_result⟩))
 (.branch 43
 (.leaf ⟨(26, 20701849323648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record042_result⟩)
 (.leaf ⟨(26, 20701915383936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(26, 20710385811456), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record044_result⟩)
 (.leaf ⟨(26, 20710435356672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record045_result⟩))
 (.branch 47
 (.leaf ⟨(26, 20711475412992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record046_result⟩)
 (.leaf ⟨(26, 20711607370368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record047_result⟩)))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf ⟨(26, 20719077720320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record048_result⟩)
 (.leaf ⟨(26, 20719077785600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record049_result⟩))
 (.branch 51
 (.leaf ⟨(26, 20719081914496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record050_result⟩)
 (.leaf ⟨(26, 20719085815936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(26, 20719211986944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record052_result⟩)
 (.leaf ⟨(26, 20719213742336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record053_result⟩))
 (.branch 55
 (.leaf ⟨(26, 20719216115840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record054_result⟩)
 (.leaf ⟨(26, 20719216148480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record055_result⟩))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf ⟨(26, 20719217936512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record056_result⟩)
 (.leaf ⟨(26, 20719337474056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record057_result⟩))
 (.branch 59
 (.leaf ⟨(26, 20719482177664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record058_result⟩)
 (.leaf ⟨(26, 20723489966336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record059_result⟩)))
 (.branch 62
 (.branch 61
 (.leaf ⟨(26, 20723490031616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record060_result⟩)
 (.leaf ⟨(26, 20723494160512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record061_result⟩))
 (.branch 63
 (.leaf ⟨(26, 20723498222600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record062_result⟩)
 (.leaf ⟨(26, 20723514998785), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00036.record063_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15924 + i))) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

public theorem complete : Block 15924 15988 :=
  block_of_table results 15924 64 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0352
