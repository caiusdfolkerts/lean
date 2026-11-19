module
prelude
import GraphInputsRow25Part00017Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0307
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 37
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 25771970199552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record000_result⟩)
 (.leaf ⟨(25, 25772110643200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 25772507004928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record002_result⟩)
 (.leaf ⟨(25, 25772622610432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(25, 25774702985216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record004_result⟩)
 (.leaf ⟨(25, 25776246423552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record005_result⟩))
 (.branch 7
 (.leaf ⟨(25, 25787001487360), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 25787185233920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record007_result⟩)
 (.leaf ⟨(25, 25789131276288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(25, 25844474970112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record009_result⟩)
 (.leaf ⟨(25, 25844697858048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record010_result⟩))
 (.branch 12
 (.leaf ⟨(25, 25848759517184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record011_result⟩)
 (.leaf ⟨(25, 25848767840256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(25, 25857353580544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record013_result⟩)
 (.leaf ⟨(25, 25857582710784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record014_result⟩))
 (.branch 16
 (.leaf ⟨(25, 25860803923968), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 25864327151872), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record016_result⟩)
 (.leaf ⟨(25, 25916395225088), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(25, 25924980965376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record018_result⟩)
 (.leaf ⟨(25, 25925228171264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record019_result⟩))
 (.branch 21
 (.leaf ⟨(25, 25926301647360), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record020_result⟩)
 (.leaf ⟨(25, 25933012668672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(25, 25963354128384), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record022_result⟩)
 (.leaf ⟨(25, 25980811411456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record023_result⟩))
 (.branch 25
 (.leaf ⟨(25, 25993159393536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record024_result⟩)
 (.branch 26
 (.leaf ⟨(25, 25993696264192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record025_result⟩)
 (.leaf ⟨(25, 25993813430272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(25, 26117981929472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record027_result⟩)
 (.leaf ⟨(25, 26122545283072), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record028_result⟩))
 (.branch 30
 (.leaf ⟨(25, 26130983948288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record029_result⟩)
 (.branch 31
 (.leaf ⟨(25, 26139171098688), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record030_result⟩)
 (.leaf ⟨(25, 26207890440708), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(25, 26319559723264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record032_result⟩)
 (.leaf ⟨(25, 26319576694784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record033_result⟩))
 (.branch 35
 (.leaf ⟨(25, 26320113500160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record034_result⟩)
 (.branch 36
 (.leaf ⟨(25, 26336739592192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record035_result⟩)
 (.leaf ⟨(25, 26393820832000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record036_result⟩)))))))
 (.branch 55
 (.branch 46
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(25, 26393952952576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record037_result⟩)
 (.leaf ⟨(25, 26398254243904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record038_result⟩))
 (.branch 40
 (.leaf ⟨(25, 26398287274048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record039_result⟩)
 (.leaf ⟨(25, 26427221647616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(25, 26428353642496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record041_result⟩)
 (.leaf ⟨(25, 26466873081856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record042_result⟩))
 (.branch 44
 (.leaf ⟨(25, 26467275653248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record043_result⟩)
 (.branch 45
 (.leaf ⟨(25, 26467275685888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record044_result⟩)
 (.leaf ⟨(25, 26467345899552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record045_result⟩)))))
 (.branch 50
 (.branch 48
 (.branch 47
 (.leaf ⟨(25, 26468419637280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record046_result⟩)
 (.leaf ⟨(25, 26502779371521), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record047_result⟩))
 (.branch 49
 (.leaf ⟨(25, 26532370808832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record048_result⟩)
 (.leaf ⟨(25, 26648730697728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record049_result⟩)))
 (.branch 52
 (.branch 51
 (.leaf ⟨(25, 26777579716608), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record050_result⟩)
 (.leaf ⟨(25, 26943986606208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record051_result⟩))
 (.branch 53
 (.leaf ⟨(25, 27015910527008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record052_result⟩)
 (.branch 54
 (.leaf ⟨(25, 27016762032640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record053_result⟩)
 (.leaf ⟨(25, 27016766226432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record054_result⟩))))))
 (.branch 64
 (.branch 59
 (.branch 57
 (.branch 56
 (.leaf ⟨(25, 27080063000576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record055_result⟩)
 (.leaf ⟨(25, 27110997557248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record056_result⟩))
 (.branch 58
 (.leaf ⟨(25, 27121378459648), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record057_result⟩)
 (.leaf ⟨(25, 27128693293056), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record058_result⟩)))
 (.branch 61
 (.branch 60
 (.leaf ⟨(25, 27130373144576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record059_result⟩)
 (.leaf ⟨(25, 27130645708800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record060_result⟩))
 (.branch 62
 (.leaf ⟨(25, 27130909949952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record061_result⟩)
 (.branch 63
 (.leaf ⟨(25, 27217505554464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record062_result⟩)
 (.leaf ⟨(25, 27224254726272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record063_result⟩)))))
 (.branch 69
 (.branch 66
 (.branch 65
 (.leaf ⟨(25, 27251301187584), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record064_result⟩)
 (.leaf ⟨(25, 27257542311936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record065_result⟩))
 (.branch 67
 (.leaf ⟨(25, 27258582499328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record066_result⟩)
 (.branch 68
 (.leaf ⟨(25, 27267812065280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record067_result⟩)
 (.leaf ⟨(25, 27268080467968), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record068_result⟩))))
 (.branch 71
 (.branch 70
 (.leaf ⟨(25, 27354179076096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record069_result⟩)
 (.leaf ⟨(25, 27387414740992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record070_result⟩))
 (.branch 72
 (.leaf ⟨(25, 27602290999296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record071_result⟩)
 (.branch 73
 (.leaf ⟨(25, 27748443619328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record072_result⟩)
 (.leaf ⟨(25, 27756368756736), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00017.record073_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13506 + i))) 0 74 :=
  interval_of_check _ 0 74 (by decide +kernel)

public theorem complete : Block 13506 13580 :=
  block_of_table results 13506 74 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0307
