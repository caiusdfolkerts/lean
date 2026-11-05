module
prelude
import GraphInputsSix0Part00024Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0989
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 8525787105296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 8525803749904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record001_result⟩)
 (.leaf ⟨(32, 8525807882496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 8530100752640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 8530364993792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record004_result⟩)
 (.leaf ⟨(32, 8530371285056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 8534503260416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 8534771663104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record007_result⟩)
 (.leaf ⟨(32, 8534783692800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 8538810222608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 8539873509632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record010_result⟩)
 (.leaf ⟨(32, 8539877736448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 8539883962369), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 8568598233344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record013_result⟩)
 (.leaf ⟨(32, 8568870862848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 8569135104000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 8569143427072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record016_result⟩)
 (.leaf ⟨(32, 8615773634816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 8628861993216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 8637456121856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record019_result⟩)
 (.leaf ⟨(32, 8637992927232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 8650202611712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record021_result⟩)
 (.leaf ⟨(32, 8654635925504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 8655164407808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record023_result⟩)
 (.leaf ⟨(32, 8727373942016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 8727374005256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 8727390781696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record026_result⟩)
 (.leaf ⟨(32, 8727398844672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 8727398909952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 8727659086080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record029_result⟩)
 (.leaf ⟨(32, 8727667474432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 8727918938120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 8727919068168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record032_result⟩)
 (.leaf ⟨(32, 8727927488768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 8727935844353), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 8727939778560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record035_result⟩)
 (.leaf ⟨(32, 8728179116288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 8729659506944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 8731689550080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record038_result⟩)
 (.leaf ⟨(32, 8731962179584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 8732226420736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 8732234743808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record041_result⟩)
 (.leaf ⟨(32, 8732474146816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 8734092886016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 8734629691392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record044_result⟩)
 (.leaf ⟨(32, 8736500484352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 8736508872704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record046_result⟩)
 (.leaf ⟨(32, 8736517128960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 8740258644224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record048_result⟩)
 (.leaf ⟨(32, 8744553547272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 8744572322048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 8744830371840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record051_result⟩)
 (.leaf ⟨(32, 8744956395520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 8745113354240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 8745358721544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record054_result⟩)
 (.leaf ⟨(32, 8746839375872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 8747111940096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 8748848546048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record057_result⟩)
 (.leaf ⟨(32, 8749653688832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 8757438513152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 8757975318528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record060_result⟩)
 (.leaf ⟨(32, 8766305140736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 8775163445248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 8783484944384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record063_result⟩)
 (.leaf ⟨(32, 8784013426688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 8792334925824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 8834087223680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record066_result⟩)
 (.leaf ⟨(32, 8836035477888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 8836167598464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 8836431839616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record069_result⟩)
 (.leaf ⟨(32, 8840462549376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 8840726790528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record071_result⟩)
 (.leaf ⟨(32, 8849316692352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 8870526288256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record073_result⟩)
 (.leaf ⟨(32, 8871599505792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 8874687037824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 8874821239168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record076_result⟩)
 (.leaf ⟨(32, 8875089641856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 8875894456704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 8876129829248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record079_result⟩)
 (.leaf ⟨(32, 8910324990208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 8910455095680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 8911862169600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record082_result⟩)
 (.leaf ⟨(32, 8940184764800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 8940318966144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 8940554338688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record085_result⟩)
 (.leaf ⟨(32, 8943406498176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 8943540715840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 8943809118528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record088_result⟩)
 (.leaf ⟨(32, 8944613933376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 8944849305920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 8952399052992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record091_result⟩)
 (.leaf ⟨(32, 8979042369792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 8979174572352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 8979914719488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record094_result⟩)
 (.leaf ⟨(32, 8980447428608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 8985634717888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record096_result⟩)
 (.leaf ⟨(32, 8987628110080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 8988768927744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record098_result⟩)
 (.leaf ⟨(32, 9056555122816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00024.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (29186 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 29186 29286 :=
  block_of_table results 29186 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0989
