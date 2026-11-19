module
prelude
import GraphInputsRow23Part00024Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0102
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 29583890186240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 29584137652224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record001_result⟩)
 (.leaf ⟨(23, 29588029835392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 29588298270720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 29588314915328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record004_result⟩)
 (.leaf ⟨(23, 29690213466112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 29692359901184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 29692384542976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record007_result⟩)
 (.leaf ⟨(23, 29692756262912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 29693928018048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 29725628596224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record010_result⟩)
 (.leaf ⟨(23, 29726140010624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 29727213486720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 29731242180608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record013_result⟩)
 (.leaf ⟨(23, 29757832462592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 29757840850944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 29760432640128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record016_result⟩)
 (.leaf ⟨(23, 29765534810112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 29766674087936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 29772914888832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record019_result⟩)
 (.leaf ⟨(23, 29773988364928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 29831098597376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record021_result⟩)
 (.leaf ⟨(23, 29833985802496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 29834120069120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record023_result⟩)
 (.leaf ⟨(23, 29835025989888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 29837172424960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 29902705328128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record026_result⟩)
 (.leaf ⟨(23, 30031686696960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 30237795057920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 30237799284736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record029_result⟩)
 (.leaf ⟨(23, 30237803446272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 30237807087616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 30238197694592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record032_result⟩)
 (.leaf ⟨(23, 30238203449344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 30241158860800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 30241175375872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record035_result⟩)
 (.leaf ⟨(23, 30241418907776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 30241435422848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 30242508898944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record038_result⟩)
 (.leaf ⟨(23, 30246537592832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 30246636683264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 30253917671552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record041_result⟩)
 (.leaf ⟨(23, 30254152552464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 30305583108096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 30314164977664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record044_result⟩)
 (.leaf ⟨(23, 30314416179216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 30315363958784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record046_result⟩)
 (.leaf ⟨(23, 30378589487104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 30382615970048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record048_result⟩)
 (.leaf ⟨(23, 30490509705216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 30511603126272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 30516027851280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record051_result⟩)
 (.leaf ⟨(23, 30717623011328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 30717623271424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 30789724045568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record054_result⟩)
 (.leaf ⟨(23, 30789724110848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 30790126682240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 30790126714880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record057_result⟩)
 (.leaf ⟨(23, 30792005787648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 30792038817792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 30792274157696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record060_result⟩)
 (.leaf ⟨(23, 30793347375232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 30825274482688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 30825290997760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record063_result⟩)
 (.leaf ⟨(23, 30825542852736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 30826393829632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 30826398024192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record066_result⟩)
 (.leaf ⟨(23, 30826402217984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 30826860413184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 30826871922688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record069_result⟩)
 (.leaf ⟨(23, 30830695088128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 30830955102464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record071_result⟩)
 (.leaf ⟨(23, 30830959329280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 30830965571584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record073_result⟩)
 (.leaf ⟨(23, 30831021162752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 30831032672256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 30831155364096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record076_result⟩)
 (.leaf ⟨(23, 30840617189504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 30864197558304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 30865053777920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record079_result⟩)
 (.leaf ⟨(23, 30865313792256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 30865325301760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 30873639518208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record082_result⟩)
 (.leaf ⟨(23, 30896119939328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 30896656809984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 30896665133056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record085_result⟩)
 (.leaf ⟨(23, 30898289442816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 30898549457152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 30898553683968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record088_result⟩)
 (.leaf ⟨(23, 30898560966656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 30900817559552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 30900825882624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record091_result⟩)
 (.leaf ⟨(23, 30903096115200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 30934041640960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 30934042681344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record094_result⟩)
 (.leaf ⟨(23, 30942354751744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 30942363140096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record096_result⟩)
 (.leaf ⟨(23, 30942364180480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 30942421852416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record098_result⟩)
 (.leaf ⟨(23, 30942824505408), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00024.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7436 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 7436 7536 :=
  block_of_table results 7436 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0102
