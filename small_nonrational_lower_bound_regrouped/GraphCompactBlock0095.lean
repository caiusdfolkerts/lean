module
prelude
import GraphInputsRow23Part00017Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0095
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 38
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 25226767237120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record000_result⟩)
 (.leaf ⟨(23, 25328634364160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 25328906993664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record002_result⟩)
 (.leaf ⟨(23, 25329171234816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 25329179557888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record004_result⟩)
 (.leaf ⟨(23, 25329303355392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 25333464104960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 25333472428032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record007_result⟩)
 (.leaf ⟨(23, 25336683757568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(23, 25341517136128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record009_result⟩)
 (.leaf ⟨(23, 25341785604096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record010_result⟩))
 (.branch 12
 (.leaf ⟨(23, 25341793927168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record011_result⟩)
 (.branch 13
 (.leaf ⟨(23, 25342188208128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record012_result⟩)
 (.leaf ⟨(23, 25345407860736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(23, 25363463864320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record014_result⟩)
 (.leaf ⟨(23, 25363472187392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record015_result⟩))
 (.branch 17
 (.leaf ⟨(23, 25363967181056), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record016_result⟩)
 (.branch 18
 (.leaf ⟨(23, 25364735262720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record017_result⟩)
 (.leaf ⟨(23, 25367219863808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(23, 25367360372736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record019_result⟩)
 (.leaf ⟨(23, 25367756734464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record020_result⟩))
 (.branch 22
 (.leaf ⟨(23, 25367765057536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record021_result⟩)
 (.leaf ⟨(23, 25368896012288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(23, 25375809765632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record023_result⟩)
 (.leaf ⟨(23, 25375946113024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record024_result⟩))
 (.branch 26
 (.leaf ⟨(23, 25375954436096), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 25376078233600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record026_result⟩)
 (.leaf ⟨(23, 25376086556672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(23, 25376350797824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record028_result⟩)
 (.leaf ⟨(23, 25376546897920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record029_result⟩))
 (.branch 31
 (.leaf ⟨(23, 25376849953024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record030_result⟩)
 (.branch 32
 (.leaf ⟨(23, 25377217511424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record031_result⟩)
 (.leaf ⟨(23, 25377620115456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(23, 25383291339008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record033_result⟩)
 (.leaf ⟨(23, 25414126797312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record034_result⟩))
 (.branch 36
 (.leaf ⟨(23, 25433320521728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record035_result⟩)
 (.branch 37
 (.leaf ⟨(23, 25444529225984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record036_result⟩)
 (.leaf ⟨(23, 25444663492608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record037_result⟩)))))))
 (.branch 57
 (.branch 47
 (.branch 42
 (.branch 40
 (.branch 39
 (.leaf ⟨(23, 25444671815680), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record038_result⟩)
 (.leaf ⟨(23, 25445066096640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record039_result⟩))
 (.branch 41
 (.leaf ⟨(23, 25445132156928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record040_result⟩)
 (.leaf ⟨(23, 25446205374464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(23, 25447715848448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record042_result⟩)
 (.leaf ⟨(23, 25513248751616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record043_result⟩))
 (.branch 45
 (.leaf ⟨(23, 25570123481344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record044_result⟩)
 (.branch 46
 (.leaf ⟨(23, 25570491039744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record045_result⟩)
 (.leaf ⟨(23, 25570893643776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record046_result⟩)))))
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf ⟨(23, 25574418432256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record047_result⟩)
 (.leaf ⟨(23, 25575054393344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record048_result⟩))
 (.branch 50
 (.leaf ⟨(23, 25576564867328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record049_result⟩)
 (.branch 51
 (.leaf ⟨(23, 25582106574848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record050_result⟩)
 (.leaf ⟨(23, 25582236614656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record051_result⟩))))
 (.branch 54
 (.branch 53
 (.leaf ⟨(23, 25582302674944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record052_result⟩)
 (.leaf ⟨(23, 25583375892480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record053_result⟩))
 (.branch 55
 (.leaf ⟨(23, 25589449769024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record054_result⟩)
 (.branch 56
 (.leaf ⟨(23, 25611561075200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record055_result⟩)
 (.leaf ⟨(23, 25642097770496), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record056_result⟩))))))
 (.branch 67
 (.branch 62
 (.branch 59
 (.branch 58
 (.leaf ⟨(23, 25659277574144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record057_result⟩)
 (.leaf ⟨(23, 25659409694720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record058_result⟩))
 (.branch 60
 (.leaf ⟨(23, 25702227263744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 25704441905152), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record060_result⟩)
 (.leaf ⟨(23, 25704978710528), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record061_result⟩))))
 (.branch 64
 (.branch 63
 (.leaf ⟨(23, 25706522279936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record062_result⟩)
 (.leaf ⟨(23, 25706662723584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record063_result⟩))
 (.branch 65
 (.leaf ⟨(23, 25707059085312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record064_result⟩)
 (.branch 66
 (.leaf ⟨(23, 25719407132672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record065_result⟩)
 (.leaf ⟨(23, 25722593755136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record066_result⟩)))))
 (.branch 72
 (.branch 69
 (.branch 68
 (.leaf ⟨(23, 25739757944832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record067_result⟩)
 (.leaf ⟨(23, 25739898388480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record068_result⟩))
 (.branch 70
 (.leaf ⟨(23, 25740294750208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record069_result⟩)
 (.branch 71
 (.leaf ⟨(23, 25740410355712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record070_result⟩)
 (.leaf ⟨(23, 25752642797568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record071_result⟩))))
 (.branch 74
 (.branch 73
 (.leaf ⟨(23, 25756919021568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record072_result⟩)
 (.leaf ⟨(23, 25769821618432), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record073_result⟩))
 (.branch 75
 (.leaf ⟨(23, 25771970199552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record074_result⟩)
 (.branch 76
 (.leaf ⟨(23, 25772110643200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record075_result⟩)
 (.leaf ⟨(23, 25772507004928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00017.record076_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7091 + i))) 0 77 :=
  interval_of_check _ 0 77 (by decide +kernel)

public theorem complete : Block 7091 7168 :=
  block_of_table results 7091 77 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0095
