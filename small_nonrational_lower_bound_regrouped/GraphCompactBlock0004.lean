module
prelude
import GraphInputsRow16Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0004
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 8740838309888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record000_result⟩)
 (.leaf ⟨(16, 8744767326208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 8745163687936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record002_result⟩)
 (.leaf ⟨(16, 8745696395520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(16, 8747913117696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record004_result⟩)
 (.leaf ⟨(16, 8748185681920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record005_result⟩))
 (.branch 7
 (.leaf ⟨(16, 8748714164224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record006_result⟩)
 (.branch 8
 (.leaf ⟨(16, 8750794539008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record007_result⟩)
 (.leaf ⟨(16, 8757446837248), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(16, 8766049288448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record009_result⟩)
 (.leaf ⟨(16, 8766321917952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record010_result⟩))
 (.branch 12
 (.leaf ⟨(16, 8766586159104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record011_result⟩)
 (.branch 13
 (.leaf ⟨(16, 8766594482176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record012_result⟩)
 (.leaf ⟨(16, 8766833885184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(16, 8775180222464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record014_result⟩)
 (.leaf ⟨(16, 8778932060416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record015_result⟩))
 (.branch 17
 (.leaf ⟨(16, 8779316133888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record016_result⟩)
 (.branch 18
 (.leaf ⟨(16, 8779473092608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record017_result⟩)
 (.leaf ⟨(16, 8783208284416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(16, 8783229157376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record019_result⟩)
 (.leaf ⟨(16, 8783501721600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record020_result⟩))
 (.branch 22
 (.leaf ⟨(16, 8784013427200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record021_result⟩)
 (.branch 23
 (.leaf ⟨(16, 8784013688832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record022_result⟩)
 (.leaf ⟨(16, 8784030203904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(16, 8791798251520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record024_result⟩)
 (.leaf ⟨(16, 8792335056896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record025_result⟩))
 (.branch 27
 (.leaf ⟨(16, 9065407250432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record026_result⟩)
 (.branch 28
 (.leaf ⟨(16, 9504332808192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record027_result⟩)
 (.leaf ⟨(16, 9545369845760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(16, 9600069804288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record029_result⟩)
 (.leaf ⟨(16, 9602217345024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record030_result⟩))
 (.branch 32
 (.leaf ⟨(16, 9614699593728), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record031_result⟩)
 (.branch 33
 (.leaf ⟨(16, 9616779968512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record032_result⟩)
 (.leaf ⟨(16, 9805825581312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(16, 9820851732480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record034_result⟩)
 (.leaf ⟨(16, 9822932107264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record035_result⟩))
 (.branch 37
 (.leaf ⟨(16, 9838037836032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record036_result⟩)
 (.branch 38
 (.leaf ⟨(16, 10129488494592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record037_result⟩)
 (.leaf ⟨(16, 10167136550912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record038_result⟩)))))))
 (.branch 58
 (.branch 48
 (.branch 43
 (.branch 41
 (.branch 40
 (.leaf ⟨(16, 10485504246016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record039_result⟩)
 (.leaf ⟨(16, 10610491277312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record040_result⟩))
 (.branch 42
 (.leaf ⟨(16, 10655423889408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record041_result⟩)
 (.leaf ⟨(16, 10657504264192), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record042_result⟩)))
 (.branch 45
 (.branch 44
 (.leaf ⟨(16, 10673811623968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record043_result⟩)
 (.leaf ⟨(16, 10678576414720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record044_result⟩))
 (.branch 46
 (.leaf ⟨(16, 10679046119424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record045_result⟩)
 (.branch 47
 (.leaf ⟨(16, 10679303077888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record046_result⟩)
 (.leaf ⟨(16, 10679311400960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record047_result⟩)))))
 (.branch 53
 (.branch 50
 (.branch 49
 (.leaf ⟨(16, 10682166681600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record048_result⟩)
 (.leaf ⟨(16, 10682389504256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record049_result⟩))
 (.branch 51
 (.leaf ⟨(16, 10690739929088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record050_result⟩)
 (.branch 52
 (.leaf ⟨(16, 10714479591424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record051_result⟩)
 (.leaf ⟨(16, 10716492858368), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record052_result⟩))))
 (.branch 55
 (.branch 54
 (.leaf ⟨(16, 10863461277952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record053_result⟩)
 (.leaf ⟨(16, 10887849115648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record054_result⟩))
 (.branch 56
 (.leaf ⟨(16, 10887915175936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record055_result⟩)
 (.branch 57
 (.leaf ⟨(16, 10887948206080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record056_result⟩)
 (.leaf ⟨(16, 10888145281280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record057_result⟩))))))
 (.branch 68
 (.branch 63
 (.branch 60
 (.branch 59
 (.leaf ⟨(16, 10896747268352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record058_result⟩)
 (.leaf ⟨(16, 10898894815232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record059_result⟩))
 (.branch 61
 (.leaf ⟨(16, 10922240442368), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record060_result⟩)
 (.branch 62
 (.leaf ⟨(16, 10922447863808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record061_result⟩)
 (.leaf ⟨(16, 10928959523072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record062_result⟩))))
 (.branch 65
 (.branch 64
 (.leaf ⟨(16, 10956533071872), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record063_result⟩)
 (.leaf ⟨(16, 10956730147072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record064_result⟩))
 (.branch 66
 (.leaf ⟨(16, 10972177629184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record065_result⟩)
 (.branch 67
 (.leaf ⟨(16, 10989084868608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record066_result⟩)
 (.leaf ⟨(16, 11044276764672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record067_result⟩)))))
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf ⟨(16, 11180390318080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record068_result⟩)
 (.leaf ⟨(16, 11414699294720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record069_result⟩))
 (.branch 71
 (.leaf ⟨(16, 12246867574784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record070_result⟩)
 (.branch 72
 (.leaf ⟨(16, 12314958954496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record071_result⟩)
 (.leaf ⟨(16, 12315428659200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record072_result⟩))))
 (.branch 75
 (.branch 74
 (.leaf ⟨(16, 12315685617664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record073_result⟩)
 (.leaf ⟨(16, 12315693940736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record074_result⟩))
 (.branch 76
 (.leaf ⟨(16, 12342003826688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record075_result⟩)
 (.branch 77
 (.leaf ⟨(16, 12350862131200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record076_result⟩)
 (.leaf ⟨(16, 12351126372352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00004.record077_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (330 + i))) 0 78 :=
  interval_of_check _ 0 78 (by decide +kernel)

public theorem complete : Block 330 408 :=
  block_of_table results 330 78 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0004
