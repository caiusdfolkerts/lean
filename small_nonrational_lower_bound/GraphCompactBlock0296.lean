module
prelude
import GraphInputsRow25Part00006Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0296
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 7560562214912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record000_result⟩)
 (.leaf ⟨(25, 7562766320384), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 7563047337984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record002_result⟩)
 (.leaf ⟨(25, 7564846695168), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(25, 7564855148544), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record004_result⟩)
 (.leaf ⟨(25, 7565119389696), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record005_result⟩))
 (.branch 7
 (.leaf ⟨(25, 7565127712768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 7572607205376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record007_result⟩)
 (.leaf ⟨(25, 7578002161664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(25, 7585718616064), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record009_result⟩)
 (.leaf ⟨(25, 7593653469440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record010_result⟩))
 (.branch 12
 (.leaf ⟨(25, 7593657696256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record011_result⟩)
 (.branch 13
 (.leaf ⟨(25, 7593665759232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record012_result⟩)
 (.leaf ⟨(25, 7593905096960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(25, 7597818183936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record014_result⟩)
 (.leaf ⟨(25, 7598065715456), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record015_result⟩))
 (.branch 17
 (.leaf ⟨(25, 7598074103808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record016_result⟩)
 (.branch 18
 (.leaf ⟨(25, 7598082360064), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record017_result⟩)
 (.leaf ⟨(25, 7598090813440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(25, 7598355054592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record019_result⟩)
 (.leaf ⟨(25, 7598363377664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record020_result⟩))
 (.branch 22
 (.leaf ⟨(25, 7598602453512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record021_result⟩)
 (.branch 23
 (.leaf ⟨(25, 7598602780672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record022_result⟩)
 (.leaf ⟨(25, 7607200776192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(25, 7611241988096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record024_result⟩)
 (.leaf ⟨(25, 7611353432064), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record025_result⟩))
 (.branch 27
 (.leaf ⟨(25, 7614977179904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record026_result⟩)
 (.branch 28
 (.leaf ⟨(25, 7615782322688), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record027_result⟩)
 (.leaf ⟨(25, 7620079386624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(25, 7623566950916), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record029_result⟩)
 (.leaf ⟨(25, 7623567082496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record030_result⟩))
 (.branch 32
 (.leaf ⟨(25, 7623843774464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record031_result⟩)
 (.branch 33
 (.leaf ⟨(25, 7624103952384), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record032_result⟩)
 (.leaf ⟨(25, 7699980910848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(25, 7702127345920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record034_result⟩)
 (.leaf ⟨(25, 7735412556032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record035_result⟩))
 (.branch 37
 (.leaf ⟨(25, 7749876350976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record036_result⟩)
 (.branch 38
 (.leaf ⟨(25, 7753087615232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record037_result⟩)
 (.leaf ⟨(25, 7784168980480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record038_result⟩)))))))
 (.branch 59
 (.branch 49
 (.branch 44
 (.branch 41
 (.branch 40
 (.leaf ⟨(25, 7785299869952), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record039_result⟩)
 (.leaf ⟨(25, 7821953335296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record040_result⟩))
 (.branch 42
 (.leaf ⟨(25, 7890538594304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record041_result⟩)
 (.branch 43
 (.leaf ⟨(25, 8019387613184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record042_result⟩)
 (.leaf ⟨(25, 8027964965504), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record043_result⟩))))
 (.branch 46
 (.branch 45
 (.leaf ⟨(25, 8041454141696), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record044_result⟩)
 (.leaf ⟨(25, 8045883032320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record045_result⟩))
 (.branch 47
 (.leaf ⟨(25, 8046164049920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record046_result⟩)
 (.branch 48
 (.leaf ⟨(25, 8156822372352), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record047_result⟩)
 (.leaf ⟨(25, 8165540233216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record048_result⟩)))))
 (.branch 54
 (.branch 51
 (.branch 50
 (.leaf ⟨(25, 8173465370624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record049_result⟩)
 (.leaf ⟨(25, 8173993852928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record050_result⟩))
 (.branch 52
 (.leaf ⟨(25, 8184337072128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record051_result⟩)
 (.branch 53
 (.leaf ⟨(25, 8184873877504), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record052_result⟩)
 (.leaf ⟨(25, 8189034627072), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record053_result⟩))))
 (.branch 56
 (.branch 55
 (.leaf ⟨(25, 8197083561984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record054_result⟩)
 (.leaf ⟨(25, 8197356126208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record055_result⟩))
 (.branch 57
 (.leaf ⟨(25, 8197752487936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record056_result⟩)
 (.branch 58
 (.leaf ⟨(25, 8247570891008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record057_result⟩)
 (.leaf ⟨(25, 8247570956288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record058_result⟩))))))
 (.branch 69
 (.branch 64
 (.branch 61
 (.branch 60
 (.leaf ⟨(25, 8247970894080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record059_result⟩)
 (.leaf ⟨(25, 8247973560320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record060_result⟩))
 (.branch 62
 (.leaf ⟨(25, 8250926305536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record061_result⟩)
 (.branch 63
 (.leaf ⟨(25, 8250926370816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record062_result⟩)
 (.leaf ⟨(25, 8251190546688), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record063_result⟩))))
 (.branch 66
 (.branch 65
 (.leaf ⟨(25, 8251190611968), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record064_result⟩)
 (.leaf ⟨(25, 8251198410768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record065_result⟩))
 (.branch 67
 (.leaf ⟨(25, 8251215185936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record066_result⟩)
 (.branch 68
 (.leaf ⟨(25, 8252288925697), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record067_result⟩)
 (.leaf ⟨(25, 8263697434640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record068_result⟩)))))
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf ⟨(25, 8264073383936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record069_result⟩)
 (.leaf ⟨(25, 8264093796368), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record070_result⟩))
 (.branch 72
 (.leaf ⟨(25, 8265167536129), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record071_result⟩)
 (.branch 73
 (.leaf ⟨(25, 8265171763200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record072_result⟩)
 (.leaf ⟨(25, 8315350552832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record073_result⟩))))
 (.branch 76
 (.branch 75
 (.leaf ⟨(25, 8324192012304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record074_result⟩)
 (.leaf ⟨(25, 8324209180673), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record075_result⟩))
 (.branch 77
 (.leaf ⟨(25, 8324209246208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record076_result⟩)
 (.branch 78
 (.leaf ⟨(25, 8325265752065), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record077_result⟩)
 (.leaf ⟨(25, 8332513511440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00006.record078_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12582 + i))) 0 79 :=
  interval_of_check _ 0 79 (by decide +kernel)

public theorem complete : Block 12582 12661 :=
  block_of_table results 12582 79 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0296
