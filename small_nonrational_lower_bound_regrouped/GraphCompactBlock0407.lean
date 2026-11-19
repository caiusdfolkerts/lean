module
prelude
import GraphInputsRow27Part00004Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0407
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 8067632594944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 8135953612800), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record001_result⟩)
 (.leaf ⟨(27, 8139074174976), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 8139140235264), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 8148236634112), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record004_result⟩)
 (.leaf ⟨(27, 8152529504256), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 8156813984512), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 8173465501696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record007_result⟩)
 (.leaf ⟨(27, 8173859782656), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 8186764525568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 8186770767872), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record010_result⟩)
 (.leaf ⟨(27, 8195143632896), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 8246396260544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 8246492989712), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record013_result⟩)
 (.leaf ⟨(27, 8247553722640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 8324209278976), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 8569143427072), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record016_result⟩)
 (.leaf ⟨(27, 8637992927232), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 8654635925504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 8732226420736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record019_result⟩)
 (.leaf ⟨(27, 8732234743808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 8744830371840), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record021_result⟩)
 (.leaf ⟨(27, 8745113354240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 8746839375872), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record023_result⟩)
 (.leaf ⟨(27, 8747111940096), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 8757975318528), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 8766305140736), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record026_result⟩)
 (.leaf ⟨(27, 8775163445248), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 8783484944384), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 8911862169600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record029_result⟩)
 (.leaf ⟨(27, 8980447428608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 8988768927744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 9064601879808), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record032_result⟩)
 (.leaf ⟨(27, 9202573541504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 9202841976832), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 9202846138368), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record035_result⟩)
 (.leaf ⟨(27, 9270898753536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 9530142359553), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 9544564475136), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record038_result⟩)
 (.leaf ⟨(27, 9682808733696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 9820985885696), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 9898998972800), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record041_result⟩)
 (.leaf ⟨(27, 10000103735304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 10041203687424), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 10088931753984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record044_result⟩)
 (.leaf ⟨(27, 10090025321728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 10090165829633), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record046_result⟩)
 (.leaf ⟨(27, 10136217288712), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 10153378365448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record048_result⟩)
 (.leaf ⟨(27, 10164723777536), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 10226185043968), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 10226189205504), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record051_result⟩)
 (.leaf ⟨(27, 10228265418752), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 10228269580288), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 10232426168320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record054_result⟩)
 (.leaf ⟨(27, 10232430329856), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 10301621829632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 10302016077952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record057_result⟩)
 (.leaf ⟨(27, 10302022222848), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 10372692049920), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 10446522892672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record060_result⟩)
 (.leaf ⟨(27, 10448066351424), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 10484292159760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 10639451881473), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record063_result⟩)
 (.leaf ⟨(27, 10708171358208), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 10716757098496), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 10741484617728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record066_result⟩)
 (.leaf ⟨(27, 10781588456448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 10781720577024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 10781984818176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record069_result⟩)
 (.leaf ⟨(27, 10782112744064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 10857729016064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record071_result⟩)
 (.leaf ⟨(27, 10884866899968), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 10892599410688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record073_result⟩)
 (.leaf ⟨(27, 10909760095240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 10956805505024), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 11180947014912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record076_result⟩)
 (.leaf ⟨(27, 11237945606144), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 11307984191488), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 11334591741952), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record079_result⟩)
 (.leaf ⟨(27, 11334721749120), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 11375512485888), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 11375636121728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record082_result⟩)
 (.leaf ⟨(27, 11384226054145), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 11401129263104), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 11401265415168), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record085_result⟩)
 (.leaf ⟨(27, 11401393341056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 11413142716416), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 11431162445824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record088_result⟩)
 (.leaf ⟨(27, 11431261536256), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 11431358513280), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 11444097744896), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record091_result⟩)
 (.leaf ⟨(27, 11444231946240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 11444353501312), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 11444500348928), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record094_result⟩)
 (.leaf ⟨(27, 11446378381312), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 11452943433729), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record096_result⟩)
 (.leaf ⟨(27, 11471924904064), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 11471927017472), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record098_result⟩)
 (.leaf ⟨(27, 11471931048960), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00004.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (18073 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 18073 18173 :=
  block_of_table results 18073 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0407
