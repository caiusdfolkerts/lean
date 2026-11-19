module
prelude
import GraphInputsRow19Part00027Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0067
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 28216459297024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 28232107687936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record001_result⟩)
 (.leaf ⟨(19, 28233139552256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 28233147875328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 28244868923648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record004_result⟩)
 (.leaf ⟨(19, 28244873085184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 28244873150464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 28244934983936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record007_result⟩)
 (.leaf ⟨(19, 28245335572480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 28248286757120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 28248294039808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record010_result⟩)
 (.leaf ⟨(19, 28248294105088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 28256641286400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 28256649674752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record013_result⟩)
 (.leaf ⟨(19, 28257144021248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 28257152409600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 28257730887936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record016_result⟩)
 (.leaf ⟨(19, 28257739276288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 28265235415040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 28265465520384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record019_result⟩)
 (.leaf ⟨(19, 28266325016576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 28273804509184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record021_result⟩)
 (.leaf ⟨(19, 28273811791872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 28278220194048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record023_result⟩)
 (.leaf ⟨(19, 28278224355584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 28278224420864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 28278228257024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record026_result⟩)
 (.leaf ⟨(19, 28278624618752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 28278627024896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 28280615141632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record029_result⟩)
 (.leaf ⟨(19, 28280767938816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 28280772165632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 28280883544320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record032_result⟩)
 (.leaf ⟨(19, 28280895834112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 28281424380160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 28282636601600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record035_result⟩)
 (.leaf ⟨(19, 28282636666880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 28282653311488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 28282909099016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record038_result⟩)
 (.leaf ⟨(19, 28282925875201), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 28295383091456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 28295787709448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record041_result⟩)
 (.leaf ⟨(19, 28295804485633), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 28298604249088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 28308129580288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record044_result⟩)
 (.leaf ⟨(19, 28308137968640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 28308666319364), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record046_result⟩)
 (.leaf ⟨(19, 28326828703744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 28362219782144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record048_result⟩)
 (.leaf ⟨(19, 28385728798976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 28385746094336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 28389939874048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record051_result⟩)
 (.leaf ⟨(19, 28394314539264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 28424232110336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 28458528952328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record054_result⟩)
 (.leaf ⟨(19, 28520868874496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 28555493048320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 28627352780800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record057_result⟩)
 (.leaf ⟨(19, 28627621150848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 28627623231616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 28627623264256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record060_result⟩)
 (.leaf ⟨(19, 28700454166784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 28704682082304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 28736998096896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record063_result⟩)
 (.leaf ⟨(19, 28743081418880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 28773131108608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 28773131173888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record066_result⟩)
 (.leaf ⟨(19, 28773133059328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 28773337531456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 28807898595328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record069_result⟩)
 (.leaf ⟨(19, 28808600158208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 28865822474368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record071_result⟩)
 (.leaf ⟨(19, 28867902849152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 28867902881792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record073_result⟩)
 (.leaf ⟨(19, 29140587692288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 29142734127360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 29176002822400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record076_result⟩)
 (.leaf ⟨(19, 29182564241664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 29215749579008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 29250142928896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record079_result⟩)
 (.leaf ⟨(19, 29288893054976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 29288901378048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 29312487063552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record082_result⟩)
 (.leaf ⟨(19, 29314567438336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 29318728187904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 29324292456448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record085_result⟩)
 (.leaf ⟨(19, 29344632146176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 29347801473280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 29356157108224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record088_result⟩)
 (.leaf ⟨(19, 29357246709760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 29357443784960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 29357510755072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record091_result⟩)
 (.leaf ⟨(19, 29380015357952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 29765516935424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 29765519081472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record094_result⟩)
 (.leaf ⟨(19, 29765525323776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 29834076495936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record096_result⟩)
 (.leaf ⟨(19, 29837197058112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 29838253629504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record098_result⟩)
 (.leaf ⟨(19, 30237799268608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00027.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (4739 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 4739 4839 :=
  block_of_table results 4739 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0067
