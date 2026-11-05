module
prelude
import GraphInputsRow19Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0045
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 10610491277312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 10655423889408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record001_result⟩)
 (.leaf ⟨(19, 10657504264192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 10673811623968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 10679046119424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record004_result⟩)
 (.leaf ⟨(19, 10679303077888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 10679311400960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 10682166681600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record007_result⟩)
 (.leaf ⟨(19, 10682389504256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 10690739929088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 10714479591424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record010_result⟩)
 (.leaf ⟨(19, 10716492858368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 10741480456704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 10884592386048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record013_result⟩)
 (.leaf ⟨(19, 10884594271488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 10884798743616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 10887849115648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record016_result⟩)
 (.leaf ⟨(19, 10887915175936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 10896747268352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 10898894815232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record019_result⟩)
 (.leaf ⟨(19, 10922240442368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 10922447863808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record021_result⟩)
 (.leaf ⟨(19, 10930989572352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 10956533071872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record023_result⟩)
 (.leaf ⟨(19, 10956730147072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 10972177629184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 10989084868608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record026_result⟩)
 (.leaf ⟨(19, 11044276764672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 11044278845440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 11044282974336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record029_result⟩)
 (.leaf ⟨(19, 11052868714624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 11052868747264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 11076491100160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record032_result⟩)
 (.leaf ⟨(19, 11076495229056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 11085080969344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 11117276479488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record035_result⟩)
 (.leaf ⟨(19, 11125114716288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 11125581201412), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 11140913463552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record038_result⟩)
 (.leaf ⟨(19, 11140913528832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 11140915609600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 11145074278400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record041_result⟩)
 (.leaf ⟨(19, 11180390318080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 11282746458240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 11282747531264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record044_result⟩)
 (.leaf ⟨(19, 11284826833024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 11318063570944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record046_result⟩)
 (.leaf ⟨(19, 11414699294720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 11418860011648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record048_result⟩)
 (.leaf ⟨(19, 11418860044288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 11418861084672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 11418861604864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record051_result⟩)
 (.leaf ⟨(19, 11420940386432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 11422500307200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 11422502322180), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record054_result⟩)
 (.leaf ⟨(19, 11422503428352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 11422507622528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 11423004016644), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record057_result⟩)
 (.leaf ⟨(19, 12134765396224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 12173601505280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 12246867574784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record060_result⟩)
 (.leaf ⟨(19, 12246873817088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 12314958954496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 12315428659200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record063_result⟩)
 (.leaf ⟨(19, 12315685617664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 12315693940736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 12327703282944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record066_result⟩)
 (.leaf ⟨(19, 12342003826688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 12350862131200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 12351126372352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record069_result⟩)
 (.leaf ⟨(19, 12383501254660), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 12383506555008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record071_result⟩)
 (.leaf ⟨(19, 12508108734720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 12578220673280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record073_result⟩)
 (.leaf ⟨(19, 12582448594944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 12625467408384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 12692043600128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record076_result⟩)
 (.leaf ⟨(19, 12757541912576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 12821966422016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 12830824726528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record079_result⟩)
 (.leaf ⟨(19, 12831088967680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 12846650425344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 12854178676736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record082_result⟩)
 (.leaf ⟨(19, 12865381597184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 12866157543424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 12866380431360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record085_result⟩)
 (.leaf ⟨(19, 12877863845888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 12878862680064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 12889494716416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record088_result⟩)
 (.leaf ⟨(19, 12915235291136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 13060330815488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 13062411190272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record091_result⟩)
 (.leaf ⟨(19, 13066571939840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 13072136208384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 13095646855168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record094_result⟩)
 (.leaf ⟨(19, 13127859109888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 13130005544960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record096_result⟩)
 (.leaf ⟨(19, 13134148536576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 13137642258432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record098_result⟩)
 (.leaf ⟨(19, 13168772710400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00005.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2598 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 2598 2698 :=
  block_of_table results 2598 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0045
