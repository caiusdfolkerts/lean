module
prelude
import GraphInputsSix0Part00001Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0966
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 744317026560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 744317091840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record001_result⟩)
 (.leaf ⟨(32, 744444985600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 744449147136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 744449212416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record004_result⟩)
 (.leaf ⟨(32, 744977629440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 744981856256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 744990179328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record007_result⟩)
 (.leaf ⟨(32, 746017816832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 748609896704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 751726297344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record010_result⟩)
 (.leaf ⟨(32, 751730458880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 751730524160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 751792357632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record013_result⟩)
 (.leaf ⟨(32, 751796519168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 751796584448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 751829549312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record016_result⟩)
 (.leaf ⟨(32, 752030916608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 776661401856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 778207068192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record019_result⟩)
 (.leaf ⟨(32, 792585142528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 792717263104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record021_result⟩)
 (.leaf ⟨(32, 792981504256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 793105235976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record023_result⟩)
 (.leaf ⟨(32, 797534388480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 799158649088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 799420809472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record026_result⟩)
 (.leaf ⟨(32, 799422890240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 799478480904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 801695138048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record029_result⟩)
 (.leaf ⟨(32, 805583388928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 805851791616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 805851856896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record032_result⟩)
 (.leaf ⟨(32, 805855823104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 806120128768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 807667859464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record035_result⟩)
 (.leaf ⟨(32, 807799980040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 808012792064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 810285039872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record038_result⟩)
 (.leaf ⟨(32, 810285105152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 814169129216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 814173290752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record041_result⟩)
 (.leaf ⟨(32, 814173356032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 814177322240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 814705869056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record044_result⟩)
 (.leaf ⟨(32, 814714191873), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 814714257408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record046_result⟩)
 (.leaf ⟨(32, 818329878784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 818334040320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record048_result⟩)
 (.leaf ⟨(32, 818334105600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 818338071808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 818602377472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record051_result⟩)
 (.leaf ⟨(32, 818734433536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 818736709632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 818866618624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record054_result⟩)
 (.leaf ⟨(32, 818874941441), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 818875006976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 819130794752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record057_result⟩)
 (.leaf ⟨(32, 819139183104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 819139248128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 843497652608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record060_result⟩)
 (.leaf ⟨(32, 862623727872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 864704102656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 865744290048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record063_result⟩)
 (.leaf ⟨(32, 868999053568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 869267456256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 870307643648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record066_result⟩)
 (.leaf ⟨(32, 872293695744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 873298231296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 873830875136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record069_result⟩)
 (.leaf ⟨(32, 874871062528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 930152022272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record071_result⟩)
 (.leaf ⟨(32, 934973309184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 934973374464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record073_result⟩)
 (.leaf ⟨(32, 936591327488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 936593408256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 936861810944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record076_result⟩)
 (.leaf ⟨(32, 938865656064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 939134058752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 939134124032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record079_result⟩)
 (.leaf ⟨(32, 947723993216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 947858194560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 952144789760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record082_result⟩)
 (.leaf ⟨(32, 952153178112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 955904951552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 956037136640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record085_result⟩)
 (.leaf ⟨(32, 956045524992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 956305539328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 956313927680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record088_result⟩)
 (.leaf ⟨(32, 956437659904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 956574007296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 956582330368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record091_result⟩)
 (.leaf ⟨(32, 965501616384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 965635817728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 967782252800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record094_result⟩)
 (.leaf ⟨(32, 971940921600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 971943002368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record096_result⟩)
 (.leaf ⟨(32, 977212080384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 977216241920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record098_result⟩)
 (.leaf ⟨(32, 977216307200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00001.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26905 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 26905 27005 :=
  block_of_table results 26905 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0966
