module
prelude
import GraphInputsSix0Part00019Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0984
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 7224698175504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 7225754165504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record001_result⟩)
 (.leaf ⟨(32, 7225754198144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 7233283915792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 7233287528576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record004_result⟩)
 (.leaf ⟨(32, 7263599264000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 7263607652352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 7276482035968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record007_result⟩)
 (.leaf ⟨(32, 7276492488705), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 7286572024064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 7286706225408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record010_result⟩)
 (.leaf ⟨(32, 7286976249872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 7288853700864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 7289122684944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record013_result⟩)
 (.leaf ⟨(32, 7291524878592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 7293417054464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 7293417635856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record016_result⟩)
 (.leaf ⟨(32, 7294142185728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 7294274306304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 7294340366592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record019_result⟩)
 (.leaf ⟨(32, 7294473625856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 7294542708992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record021_result⟩)
 (.leaf ⟨(32, 7294542774272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 7294544789760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record023_result⟩)
 (.leaf ⟨(32, 7295685628160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 7297766002944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 7302001295376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record026_result⟩)
 (.leaf ⟨(32, 7302003376144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 7302004416528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 7302006988928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record029_result⟩)
 (.leaf ⟨(32, 7302571720704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 7302732087552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 7302732152832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record032_result⟩)
 (.leaf ⟨(32, 7302860046592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 7302864208128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 7302864273408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record035_result⟩)
 (.leaf ⟨(32, 7302866288896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 7302930268416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 7303336042560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record038_result⟩)
 (.leaf ⟨(32, 7304409780288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 7331920281856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 7332184523008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record041_result⟩)
 (.leaf ⟨(32, 7332192911360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 7340906545408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 7340916998145), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record044_result⟩)
 (.leaf ⟨(32, 7366675333376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 7375265235200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record046_result⟩)
 (.leaf ⟨(32, 7375276744704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 7424014647312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record048_result⟩)
 (.leaf ⟨(32, 7424146767888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 7424411009040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 7426293202960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record051_result⟩)
 (.leaf ⟨(32, 7426557444112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 7430588153872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 7430850314256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record054_result⟩)
 (.leaf ⟨(32, 7430852395024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 7430853435408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 7432856146176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record057_result⟩)
 (.leaf ⟨(32, 7439442296848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 7448724275200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 7449118523520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record060_result⟩)
 (.leaf ⟨(32, 7469355041024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 7469363429376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 7469755564288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record063_result⟩)
 (.leaf ⟨(32, 7518138925568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 7524803840256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 7525072437504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record066_result⟩)
 (.leaf ⟨(32, 7525076599040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 7525076664320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 7525080500480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record069_result⟩)
 (.leaf ⟨(32, 7525345034368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 7525348935808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record071_result⟩)
 (.leaf ⟨(32, 7525600593928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 7533649594624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record073_result⟩)
 (.leaf ⟨(32, 7533649659904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 7533662109952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 7533666304512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record076_result⟩)
 (.leaf ⟨(32, 7533670498304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 7533918029952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 7533922092040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record079_result⟩)
 (.leaf ⟨(32, 7533938868225), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 7542235334912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 7542239529088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record082_result⟩)
 (.leaf ⟨(32, 7551374590464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 7559194132736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 7559196016648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record085_result⟩)
 (.leaf ⟨(32, 7559198097416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 7560285554944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 7560285618184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record088_result⟩)
 (.leaf ⟨(32, 7560302199552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 7560306426112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 7560310587648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record091_result⟩)
 (.leaf ⟨(32, 7560310652928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 7560372486400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 7560376647936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record094_result⟩)
 (.leaf ⟨(32, 7560376713216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 7560430094592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record096_result⟩)
 (.leaf ⟨(32, 7560628275456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 7560773009664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record098_result⟩)
 (.leaf ⟨(32, 7560773074944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00019.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (28686 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 28686 28786 :=
  block_of_table results 28686 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0984
