module
prelude
import GraphInputsSix0Part00021Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0986
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 7634577064192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 7635113934848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record001_result⟩)
 (.leaf ⟨(32, 7635122257920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 7638737813760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 7639010443264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record004_result⟩)
 (.leaf ⟨(32, 7639274684416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 7639283007488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 7640818188544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record007_result⟩)
 (.leaf ⟨(32, 7641553240064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 7647596183552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 7647604506624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record010_result⟩)
 (.leaf ⟨(32, 7653700960512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 7657998057472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 7658270621696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record013_result⟩)
 (.leaf ⟨(32, 7658733043712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 7700383613056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 7702530048128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record016_result⟩)
 (.leaf ⟨(32, 7715408658560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 7735798743168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 7736725143808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record019_result⟩)
 (.leaf ⟨(32, 7736855314560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 7736993546496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record021_result⟩)
 (.leaf ⟨(32, 7736993611776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 7737127747840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record023_result⟩)
 (.leaf ⟨(32, 7741018013952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 7741286416640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 7741286481920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record026_result⟩)
 (.leaf ⟨(32, 7741288497408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 7744509710592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 7749603754240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record029_result⟩)
 (.leaf ⟨(32, 7749607915776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 7749607981056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 7749609996544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record032_result⟩)
 (.leaf ⟨(32, 7750012649536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 7753233862720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 7770158473344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record035_result⟩)
 (.leaf ⟨(32, 7771017773312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 7771215044736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 7771286176000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record038_result⟩)
 (.leaf ⟨(32, 7771286241280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 7772561215744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 7775178522880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record041_result⟩)
 (.leaf ⟨(32, 7775310643456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 7775574884608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 7775579046144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record044_result⟩)
 (.leaf ⟨(32, 7775579111424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 7775581126912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record046_result⟩)
 (.leaf ⟨(32, 7776721965312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 7783043326080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record048_result⟩)
 (.leaf ⟨(32, 7783768424704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 7783768489984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 7783896383744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record051_result⟩)
 (.leaf ⟨(32, 7783900545280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 7783900610560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 7783902626048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record054_result⟩)
 (.leaf ⟨(32, 7784164786432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 7784164851712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 7784372379712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record057_result⟩)
 (.leaf ⟨(32, 7785043464448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 7785446117440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 7813220860160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record060_result⟩)
 (.leaf ⟨(32, 7821953335297), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 7841146474752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 7843895902464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record063_result⟩)
 (.leaf ⟨(32, 7844298506496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 7844298571776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 7845439344896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record066_result⟩)
 (.leaf ⟨(32, 7852481642752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 7852485804288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 7852485869568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record069_result⟩)
 (.leaf ⟨(32, 7852487885056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 7852620005632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record071_result⟩)
 (.leaf ⟨(32, 7852620070912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 7852884246784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record073_result⟩)
 (.leaf ⟨(32, 7852884312064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 7852890538048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 7852957638720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record076_result⟩)
 (.leaf ⟨(32, 7853760844032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 7854031376448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 7890538594305), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record079_result⟩)
 (.leaf ⟨(32, 7921799807232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 7924886831360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 7929652642048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record082_result⟩)
 (.leaf ⟨(32, 7929793150976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 7930189512704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 7930197835776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record085_result⟩)
 (.leaf ⟨(32, 7978316992768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 7978719645760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 7982609862912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record088_result⟩)
 (.leaf ⟨(32, 7982880395328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 7989920563456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 7989920628736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record091_result⟩)
 (.leaf ⟨(32, 7990054764800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 7990054830080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 7990061056064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record094_result⟩)
 (.leaf ⟨(32, 7990128156736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 7990323232768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record096_result⟩)
 (.leaf ⟨(32, 7991195603200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 7991201894464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record098_result⟩)
 (.leaf ⟨(32, 7994185121792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00021.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (28886 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 28886 28986 :=
  block_of_table results 28886 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0986
