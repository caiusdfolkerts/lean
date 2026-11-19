module
prelude
import GraphInputsSix0Part00045Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1010
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 18246653755648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 18248657600768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record001_result⟩)
 (.leaf ⟨(32, 18248926003456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 18248926068736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 18252281446656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record004_result⟩)
 (.leaf ⟨(32, 18252281511936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 18252814254336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 18252814319616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record007_result⟩)
 (.leaf ⟨(32, 18253346832640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 18253355220992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 18253722255368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record010_result⟩)
 (.leaf ⟨(32, 18253888031104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 18253897875712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 18253904675712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record013_result⟩)
 (.leaf ⟨(32, 18253906804992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 18253922517000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 18254166278400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record016_result⟩)
 (.leaf ⟨(32, 18254171046144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 18254177337408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 18255030845696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record019_result⟩)
 (.leaf ⟨(32, 18255299248384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 18255299313664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record021_result⟩)
 (.leaf ⟨(32, 18256173793536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 18256442196224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record023_result⟩)
 (.leaf ⟨(32, 18256442261504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 18256576397568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 18256975003904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record026_result⟩)
 (.leaf ⟨(32, 18256975069184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 18256979035392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 18257507582208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record029_result⟩)
 (.leaf ⟨(32, 18258589679872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 18263889182848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 18263891263616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record032_result⟩)
 (.leaf ⟨(32, 18265696896256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 18265829081344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 18265837469696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record035_result⟩)
 (.leaf ⟨(32, 18266097484032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 18266105872384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 18266229604608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record038_result⟩)
 (.leaf ⟨(32, 18266365952000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 18266374275072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 18270844387584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record041_result⟩)
 (.leaf ⟨(32, 18271608774720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 18271933989120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 18271934054400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record044_result⟩)
 (.leaf ⟨(32, 18272070205696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 18272078528513), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record046_result⟩)
 (.leaf ⟨(32, 18272479117312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 18287008186624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record048_result⟩)
 (.leaf ⟨(32, 18287107277056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 18288264945984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 18288533348672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record051_result⟩)
 (.leaf ⟨(32, 18289390600448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 18289589920064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 18289654841600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record054_result⟩)
 (.leaf ⟨(32, 18289659052096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 18289726160928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 18297845268608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record057_result⟩)
 (.leaf ⟨(32, 18297976340736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 18297980551232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 18298047660064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record060_result⟩)
 (.leaf ⟨(32, 18298244743424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 18299952857344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 18317643383040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record063_result⟩)
 (.leaf ⟨(32, 18319723757824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 18324891173120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 18325159575808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record066_result⟩)
 (.leaf ⟨(32, 18325159641088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 18325161656576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 18327239950592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record069_result⟩)
 (.leaf ⟨(32, 18327307059456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 18333481140224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record071_result⟩)
 (.leaf ⟨(32, 18333483155712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 18333885808704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record073_result⟩)
 (.leaf ⟨(32, 18334278123776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 18334823251968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 18335268897024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record076_result⟩)
 (.leaf ⟨(32, 18335301927168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 18335367987456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 18336033284160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record079_result⟩)
 (.leaf ⟨(32, 18336358498560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 18336358563840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 18336494715136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record082_result⟩)
 (.leaf ⟨(32, 18336503037953), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 18336903626752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 18337031585792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record085_result⟩)
 (.leaf ⟨(32, 18337039908864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 18367514247168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 18382546370816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record088_result⟩)
 (.leaf ⟨(32, 18384750346248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 18385171677440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 18389712044288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record091_result⟩)
 (.leaf ⟨(32, 18389720432640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 18393608552704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 18393872793856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record094_result⟩)
 (.leaf ⟨(32, 18393881182208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 18394004914432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record096_result⟩)
 (.leaf ⟨(32, 18397769302272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 18398306172928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record098_result⟩)
 (.leaf ⟨(32, 18399709331464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00045.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (31250 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 31250 31350 :=
  block_of_table results 31250 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1010
