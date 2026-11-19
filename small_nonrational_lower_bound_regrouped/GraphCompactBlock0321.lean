module
prelude
import GraphInputsRow26Part00005Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0321
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 41
 (.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 2607457271808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record000_result⟩)
 (.leaf ⟨(26, 2607651258496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 2607851520128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 2652555477248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record003_result⟩)
 (.leaf ⟨(26, 2675976470528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(26, 2682363363584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record005_result⟩)
 (.leaf ⟨(26, 2686715986176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record006_result⟩))
 (.branch 8
 (.leaf ⟨(26, 2686843945216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record007_result⟩)
 (.branch 9
 (.leaf ⟨(26, 2686848106752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record008_result⟩)
 (.leaf ⟨(26, 2686848172032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(26, 2686914167040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record010_result⟩)
 (.leaf ⟨(26, 2686914232320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record011_result⟩))
 (.branch 13
 (.leaf ⟨(26, 2687116542080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 2687118622848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record013_result⟩)
 (.leaf ⟨(26, 2693557928064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(26, 2789191286912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record015_result⟩)
 (.leaf ⟨(26, 2796707479568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record016_result⟩))
 (.branch 18
 (.leaf ⟨(26, 2828919734288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 2835966165120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record018_result⟩)
 (.leaf ⟨(26, 2836164345984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(26, 2934280569088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record020_result⟩)
 (.leaf ⟨(26, 2956301779200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record021_result⟩))
 (.branch 23
 (.leaf ⟨(26, 2956302819584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record022_result⟩)
 (.branch 24
 (.leaf ⟨(26, 2956570181888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record023_result⟩)
 (.leaf ⟨(26, 2981854446848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(26, 2982193201152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record025_result⟩)
 (.leaf ⟨(26, 2982387155200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record026_result⟩))
 (.branch 28
 (.leaf ⟨(26, 2982395543552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 3036954066960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record028_result⟩)
 (.leaf ⟨(26, 3093740699904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(26, 3098093387776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record030_result⟩)
 (.leaf ⟨(26, 3102452318208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record031_result⟩))
 (.branch 33
 (.leaf ⟨(26, 3102656708736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record032_result⟩)
 (.branch 34
 (.leaf ⟨(26, 3115801673728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record033_result⟩)
 (.leaf ⟨(26, 3119557673216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(26, 3119561900032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record035_result⟩)
 (.branch 37
 (.leaf ⟨(26, 3119632121856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record036_result⟩)
 (.leaf ⟨(26, 3119826108544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(26, 3120094543872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record038_result⟩)
 (.branch 40
 (.leaf ⟨(26, 3120098705408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record039_result⟩)
 (.leaf ⟨(26, 3131329052672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record040_result⟩)))))))
 (.branch 62
 (.branch 51
 (.branch 46
 (.branch 43
 (.branch 42
 (.leaf ⟨(26, 3131849050240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record041_result⟩)
 (.leaf ⟨(26, 3135886163968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record042_result⟩))
 (.branch 44
 (.leaf ⟨(26, 3135892373632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record043_result⟩)
 (.branch 45
 (.leaf ⟨(26, 3140438982657), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record044_result⟩)
 (.leaf ⟨(26, 3144331298944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record045_result⟩))))
 (.branch 48
 (.branch 47
 (.leaf ⟨(26, 3153330208768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record046_result⟩)
 (.leaf ⟨(26, 3153334370304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record047_result⟩))
 (.branch 49
 (.leaf ⟨(26, 3157077950464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record048_result⟩)
 (.branch 50
 (.leaf ⟨(26, 3157081981952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record049_result⟩)
 (.leaf ⟨(26, 3157337997440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record050_result⟩)))))
 (.branch 56
 (.branch 53
 (.branch 52
 (.leaf ⟨(26, 3157606269568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record051_result⟩)
 (.leaf ⟨(26, 3162259898624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record052_result⟩))
 (.branch 54
 (.leaf ⟨(26, 3162325958912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record053_result⟩)
 (.branch 55
 (.leaf ⟨(26, 3164998762624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record054_result⟩)
 (.leaf ⟨(26, 3165678772480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(26, 3166810702080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record056_result⟩)
 (.branch 58
 (.leaf ⟨(26, 3166810767360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record057_result⟩)
 (.leaf ⟨(26, 3166876762368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(26, 3166876827648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record059_result⟩)
 (.branch 61
 (.leaf ⟨(26, 3167079137408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record060_result⟩)
 (.leaf ⟨(26, 3174392471552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record061_result⟩))))))
 (.branch 72
 (.branch 67
 (.branch 64
 (.branch 63
 (.leaf ⟨(26, 3188151320576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record062_result⟩)
 (.leaf ⟨(26, 3191271882752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record063_result⟩))
 (.branch 65
 (.leaf ⟨(26, 3191333781504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record064_result⟩)
 (.branch 66
 (.leaf ⟨(26, 3191337943040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record065_result⟩)
 (.leaf ⟨(26, 3195611169024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record066_result⟩))))
 (.branch 69
 (.branch 68
 (.leaf ⟨(26, 3199889213696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record067_result⟩)
 (.leaf ⟨(26, 3200310608128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record068_result⟩))
 (.branch 70
 (.leaf ⟨(26, 3200310673408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record069_result⟩)
 (.branch 71
 (.leaf ⟨(26, 3200316883072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record070_result⟩)
 (.leaf ⟨(26, 3200434309248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record071_result⟩)))))
 (.branch 77
 (.branch 74
 (.branch 73
 (.leaf ⟨(26, 3209024241665), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record072_result⟩)
 (.leaf ⟨(26, 3213044484352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record073_result⟩))
 (.branch 75
 (.leaf ⟨(26, 3213048678528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record074_result⟩)
 (.branch 76
 (.leaf ⟨(26, 3213195493504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record075_result⟩)
 (.leaf ⟨(26, 3213195526144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record076_result⟩))))
 (.branch 80
 (.branch 78
 (.leaf ⟨(26, 3225654821120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record077_result⟩)
 (.branch 79
 (.leaf ⟨(26, 3225659047936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record078_result⟩)
 (.leaf ⟨(26, 3225663209472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record079_result⟩)))
 (.branch 81
 (.leaf ⟨(26, 3225667240960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record080_result⟩)
 (.branch 82
 (.leaf ⟨(26, 3225923093248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record081_result⟩)
 (.leaf ⟨(26, 3226057457792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00005.record082_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14301 + i))) 0 83 :=
  interval_of_check _ 0 83 (by decide +kernel)

public theorem complete : Block 14301 14384 :=
  block_of_table results 14301 83 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0321
