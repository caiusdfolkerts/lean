module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import IntegerTables
public import RootedSixExtra05
public import RawKindedFacePlacement
public import RootedSixExtra05OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4
open ConcreteGrowth
abbrev blockCount : Nat := 100
noncomputable def template : Cell := ⟨10, 63, [3, 5, 6, 10, 12, 20, 24, 33, 36, 48], [7, 14, 28, 37, 52, 59]⟩
cert_root_6 05
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨2, 4, 5517840, 5517840, 361626105360, 361626105360⟩, 104793658))
 (.branch 2
 (.leaf (⟨2, 4, 5517840, 5517840, 361609328160, 361626104160⟩, 107939434))
 (.leaf (⟨2, 4, 5517840, 5517840, 361592550945, 361626104070⟩, 111085210))))
 (.branch 4
 (.leaf (⟨2, 4, 5517840, 5517840, 361340892720, 361626081120⟩, 118949650))
 (.branch 5
 (.leaf (⟨2, 4, 5517840, 5517840, 357029148225, 361625650950⟩, 122095426))
 (.leaf (⟨2, 4, 5517840, 5517840, 352465745475, 361625618550⟩, 125241202)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨2, 4, 5517840, 5517840, 288041236050, 361617784950⟩, 128386978))
 (.branch 8
 (.leaf (⟨2, 4, 5517840, 5517840, 283746268755, 361617754230⟩, 131532754))
 (.leaf (⟨2, 4, 5517840, 5517840, 215026792020, 361617201270⟩, 134678530))))
 (.branch 10
 (.leaf (⟨2, 4, 5517600, 5517600, 361626105360, 361626105360⟩, 106825298))
 (.branch 11
 (.leaf (⟨2, 4, 5517600, 5517600, 361609328160, 361626104160⟩, 109971074))
 (.leaf (⟨2, 4, 5517600, 5517600, 361592550945, 361626104070⟩, 113116850))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (⟨2, 4, 5517600, 5517600, 361340892720, 361626081120⟩, 120981290))
 (.branch 14
 (.leaf (⟨2, 4, 5517600, 5517600, 357029148225, 361625650950⟩, 124127066))
 (.leaf (⟨2, 4, 5517600, 5517600, 352465745475, 361625618550⟩, 127272842))))
 (.branch 16
 (.leaf (⟨2, 4, 5517600, 5517600, 288041236050, 361617784950⟩, 130418618))
 (.branch 17
 (.leaf (⟨2, 4, 5517600, 5517600, 283746268755, 361617754230⟩, 133564394))
 (.leaf (⟨2, 4, 5517600, 5517600, 215026792020, 361617201270⟩, 136710170)))))
 (.branch 21
 (.branch 19
 (.leaf (⟨2, 4, 5517345, 5517570, 361626105360, 361626105360⟩, 107152983))
 (.branch 20
 (.leaf (⟨2, 4, 5517345, 5517570, 361609328160, 361626104160⟩, 110298759))
 (.leaf (⟨2, 4, 5517345, 5517570, 361592550945, 361626104070⟩, 113444535))))
 (.branch 23
 (.branch 22
 (.leaf (⟨2, 4, 5517345, 5517570, 361340892720, 361626081120⟩, 121308975))
 (.leaf (⟨2, 4, 5517345, 5517570, 357029148225, 361625650950⟩, 124454751)))
 (.branch 24
 (.leaf (⟨2, 4, 5517345, 5517570, 352465745475, 361625618550⟩, 127600527))
 (.leaf (⟨2, 4, 5517345, 5517570, 288041236050, 361617784950⟩, 130746303)))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf (⟨2, 4, 5517345, 5517570, 283746268755, 361617754230⟩, 133892079))
 (.branch 27
 (.leaf (⟨2, 4, 5517345, 5517570, 215026792020, 361617201270⟩, 137037855))
 (.leaf (⟨3, 4, 5517840, 5517840, 361742426640, 434925761040⟩, 2121697095716703064720082634))))
 (.branch 29
 (.leaf (⟨3, 4, 5517840, 5517840, 141893788995, 434917935495⟩, 2556917031707168640880543794))
 (.branch 30
 (.leaf (⟨2, 4, 5513265, 5509890, 361626105360, 361626105360⟩, 104924739))
 (.leaf (⟨2, 4, 5513265, 5509890, 361609328160, 361626104160⟩, 108070515)))))
 (.branch 34
 (.branch 32
 (.leaf (⟨2, 4, 5513265, 5509890, 361592550945, 361626104070⟩, 111216291))
 (.branch 33
 (.leaf (⟨2, 4, 5513265, 5509890, 361340892720, 361626081120⟩, 119080731))
 (.leaf (⟨2, 4, 5513265, 5509890, 357029148225, 361625650950⟩, 122226507))))
 (.branch 35
 (.leaf (⟨2, 4, 5513265, 5509890, 352465745475, 361625618550⟩, 125372283))
 (.branch 36
 (.leaf (⟨2, 4, 5513265, 5509890, 288041236050, 361617784950⟩, 128518059))
 (.leaf (⟨2, 4, 5513265, 5509890, 283746268755, 361617754230⟩, 131663835))))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf (⟨2, 4, 5513265, 5509890, 215026792020, 361617201270⟩, 134809611))
 (.branch 39
 (.leaf (⟨2, 4, 5509170, 5509170, 361626105360, 361626105360⟩, 106497637))
 (.leaf (⟨2, 4, 5509170, 5509170, 361609328160, 361626104160⟩, 109643413))))
 (.branch 41
 (.leaf (⟨2, 4, 5509170, 5509170, 361592550945, 361626104070⟩, 112789189))
 (.branch 42
 (.leaf (⟨2, 4, 5509170, 5509170, 361340892720, 361626081120⟩, 120653629))
 (.leaf (⟨2, 4, 5509170, 5509170, 357029148225, 361625650950⟩, 123799405)))))
 (.branch 46
 (.branch 44
 (.leaf (⟨2, 4, 5509170, 5509170, 352465745475, 361625618550⟩, 126945181))
 (.branch 45
 (.leaf (⟨2, 4, 5509170, 5509170, 288041236050, 361617784950⟩, 130090957))
 (.leaf (⟨2, 4, 5509170, 5509170, 283746268755, 361617754230⟩, 133236733))))
 (.branch 48
 (.branch 47
 (.leaf (⟨2, 4, 5509170, 5509170, 215026792020, 361617201270⟩, 136382509))
 (.leaf (⟨3, 4, 5505825, 5513475, 361742426640, 434925761040⟩, 2109607634605527545828411091)))
 (.branch 49
 (.leaf (⟨3, 4, 5505825, 5513475, 141893788995, 434917935495⟩, 2544827570595993121988872251))
 (.leaf (⟨2, 4, 5443650, 5324850, 361626105360, 361626105360⟩, 106759785))))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf (⟨2, 4, 5443650, 5324850, 361609328160, 361626104160⟩, 109905561))
 (.branch 52
 (.leaf (⟨2, 4, 5443650, 5324850, 361592550945, 361626104070⟩, 113051337))
 (.leaf (⟨2, 4, 5443650, 5324850, 361340892720, 361626081120⟩, 120915777))))
 (.branch 54
 (.leaf (⟨2, 4, 5443650, 5324850, 357029148225, 361625650950⟩, 124061553))
 (.branch 55
 (.leaf (⟨2, 4, 5443650, 5324850, 352465745475, 361625618550⟩, 127207329))
 (.leaf (⟨2, 4, 5443650, 5324850, 288041236050, 361617784950⟩, 130353105)))))
 (.branch 59
 (.branch 57
 (.leaf (⟨2, 4, 5443650, 5324850, 283746268755, 361617754230⟩, 133498881))
 (.branch 58
 (.leaf (⟨2, 4, 5443650, 5324850, 215026792020, 361617201270⟩, 136644657))
 (.leaf (⟨2, 4, 5378115, 5309490, 361626105360, 361626105360⟩, 105383498))))
 (.branch 60
 (.leaf (⟨2, 4, 5378115, 5309490, 361609328160, 361626104160⟩, 108529274))
 (.branch 61
 (.leaf (⟨2, 4, 5378115, 5309490, 361592550945, 361626104070⟩, 111675050))
 (.leaf (⟨2, 4, 5378115, 5309490, 361340892720, 361626081120⟩, 119539490))))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf (⟨2, 4, 5378115, 5309490, 357029148225, 361625650950⟩, 122685266))
 (.branch 64
 (.leaf (⟨2, 4, 5378115, 5309490, 352465745475, 361625618550⟩, 125831042))
 (.leaf (⟨2, 4, 5378115, 5309490, 288041236050, 361617784950⟩, 128976818))))
 (.branch 66
 (.leaf (⟨2, 4, 5378115, 5309490, 283746268755, 361617754230⟩, 132122594))
 (.branch 67
 (.leaf (⟨2, 4, 5378115, 5309490, 215026792020, 361617201270⟩, 135268370))
 (.leaf (⟨3, 4, 5309490, 5378115, 361742426640, 434925761040⟩, 2103563134637759102010525402)))))
 (.branch 71
 (.branch 69
 (.leaf (⟨3, 4, 5309490, 5378115, 141893788995, 434917935495⟩, 2538783070628224678170986562))
 (.branch 70
 (.leaf (⟨2, 4, 4399440, 1393440, 361626105360, 361626105360⟩, 104859205))
 (.leaf (⟨2, 4, 4399440, 1393440, 361609328160, 361626104160⟩, 108004981))))
 (.branch 73
 (.branch 72
 (.leaf (⟨2, 4, 4399440, 1393440, 361592550945, 361626104070⟩, 111150757))
 (.leaf (⟨2, 4, 4399440, 1393440, 361340892720, 361626081120⟩, 119015197)))
 (.branch 74
 (.leaf (⟨2, 4, 4399440, 1393440, 357029148225, 361625650950⟩, 122160973))
 (.leaf (⟨2, 4, 4399440, 1393440, 352465745475, 361625618550⟩, 125306749)))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf (⟨2, 4, 4399440, 1393440, 288041236050, 361617784950⟩, 128452525))
 (.branch 77
 (.leaf (⟨2, 4, 4399440, 1393440, 283746268755, 361617754230⟩, 131598301))
 (.leaf (⟨2, 4, 4399440, 1393440, 215026792020, 361617201270⟩, 134744077))))
 (.branch 79
 (.leaf (⟨2, 4, 4395090, 1392690, 361626105360, 361626105360⟩, 106038878))
 (.branch 80
 (.leaf (⟨2, 4, 4395090, 1392690, 361609328160, 361626104160⟩, 109184654))
 (.leaf (⟨2, 4, 4395090, 1392690, 361592550945, 361626104070⟩, 112330430)))))
 (.branch 84
 (.branch 82
 (.leaf (⟨2, 4, 4395090, 1392690, 361340892720, 361626081120⟩, 120194870))
 (.branch 83
 (.leaf (⟨2, 4, 4395090, 1392690, 357029148225, 361625650950⟩, 123340646))
 (.leaf (⟨2, 4, 4395090, 1392690, 352465745475, 361625618550⟩, 126486422))))
 (.branch 85
 (.leaf (⟨2, 4, 4395090, 1392690, 288041236050, 361617784950⟩, 129632198))
 (.branch 86
 (.leaf (⟨2, 4, 4395090, 1392690, 283746268755, 361617754230⟩, 132777974))
 (.leaf (⟨2, 4, 4395090, 1392690, 215026792020, 361617201270⟩, 135923750))))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf (⟨3, 4, 4396320, 2441520, 361742426640, 434925761040⟩, 2108398690339731788602738389))
 (.branch 89
 (.leaf (⟨3, 4, 4396320, 2441520, 141893788995, 434917935495⟩, 2543618626330197364763199549))
 (.leaf (⟨2, 4, 3280980, 1070130, 361626105360, 361626105360⟩, 105580102))))
 (.branch 91
 (.leaf (⟨2, 4, 3280980, 1070130, 361609328160, 361626104160⟩, 108725878))
 (.branch 92
 (.leaf (⟨2, 4, 3280980, 1070130, 361592550945, 361626104070⟩, 111871654))
 (.leaf (⟨2, 4, 3280980, 1070130, 361340892720, 361626081120⟩, 119736094)))))
 (.branch 96
 (.branch 94
 (.leaf (⟨2, 4, 3280980, 1070130, 357029148225, 361625650950⟩, 122881870))
 (.branch 95
 (.leaf (⟨2, 4, 3280980, 1070130, 352465745475, 361625618550⟩, 126027646))
 (.leaf (⟨2, 4, 3280980, 1070130, 288041236050, 361617784950⟩, 129173422))))
 (.branch 98
 (.branch 97
 (.leaf (⟨2, 4, 3280980, 1070130, 283746268755, 361617754230⟩, 132319198))
 (.leaf (⟨2, 4, 3280980, 1070130, 215026792020, 361617201270⟩, 135464974)))
 (.branch 99
 (.leaf (⟨3, 4, 3212610, 2183235, 361742426640, 434925761040⟩, 2107189967437679618413299414))
 (.leaf (⟨3, 4, 3212610, 2183235, 141893788995, 434917935495⟩, 2542409903428145194573760574)))))))))
cert_raw_4
cert_witness_4 2170
cert_faceTable_4 199
cert_faceWitness_4
cert_validity_4 6
cert_placement_4 6 05
cert_test_10
cert_symmetry_4 05
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4
cert_check_4 0000 0000 0 0 2 2
cert_block_8 0000 0 2
cert_check_4 0001 0000 1 0 2 2
cert_block_8 0001 1 2
cert_check_4 0002 0000 2 0 2 2
cert_block_8 0002 2 2
cert_check_4 0003 0000 3 0 2 2
cert_block_8 0003 3 2
cert_check_4 0004 0000 4 0 2 2
cert_block_8 0004 4 2
cert_check_4 0005 0000 5 0 2 2
cert_block_8 0005 5 2
cert_check_4 0006 0000 6 0 2 2
cert_block_8 0006 6 2
cert_check_4 0007 0000 7 0 2 2
cert_block_8 0007 7 2
cert_check_4 0008 0000 8 0 2 2
cert_block_8 0008 8 2
cert_check_4 0009 0000 9 0 2 2
cert_block_8 0009 9 2
cert_check_4 0010 0000 10 0 2 2
cert_block_8 0010 10 2
cert_check_4 0011 0000 11 0 2 2
cert_block_8 0011 11 2
cert_check_4 0012 0000 12 0 2 2
cert_block_8 0012 12 2
cert_check_4 0013 0000 13 0 2 2
cert_block_8 0013 13 2
cert_check_4 0014 0000 14 0 2 2
cert_block_8 0014 14 2
cert_check_4 0015 0000 15 0 2 2
cert_block_8 0015 15 2
cert_check_4 0016 0000 16 0 2 2
cert_block_8 0016 16 2
cert_check_4 0017 0000 17 0 2 2
cert_block_8 0017 17 2
cert_check_4 0018 0000 18 0 2 2
cert_block_8 0018 18 2
cert_check_4 0019 0000 19 0 2 2
cert_block_8 0019 19 2
cert_check_4 0020 0000 20 0 2 2
cert_block_8 0020 20 2
cert_check_4 0021 0000 21 0 2 2
cert_block_8 0021 21 2
cert_check_4 0022 0000 22 0 2 2
cert_block_8 0022 22 2
cert_check_4 0023 0000 23 0 2 2
cert_block_8 0023 23 2
cert_check_4 0024 0000 24 0 2 2
cert_block_8 0024 24 2
cert_check_4 0025 0000 25 0 2 2
cert_block_8 0025 25 2
cert_check_4 0026 0000 26 0 2 2
cert_block_8 0026 26 2
cert_check_4 0027 0000 27 0 6 6
cert_block_8 0027 27 6
cert_check_4 0028 0000 28 0 6 6
cert_block_8 0028 28 6
cert_check_4 0029 0000 29 0 2 2
cert_block_8 0029 29 2
cert_check_4 0030 0000 30 0 2 2
cert_block_8 0030 30 2
cert_check_4 0031 0000 31 0 2 2
cert_block_8 0031 31 2
cert_check_4 0032 0000 32 0 2 2
cert_block_8 0032 32 2
cert_check_4 0033 0000 33 0 2 2
cert_block_8 0033 33 2
cert_check_4 0034 0000 34 0 2 2
cert_block_8 0034 34 2
cert_check_4 0035 0000 35 0 2 2
cert_block_8 0035 35 2
cert_check_4 0036 0000 36 0 2 2
cert_block_8 0036 36 2
cert_check_4 0037 0000 37 0 2 2
cert_block_8 0037 37 2
cert_check_4 0038 0000 38 0 2 2
cert_block_8 0038 38 2
cert_check_4 0039 0000 39 0 2 2
cert_block_8 0039 39 2
cert_check_4 0040 0000 40 0 2 2
cert_block_8 0040 40 2
cert_check_4 0041 0000 41 0 2 2
cert_block_8 0041 41 2
cert_check_4 0042 0000 42 0 2 2
cert_block_8 0042 42 2
cert_check_4 0043 0000 43 0 2 2
cert_block_8 0043 43 2
cert_check_4 0044 0000 44 0 2 2
cert_block_8 0044 44 2
cert_check_4 0045 0000 45 0 2 2
cert_block_8 0045 45 2
cert_check_4 0046 0000 46 0 2 2
cert_block_8 0046 46 2
cert_check_4 0047 0000 47 0 6 6
cert_block_8 0047 47 6
cert_check_4 0048 0000 48 0 6 6
cert_block_8 0048 48 6
cert_check_4 0049 0000 49 0 2 2
cert_block_8 0049 49 2
cert_check_4 0050 0000 50 0 2 2
cert_block_8 0050 50 2
cert_check_4 0051 0000 51 0 2 2
cert_block_8 0051 51 2
cert_check_4 0052 0000 52 0 2 2
cert_block_8 0052 52 2
cert_check_4 0053 0000 53 0 2 2
cert_block_8 0053 53 2
cert_check_4 0054 0000 54 0 2 2
cert_block_8 0054 54 2
cert_check_4 0055 0000 55 0 2 2
cert_block_8 0055 55 2
cert_check_4 0056 0000 56 0 2 2
cert_block_8 0056 56 2
cert_check_4 0057 0000 57 0 2 2
cert_block_8 0057 57 2
cert_check_4 0058 0000 58 0 2 2
cert_block_8 0058 58 2
cert_check_4 0059 0000 59 0 2 2
cert_block_8 0059 59 2
cert_check_4 0060 0000 60 0 2 2
cert_block_8 0060 60 2
cert_check_4 0061 0000 61 0 2 2
cert_block_8 0061 61 2
cert_check_4 0062 0000 62 0 2 2
cert_block_8 0062 62 2
cert_check_4 0063 0000 63 0 2 2
cert_block_8 0063 63 2
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4
cert_check_4 0064 0000 64 0 2 2
cert_block_8 0064 64 2
cert_check_4 0065 0000 65 0 2 2
cert_block_8 0065 65 2
cert_check_4 0066 0000 66 0 2 2
cert_block_8 0066 66 2
cert_check_4 0067 0000 67 0 6 6
cert_block_8 0067 67 6
cert_check_4 0068 0000 68 0 6 6
cert_block_8 0068 68 6
cert_check_4 0069 0000 69 0 2 2
cert_block_8 0069 69 2
cert_check_4 0070 0000 70 0 2 2
cert_block_8 0070 70 2
cert_check_4 0071 0000 71 0 2 2
cert_block_8 0071 71 2
cert_check_4 0072 0000 72 0 2 2
cert_block_8 0072 72 2
cert_check_4 0073 0000 73 0 2 2
cert_block_8 0073 73 2
cert_check_4 0074 0000 74 0 2 2
cert_block_8 0074 74 2
cert_check_4 0075 0000 75 0 2 2
cert_block_8 0075 75 2
cert_check_4 0076 0000 76 0 2 2
cert_block_8 0076 76 2
cert_check_4 0077 0000 77 0 2 2
cert_block_8 0077 77 2
cert_check_4 0078 0000 78 0 2 2
cert_block_8 0078 78 2
cert_check_4 0079 0000 79 0 2 2
cert_block_8 0079 79 2
cert_check_4 0080 0000 80 0 2 2
cert_block_8 0080 80 2
cert_check_4 0081 0000 81 0 2 2
cert_block_8 0081 81 2
cert_check_4 0082 0000 82 0 2 2
cert_block_8 0082 82 2
cert_check_4 0083 0000 83 0 2 2
cert_block_8 0083 83 2
cert_check_4 0084 0000 84 0 2 2
cert_block_8 0084 84 2
cert_check_4 0085 0000 85 0 2 2
cert_block_8 0085 85 2
cert_check_4 0086 0000 86 0 2 2
cert_block_8 0086 86 2
cert_check_4 0087 0000 87 0 6 6
cert_block_8 0087 87 6
cert_check_4 0088 0000 88 0 6 6
cert_block_8 0088 88 6
cert_check_4 0089 0000 89 0 2 2
cert_block_8 0089 89 2
cert_check_4 0090 0000 90 0 2 2
cert_block_8 0090 90 2
cert_check_4 0091 0000 91 0 2 2
cert_block_8 0091 91 2
cert_check_4 0092 0000 92 0 2 2
cert_block_8 0092 92 2
cert_check_4 0093 0000 93 0 2 2
cert_block_8 0093 93 2
cert_check_4 0094 0000 94 0 2 2
cert_block_8 0094 94 2
cert_check_4 0095 0000 95 0 2 2
cert_block_8 0095 95 2
cert_check_4 0096 0000 96 0 2 2
cert_block_8 0096 96 2
cert_check_4 0097 0000 97 0 2 2
cert_block_8 0097 97 2
cert_check_4 0098 0000 98 0 6 6
cert_block_8 0098 98 6
cert_check_4 0099 0000 99 0 6 6
cert_block_8 0099 99 6
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4
cert_metadata_validity_12 0000 0 16 16
cert_metadata_validity_12 0016 16 32 16
cert_metadata_validity_12 0032 32 48 16
cert_metadata_validity_12 0048 48 64 16
cert_metadata_validity_12 0064 64 80 16
cert_metadata_validity_12 0080 80 96 16
cert_metadata_validity_12 0096 96 100 4
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 48 100
  (FiniteChecks.interval_append (validity) 0 16 48
  metadata_validity_0000
  (FiniteChecks.interval_append (validity) 16 32 48
  metadata_validity_0016
  metadata_validity_0032))
  (FiniteChecks.interval_append (validity) 48 80 100
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)
  (FiniteChecks.interval_append (validity) 80 96 100
  metadata_validity_0080
  metadata_validity_0096)))
cert_metadata_symmetry_13 0000 0 16 16
cert_metadata_symmetry_13 0016 16 32 16
cert_metadata_symmetry_13 0032 32 48 16
cert_metadata_symmetry_13 0048 48 64 16
cert_metadata_symmetry_13 0064 64 80 16
cert_metadata_symmetry_13 0080 80 96 16
cert_metadata_symmetry_13 0096 96 100 4
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 48 100
  (FiniteChecks.interval_append (symmetry) 0 16 48
  metadata_symmetry_0000
  (FiniteChecks.interval_append (symmetry) 16 32 48
  metadata_symmetry_0016
  metadata_symmetry_0032))
  (FiniteChecks.interval_append (symmetry) 48 80 100
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)
  (FiniteChecks.interval_append (symmetry) 80 96 100
  metadata_symmetry_0080
  metadata_symmetry_0096)))
cert_metadata_normalizers_4 6
cert_metadata_root_4
end Papers.RationalityTen.RootedCanonical.RootedSixExtra05.T4
