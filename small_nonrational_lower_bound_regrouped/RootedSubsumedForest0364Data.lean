module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public meta import CertificateNumbers
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import RootedSubsumedForest0364Packed000
public import RootedSubsumedForest0364Packed001
public import RootedSubsumedForest0364Packed002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0364
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 8084
abbrev nodeCount : Nat := 18464
abbrev leafCount : Nat := 350
cert_widths_3 13 15 6 9
cert_blocks_11
cert_counterTable_3
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table Nat :=
(.branch 175
 (.branch 87
 (.branch 43
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (certNat% 0))
 (.leaf (certNat% 1)))
 (.branch 3
 (.leaf (certNat% 2))
 (.branch 4
 (.leaf (certNat% 3))
 (.leaf (certNat% 4)))))
 (.branch 7
 (.branch 6
 (.leaf (certNat% 5))
 (.leaf (certNat% 6)))
 (.branch 8
 (.leaf (certNat% 7))
 (.branch 9
 (.leaf (certNat% 8))
 (.leaf (certNat% 9))))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf (certNat% 10))
 (.leaf (certNat% 11)))
 (.branch 13
 (.leaf (certNat% 12))
 (.branch 14
 (.leaf (certNat% 13))
 (.leaf (certNat% 14)))))
 (.branch 18
 (.branch 16
 (.leaf (certNat% 15))
 (.branch 17
 (.leaf (certNat% 16))
 (.leaf (certNat% 17))))
 (.branch 19
 (.leaf (certNat% 18))
 (.branch 20
 (.leaf (certNat% 19))
 (.leaf (certNat% 20)))))))
 (.branch 32
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf (certNat% 21))
 (.leaf (certNat% 22)))
 (.branch 24
 (.leaf (certNat% 23))
 (.branch 25
 (.leaf (certNat% 24))
 (.leaf (certNat% 25)))))
 (.branch 29
 (.branch 27
 (.leaf (certNat% 26))
 (.branch 28
 (.leaf (certNat% 27))
 (.leaf (certNat% 28))))
 (.branch 30
 (.leaf (certNat% 29))
 (.branch 31
 (.leaf (certNat% 30))
 (.leaf (certNat% 31))))))
 (.branch 37
 (.branch 34
 (.branch 33
 (.leaf (certNat% 32))
 (.leaf (certNat% 33)))
 (.branch 35
 (.leaf (certNat% 34))
 (.branch 36
 (.leaf (certNat% 35))
 (.leaf (certNat% 36)))))
 (.branch 40
 (.branch 38
 (.leaf (certNat% 37))
 (.branch 39
 (.leaf (certNat% 38))
 (.leaf (certNat% 39))))
 (.branch 41
 (.leaf (certNat% 40))
 (.branch 42
 (.leaf (certNat% 41))
 (.leaf (certNat% 42))))))))
 (.branch 65
 (.branch 54
 (.branch 48
 (.branch 45
 (.branch 44
 (.leaf (certNat% 43))
 (.leaf (certNat% 44)))
 (.branch 46
 (.leaf (certNat% 45))
 (.branch 47
 (.leaf (certNat% 46))
 (.leaf (certNat% 47)))))
 (.branch 51
 (.branch 49
 (.leaf (certNat% 48))
 (.branch 50
 (.leaf (certNat% 49))
 (.leaf (certNat% 50))))
 (.branch 52
 (.leaf (certNat% 51))
 (.branch 53
 (.leaf (certNat% 52))
 (.leaf (certNat% 53))))))
 (.branch 59
 (.branch 56
 (.branch 55
 (.leaf (certNat% 54))
 (.leaf (certNat% 55)))
 (.branch 57
 (.leaf (certNat% 56))
 (.branch 58
 (.leaf (certNat% 57))
 (.leaf (certNat% 58)))))
 (.branch 62
 (.branch 60
 (.leaf (certNat% 59))
 (.branch 61
 (.leaf (certNat% 60))
 (.leaf (certNat% 61))))
 (.branch 63
 (.leaf (certNat% 62))
 (.branch 64
 (.leaf (certNat% 63))
 (.leaf (certNat% 64)))))))
 (.branch 76
 (.branch 70
 (.branch 67
 (.branch 66
 (.leaf (certNat% 65))
 (.leaf (certNat% 66)))
 (.branch 68
 (.leaf (certNat% 67))
 (.branch 69
 (.leaf (certNat% 68))
 (.leaf (certNat% 69)))))
 (.branch 73
 (.branch 71
 (.leaf (certNat% 70))
 (.branch 72
 (.leaf (certNat% 71))
 (.leaf (certNat% 72))))
 (.branch 74
 (.leaf (certNat% 73))
 (.branch 75
 (.leaf (certNat% 74))
 (.leaf (certNat% 75))))))
 (.branch 81
 (.branch 78
 (.branch 77
 (.leaf (certNat% 76))
 (.leaf (certNat% 77)))
 (.branch 79
 (.leaf (certNat% 78))
 (.branch 80
 (.leaf (certNat% 79))
 (.leaf (certNat% 80)))))
 (.branch 84
 (.branch 82
 (.leaf (certNat% 81))
 (.branch 83
 (.leaf (certNat% 82))
 (.leaf (certNat% 83))))
 (.branch 85
 (.leaf (certNat% 84))
 (.branch 86
 (.leaf (certNat% 85))
 (.leaf (certNat% 86)))))))))
 (.branch 131
 (.branch 109
 (.branch 98
 (.branch 92
 (.branch 89
 (.branch 88
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))
 (.branch 90
 (.leaf (certNat% 89))
 (.branch 91
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))))
 (.branch 95
 (.branch 93
 (.leaf (certNat% 92))
 (.branch 94
 (.leaf (certNat% 93))
 (.leaf (certNat% 94))))
 (.branch 96
 (.leaf (certNat% 95))
 (.branch 97
 (.leaf (certNat% 96))
 (.leaf (certNat% 97))))))
 (.branch 103
 (.branch 100
 (.branch 99
 (.leaf (certNat% 98))
 (.leaf (certNat% 99)))
 (.branch 101
 (.leaf (certNat% 100))
 (.branch 102
 (.leaf (certNat% 101))
 (.leaf (certNat% 102)))))
 (.branch 106
 (.branch 104
 (.leaf (certNat% 103))
 (.branch 105
 (.leaf (certNat% 104))
 (.leaf (certNat% 105))))
 (.branch 107
 (.leaf (certNat% 106))
 (.branch 108
 (.leaf (certNat% 107))
 (.leaf (certNat% 108)))))))
 (.branch 120
 (.branch 114
 (.branch 111
 (.branch 110
 (.leaf (certNat% 109))
 (.leaf (certNat% 110)))
 (.branch 112
 (.leaf (certNat% 111))
 (.branch 113
 (.leaf (certNat% 112))
 (.leaf (certNat% 113)))))
 (.branch 117
 (.branch 115
 (.leaf (certNat% 114))
 (.branch 116
 (.leaf (certNat% 115))
 (.leaf (certNat% 116))))
 (.branch 118
 (.leaf (certNat% 117))
 (.branch 119
 (.leaf (certNat% 118))
 (.leaf (certNat% 119))))))
 (.branch 125
 (.branch 122
 (.branch 121
 (.leaf (certNat% 120))
 (.leaf (certNat% 121)))
 (.branch 123
 (.leaf (certNat% 122))
 (.branch 124
 (.leaf (certNat% 123))
 (.leaf (certNat% 124)))))
 (.branch 128
 (.branch 126
 (.leaf (certNat% 125))
 (.branch 127
 (.leaf (certNat% 126))
 (.leaf (certNat% 127))))
 (.branch 129
 (.leaf (certNat% 128))
 (.branch 130
 (.leaf (certNat% 129))
 (.leaf (certNat% 130))))))))
 (.branch 153
 (.branch 142
 (.branch 136
 (.branch 133
 (.branch 132
 (.leaf (certNat% 131))
 (.leaf (certNat% 132)))
 (.branch 134
 (.leaf (certNat% 133))
 (.branch 135
 (.leaf (certNat% 134))
 (.leaf (certNat% 135)))))
 (.branch 139
 (.branch 137
 (.leaf (certNat% 136))
 (.branch 138
 (.leaf (certNat% 137))
 (.leaf (certNat% 138))))
 (.branch 140
 (.leaf (certNat% 139))
 (.branch 141
 (.leaf (certNat% 140))
 (.leaf (certNat% 141))))))
 (.branch 147
 (.branch 144
 (.branch 143
 (.leaf (certNat% 142))
 (.leaf (certNat% 143)))
 (.branch 145
 (.leaf (certNat% 144))
 (.branch 146
 (.leaf (certNat% 145))
 (.leaf (certNat% 146)))))
 (.branch 150
 (.branch 148
 (.leaf (certNat% 147))
 (.branch 149
 (.leaf (certNat% 148))
 (.leaf (certNat% 149))))
 (.branch 151
 (.leaf (certNat% 150))
 (.branch 152
 (.leaf (certNat% 151))
 (.leaf (certNat% 152)))))))
 (.branch 164
 (.branch 158
 (.branch 155
 (.branch 154
 (.leaf (certNat% 153))
 (.leaf (certNat% 154)))
 (.branch 156
 (.leaf (certNat% 155))
 (.branch 157
 (.leaf (certNat% 156))
 (.leaf (certNat% 157)))))
 (.branch 161
 (.branch 159
 (.leaf (certNat% 158))
 (.branch 160
 (.leaf (certNat% 159))
 (.leaf (certNat% 160))))
 (.branch 162
 (.leaf (certNat% 161))
 (.branch 163
 (.leaf (certNat% 162))
 (.leaf (certNat% 163))))))
 (.branch 169
 (.branch 166
 (.branch 165
 (.leaf (certNat% 164))
 (.leaf (certNat% 165)))
 (.branch 167
 (.leaf (certNat% 166))
 (.branch 168
 (.leaf (certNat% 167))
 (.leaf (certNat% 168)))))
 (.branch 172
 (.branch 170
 (.leaf (certNat% 169))
 (.branch 171
 (.leaf (certNat% 170))
 (.leaf (certNat% 171))))
 (.branch 173
 (.leaf (certNat% 172))
 (.branch 174
 (.leaf (certNat% 173))
 (.leaf (certNat% 174))))))))))
 (.branch 262
 (.branch 218
 (.branch 196
 (.branch 185
 (.branch 180
 (.branch 177
 (.branch 176
 (.leaf (certNat% 175))
 (.leaf (certNat% 176)))
 (.branch 178
 (.leaf (certNat% 177))
 (.branch 179
 (.leaf (certNat% 178))
 (.leaf (certNat% 179)))))
 (.branch 182
 (.branch 181
 (.leaf (certNat% 180))
 (.leaf (certNat% 181)))
 (.branch 183
 (.leaf (certNat% 182))
 (.branch 184
 (.leaf (certNat% 183))
 (.leaf (certNat% 184))))))
 (.branch 190
 (.branch 187
 (.branch 186
 (.leaf (certNat% 185))
 (.leaf (certNat% 186)))
 (.branch 188
 (.leaf (certNat% 187))
 (.branch 189
 (.leaf (certNat% 188))
 (.leaf (certNat% 189)))))
 (.branch 193
 (.branch 191
 (.leaf (certNat% 190))
 (.branch 192
 (.leaf (certNat% 191))
 (.leaf (certNat% 192))))
 (.branch 194
 (.leaf (certNat% 193))
 (.branch 195
 (.leaf (certNat% 194))
 (.leaf (certNat% 195)))))))
 (.branch 207
 (.branch 201
 (.branch 198
 (.branch 197
 (.leaf (certNat% 196))
 (.leaf (certNat% 197)))
 (.branch 199
 (.leaf (certNat% 198))
 (.branch 200
 (.leaf (certNat% 199))
 (.leaf (certNat% 200)))))
 (.branch 204
 (.branch 202
 (.leaf (certNat% 201))
 (.branch 203
 (.leaf (certNat% 202))
 (.leaf (certNat% 203))))
 (.branch 205
 (.leaf (certNat% 204))
 (.branch 206
 (.leaf (certNat% 205))
 (.leaf (certNat% 206))))))
 (.branch 212
 (.branch 209
 (.branch 208
 (.leaf (certNat% 207))
 (.leaf (certNat% 208)))
 (.branch 210
 (.leaf (certNat% 209))
 (.branch 211
 (.leaf (certNat% 210))
 (.leaf (certNat% 211)))))
 (.branch 215
 (.branch 213
 (.leaf (certNat% 212))
 (.branch 214
 (.leaf (certNat% 213))
 (.leaf (certNat% 214))))
 (.branch 216
 (.leaf (certNat% 215))
 (.branch 217
 (.leaf (certNat% 216))
 (.leaf (certNat% 217))))))))
 (.branch 240
 (.branch 229
 (.branch 223
 (.branch 220
 (.branch 219
 (.leaf (certNat% 218))
 (.leaf (certNat% 219)))
 (.branch 221
 (.leaf (certNat% 220))
 (.branch 222
 (.leaf (certNat% 221))
 (.leaf (certNat% 222)))))
 (.branch 226
 (.branch 224
 (.leaf (certNat% 223))
 (.branch 225
 (.leaf (certNat% 224))
 (.leaf (certNat% 225))))
 (.branch 227
 (.leaf (certNat% 226))
 (.branch 228
 (.leaf (certNat% 227))
 (.leaf (certNat% 228))))))
 (.branch 234
 (.branch 231
 (.branch 230
 (.leaf (certNat% 229))
 (.leaf (certNat% 230)))
 (.branch 232
 (.leaf (certNat% 231))
 (.branch 233
 (.leaf (certNat% 232))
 (.leaf (certNat% 233)))))
 (.branch 237
 (.branch 235
 (.leaf (certNat% 234))
 (.branch 236
 (.leaf (certNat% 235))
 (.leaf (certNat% 236))))
 (.branch 238
 (.leaf (certNat% 237))
 (.branch 239
 (.leaf (certNat% 238))
 (.leaf (certNat% 239)))))))
 (.branch 251
 (.branch 245
 (.branch 242
 (.branch 241
 (.leaf (certNat% 240))
 (.leaf (certNat% 241)))
 (.branch 243
 (.leaf (certNat% 242))
 (.branch 244
 (.leaf (certNat% 243))
 (.leaf (certNat% 244)))))
 (.branch 248
 (.branch 246
 (.leaf (certNat% 245))
 (.branch 247
 (.leaf (certNat% 246))
 (.leaf (certNat% 247))))
 (.branch 249
 (.leaf (certNat% 248))
 (.branch 250
 (.leaf (certNat% 249))
 (.leaf (certNat% 250))))))
 (.branch 256
 (.branch 253
 (.branch 252
 (.leaf (certNat% 251))
 (.leaf (certNat% 252)))
 (.branch 254
 (.leaf (certNat% 253))
 (.branch 255
 (.leaf (certNat% 254))
 (.leaf (certNat% 255)))))
 (.branch 259
 (.branch 257
 (.leaf (certNat% 256))
 (.branch 258
 (.leaf (certNat% 257))
 (.leaf (certNat% 258))))
 (.branch 260
 (.leaf (certNat% 259))
 (.branch 261
 (.leaf (certNat% 260))
 (.leaf (certNat% 261)))))))))
 (.branch 306
 (.branch 284
 (.branch 273
 (.branch 267
 (.branch 264
 (.branch 263
 (.leaf (certNat% 262))
 (.leaf (certNat% 263)))
 (.branch 265
 (.leaf (certNat% 264))
 (.branch 266
 (.leaf (certNat% 265))
 (.leaf (certNat% 266)))))
 (.branch 270
 (.branch 268
 (.leaf (certNat% 267))
 (.branch 269
 (.leaf (certNat% 268))
 (.leaf (certNat% 269))))
 (.branch 271
 (.leaf (certNat% 270))
 (.branch 272
 (.leaf (certNat% 271))
 (.leaf (certNat% 272))))))
 (.branch 278
 (.branch 275
 (.branch 274
 (.leaf (certNat% 273))
 (.leaf (certNat% 274)))
 (.branch 276
 (.leaf (certNat% 275))
 (.branch 277
 (.leaf (certNat% 276))
 (.leaf (certNat% 277)))))
 (.branch 281
 (.branch 279
 (.leaf (certNat% 278))
 (.branch 280
 (.leaf (certNat% 279))
 (.leaf (certNat% 280))))
 (.branch 282
 (.leaf (certNat% 281))
 (.branch 283
 (.leaf (certNat% 282))
 (.leaf (certNat% 283)))))))
 (.branch 295
 (.branch 289
 (.branch 286
 (.branch 285
 (.leaf (certNat% 284))
 (.leaf (certNat% 285)))
 (.branch 287
 (.leaf (certNat% 286))
 (.branch 288
 (.leaf (certNat% 287))
 (.leaf (certNat% 288)))))
 (.branch 292
 (.branch 290
 (.leaf (certNat% 289))
 (.branch 291
 (.leaf (certNat% 290))
 (.leaf (certNat% 291))))
 (.branch 293
 (.leaf (certNat% 292))
 (.branch 294
 (.leaf (certNat% 293))
 (.leaf (certNat% 294))))))
 (.branch 300
 (.branch 297
 (.branch 296
 (.leaf (certNat% 295))
 (.leaf (certNat% 296)))
 (.branch 298
 (.leaf (certNat% 297))
 (.branch 299
 (.leaf (certNat% 298))
 (.leaf (certNat% 299)))))
 (.branch 303
 (.branch 301
 (.leaf (certNat% 300))
 (.branch 302
 (.leaf (certNat% 301))
 (.leaf (certNat% 302))))
 (.branch 304
 (.leaf (certNat% 303))
 (.branch 305
 (.leaf (certNat% 304))
 (.leaf (certNat% 305))))))))
 (.branch 328
 (.branch 317
 (.branch 311
 (.branch 308
 (.branch 307
 (.leaf (certNat% 306))
 (.leaf (certNat% 307)))
 (.branch 309
 (.leaf (certNat% 308))
 (.branch 310
 (.leaf (certNat% 309))
 (.leaf (certNat% 310)))))
 (.branch 314
 (.branch 312
 (.leaf (certNat% 311))
 (.branch 313
 (.leaf (certNat% 312))
 (.leaf (certNat% 313))))
 (.branch 315
 (.leaf (certNat% 314))
 (.branch 316
 (.leaf (certNat% 315))
 (.leaf (certNat% 316))))))
 (.branch 322
 (.branch 319
 (.branch 318
 (.leaf (certNat% 317))
 (.leaf (certNat% 318)))
 (.branch 320
 (.leaf (certNat% 319))
 (.branch 321
 (.leaf (certNat% 320))
 (.leaf (certNat% 321)))))
 (.branch 325
 (.branch 323
 (.leaf (certNat% 322))
 (.branch 324
 (.leaf (certNat% 323))
 (.leaf (certNat% 324))))
 (.branch 326
 (.leaf (certNat% 325))
 (.branch 327
 (.leaf (certNat% 326))
 (.leaf (certNat% 327)))))))
 (.branch 339
 (.branch 333
 (.branch 330
 (.branch 329
 (.leaf (certNat% 328))
 (.leaf (certNat% 329)))
 (.branch 331
 (.leaf (certNat% 330))
 (.branch 332
 (.leaf (certNat% 331))
 (.leaf (certNat% 332)))))
 (.branch 336
 (.branch 334
 (.leaf (certNat% 333))
 (.branch 335
 (.leaf (certNat% 334))
 (.leaf (certNat% 335))))
 (.branch 337
 (.leaf (certNat% 336))
 (.branch 338
 (.leaf (certNat% 337))
 (.leaf (certNat% 338))))))
 (.branch 344
 (.branch 341
 (.branch 340
 (.leaf (certNat% 339))
 (.leaf (certNat% 340)))
 (.branch 342
 (.leaf (certNat% 341))
 (.branch 343
 (.leaf (certNat% 342))
 (.leaf (certNat% 343)))))
 (.branch 347
 (.branch 345
 (.leaf (certNat% 344))
 (.branch 346
 (.leaf (certNat% 345))
 (.leaf (certNat% 346))))
 (.branch 348
 (.leaf (certNat% 347))
 (.branch 349
 (.leaf (certNat% 348))
 (.leaf (certNat% 349)))))))))))
cert_rawLeaves_4 13
cert_leaves_3
cert_quota_3 0 3 0 0 0 0 0 0 2 7
cert_nodeTest_5 48 02
cert_nodeTest_sound_4 48 02
cert_leafTest_4 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0364
