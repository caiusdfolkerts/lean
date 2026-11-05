module
prelude
public import RootedSubsumedForest0338Data
public import RawLeafCertificate
public import OldTerminalMatches.M008
public import OldTerminalMatches.M009
public import OldTerminalMatches.M010
public import OldTerminalMatches.M011

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 191
 (.branch 95
 (.branch 47
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.quota 2))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0539))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0540)))))
 (.branch 8
 (.branch 6
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0541))
 (.branch 7
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0542))
 (.leaf (.quota 2))))
 (.branch 9
 (.leaf (.incidence 0))
 (.branch 10
 (.leaf (.incidence 5))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0543))))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0544))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 20
 (.branch 18
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0545))
 (.branch 19
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0546))
 (.leaf (.quota 2))))
 (.branch 21
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0547))
 (.branch 22
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0548))
 (.leaf (.quota 2)))))))
 (.branch 35
 (.branch 29
 (.branch 26
 (.branch 24
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0549))
 (.branch 25
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0550))
 (.leaf (.quota 2))))
 (.branch 27
 (.leaf (.quota 2))
 (.leaf (.incidence 5))))
 (.branch 32
 (.branch 30
 (.leaf (.incidence 0))
 (.branch 31
 (.leaf (.incidence 0))
 (.leaf (.incidence 7))))
 (.branch 33
 (.leaf (.incidence 9))
 (.branch 34
 (.leaf .euler)
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0551))))))
 (.branch 41
 (.branch 38
 (.branch 36
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0552))
 (.branch 37
 (.leaf .euler)
 (.leaf (.incidence 9))))
 (.branch 39
 (.leaf (.incidence 0))
 (.branch 40
 (.leaf (.incidence 9))
 (.leaf .euler))))
 (.branch 44
 (.branch 42
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0553))
 (.branch 43
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0554))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))))
 (.branch 71
 (.branch 59
 (.branch 53
 (.branch 50
 (.leaf (.quota 2))
 (.branch 51
 (.leaf (.quota 2))
 (.branch 52
 (.leaf (.incidence 5))
 (.leaf (.quota 3)))))
 (.branch 56
 (.branch 54
 (.leaf (.quota 3))
 (.branch 55
 (.leaf (.incidence 5))
 (.leaf (.quota 3))))
 (.branch 57
 (.leaf (.quota 3))
 (.branch 58
 (.leaf (.quota 3))
 (.leaf (.quota 2))))))
 (.branch 65
 (.branch 62
 (.branch 60
 (.leaf (.quota 2))
 (.branch 61
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0555))))
 (.branch 63
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0556))
 (.branch 64
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0557))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2))))
 (.branch 83
 (.branch 77
 (.branch 74
 (.branch 72
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0558))
 (.leaf (.quota 2)))
 (.branch 75
 (.leaf (.quota 2))
 (.leaf (.incidence 0))))
 (.branch 80
 (.branch 78
 (.leaf (.incidence 5))
 (.branch 79
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))
 (.branch 81
 (.leaf (.quota 2))
 (.branch 82
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0559))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0560))))))
 (.branch 89
 (.branch 86
 (.branch 84
 (.leaf (.quota 2))
 (.branch 85
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0561))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0562))))
 (.leaf (.quota 2)))
 (.branch 92
 (.leaf (.quota 2))
 (.branch 93
 (.leaf (.quota 2))
 (.branch 94
 (.leaf (.quota 2))
 (.leaf (.quota 3)))))))))
 (.branch 143
 (.branch 119
 (.branch 107
 (.branch 101
 (.branch 98
 (.branch 96
 (.leaf (.quota 3))
 (.leaf (.quota 2)))
 (.branch 99
 (.leaf (.quota 2))
 (.branch 100
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0563))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0564)))))
 (.branch 104
 (.branch 102
 (.leaf (.quota 2))
 (.branch 103
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0565))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0566))))
 (.branch 105
 (.leaf (.quota 2))
 (.branch 106
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0567))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0568))))))
 (.branch 113
 (.branch 110
 (.branch 108
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0569))
 (.branch 109
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0570))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0571))))
 (.branch 111
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0572))
 (.branch 112
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0573))
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0574)))))
 (.branch 116
 (.branch 114
 (.leaf (.matching Nonrational.OldTerminalMatches.M008.r0575))
 (.leaf (.quota 3)))
 (.branch 117
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0576))
 (.branch 118
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0577))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0578)))))))
 (.branch 131
 (.branch 125
 (.branch 122
 (.branch 120
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0579))
 (.branch 121
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0580))
 (.leaf (.quota 2))))
 (.branch 123
 (.leaf (.quota 3))
 (.leaf (.quota 2))))
 (.branch 128
 (.branch 126
 (.leaf (.quota 2))
 (.branch 127
 (.leaf (.quota 2))
 (.leaf (.quota 1))))
 (.branch 129
 (.leaf (.quota 2))
 (.branch 130
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0581))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0582))))))
 (.branch 137
 (.branch 134
 (.branch 132
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0583))
 (.branch 133
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0584))
 (.leaf (.quota 2))))
 (.branch 135
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0585))
 (.branch 136
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0586))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0587)))))
 (.branch 140
 (.branch 138
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.leaf (.quota 2))))))
 (.branch 167
 (.branch 155
 (.branch 149
 (.branch 146
 (.branch 144
 (.leaf (.incidence 0))
 (.branch 145
 (.leaf (.incidence 0))
 (.leaf (.quota 2))))
 (.branch 147
 (.leaf (.incidence 7))
 (.branch 148
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0588))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0589)))))
 (.branch 152
 (.branch 150
 (.leaf (.quota 2))
 (.branch 151
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 153
 (.leaf (.quota 2))
 (.branch 154
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0590))
 (.leaf (.quota 1))))))
 (.branch 161
 (.branch 158
 (.branch 156
 (.leaf (.quota 2))
 (.branch 157
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0591))
 (.leaf (.quota 3))))
 (.branch 159
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0592))
 (.branch 160
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0593))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0594)))))
 (.branch 164
 (.branch 162
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0595))
 (.leaf (.quota 2)))
 (.branch 165
 (.leaf (.quota 2))
 (.branch 166
 (.leaf (.quota 1))
 (.leaf (.incidence 5)))))))
 (.branch 179
 (.branch 173
 (.branch 170
 (.branch 168
 (.leaf (.quota 2))
 (.branch 169
 (.leaf (.quota 2))
 (.leaf (.incidence 0))))
 (.branch 171
 (.leaf (.incidence 0))
 (.branch 172
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0596))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0597)))))
 (.branch 176
 (.branch 174
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0598))
 (.branch 175
 (.leaf (.incidence 0))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0599))))
 (.branch 177
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0600))
 (.branch 178
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0601))
 (.leaf (.quota 2))))))
 (.branch 185
 (.branch 182
 (.branch 180
 (.leaf (.quota 1))
 (.branch 181
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.leaf (.quota 2)))
 (.branch 188
 (.branch 186
 (.leaf (.quota 2))
 (.branch 187
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0602))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0603))))
 (.branch 189
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0604))
 (.branch 190
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0605))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0606))))))))))
 (.branch 287
 (.branch 239
 (.branch 215
 (.branch 203
 (.branch 197
 (.branch 194
 (.branch 192
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0607))
 (.leaf (.quota 2)))
 (.branch 195
 (.leaf (.quota 1))
 (.leaf (.quota 2))))
 (.branch 200
 (.leaf (.quota 2))
 (.branch 201
 (.leaf (.incidence 9))
 (.branch 202
 (.leaf (.incidence 9))
 (.leaf .euler)))))
 (.branch 209
 (.branch 206
 (.branch 204
 (.leaf (.quota 2))
 (.branch 205
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0608))))
 (.branch 207
 (.leaf (.quota 2))
 (.branch 208
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0609)))))
 (.branch 212
 (.branch 210
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0610))
 (.branch 211
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0611))))
 (.branch 213
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0612))
 (.branch 214
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0613))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0614)))))))
 (.branch 227
 (.branch 221
 (.branch 218
 (.branch 216
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0615))
 (.branch 217
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0616))
 (.leaf (.quota 2))))
 (.branch 219
 (.leaf (.quota 2))
 (.branch 220
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0617))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0618)))))
 (.branch 224
 (.branch 222
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0619))
 (.branch 223
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0620))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0621))))
 (.branch 225
 (.leaf (.incidence 0))
 (.branch 226
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0622))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0623))))))
 (.branch 233
 (.branch 230
 (.branch 228
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0624))
 (.branch 229
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0625))
 (.leaf (.quota 2))))
 (.branch 231
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0626))
 (.leaf (.quota 2))))
 (.branch 236
 (.branch 234
 (.leaf (.quota 2))
 (.branch 235
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0627))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0628))))
 (.branch 237
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0629))
 (.branch 238
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0630))))))))
 (.branch 263
 (.branch 251
 (.branch 245
 (.branch 242
 (.branch 240
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0631))
 (.branch 241
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0632))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0633))))
 (.branch 243
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0634))
 (.branch 244
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0635))
 (.leaf (.quota 2)))))
 (.branch 248
 (.leaf (.quota 2))
 (.branch 249
 (.leaf (.quota 2))
 (.branch 250
 (.leaf (.incidence 0))
 (.leaf (.quota 2))))))
 (.branch 257
 (.branch 254
 (.branch 252
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))
 (.branch 255
 (.leaf (.incidence 0))
 (.branch 256
 (.leaf (.incidence 0))
 (.leaf (.quota 2)))))
 (.branch 260
 (.branch 258
 (.leaf (.quota 2))
 (.branch 259
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0636))
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0637))))
 (.branch 261
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0638))
 (.branch 262
 (.leaf (.matching Nonrational.OldTerminalMatches.M009.r0639))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0640)))))))
 (.branch 275
 (.branch 269
 (.branch 266
 (.branch 264
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0641))
 (.branch 265
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0642))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0643))))
 (.branch 267
 (.leaf (.quota 2))
 (.branch 268
 (.leaf (.incidence 7))
 (.leaf (.quota 2)))))
 (.branch 272
 (.branch 270
 (.leaf (.quota 2))
 (.branch 271
 (.leaf (.quota 2))
 (.leaf (.incidence 5))))
 (.leaf (.incidence 5))))
 (.branch 281
 (.branch 278
 (.branch 276
 (.leaf (.incidence 5))
 (.branch 277
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))
 (.branch 279
 (.leaf (.incidence 5))
 (.branch 280
 (.leaf (.quota 2))
 (.leaf (.incidence 5)))))
 (.branch 284
 (.branch 282
 (.leaf (.quota 2))
 (.branch 283
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0644))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0645))))
 (.branch 285
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0646))
 (.branch 286
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0647))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0648)))))))))
 (.branch 335
 (.branch 311
 (.branch 299
 (.branch 293
 (.branch 290
 (.branch 288
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0649))
 (.branch 289
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0650))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0651))))
 (.branch 291
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0652))
 (.branch 292
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0653))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0654)))))
 (.branch 296
 (.branch 294
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0655))
 (.branch 295
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0656))
 (.leaf (.quota 2))))
 (.branch 297
 (.leaf (.quota 2))
 (.branch 298
 (.leaf (.incidence 5))
 (.leaf (.quota 2))))))
 (.branch 305
 (.branch 302
 (.branch 300
 (.leaf (.incidence 5))
 (.branch 301
 (.leaf (.incidence 5))
 (.leaf (.quota 1))))
 (.branch 303
 (.leaf (.quota 1))
 (.branch 304
 (.leaf (.quota 2))
 (.leaf (.incidence 5)))))
 (.branch 308
 (.branch 306
 (.leaf (.incidence 5))
 (.branch 307
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0657))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0658))))
 (.branch 309
 (.leaf (.incidence 5))
 (.branch 310
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0659))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0660)))))))
 (.branch 323
 (.branch 317
 (.branch 314
 (.branch 312
 (.leaf (.incidence 5))
 (.branch 313
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0661))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0662))))
 (.branch 315
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0663))
 (.branch 316
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0664))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0665)))))
 (.branch 320
 (.branch 318
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0666))
 (.branch 319
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0667))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0668))))
 (.branch 321
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0669))
 (.branch 322
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0670))
 (.leaf (.quota 2))))))
 (.branch 329
 (.branch 326
 (.branch 324
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0671))
 (.branch 325
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0672))
 (.leaf (.quota 2))))
 (.branch 327
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0673))
 (.leaf (.quota 2))))
 (.branch 332
 (.branch 330
 (.leaf (.incidence 5))
 (.branch 331
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0674))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0675))))
 (.branch 333
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0676))
 (.branch 334
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0677))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0678))))))))
 (.branch 359
 (.branch 347
 (.branch 341
 (.branch 338
 (.branch 336
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0679))
 (.branch 337
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0680))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0681))))
 (.branch 339
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0682))
 (.branch 340
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0683))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0684)))))
 (.branch 344
 (.branch 342
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0685))
 (.branch 343
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0686))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0687))))
 (.branch 345
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0688))
 (.branch 346
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0689))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0690))))))
 (.branch 353
 (.branch 350
 (.branch 348
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0691))
 (.branch 349
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0692))
 (.leaf (.quota 1))))
 (.leaf (.quota 2)))
 (.branch 356
 (.leaf (.quota 2))
 (.branch 357
 (.leaf (.quota 2))
 (.branch 358
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0693))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0694)))))))
 (.branch 371
 (.branch 365
 (.branch 362
 (.branch 360
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0695))
 (.branch 361
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0696))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0697))))
 (.branch 363
 (.leaf (.quota 2))
 (.branch 364
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0698))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0699)))))
 (.branch 368
 (.branch 366
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0700))
 (.branch 367
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0701))
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0702))))
 (.branch 369
 (.leaf (.matching Nonrational.OldTerminalMatches.M010.r0703))
 (.branch 370
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0704))))))
 (.branch 377
 (.branch 374
 (.branch 372
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0705))
 (.branch 373
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0706))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0707))))
 (.branch 375
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0708))
 (.branch 376
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0709))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0710)))))
 (.branch 380
 (.branch 378
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0711))
 (.branch 379
 (.leaf (.quota 2))
 (.leaf (.incidence 5))))
 (.branch 381
 (.leaf (.quota 2))
 (.branch 382
 (.leaf (.quota 2))
 (.leaf (.incidence 0)))))))))))
def disposition (j : Fin leafCount) := dispositionTable.get j.val
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase00.rawCells) (dispositionTable.get i)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
