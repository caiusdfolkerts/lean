import cubical_indecomposability.face_data
import Lean.Elab.Tactic.Omega

/-!
# A specified vertex in each catalogue face

The proposed anchor is the least vertex label of each nonempty mask.
Only the membership statement is needed in subsequent proofs, and that
statement is checked independently by ordinary kernel reduction for
every catalogue entry. The exhaustive case splits have at most 32
leaves per declaration.

Regenerate with `python3 scripts/sparse_cube_complete.py`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability

private def faceAnchorTable : ℕ → Fin 144 :=
fun index =>
    if index < 534 then
      if index < 267 then
        if index < 133 then
          if index < 66 then
            if index < 33 then
              if index < 16 then
                if index < 8 then
                  if index < 4 then
                    if index < 2 then
                      if index < 1 then
                        0
                      else
                        1
                    else
                      if index < 3 then
                        2
                      else
                        3
                  else
                    if index < 6 then
                      if index < 5 then
                        4
                      else
                        5
                    else
                      if index < 7 then
                        6
                      else
                        7
                else
                  if index < 12 then
                    if index < 10 then
                      if index < 9 then
                        8
                      else
                        9
                    else
                      if index < 11 then
                        10
                      else
                        11
                  else
                    if index < 14 then
                      if index < 13 then
                        12
                      else
                        13
                    else
                      if index < 15 then
                        14
                      else
                        15
              else
                if index < 24 then
                  if index < 20 then
                    if index < 18 then
                      if index < 17 then
                        16
                      else
                        17
                    else
                      if index < 19 then
                        18
                      else
                        19
                  else
                    if index < 22 then
                      if index < 21 then
                        20
                      else
                        21
                    else
                      if index < 23 then
                        22
                      else
                        23
                else
                  if index < 28 then
                    if index < 26 then
                      if index < 25 then
                        24
                      else
                        25
                    else
                      if index < 27 then
                        26
                      else
                        27
                  else
                    if index < 30 then
                      if index < 29 then
                        28
                      else
                        29
                    else
                      if index < 31 then
                        30
                      else
                        if index < 32 then
                          31
                        else
                          32
            else
              if index < 49 then
                if index < 41 then
                  if index < 37 then
                    if index < 35 then
                      if index < 34 then
                        33
                      else
                        34
                    else
                      if index < 36 then
                        35
                      else
                        36
                  else
                    if index < 39 then
                      if index < 38 then
                        37
                      else
                        38
                    else
                      if index < 40 then
                        39
                      else
                        40
                else
                  if index < 45 then
                    if index < 43 then
                      if index < 42 then
                        41
                      else
                        42
                    else
                      if index < 44 then
                        43
                      else
                        44
                  else
                    if index < 47 then
                      if index < 46 then
                        45
                      else
                        46
                    else
                      if index < 48 then
                        47
                      else
                        48
              else
                if index < 57 then
                  if index < 53 then
                    if index < 51 then
                      if index < 50 then
                        49
                      else
                        50
                    else
                      if index < 52 then
                        51
                      else
                        52
                  else
                    if index < 55 then
                      if index < 54 then
                        53
                      else
                        54
                    else
                      if index < 56 then
                        55
                      else
                        56
                else
                  if index < 61 then
                    if index < 59 then
                      if index < 58 then
                        57
                      else
                        58
                    else
                      if index < 60 then
                        59
                      else
                        60
                  else
                    if index < 63 then
                      if index < 62 then
                        61
                      else
                        62
                    else
                      if index < 64 then
                        63
                      else
                        if index < 65 then
                          64
                        else
                          65
          else
            if index < 99 then
              if index < 82 then
                if index < 74 then
                  if index < 70 then
                    if index < 68 then
                      if index < 67 then
                        66
                      else
                        67
                    else
                      if index < 69 then
                        68
                      else
                        69
                  else
                    if index < 72 then
                      if index < 71 then
                        70
                      else
                        71
                    else
                      if index < 73 then
                        72
                      else
                        73
                else
                  if index < 78 then
                    if index < 76 then
                      if index < 75 then
                        74
                      else
                        75
                    else
                      if index < 77 then
                        76
                      else
                        77
                  else
                    if index < 80 then
                      if index < 79 then
                        78
                      else
                        79
                    else
                      if index < 81 then
                        80
                      else
                        81
              else
                if index < 90 then
                  if index < 86 then
                    if index < 84 then
                      if index < 83 then
                        82
                      else
                        83
                    else
                      if index < 85 then
                        84
                      else
                        85
                  else
                    if index < 88 then
                      if index < 87 then
                        86
                      else
                        87
                    else
                      if index < 89 then
                        88
                      else
                        89
                else
                  if index < 94 then
                    if index < 92 then
                      if index < 91 then
                        90
                      else
                        91
                    else
                      if index < 93 then
                        92
                      else
                        93
                  else
                    if index < 96 then
                      if index < 95 then
                        94
                      else
                        95
                    else
                      if index < 97 then
                        96
                      else
                        if index < 98 then
                          97
                        else
                          98
            else
              if index < 116 then
                if index < 107 then
                  if index < 103 then
                    if index < 101 then
                      if index < 100 then
                        99
                      else
                        100
                    else
                      if index < 102 then
                        101
                      else
                        102
                  else
                    if index < 105 then
                      if index < 104 then
                        103
                      else
                        104
                    else
                      if index < 106 then
                        105
                      else
                        106
                else
                  if index < 111 then
                    if index < 109 then
                      if index < 108 then
                        107
                      else
                        108
                    else
                      if index < 110 then
                        109
                      else
                        110
                  else
                    if index < 113 then
                      if index < 112 then
                        111
                      else
                        112
                    else
                      if index < 114 then
                        113
                      else
                        if index < 115 then
                          114
                        else
                          115
              else
                if index < 124 then
                  if index < 120 then
                    if index < 118 then
                      if index < 117 then
                        116
                      else
                        117
                    else
                      if index < 119 then
                        118
                      else
                        119
                  else
                    if index < 122 then
                      if index < 121 then
                        120
                      else
                        121
                    else
                      if index < 123 then
                        122
                      else
                        123
                else
                  if index < 128 then
                    if index < 126 then
                      if index < 125 then
                        124
                      else
                        125
                    else
                      if index < 127 then
                        126
                      else
                        127
                  else
                    if index < 130 then
                      if index < 129 then
                        128
                      else
                        129
                    else
                      if index < 131 then
                        130
                      else
                        if index < 132 then
                          131
                        else
                          132
        else
          if index < 200 then
            if index < 166 then
              if index < 149 then
                if index < 141 then
                  if index < 137 then
                    if index < 135 then
                      if index < 134 then
                        133
                      else
                        134
                    else
                      if index < 136 then
                        135
                      else
                        136
                  else
                    if index < 139 then
                      if index < 138 then
                        137
                      else
                        138
                    else
                      if index < 140 then
                        139
                      else
                        140
                else
                  if index < 145 then
                    if index < 143 then
                      if index < 142 then
                        141
                      else
                        142
                    else
                      if index < 144 then
                        143
                      else
                        0
                  else
                    if index < 147 then
                      if index < 146 then
                        0
                      else
                        0
                    else
                      if index < 148 then
                        0
                      else
                        0
              else
                if index < 157 then
                  if index < 153 then
                    if index < 151 then
                      if index < 150 then
                        1
                      else
                        1
                    else
                      if index < 152 then
                        1
                      else
                        1
                  else
                    if index < 155 then
                      if index < 154 then
                        1
                      else
                        1
                    else
                      if index < 156 then
                        2
                      else
                        2
                else
                  if index < 161 then
                    if index < 159 then
                      if index < 158 then
                        2
                      else
                        2
                    else
                      if index < 160 then
                        3
                      else
                        3
                  else
                    if index < 163 then
                      if index < 162 then
                        3
                      else
                        3
                    else
                      if index < 164 then
                        3
                      else
                        if index < 165 then
                          4
                        else
                          4
            else
              if index < 183 then
                if index < 174 then
                  if index < 170 then
                    if index < 168 then
                      if index < 167 then
                        4
                      else
                        4
                    else
                      if index < 169 then
                        5
                      else
                        5
                  else
                    if index < 172 then
                      if index < 171 then
                        5
                      else
                        5
                    else
                      if index < 173 then
                        5
                      else
                        6
                else
                  if index < 178 then
                    if index < 176 then
                      if index < 175 then
                        6
                      else
                        6
                    else
                      if index < 177 then
                        7
                      else
                        7
                  else
                    if index < 180 then
                      if index < 179 then
                        7
                      else
                        7
                    else
                      if index < 181 then
                        8
                      else
                        if index < 182 then
                          8
                        else
                          8
              else
                if index < 191 then
                  if index < 187 then
                    if index < 185 then
                      if index < 184 then
                        8
                      else
                        8
                    else
                      if index < 186 then
                        8
                      else
                        9
                  else
                    if index < 189 then
                      if index < 188 then
                        9
                      else
                        9
                    else
                      if index < 190 then
                        9
                      else
                        9
                else
                  if index < 195 then
                    if index < 193 then
                      if index < 192 then
                        10
                      else
                        10
                    else
                      if index < 194 then
                        10
                      else
                        10
                  else
                    if index < 197 then
                      if index < 196 then
                        10
                      else
                        11
                    else
                      if index < 198 then
                        11
                      else
                        if index < 199 then
                          11
                        else
                          11
          else
            if index < 233 then
              if index < 216 then
                if index < 208 then
                  if index < 204 then
                    if index < 202 then
                      if index < 201 then
                        12
                      else
                        12
                    else
                      if index < 203 then
                        12
                      else
                        12
                  else
                    if index < 206 then
                      if index < 205 then
                        12
                      else
                        13
                    else
                      if index < 207 then
                        13
                      else
                        13
                else
                  if index < 212 then
                    if index < 210 then
                      if index < 209 then
                        13
                      else
                        14
                    else
                      if index < 211 then
                        14
                      else
                        14
                  else
                    if index < 214 then
                      if index < 213 then
                        14
                      else
                        15
                    else
                      if index < 215 then
                        15
                      else
                        15
              else
                if index < 224 then
                  if index < 220 then
                    if index < 218 then
                      if index < 217 then
                        16
                      else
                        16
                    else
                      if index < 219 then
                        16
                      else
                        16
                  else
                    if index < 222 then
                      if index < 221 then
                        17
                      else
                        17
                    else
                      if index < 223 then
                        17
                      else
                        18
                else
                  if index < 228 then
                    if index < 226 then
                      if index < 225 then
                        18
                      else
                        18
                    else
                      if index < 227 then
                        19
                      else
                        19
                  else
                    if index < 230 then
                      if index < 229 then
                        20
                      else
                        20
                    else
                      if index < 231 then
                        20
                      else
                        if index < 232 then
                          21
                        else
                          21
            else
              if index < 250 then
                if index < 241 then
                  if index < 237 then
                    if index < 235 then
                      if index < 234 then
                        22
                      else
                        22
                    else
                      if index < 236 then
                        23
                      else
                        24
                  else
                    if index < 239 then
                      if index < 238 then
                        24
                      else
                        24
                    else
                      if index < 240 then
                        24
                      else
                        24
                else
                  if index < 245 then
                    if index < 243 then
                      if index < 242 then
                        24
                      else
                        25
                    else
                      if index < 244 then
                        25
                      else
                        25
                  else
                    if index < 247 then
                      if index < 246 then
                        25
                      else
                        26
                    else
                      if index < 248 then
                        26
                      else
                        if index < 249 then
                          26
                        else
                          26
              else
                if index < 258 then
                  if index < 254 then
                    if index < 252 then
                      if index < 251 then
                        26
                      else
                        27
                    else
                      if index < 253 then
                        27
                      else
                        27
                  else
                    if index < 256 then
                      if index < 255 then
                        28
                      else
                        28
                    else
                      if index < 257 then
                        28
                      else
                        28
                else
                  if index < 262 then
                    if index < 260 then
                      if index < 259 then
                        28
                      else
                        29
                    else
                      if index < 261 then
                        29
                      else
                        29
                  else
                    if index < 264 then
                      if index < 263 then
                        30
                      else
                        30
                    else
                      if index < 265 then
                        30
                      else
                        if index < 266 then
                          30
                        else
                          31
      else
        if index < 400 then
          if index < 333 then
            if index < 300 then
              if index < 283 then
                if index < 275 then
                  if index < 271 then
                    if index < 269 then
                      if index < 268 then
                        31
                      else
                        32
                    else
                      if index < 270 then
                        32
                      else
                        32
                  else
                    if index < 273 then
                      if index < 272 then
                        32
                      else
                        32
                    else
                      if index < 274 then
                        33
                      else
                        33
                else
                  if index < 279 then
                    if index < 277 then
                      if index < 276 then
                        33
                      else
                        33
                    else
                      if index < 278 then
                        34
                      else
                        34
                  else
                    if index < 281 then
                      if index < 280 then
                        34
                      else
                        34
                    else
                      if index < 282 then
                        35
                      else
                        35
              else
                if index < 291 then
                  if index < 287 then
                    if index < 285 then
                      if index < 284 then
                        35
                      else
                        36
                    else
                      if index < 286 then
                        36
                      else
                        36
                  else
                    if index < 289 then
                      if index < 288 then
                        36
                      else
                        37
                    else
                      if index < 290 then
                        37
                      else
                        37
                else
                  if index < 295 then
                    if index < 293 then
                      if index < 292 then
                        38
                      else
                        38
                    else
                      if index < 294 then
                        38
                      else
                        39
                  else
                    if index < 297 then
                      if index < 296 then
                        39
                      else
                        40
                    else
                      if index < 298 then
                        40
                      else
                        if index < 299 then
                          40
                        else
                          40
            else
              if index < 316 then
                if index < 308 then
                  if index < 304 then
                    if index < 302 then
                      if index < 301 then
                        40
                      else
                        41
                    else
                      if index < 303 then
                        41
                      else
                        42
                  else
                    if index < 306 then
                      if index < 305 then
                        42
                      else
                        42
                    else
                      if index < 307 then
                        42
                      else
                        43
                else
                  if index < 312 then
                    if index < 310 then
                      if index < 309 then
                        44
                      else
                        44
                    else
                      if index < 311 then
                        44
                      else
                        44
                  else
                    if index < 314 then
                      if index < 313 then
                        45
                      else
                        46
                    else
                      if index < 315 then
                        46
                      else
                        46
              else
                if index < 324 then
                  if index < 320 then
                    if index < 318 then
                      if index < 317 then
                        48
                      else
                        48
                    else
                      if index < 319 then
                        48
                      else
                        49
                  else
                    if index < 322 then
                      if index < 321 then
                        49
                      else
                        50
                    else
                      if index < 323 then
                        50
                      else
                        51
                else
                  if index < 328 then
                    if index < 326 then
                      if index < 325 then
                        52
                      else
                        52
                    else
                      if index < 327 then
                        53
                      else
                        54
                  else
                    if index < 330 then
                      if index < 329 then
                        56
                      else
                        56
                    else
                      if index < 331 then
                        56
                      else
                        if index < 332 then
                          56
                        else
                          57
          else
            if index < 366 then
              if index < 349 then
                if index < 341 then
                  if index < 337 then
                    if index < 335 then
                      if index < 334 then
                        57
                      else
                        57
                    else
                      if index < 336 then
                        57
                      else
                        58
                  else
                    if index < 339 then
                      if index < 338 then
                        58
                      else
                        58
                    else
                      if index < 340 then
                        59
                      else
                        59
                else
                  if index < 345 then
                    if index < 343 then
                      if index < 342 then
                        59
                      else
                        60
                    else
                      if index < 344 then
                        60
                      else
                        60
                  else
                    if index < 347 then
                      if index < 346 then
                        61
                      else
                        61
                    else
                      if index < 348 then
                        61
                      else
                        62
              else
                if index < 357 then
                  if index < 353 then
                    if index < 351 then
                      if index < 350 then
                        62
                      else
                        63
                    else
                      if index < 352 then
                        63
                      else
                        64
                  else
                    if index < 355 then
                      if index < 354 then
                        64
                      else
                        65
                    else
                      if index < 356 then
                        66
                      else
                        68
                else
                  if index < 361 then
                    if index < 359 then
                      if index < 358 then
                        68
                      else
                        68
                    else
                      if index < 360 then
                        69
                      else
                        69
                  else
                    if index < 363 then
                      if index < 362 then
                        70
                      else
                        70
                    else
                      if index < 364 then
                        71
                      else
                        if index < 365 then
                          72
                        else
                          72
            else
              if index < 383 then
                if index < 374 then
                  if index < 370 then
                    if index < 368 then
                      if index < 367 then
                        73
                      else
                        74
                    else
                      if index < 369 then
                        76
                      else
                        76
                  else
                    if index < 372 then
                      if index < 371 then
                        76
                      else
                        76
                    else
                      if index < 373 then
                        77
                      else
                        77
                else
                  if index < 378 then
                    if index < 376 then
                      if index < 375 then
                        77
                      else
                        78
                    else
                      if index < 377 then
                        78
                      else
                        78
                  else
                    if index < 380 then
                      if index < 379 then
                        79
                      else
                        79
                    else
                      if index < 381 then
                        80
                      else
                        if index < 382 then
                          80
                        else
                          80
              else
                if index < 391 then
                  if index < 387 then
                    if index < 385 then
                      if index < 384 then
                        80
                      else
                        80
                    else
                      if index < 386 then
                        81
                      else
                        81
                  else
                    if index < 389 then
                      if index < 388 then
                        81
                      else
                        81
                    else
                      if index < 390 then
                        82
                      else
                        82
                else
                  if index < 395 then
                    if index < 393 then
                      if index < 392 then
                        82
                      else
                        82
                    else
                      if index < 394 then
                        83
                      else
                        83
                  else
                    if index < 397 then
                      if index < 396 then
                        83
                      else
                        84
                    else
                      if index < 398 then
                        84
                      else
                        if index < 399 then
                          84
                        else
                          84
        else
          if index < 467 then
            if index < 433 then
              if index < 416 then
                if index < 408 then
                  if index < 404 then
                    if index < 402 then
                      if index < 401 then
                        85
                      else
                        85
                    else
                      if index < 403 then
                        85
                      else
                        86
                  else
                    if index < 406 then
                      if index < 405 then
                        86
                      else
                        86
                    else
                      if index < 407 then
                        87
                      else
                        87
                else
                  if index < 412 then
                    if index < 410 then
                      if index < 409 then
                        88
                      else
                        88
                    else
                      if index < 411 then
                        88
                      else
                        89
                  else
                    if index < 414 then
                      if index < 413 then
                        89
                      else
                        90
                    else
                      if index < 415 then
                        90
                      else
                        91
              else
                if index < 424 then
                  if index < 420 then
                    if index < 418 then
                      if index < 417 then
                        92
                      else
                        92
                    else
                      if index < 419 then
                        92
                      else
                        92
                  else
                    if index < 422 then
                      if index < 421 then
                        92
                      else
                        92
                    else
                      if index < 423 then
                        93
                      else
                        93
                else
                  if index < 428 then
                    if index < 426 then
                      if index < 425 then
                        93
                      else
                        93
                    else
                      if index < 427 then
                        94
                      else
                        94
                  else
                    if index < 430 then
                      if index < 429 then
                        94
                      else
                        94
                    else
                      if index < 431 then
                        94
                      else
                        if index < 432 then
                          95
                        else
                          95
            else
              if index < 450 then
                if index < 441 then
                  if index < 437 then
                    if index < 435 then
                      if index < 434 then
                        95
                      else
                        96
                    else
                      if index < 436 then
                        96
                      else
                        96
                  else
                    if index < 439 then
                      if index < 438 then
                        96
                      else
                        96
                    else
                      if index < 440 then
                        97
                      else
                        97
                else
                  if index < 445 then
                    if index < 443 then
                      if index < 442 then
                        97
                      else
                        98
                    else
                      if index < 444 then
                        98
                      else
                        98
                  else
                    if index < 447 then
                      if index < 446 then
                        98
                      else
                        99
                    else
                      if index < 448 then
                        99
                      else
                        if index < 449 then
                          100
                        else
                          100
              else
                if index < 458 then
                  if index < 454 then
                    if index < 452 then
                      if index < 451 then
                        100
                      else
                        100
                    else
                      if index < 453 then
                        100
                      else
                        101
                  else
                    if index < 456 then
                      if index < 455 then
                        101
                      else
                        101
                    else
                      if index < 457 then
                        101
                      else
                        102
                else
                  if index < 462 then
                    if index < 460 then
                      if index < 459 then
                        102
                      else
                        102
                    else
                      if index < 461 then
                        102
                      else
                        103
                  else
                    if index < 464 then
                      if index < 463 then
                        103
                      else
                        103
                    else
                      if index < 465 then
                        104
                      else
                        if index < 466 then
                          104
                        else
                          104
          else
            if index < 500 then
              if index < 483 then
                if index < 475 then
                  if index < 471 then
                    if index < 469 then
                      if index < 468 then
                        104
                      else
                        105
                    else
                      if index < 470 then
                        105
                      else
                        105
                  else
                    if index < 473 then
                      if index < 472 then
                        106
                      else
                        106
                    else
                      if index < 474 then
                        106
                      else
                        107
                else
                  if index < 479 then
                    if index < 477 then
                      if index < 476 then
                        107
                      else
                        108
                    else
                      if index < 478 then
                        108
                      else
                        108
                  else
                    if index < 481 then
                      if index < 480 then
                        108
                      else
                        108
                    else
                      if index < 482 then
                        109
                      else
                        109
              else
                if index < 491 then
                  if index < 487 then
                    if index < 485 then
                      if index < 484 then
                        110
                      else
                        110
                    else
                      if index < 486 then
                        110
                      else
                        110
                  else
                    if index < 489 then
                      if index < 488 then
                        111
                      else
                        112
                    else
                      if index < 490 then
                        112
                      else
                        112
                else
                  if index < 495 then
                    if index < 493 then
                      if index < 492 then
                        112
                      else
                        113
                    else
                      if index < 494 then
                        114
                      else
                        114
                  else
                    if index < 497 then
                      if index < 496 then
                        114
                      else
                        116
                    else
                      if index < 498 then
                        116
                      else
                        if index < 499 then
                          116
                        else
                          117
            else
              if index < 517 then
                if index < 508 then
                  if index < 504 then
                    if index < 502 then
                      if index < 501 then
                        117
                      else
                        118
                    else
                      if index < 503 then
                        118
                      else
                        119
                  else
                    if index < 506 then
                      if index < 505 then
                        120
                      else
                        120
                    else
                      if index < 507 then
                        121
                      else
                        122
                else
                  if index < 512 then
                    if index < 510 then
                      if index < 509 then
                        124
                      else
                        124
                    else
                      if index < 511 then
                        124
                      else
                        124
                  else
                    if index < 514 then
                      if index < 513 then
                        125
                      else
                        125
                    else
                      if index < 515 then
                        125
                      else
                        if index < 516 then
                          125
                        else
                          126
              else
                if index < 525 then
                  if index < 521 then
                    if index < 519 then
                      if index < 518 then
                        126
                      else
                        126
                    else
                      if index < 520 then
                        127
                      else
                        127
                  else
                    if index < 523 then
                      if index < 522 then
                        127
                      else
                        128
                    else
                      if index < 524 then
                        128
                      else
                        128
                else
                  if index < 529 then
                    if index < 527 then
                      if index < 526 then
                        129
                      else
                        129
                    else
                      if index < 528 then
                        129
                      else
                        130
                  else
                    if index < 531 then
                      if index < 530 then
                        130
                      else
                        131
                    else
                      if index < 532 then
                        131
                      else
                        if index < 533 then
                          132
                        else
                          132
    else
      if index < 801 then
        if index < 667 then
          if index < 600 then
            if index < 567 then
              if index < 550 then
                if index < 542 then
                  if index < 538 then
                    if index < 536 then
                      if index < 535 then
                        133
                      else
                        134
                    else
                      if index < 537 then
                        136
                      else
                        136
                  else
                    if index < 540 then
                      if index < 539 then
                        136
                      else
                        137
                    else
                      if index < 541 then
                        137
                      else
                        138
                else
                  if index < 546 then
                    if index < 544 then
                      if index < 543 then
                        138
                      else
                        139
                    else
                      if index < 545 then
                        140
                      else
                        140
                  else
                    if index < 548 then
                      if index < 547 then
                        141
                      else
                        142
                    else
                      if index < 549 then
                        0
                      else
                        0
              else
                if index < 558 then
                  if index < 554 then
                    if index < 552 then
                      if index < 551 then
                        0
                      else
                        0
                    else
                      if index < 553 then
                        0
                      else
                        0
                  else
                    if index < 556 then
                      if index < 555 then
                        0
                      else
                        0
                    else
                      if index < 557 then
                        0
                      else
                        1
                else
                  if index < 562 then
                    if index < 560 then
                      if index < 559 then
                        1
                      else
                        1
                    else
                      if index < 561 then
                        1
                      else
                        1
                  else
                    if index < 564 then
                      if index < 563 then
                        1
                      else
                        1
                    else
                      if index < 565 then
                        1
                      else
                        if index < 566 then
                          1
                        else
                          1
            else
              if index < 583 then
                if index < 575 then
                  if index < 571 then
                    if index < 569 then
                      if index < 568 then
                        1
                      else
                        1
                    else
                      if index < 570 then
                        2
                      else
                        2
                  else
                    if index < 573 then
                      if index < 572 then
                        2
                      else
                        2
                    else
                      if index < 574 then
                        2
                      else
                        2
                else
                  if index < 579 then
                    if index < 577 then
                      if index < 576 then
                        3
                      else
                        3
                    else
                      if index < 578 then
                        3
                      else
                        3
                  else
                    if index < 581 then
                      if index < 580 then
                        3
                      else
                        3
                    else
                      if index < 582 then
                        3
                      else
                        4
              else
                if index < 591 then
                  if index < 587 then
                    if index < 585 then
                      if index < 584 then
                        4
                      else
                        4
                    else
                      if index < 586 then
                        4
                      else
                        4
                  else
                    if index < 589 then
                      if index < 588 then
                        5
                      else
                        5
                    else
                      if index < 590 then
                        5
                      else
                        5
                else
                  if index < 595 then
                    if index < 593 then
                      if index < 592 then
                        5
                      else
                        5
                    else
                      if index < 594 then
                        5
                      else
                        5
                  else
                    if index < 597 then
                      if index < 596 then
                        6
                      else
                        6
                    else
                      if index < 598 then
                        6
                      else
                        if index < 599 then
                          7
                        else
                          7
          else
            if index < 633 then
              if index < 616 then
                if index < 608 then
                  if index < 604 then
                    if index < 602 then
                      if index < 601 then
                        7
                      else
                        7
                    else
                      if index < 603 then
                        8
                      else
                        8
                  else
                    if index < 606 then
                      if index < 605 then
                        8
                      else
                        8
                    else
                      if index < 607 then
                        8
                      else
                        8
                else
                  if index < 612 then
                    if index < 610 then
                      if index < 609 then
                        8
                      else
                        8
                    else
                      if index < 611 then
                        8
                      else
                        8
                  else
                    if index < 614 then
                      if index < 613 then
                        8
                      else
                        9
                    else
                      if index < 615 then
                        9
                      else
                        9
              else
                if index < 624 then
                  if index < 620 then
                    if index < 618 then
                      if index < 617 then
                        9
                      else
                        9
                    else
                      if index < 619 then
                        9
                      else
                        9
                  else
                    if index < 622 then
                      if index < 621 then
                        10
                      else
                        10
                    else
                      if index < 623 then
                        10
                      else
                        10
                else
                  if index < 628 then
                    if index < 626 then
                      if index < 625 then
                        10
                      else
                        10
                    else
                      if index < 627 then
                        10
                      else
                        11
                  else
                    if index < 630 then
                      if index < 629 then
                        11
                      else
                        11
                    else
                      if index < 631 then
                        12
                      else
                        if index < 632 then
                          12
                        else
                          12
            else
              if index < 650 then
                if index < 641 then
                  if index < 637 then
                    if index < 635 then
                      if index < 634 then
                        12
                      else
                        12
                    else
                      if index < 636 then
                        12
                      else
                        12
                  else
                    if index < 639 then
                      if index < 638 then
                        13
                      else
                        13
                    else
                      if index < 640 then
                        13
                      else
                        13
                else
                  if index < 645 then
                    if index < 643 then
                      if index < 642 then
                        14
                      else
                        14
                    else
                      if index < 644 then
                        14
                      else
                        14
                  else
                    if index < 647 then
                      if index < 646 then
                        15
                      else
                        16
                    else
                      if index < 648 then
                        16
                      else
                        if index < 649 then
                          16
                        else
                          16
              else
                if index < 658 then
                  if index < 654 then
                    if index < 652 then
                      if index < 651 then
                        16
                      else
                        17
                    else
                      if index < 653 then
                        17
                      else
                        18
                  else
                    if index < 656 then
                      if index < 655 then
                        18
                      else
                        20
                    else
                      if index < 657 then
                        20
                      else
                        20
                else
                  if index < 662 then
                    if index < 660 then
                      if index < 659 then
                        21
                      else
                        22
                    else
                      if index < 661 then
                        24
                      else
                        24
                  else
                    if index < 664 then
                      if index < 663 then
                        24
                      else
                        24
                    else
                      if index < 665 then
                        24
                      else
                        if index < 666 then
                          24
                        else
                          24
        else
          if index < 734 then
            if index < 700 then
              if index < 683 then
                if index < 675 then
                  if index < 671 then
                    if index < 669 then
                      if index < 668 then
                        24
                      else
                        24
                    else
                      if index < 670 then
                        24
                      else
                        25
                  else
                    if index < 673 then
                      if index < 672 then
                        25
                      else
                        25
                    else
                      if index < 674 then
                        25
                      else
                        25
                else
                  if index < 679 then
                    if index < 677 then
                      if index < 676 then
                        26
                      else
                        26
                    else
                      if index < 678 then
                        26
                      else
                        26
                  else
                    if index < 681 then
                      if index < 680 then
                        26
                      else
                        26
                    else
                      if index < 682 then
                        27
                      else
                        27
              else
                if index < 691 then
                  if index < 687 then
                    if index < 685 then
                      if index < 684 then
                        27
                      else
                        28
                    else
                      if index < 686 then
                        28
                      else
                        28
                  else
                    if index < 689 then
                      if index < 688 then
                        28
                      else
                        28
                    else
                      if index < 690 then
                        28
                      else
                        28
                else
                  if index < 695 then
                    if index < 693 then
                      if index < 692 then
                        28
                      else
                        29
                    else
                      if index < 694 then
                        29
                      else
                        30
                  else
                    if index < 697 then
                      if index < 696 then
                        30
                      else
                        30
                    else
                      if index < 698 then
                        30
                      else
                        if index < 699 then
                          31
                        else
                          32
            else
              if index < 717 then
                if index < 708 then
                  if index < 704 then
                    if index < 702 then
                      if index < 701 then
                        32
                      else
                        32
                    else
                      if index < 703 then
                        32
                      else
                        32
                  else
                    if index < 706 then
                      if index < 705 then
                        32
                      else
                        32
                    else
                      if index < 707 then
                        32
                      else
                        33
                else
                  if index < 712 then
                    if index < 710 then
                      if index < 709 then
                        33
                      else
                        33
                    else
                      if index < 711 then
                        33
                      else
                        33
                  else
                    if index < 714 then
                      if index < 713 then
                        34
                      else
                        34
                    else
                      if index < 715 then
                        34
                      else
                        if index < 716 then
                          34
                        else
                          34
              else
                if index < 725 then
                  if index < 721 then
                    if index < 719 then
                      if index < 718 then
                        35
                      else
                        35
                    else
                      if index < 720 then
                        36
                      else
                        36
                  else
                    if index < 723 then
                      if index < 722 then
                        36
                      else
                        36
                    else
                      if index < 724 then
                        37
                      else
                        37
                else
                  if index < 729 then
                    if index < 727 then
                      if index < 726 then
                        38
                      else
                        38
                    else
                      if index < 728 then
                        40
                      else
                        40
                  else
                    if index < 731 then
                      if index < 730 then
                        40
                      else
                        40
                    else
                      if index < 732 then
                        40
                      else
                        if index < 733 then
                          40
                        else
                          41
          else
            if index < 767 then
              if index < 750 then
                if index < 742 then
                  if index < 738 then
                    if index < 736 then
                      if index < 735 then
                        42
                      else
                        42
                    else
                      if index < 737 then
                        42
                      else
                        44
                  else
                    if index < 740 then
                      if index < 739 then
                        44
                      else
                        44
                    else
                      if index < 741 then
                        46
                      else
                        48
                else
                  if index < 746 then
                    if index < 744 then
                      if index < 743 then
                        48
                      else
                        48
                    else
                      if index < 745 then
                        49
                      else
                        50
                  else
                    if index < 748 then
                      if index < 747 then
                        52
                      else
                        56
                    else
                      if index < 749 then
                        56
                      else
                        56
              else
                if index < 758 then
                  if index < 754 then
                    if index < 752 then
                      if index < 751 then
                        56
                      else
                        56
                    else
                      if index < 753 then
                        57
                      else
                        57
                  else
                    if index < 756 then
                      if index < 755 then
                        57
                      else
                        57
                    else
                      if index < 757 then
                        57
                      else
                        58
                else
                  if index < 762 then
                    if index < 760 then
                      if index < 759 then
                        58
                      else
                        58
                    else
                      if index < 761 then
                        59
                      else
                        59
                  else
                    if index < 764 then
                      if index < 763 then
                        60
                      else
                        60
                    else
                      if index < 765 then
                        61
                      else
                        if index < 766 then
                          61
                        else
                          62
            else
              if index < 784 then
                if index < 775 then
                  if index < 771 then
                    if index < 769 then
                      if index < 768 then
                        64
                      else
                        68
                    else
                      if index < 770 then
                        68
                      else
                        68
                  else
                    if index < 773 then
                      if index < 772 then
                        69
                      else
                        70
                    else
                      if index < 774 then
                        72
                      else
                        76
                else
                  if index < 779 then
                    if index < 777 then
                      if index < 776 then
                        76
                      else
                        76
                    else
                      if index < 778 then
                        76
                      else
                        76
                  else
                    if index < 781 then
                      if index < 780 then
                        76
                      else
                        77
                    else
                      if index < 782 then
                        77
                      else
                        if index < 783 then
                          77
                        else
                          78
              else
                if index < 792 then
                  if index < 788 then
                    if index < 786 then
                      if index < 785 then
                        78
                      else
                        78
                    else
                      if index < 787 then
                        79
                      else
                        80
                  else
                    if index < 790 then
                      if index < 789 then
                        80
                      else
                        80
                    else
                      if index < 791 then
                        80
                      else
                        80
                else
                  if index < 796 then
                    if index < 794 then
                      if index < 793 then
                        80
                      else
                        80
                    else
                      if index < 795 then
                        80
                      else
                        80
                  else
                    if index < 798 then
                      if index < 797 then
                        81
                      else
                        81
                    else
                      if index < 799 then
                        81
                      else
                        if index < 800 then
                          81
                        else
                          81
      else
        if index < 935 then
          if index < 868 then
            if index < 834 then
              if index < 817 then
                if index < 809 then
                  if index < 805 then
                    if index < 803 then
                      if index < 802 then
                        82
                      else
                        82
                    else
                      if index < 804 then
                        82
                      else
                        82
                  else
                    if index < 807 then
                      if index < 806 then
                        82
                      else
                        82
                    else
                      if index < 808 then
                        83
                      else
                        83
                else
                  if index < 813 then
                    if index < 811 then
                      if index < 810 then
                        83
                      else
                        84
                    else
                      if index < 812 then
                        84
                      else
                        84
                  else
                    if index < 815 then
                      if index < 814 then
                        84
                      else
                        84
                    else
                      if index < 816 then
                        85
                      else
                        85
              else
                if index < 825 then
                  if index < 821 then
                    if index < 819 then
                      if index < 818 then
                        86
                      else
                        86
                    else
                      if index < 820 then
                        88
                      else
                        88
                  else
                    if index < 823 then
                      if index < 822 then
                        88
                      else
                        89
                    else
                      if index < 824 then
                        90
                      else
                        92
                else
                  if index < 829 then
                    if index < 827 then
                      if index < 826 then
                        92
                      else
                        92
                    else
                      if index < 828 then
                        92
                      else
                        92
                  else
                    if index < 831 then
                      if index < 830 then
                        92
                      else
                        92
                    else
                      if index < 832 then
                        92
                      else
                        if index < 833 then
                          92
                        else
                          92
            else
              if index < 851 then
                if index < 842 then
                  if index < 838 then
                    if index < 836 then
                      if index < 835 then
                        93
                      else
                        93
                    else
                      if index < 837 then
                        93
                      else
                        93
                  else
                    if index < 840 then
                      if index < 839 then
                        93
                      else
                        94
                    else
                      if index < 841 then
                        94
                      else
                        94
                else
                  if index < 846 then
                    if index < 844 then
                      if index < 843 then
                        94
                      else
                        94
                    else
                      if index < 845 then
                        94
                      else
                        95
                  else
                    if index < 848 then
                      if index < 847 then
                        95
                      else
                        95
                    else
                      if index < 849 then
                        96
                      else
                        if index < 850 then
                          96
                        else
                          96
              else
                if index < 859 then
                  if index < 855 then
                    if index < 853 then
                      if index < 852 then
                        96
                      else
                        96
                    else
                      if index < 854 then
                        96
                      else
                        96
                  else
                    if index < 857 then
                      if index < 856 then
                        96
                      else
                        97
                    else
                      if index < 858 then
                        97
                      else
                        98
                else
                  if index < 863 then
                    if index < 861 then
                      if index < 860 then
                        98
                      else
                        98
                    else
                      if index < 862 then
                        98
                      else
                        99
                  else
                    if index < 865 then
                      if index < 864 then
                        100
                      else
                        100
                    else
                      if index < 866 then
                        100
                      else
                        if index < 867 then
                          100
                        else
                          100
          else
            if index < 901 then
              if index < 884 then
                if index < 876 then
                  if index < 872 then
                    if index < 870 then
                      if index < 869 then
                        100
                      else
                        100
                    else
                      if index < 871 then
                        100
                      else
                        101
                  else
                    if index < 874 then
                      if index < 873 then
                        101
                      else
                        101
                    else
                      if index < 875 then
                        101
                      else
                        101
                else
                  if index < 880 then
                    if index < 878 then
                      if index < 877 then
                        102
                      else
                        102
                    else
                      if index < 879 then
                        102
                      else
                        102
                  else
                    if index < 882 then
                      if index < 881 then
                        102
                      else
                        103
                    else
                      if index < 883 then
                        103
                      else
                        104
              else
                if index < 892 then
                  if index < 888 then
                    if index < 886 then
                      if index < 885 then
                        104
                      else
                        104
                    else
                      if index < 887 then
                        104
                      else
                        105
                  else
                    if index < 890 then
                      if index < 889 then
                        105
                      else
                        106
                    else
                      if index < 891 then
                        106
                      else
                        108
                else
                  if index < 896 then
                    if index < 894 then
                      if index < 893 then
                        108
                      else
                        108
                    else
                      if index < 895 then
                        108
                      else
                        108
                  else
                    if index < 898 then
                      if index < 897 then
                        108
                      else
                        109
                    else
                      if index < 899 then
                        110
                      else
                        if index < 900 then
                          110
                        else
                          110
            else
              if index < 918 then
                if index < 909 then
                  if index < 905 then
                    if index < 903 then
                      if index < 902 then
                        112
                      else
                        112
                    else
                      if index < 904 then
                        112
                      else
                        114
                  else
                    if index < 907 then
                      if index < 906 then
                        116
                      else
                        116
                    else
                      if index < 908 then
                        116
                      else
                        117
                else
                  if index < 913 then
                    if index < 911 then
                      if index < 910 then
                        118
                      else
                        120
                    else
                      if index < 912 then
                        124
                      else
                        124
                  else
                    if index < 915 then
                      if index < 914 then
                        124
                      else
                        124
                    else
                      if index < 916 then
                        124
                      else
                        if index < 917 then
                          125
                        else
                          125
              else
                if index < 926 then
                  if index < 922 then
                    if index < 920 then
                      if index < 919 then
                        125
                      else
                        125
                    else
                      if index < 921 then
                        125
                      else
                        126
                  else
                    if index < 924 then
                      if index < 923 then
                        126
                      else
                        126
                    else
                      if index < 925 then
                        127
                      else
                        127
                else
                  if index < 930 then
                    if index < 928 then
                      if index < 927 then
                        128
                      else
                        128
                    else
                      if index < 929 then
                        129
                      else
                        129
                  else
                    if index < 932 then
                      if index < 931 then
                        130
                      else
                        132
                    else
                      if index < 933 then
                        136
                      else
                        if index < 934 then
                          136
                        else
                          136
        else
          if index < 1002 then
            if index < 968 then
              if index < 951 then
                if index < 943 then
                  if index < 939 then
                    if index < 937 then
                      if index < 936 then
                        137
                      else
                        138
                    else
                      if index < 938 then
                        140
                      else
                        0
                  else
                    if index < 941 then
                      if index < 940 then
                        0
                      else
                        0
                    else
                      if index < 942 then
                        0
                      else
                        0
                else
                  if index < 947 then
                    if index < 945 then
                      if index < 944 then
                        0
                      else
                        1
                    else
                      if index < 946 then
                        1
                      else
                        1
                  else
                    if index < 949 then
                      if index < 948 then
                        1
                      else
                        1
                    else
                      if index < 950 then
                        1
                      else
                        1
              else
                if index < 959 then
                  if index < 955 then
                    if index < 953 then
                      if index < 952 then
                        2
                      else
                        2
                    else
                      if index < 954 then
                        2
                      else
                        3
                  else
                    if index < 957 then
                      if index < 956 then
                        3
                      else
                        4
                    else
                      if index < 958 then
                        4
                      else
                        5
                else
                  if index < 963 then
                    if index < 961 then
                      if index < 960 then
                        5
                      else
                        5
                    else
                      if index < 962 then
                        5
                      else
                        6
                  else
                    if index < 965 then
                      if index < 964 then
                        7
                      else
                        8
                    else
                      if index < 966 then
                        8
                      else
                        if index < 967 then
                          8
                        else
                          8
            else
              if index < 985 then
                if index < 976 then
                  if index < 972 then
                    if index < 970 then
                      if index < 969 then
                        8
                      else
                        8
                    else
                      if index < 971 then
                        9
                      else
                        9
                  else
                    if index < 974 then
                      if index < 973 then
                        9
                      else
                        10
                    else
                      if index < 975 then
                        10
                      else
                        10
                else
                  if index < 980 then
                    if index < 978 then
                      if index < 977 then
                        12
                      else
                        12
                    else
                      if index < 979 then
                        12
                      else
                        13
                  else
                    if index < 982 then
                      if index < 981 then
                        14
                      else
                        16
                    else
                      if index < 983 then
                        16
                      else
                        if index < 984 then
                          20
                        else
                          24
              else
                if index < 993 then
                  if index < 989 then
                    if index < 987 then
                      if index < 986 then
                        24
                      else
                        24
                    else
                      if index < 988 then
                        24
                      else
                        24
                  else
                    if index < 991 then
                      if index < 990 then
                        25
                      else
                        25
                    else
                      if index < 992 then
                        26
                      else
                        26
                else
                  if index < 997 then
                    if index < 995 then
                      if index < 994 then
                        27
                      else
                        28
                    else
                      if index < 996 then
                        28
                      else
                        28
                  else
                    if index < 999 then
                      if index < 998 then
                        28
                      else
                        30
                    else
                      if index < 1000 then
                        32
                      else
                        if index < 1001 then
                          32
                        else
                          32
          else
            if index < 1035 then
              if index < 1018 then
                if index < 1010 then
                  if index < 1006 then
                    if index < 1004 then
                      if index < 1003 then
                        32
                      else
                        33
                    else
                      if index < 1005 then
                        33
                      else
                        34
                  else
                    if index < 1008 then
                      if index < 1007 then
                        34
                      else
                        40
                    else
                      if index < 1009 then
                        40
                      else
                        44
                else
                  if index < 1014 then
                    if index < 1012 then
                      if index < 1011 then
                        48
                      else
                        56
                    else
                      if index < 1013 then
                        56
                      else
                        57
                  else
                    if index < 1016 then
                      if index < 1015 then
                        57
                      else
                        58
                    else
                      if index < 1017 then
                        68
                      else
                        76
              else
                if index < 1026 then
                  if index < 1022 then
                    if index < 1020 then
                      if index < 1019 then
                        76
                      else
                        76
                    else
                      if index < 1021 then
                        78
                      else
                        80
                  else
                    if index < 1024 then
                      if index < 1023 then
                        80
                      else
                        80
                    else
                      if index < 1025 then
                        80
                      else
                        80
                else
                  if index < 1030 then
                    if index < 1028 then
                      if index < 1027 then
                        81
                      else
                        81
                    else
                      if index < 1029 then
                        82
                      else
                        82
                  else
                    if index < 1032 then
                      if index < 1031 then
                        82
                      else
                        83
                    else
                      if index < 1033 then
                        84
                      else
                        if index < 1034 then
                          84
                        else
                          88
            else
              if index < 1052 then
                if index < 1043 then
                  if index < 1039 then
                    if index < 1037 then
                      if index < 1036 then
                        92
                      else
                        92
                    else
                      if index < 1038 then
                        92
                      else
                        92
                  else
                    if index < 1041 then
                      if index < 1040 then
                        92
                      else
                        93
                    else
                      if index < 1042 then
                        93
                      else
                        94
                else
                  if index < 1047 then
                    if index < 1045 then
                      if index < 1044 then
                        94
                      else
                        95
                    else
                      if index < 1046 then
                        96
                      else
                        96
                  else
                    if index < 1049 then
                      if index < 1048 then
                        96
                      else
                        96
                    else
                      if index < 1050 then
                        98
                      else
                        if index < 1051 then
                          100
                        else
                          100
              else
                if index < 1060 then
                  if index < 1056 then
                    if index < 1054 then
                      if index < 1053 then
                        100
                      else
                        100
                    else
                      if index < 1055 then
                        101
                      else
                        101
                  else
                    if index < 1058 then
                      if index < 1057 then
                        102
                      else
                        102
                    else
                      if index < 1059 then
                        108
                      else
                        108
                else
                  if index < 1064 then
                    if index < 1062 then
                      if index < 1061 then
                        112
                      else
                        116
                    else
                      if index < 1063 then
                        124
                      else
                        124
                  else
                    if index < 1066 then
                      if index < 1065 then
                        125
                      else
                        125
                    else
                      if index < 1067 then
                        126
                      else
                        if index < 1068 then
                          136
                        else
                          0

/-- An explicit vertex label belonging to the given catalogue face. -/
def faceAnchor (i : Fin 1069) : Fin 144 :=
  faceAnchorTable i.val

private theorem anchor0000 :
    faceAnchor (⟨0, by decide⟩ : Fin 1069) ∈ faceMask (⟨0, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0001 :
    faceAnchor (⟨1, by decide⟩ : Fin 1069) ∈ faceMask (⟨1, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0002 :
    faceAnchor (⟨2, by decide⟩ : Fin 1069) ∈ faceMask (⟨2, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0003 :
    faceAnchor (⟨3, by decide⟩ : Fin 1069) ∈ faceMask (⟨3, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0004 :
    faceAnchor (⟨4, by decide⟩ : Fin 1069) ∈ faceMask (⟨4, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0005 :
    faceAnchor (⟨5, by decide⟩ : Fin 1069) ∈ faceMask (⟨5, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0006 :
    faceAnchor (⟨6, by decide⟩ : Fin 1069) ∈ faceMask (⟨6, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0007 :
    faceAnchor (⟨7, by decide⟩ : Fin 1069) ∈ faceMask (⟨7, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0008 :
    faceAnchor (⟨8, by decide⟩ : Fin 1069) ∈ faceMask (⟨8, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0009 :
    faceAnchor (⟨9, by decide⟩ : Fin 1069) ∈ faceMask (⟨9, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0010 :
    faceAnchor (⟨10, by decide⟩ : Fin 1069) ∈ faceMask (⟨10, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0011 :
    faceAnchor (⟨11, by decide⟩ : Fin 1069) ∈ faceMask (⟨11, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0012 :
    faceAnchor (⟨12, by decide⟩ : Fin 1069) ∈ faceMask (⟨12, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0013 :
    faceAnchor (⟨13, by decide⟩ : Fin 1069) ∈ faceMask (⟨13, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0014 :
    faceAnchor (⟨14, by decide⟩ : Fin 1069) ∈ faceMask (⟨14, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0015 :
    faceAnchor (⟨15, by decide⟩ : Fin 1069) ∈ faceMask (⟨15, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0016 :
    faceAnchor (⟨16, by decide⟩ : Fin 1069) ∈ faceMask (⟨16, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0017 :
    faceAnchor (⟨17, by decide⟩ : Fin 1069) ∈ faceMask (⟨17, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0018 :
    faceAnchor (⟨18, by decide⟩ : Fin 1069) ∈ faceMask (⟨18, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0019 :
    faceAnchor (⟨19, by decide⟩ : Fin 1069) ∈ faceMask (⟨19, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0020 :
    faceAnchor (⟨20, by decide⟩ : Fin 1069) ∈ faceMask (⟨20, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0021 :
    faceAnchor (⟨21, by decide⟩ : Fin 1069) ∈ faceMask (⟨21, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0022 :
    faceAnchor (⟨22, by decide⟩ : Fin 1069) ∈ faceMask (⟨22, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0023 :
    faceAnchor (⟨23, by decide⟩ : Fin 1069) ∈ faceMask (⟨23, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0024 :
    faceAnchor (⟨24, by decide⟩ : Fin 1069) ∈ faceMask (⟨24, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0025 :
    faceAnchor (⟨25, by decide⟩ : Fin 1069) ∈ faceMask (⟨25, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0026 :
    faceAnchor (⟨26, by decide⟩ : Fin 1069) ∈ faceMask (⟨26, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0027 :
    faceAnchor (⟨27, by decide⟩ : Fin 1069) ∈ faceMask (⟨27, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0028 :
    faceAnchor (⟨28, by decide⟩ : Fin 1069) ∈ faceMask (⟨28, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0029 :
    faceAnchor (⟨29, by decide⟩ : Fin 1069) ∈ faceMask (⟨29, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0030 :
    faceAnchor (⟨30, by decide⟩ : Fin 1069) ∈ faceMask (⟨30, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0031 :
    faceAnchor (⟨31, by decide⟩ : Fin 1069) ∈ faceMask (⟨31, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0032 :
    faceAnchor (⟨32, by decide⟩ : Fin 1069) ∈ faceMask (⟨32, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0033 :
    faceAnchor (⟨33, by decide⟩ : Fin 1069) ∈ faceMask (⟨33, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0034 :
    faceAnchor (⟨34, by decide⟩ : Fin 1069) ∈ faceMask (⟨34, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0035 :
    faceAnchor (⟨35, by decide⟩ : Fin 1069) ∈ faceMask (⟨35, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0036 :
    faceAnchor (⟨36, by decide⟩ : Fin 1069) ∈ faceMask (⟨36, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0037 :
    faceAnchor (⟨37, by decide⟩ : Fin 1069) ∈ faceMask (⟨37, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0038 :
    faceAnchor (⟨38, by decide⟩ : Fin 1069) ∈ faceMask (⟨38, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0039 :
    faceAnchor (⟨39, by decide⟩ : Fin 1069) ∈ faceMask (⟨39, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0040 :
    faceAnchor (⟨40, by decide⟩ : Fin 1069) ∈ faceMask (⟨40, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0041 :
    faceAnchor (⟨41, by decide⟩ : Fin 1069) ∈ faceMask (⟨41, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0042 :
    faceAnchor (⟨42, by decide⟩ : Fin 1069) ∈ faceMask (⟨42, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0043 :
    faceAnchor (⟨43, by decide⟩ : Fin 1069) ∈ faceMask (⟨43, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0044 :
    faceAnchor (⟨44, by decide⟩ : Fin 1069) ∈ faceMask (⟨44, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0045 :
    faceAnchor (⟨45, by decide⟩ : Fin 1069) ∈ faceMask (⟨45, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0046 :
    faceAnchor (⟨46, by decide⟩ : Fin 1069) ∈ faceMask (⟨46, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0047 :
    faceAnchor (⟨47, by decide⟩ : Fin 1069) ∈ faceMask (⟨47, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0048 :
    faceAnchor (⟨48, by decide⟩ : Fin 1069) ∈ faceMask (⟨48, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0049 :
    faceAnchor (⟨49, by decide⟩ : Fin 1069) ∈ faceMask (⟨49, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0050 :
    faceAnchor (⟨50, by decide⟩ : Fin 1069) ∈ faceMask (⟨50, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0051 :
    faceAnchor (⟨51, by decide⟩ : Fin 1069) ∈ faceMask (⟨51, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0052 :
    faceAnchor (⟨52, by decide⟩ : Fin 1069) ∈ faceMask (⟨52, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0053 :
    faceAnchor (⟨53, by decide⟩ : Fin 1069) ∈ faceMask (⟨53, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0054 :
    faceAnchor (⟨54, by decide⟩ : Fin 1069) ∈ faceMask (⟨54, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0055 :
    faceAnchor (⟨55, by decide⟩ : Fin 1069) ∈ faceMask (⟨55, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0056 :
    faceAnchor (⟨56, by decide⟩ : Fin 1069) ∈ faceMask (⟨56, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0057 :
    faceAnchor (⟨57, by decide⟩ : Fin 1069) ∈ faceMask (⟨57, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0058 :
    faceAnchor (⟨58, by decide⟩ : Fin 1069) ∈ faceMask (⟨58, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0059 :
    faceAnchor (⟨59, by decide⟩ : Fin 1069) ∈ faceMask (⟨59, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0060 :
    faceAnchor (⟨60, by decide⟩ : Fin 1069) ∈ faceMask (⟨60, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0061 :
    faceAnchor (⟨61, by decide⟩ : Fin 1069) ∈ faceMask (⟨61, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0062 :
    faceAnchor (⟨62, by decide⟩ : Fin 1069) ∈ faceMask (⟨62, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0063 :
    faceAnchor (⟨63, by decide⟩ : Fin 1069) ∈ faceMask (⟨63, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0064 :
    faceAnchor (⟨64, by decide⟩ : Fin 1069) ∈ faceMask (⟨64, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0065 :
    faceAnchor (⟨65, by decide⟩ : Fin 1069) ∈ faceMask (⟨65, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0066 :
    faceAnchor (⟨66, by decide⟩ : Fin 1069) ∈ faceMask (⟨66, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0067 :
    faceAnchor (⟨67, by decide⟩ : Fin 1069) ∈ faceMask (⟨67, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0068 :
    faceAnchor (⟨68, by decide⟩ : Fin 1069) ∈ faceMask (⟨68, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0069 :
    faceAnchor (⟨69, by decide⟩ : Fin 1069) ∈ faceMask (⟨69, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0070 :
    faceAnchor (⟨70, by decide⟩ : Fin 1069) ∈ faceMask (⟨70, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0071 :
    faceAnchor (⟨71, by decide⟩ : Fin 1069) ∈ faceMask (⟨71, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0072 :
    faceAnchor (⟨72, by decide⟩ : Fin 1069) ∈ faceMask (⟨72, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0073 :
    faceAnchor (⟨73, by decide⟩ : Fin 1069) ∈ faceMask (⟨73, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0074 :
    faceAnchor (⟨74, by decide⟩ : Fin 1069) ∈ faceMask (⟨74, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0075 :
    faceAnchor (⟨75, by decide⟩ : Fin 1069) ∈ faceMask (⟨75, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0076 :
    faceAnchor (⟨76, by decide⟩ : Fin 1069) ∈ faceMask (⟨76, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0077 :
    faceAnchor (⟨77, by decide⟩ : Fin 1069) ∈ faceMask (⟨77, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0078 :
    faceAnchor (⟨78, by decide⟩ : Fin 1069) ∈ faceMask (⟨78, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0079 :
    faceAnchor (⟨79, by decide⟩ : Fin 1069) ∈ faceMask (⟨79, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0080 :
    faceAnchor (⟨80, by decide⟩ : Fin 1069) ∈ faceMask (⟨80, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0081 :
    faceAnchor (⟨81, by decide⟩ : Fin 1069) ∈ faceMask (⟨81, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0082 :
    faceAnchor (⟨82, by decide⟩ : Fin 1069) ∈ faceMask (⟨82, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0083 :
    faceAnchor (⟨83, by decide⟩ : Fin 1069) ∈ faceMask (⟨83, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0084 :
    faceAnchor (⟨84, by decide⟩ : Fin 1069) ∈ faceMask (⟨84, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0085 :
    faceAnchor (⟨85, by decide⟩ : Fin 1069) ∈ faceMask (⟨85, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0086 :
    faceAnchor (⟨86, by decide⟩ : Fin 1069) ∈ faceMask (⟨86, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0087 :
    faceAnchor (⟨87, by decide⟩ : Fin 1069) ∈ faceMask (⟨87, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0088 :
    faceAnchor (⟨88, by decide⟩ : Fin 1069) ∈ faceMask (⟨88, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0089 :
    faceAnchor (⟨89, by decide⟩ : Fin 1069) ∈ faceMask (⟨89, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0090 :
    faceAnchor (⟨90, by decide⟩ : Fin 1069) ∈ faceMask (⟨90, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0091 :
    faceAnchor (⟨91, by decide⟩ : Fin 1069) ∈ faceMask (⟨91, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0092 :
    faceAnchor (⟨92, by decide⟩ : Fin 1069) ∈ faceMask (⟨92, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0093 :
    faceAnchor (⟨93, by decide⟩ : Fin 1069) ∈ faceMask (⟨93, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0094 :
    faceAnchor (⟨94, by decide⟩ : Fin 1069) ∈ faceMask (⟨94, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0095 :
    faceAnchor (⟨95, by decide⟩ : Fin 1069) ∈ faceMask (⟨95, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0096 :
    faceAnchor (⟨96, by decide⟩ : Fin 1069) ∈ faceMask (⟨96, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0097 :
    faceAnchor (⟨97, by decide⟩ : Fin 1069) ∈ faceMask (⟨97, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0098 :
    faceAnchor (⟨98, by decide⟩ : Fin 1069) ∈ faceMask (⟨98, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0099 :
    faceAnchor (⟨99, by decide⟩ : Fin 1069) ∈ faceMask (⟨99, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0100 :
    faceAnchor (⟨100, by decide⟩ : Fin 1069) ∈ faceMask (⟨100, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0101 :
    faceAnchor (⟨101, by decide⟩ : Fin 1069) ∈ faceMask (⟨101, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0102 :
    faceAnchor (⟨102, by decide⟩ : Fin 1069) ∈ faceMask (⟨102, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0103 :
    faceAnchor (⟨103, by decide⟩ : Fin 1069) ∈ faceMask (⟨103, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0104 :
    faceAnchor (⟨104, by decide⟩ : Fin 1069) ∈ faceMask (⟨104, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0105 :
    faceAnchor (⟨105, by decide⟩ : Fin 1069) ∈ faceMask (⟨105, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0106 :
    faceAnchor (⟨106, by decide⟩ : Fin 1069) ∈ faceMask (⟨106, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0107 :
    faceAnchor (⟨107, by decide⟩ : Fin 1069) ∈ faceMask (⟨107, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0108 :
    faceAnchor (⟨108, by decide⟩ : Fin 1069) ∈ faceMask (⟨108, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0109 :
    faceAnchor (⟨109, by decide⟩ : Fin 1069) ∈ faceMask (⟨109, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0110 :
    faceAnchor (⟨110, by decide⟩ : Fin 1069) ∈ faceMask (⟨110, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0111 :
    faceAnchor (⟨111, by decide⟩ : Fin 1069) ∈ faceMask (⟨111, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0112 :
    faceAnchor (⟨112, by decide⟩ : Fin 1069) ∈ faceMask (⟨112, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0113 :
    faceAnchor (⟨113, by decide⟩ : Fin 1069) ∈ faceMask (⟨113, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0114 :
    faceAnchor (⟨114, by decide⟩ : Fin 1069) ∈ faceMask (⟨114, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0115 :
    faceAnchor (⟨115, by decide⟩ : Fin 1069) ∈ faceMask (⟨115, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0116 :
    faceAnchor (⟨116, by decide⟩ : Fin 1069) ∈ faceMask (⟨116, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0117 :
    faceAnchor (⟨117, by decide⟩ : Fin 1069) ∈ faceMask (⟨117, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0118 :
    faceAnchor (⟨118, by decide⟩ : Fin 1069) ∈ faceMask (⟨118, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0119 :
    faceAnchor (⟨119, by decide⟩ : Fin 1069) ∈ faceMask (⟨119, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0120 :
    faceAnchor (⟨120, by decide⟩ : Fin 1069) ∈ faceMask (⟨120, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0121 :
    faceAnchor (⟨121, by decide⟩ : Fin 1069) ∈ faceMask (⟨121, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0122 :
    faceAnchor (⟨122, by decide⟩ : Fin 1069) ∈ faceMask (⟨122, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0123 :
    faceAnchor (⟨123, by decide⟩ : Fin 1069) ∈ faceMask (⟨123, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0124 :
    faceAnchor (⟨124, by decide⟩ : Fin 1069) ∈ faceMask (⟨124, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0125 :
    faceAnchor (⟨125, by decide⟩ : Fin 1069) ∈ faceMask (⟨125, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0126 :
    faceAnchor (⟨126, by decide⟩ : Fin 1069) ∈ faceMask (⟨126, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0127 :
    faceAnchor (⟨127, by decide⟩ : Fin 1069) ∈ faceMask (⟨127, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0128 :
    faceAnchor (⟨128, by decide⟩ : Fin 1069) ∈ faceMask (⟨128, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0129 :
    faceAnchor (⟨129, by decide⟩ : Fin 1069) ∈ faceMask (⟨129, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0130 :
    faceAnchor (⟨130, by decide⟩ : Fin 1069) ∈ faceMask (⟨130, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0131 :
    faceAnchor (⟨131, by decide⟩ : Fin 1069) ∈ faceMask (⟨131, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0132 :
    faceAnchor (⟨132, by decide⟩ : Fin 1069) ∈ faceMask (⟨132, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0133 :
    faceAnchor (⟨133, by decide⟩ : Fin 1069) ∈ faceMask (⟨133, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0134 :
    faceAnchor (⟨134, by decide⟩ : Fin 1069) ∈ faceMask (⟨134, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0135 :
    faceAnchor (⟨135, by decide⟩ : Fin 1069) ∈ faceMask (⟨135, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0136 :
    faceAnchor (⟨136, by decide⟩ : Fin 1069) ∈ faceMask (⟨136, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0137 :
    faceAnchor (⟨137, by decide⟩ : Fin 1069) ∈ faceMask (⟨137, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0138 :
    faceAnchor (⟨138, by decide⟩ : Fin 1069) ∈ faceMask (⟨138, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0139 :
    faceAnchor (⟨139, by decide⟩ : Fin 1069) ∈ faceMask (⟨139, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0140 :
    faceAnchor (⟨140, by decide⟩ : Fin 1069) ∈ faceMask (⟨140, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0141 :
    faceAnchor (⟨141, by decide⟩ : Fin 1069) ∈ faceMask (⟨141, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0142 :
    faceAnchor (⟨142, by decide⟩ : Fin 1069) ∈ faceMask (⟨142, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0143 :
    faceAnchor (⟨143, by decide⟩ : Fin 1069) ∈ faceMask (⟨143, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0144 :
    faceAnchor (⟨144, by decide⟩ : Fin 1069) ∈ faceMask (⟨144, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0145 :
    faceAnchor (⟨145, by decide⟩ : Fin 1069) ∈ faceMask (⟨145, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0146 :
    faceAnchor (⟨146, by decide⟩ : Fin 1069) ∈ faceMask (⟨146, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0147 :
    faceAnchor (⟨147, by decide⟩ : Fin 1069) ∈ faceMask (⟨147, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0148 :
    faceAnchor (⟨148, by decide⟩ : Fin 1069) ∈ faceMask (⟨148, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0149 :
    faceAnchor (⟨149, by decide⟩ : Fin 1069) ∈ faceMask (⟨149, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0150 :
    faceAnchor (⟨150, by decide⟩ : Fin 1069) ∈ faceMask (⟨150, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0151 :
    faceAnchor (⟨151, by decide⟩ : Fin 1069) ∈ faceMask (⟨151, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0152 :
    faceAnchor (⟨152, by decide⟩ : Fin 1069) ∈ faceMask (⟨152, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0153 :
    faceAnchor (⟨153, by decide⟩ : Fin 1069) ∈ faceMask (⟨153, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0154 :
    faceAnchor (⟨154, by decide⟩ : Fin 1069) ∈ faceMask (⟨154, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0155 :
    faceAnchor (⟨155, by decide⟩ : Fin 1069) ∈ faceMask (⟨155, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0156 :
    faceAnchor (⟨156, by decide⟩ : Fin 1069) ∈ faceMask (⟨156, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0157 :
    faceAnchor (⟨157, by decide⟩ : Fin 1069) ∈ faceMask (⟨157, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0158 :
    faceAnchor (⟨158, by decide⟩ : Fin 1069) ∈ faceMask (⟨158, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0159 :
    faceAnchor (⟨159, by decide⟩ : Fin 1069) ∈ faceMask (⟨159, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0160 :
    faceAnchor (⟨160, by decide⟩ : Fin 1069) ∈ faceMask (⟨160, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0161 :
    faceAnchor (⟨161, by decide⟩ : Fin 1069) ∈ faceMask (⟨161, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0162 :
    faceAnchor (⟨162, by decide⟩ : Fin 1069) ∈ faceMask (⟨162, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0163 :
    faceAnchor (⟨163, by decide⟩ : Fin 1069) ∈ faceMask (⟨163, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0164 :
    faceAnchor (⟨164, by decide⟩ : Fin 1069) ∈ faceMask (⟨164, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0165 :
    faceAnchor (⟨165, by decide⟩ : Fin 1069) ∈ faceMask (⟨165, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0166 :
    faceAnchor (⟨166, by decide⟩ : Fin 1069) ∈ faceMask (⟨166, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0167 :
    faceAnchor (⟨167, by decide⟩ : Fin 1069) ∈ faceMask (⟨167, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0168 :
    faceAnchor (⟨168, by decide⟩ : Fin 1069) ∈ faceMask (⟨168, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0169 :
    faceAnchor (⟨169, by decide⟩ : Fin 1069) ∈ faceMask (⟨169, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0170 :
    faceAnchor (⟨170, by decide⟩ : Fin 1069) ∈ faceMask (⟨170, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0171 :
    faceAnchor (⟨171, by decide⟩ : Fin 1069) ∈ faceMask (⟨171, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0172 :
    faceAnchor (⟨172, by decide⟩ : Fin 1069) ∈ faceMask (⟨172, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0173 :
    faceAnchor (⟨173, by decide⟩ : Fin 1069) ∈ faceMask (⟨173, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0174 :
    faceAnchor (⟨174, by decide⟩ : Fin 1069) ∈ faceMask (⟨174, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0175 :
    faceAnchor (⟨175, by decide⟩ : Fin 1069) ∈ faceMask (⟨175, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0176 :
    faceAnchor (⟨176, by decide⟩ : Fin 1069) ∈ faceMask (⟨176, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0177 :
    faceAnchor (⟨177, by decide⟩ : Fin 1069) ∈ faceMask (⟨177, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0178 :
    faceAnchor (⟨178, by decide⟩ : Fin 1069) ∈ faceMask (⟨178, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0179 :
    faceAnchor (⟨179, by decide⟩ : Fin 1069) ∈ faceMask (⟨179, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0180 :
    faceAnchor (⟨180, by decide⟩ : Fin 1069) ∈ faceMask (⟨180, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0181 :
    faceAnchor (⟨181, by decide⟩ : Fin 1069) ∈ faceMask (⟨181, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0182 :
    faceAnchor (⟨182, by decide⟩ : Fin 1069) ∈ faceMask (⟨182, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0183 :
    faceAnchor (⟨183, by decide⟩ : Fin 1069) ∈ faceMask (⟨183, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0184 :
    faceAnchor (⟨184, by decide⟩ : Fin 1069) ∈ faceMask (⟨184, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0185 :
    faceAnchor (⟨185, by decide⟩ : Fin 1069) ∈ faceMask (⟨185, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0186 :
    faceAnchor (⟨186, by decide⟩ : Fin 1069) ∈ faceMask (⟨186, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0187 :
    faceAnchor (⟨187, by decide⟩ : Fin 1069) ∈ faceMask (⟨187, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0188 :
    faceAnchor (⟨188, by decide⟩ : Fin 1069) ∈ faceMask (⟨188, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0189 :
    faceAnchor (⟨189, by decide⟩ : Fin 1069) ∈ faceMask (⟨189, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0190 :
    faceAnchor (⟨190, by decide⟩ : Fin 1069) ∈ faceMask (⟨190, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0191 :
    faceAnchor (⟨191, by decide⟩ : Fin 1069) ∈ faceMask (⟨191, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0192 :
    faceAnchor (⟨192, by decide⟩ : Fin 1069) ∈ faceMask (⟨192, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0193 :
    faceAnchor (⟨193, by decide⟩ : Fin 1069) ∈ faceMask (⟨193, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0194 :
    faceAnchor (⟨194, by decide⟩ : Fin 1069) ∈ faceMask (⟨194, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0195 :
    faceAnchor (⟨195, by decide⟩ : Fin 1069) ∈ faceMask (⟨195, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0196 :
    faceAnchor (⟨196, by decide⟩ : Fin 1069) ∈ faceMask (⟨196, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0197 :
    faceAnchor (⟨197, by decide⟩ : Fin 1069) ∈ faceMask (⟨197, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0198 :
    faceAnchor (⟨198, by decide⟩ : Fin 1069) ∈ faceMask (⟨198, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0199 :
    faceAnchor (⟨199, by decide⟩ : Fin 1069) ∈ faceMask (⟨199, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0200 :
    faceAnchor (⟨200, by decide⟩ : Fin 1069) ∈ faceMask (⟨200, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0201 :
    faceAnchor (⟨201, by decide⟩ : Fin 1069) ∈ faceMask (⟨201, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0202 :
    faceAnchor (⟨202, by decide⟩ : Fin 1069) ∈ faceMask (⟨202, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0203 :
    faceAnchor (⟨203, by decide⟩ : Fin 1069) ∈ faceMask (⟨203, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0204 :
    faceAnchor (⟨204, by decide⟩ : Fin 1069) ∈ faceMask (⟨204, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0205 :
    faceAnchor (⟨205, by decide⟩ : Fin 1069) ∈ faceMask (⟨205, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0206 :
    faceAnchor (⟨206, by decide⟩ : Fin 1069) ∈ faceMask (⟨206, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0207 :
    faceAnchor (⟨207, by decide⟩ : Fin 1069) ∈ faceMask (⟨207, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0208 :
    faceAnchor (⟨208, by decide⟩ : Fin 1069) ∈ faceMask (⟨208, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0209 :
    faceAnchor (⟨209, by decide⟩ : Fin 1069) ∈ faceMask (⟨209, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0210 :
    faceAnchor (⟨210, by decide⟩ : Fin 1069) ∈ faceMask (⟨210, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0211 :
    faceAnchor (⟨211, by decide⟩ : Fin 1069) ∈ faceMask (⟨211, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0212 :
    faceAnchor (⟨212, by decide⟩ : Fin 1069) ∈ faceMask (⟨212, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0213 :
    faceAnchor (⟨213, by decide⟩ : Fin 1069) ∈ faceMask (⟨213, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0214 :
    faceAnchor (⟨214, by decide⟩ : Fin 1069) ∈ faceMask (⟨214, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0215 :
    faceAnchor (⟨215, by decide⟩ : Fin 1069) ∈ faceMask (⟨215, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0216 :
    faceAnchor (⟨216, by decide⟩ : Fin 1069) ∈ faceMask (⟨216, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0217 :
    faceAnchor (⟨217, by decide⟩ : Fin 1069) ∈ faceMask (⟨217, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0218 :
    faceAnchor (⟨218, by decide⟩ : Fin 1069) ∈ faceMask (⟨218, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0219 :
    faceAnchor (⟨219, by decide⟩ : Fin 1069) ∈ faceMask (⟨219, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0220 :
    faceAnchor (⟨220, by decide⟩ : Fin 1069) ∈ faceMask (⟨220, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0221 :
    faceAnchor (⟨221, by decide⟩ : Fin 1069) ∈ faceMask (⟨221, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0222 :
    faceAnchor (⟨222, by decide⟩ : Fin 1069) ∈ faceMask (⟨222, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0223 :
    faceAnchor (⟨223, by decide⟩ : Fin 1069) ∈ faceMask (⟨223, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0224 :
    faceAnchor (⟨224, by decide⟩ : Fin 1069) ∈ faceMask (⟨224, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0225 :
    faceAnchor (⟨225, by decide⟩ : Fin 1069) ∈ faceMask (⟨225, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0226 :
    faceAnchor (⟨226, by decide⟩ : Fin 1069) ∈ faceMask (⟨226, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0227 :
    faceAnchor (⟨227, by decide⟩ : Fin 1069) ∈ faceMask (⟨227, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0228 :
    faceAnchor (⟨228, by decide⟩ : Fin 1069) ∈ faceMask (⟨228, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0229 :
    faceAnchor (⟨229, by decide⟩ : Fin 1069) ∈ faceMask (⟨229, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0230 :
    faceAnchor (⟨230, by decide⟩ : Fin 1069) ∈ faceMask (⟨230, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0231 :
    faceAnchor (⟨231, by decide⟩ : Fin 1069) ∈ faceMask (⟨231, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0232 :
    faceAnchor (⟨232, by decide⟩ : Fin 1069) ∈ faceMask (⟨232, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0233 :
    faceAnchor (⟨233, by decide⟩ : Fin 1069) ∈ faceMask (⟨233, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0234 :
    faceAnchor (⟨234, by decide⟩ : Fin 1069) ∈ faceMask (⟨234, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0235 :
    faceAnchor (⟨235, by decide⟩ : Fin 1069) ∈ faceMask (⟨235, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0236 :
    faceAnchor (⟨236, by decide⟩ : Fin 1069) ∈ faceMask (⟨236, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0237 :
    faceAnchor (⟨237, by decide⟩ : Fin 1069) ∈ faceMask (⟨237, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0238 :
    faceAnchor (⟨238, by decide⟩ : Fin 1069) ∈ faceMask (⟨238, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0239 :
    faceAnchor (⟨239, by decide⟩ : Fin 1069) ∈ faceMask (⟨239, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0240 :
    faceAnchor (⟨240, by decide⟩ : Fin 1069) ∈ faceMask (⟨240, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0241 :
    faceAnchor (⟨241, by decide⟩ : Fin 1069) ∈ faceMask (⟨241, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0242 :
    faceAnchor (⟨242, by decide⟩ : Fin 1069) ∈ faceMask (⟨242, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0243 :
    faceAnchor (⟨243, by decide⟩ : Fin 1069) ∈ faceMask (⟨243, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0244 :
    faceAnchor (⟨244, by decide⟩ : Fin 1069) ∈ faceMask (⟨244, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0245 :
    faceAnchor (⟨245, by decide⟩ : Fin 1069) ∈ faceMask (⟨245, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0246 :
    faceAnchor (⟨246, by decide⟩ : Fin 1069) ∈ faceMask (⟨246, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0247 :
    faceAnchor (⟨247, by decide⟩ : Fin 1069) ∈ faceMask (⟨247, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0248 :
    faceAnchor (⟨248, by decide⟩ : Fin 1069) ∈ faceMask (⟨248, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0249 :
    faceAnchor (⟨249, by decide⟩ : Fin 1069) ∈ faceMask (⟨249, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0250 :
    faceAnchor (⟨250, by decide⟩ : Fin 1069) ∈ faceMask (⟨250, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0251 :
    faceAnchor (⟨251, by decide⟩ : Fin 1069) ∈ faceMask (⟨251, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0252 :
    faceAnchor (⟨252, by decide⟩ : Fin 1069) ∈ faceMask (⟨252, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0253 :
    faceAnchor (⟨253, by decide⟩ : Fin 1069) ∈ faceMask (⟨253, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0254 :
    faceAnchor (⟨254, by decide⟩ : Fin 1069) ∈ faceMask (⟨254, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0255 :
    faceAnchor (⟨255, by decide⟩ : Fin 1069) ∈ faceMask (⟨255, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0256 :
    faceAnchor (⟨256, by decide⟩ : Fin 1069) ∈ faceMask (⟨256, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0257 :
    faceAnchor (⟨257, by decide⟩ : Fin 1069) ∈ faceMask (⟨257, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0258 :
    faceAnchor (⟨258, by decide⟩ : Fin 1069) ∈ faceMask (⟨258, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0259 :
    faceAnchor (⟨259, by decide⟩ : Fin 1069) ∈ faceMask (⟨259, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0260 :
    faceAnchor (⟨260, by decide⟩ : Fin 1069) ∈ faceMask (⟨260, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0261 :
    faceAnchor (⟨261, by decide⟩ : Fin 1069) ∈ faceMask (⟨261, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0262 :
    faceAnchor (⟨262, by decide⟩ : Fin 1069) ∈ faceMask (⟨262, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0263 :
    faceAnchor (⟨263, by decide⟩ : Fin 1069) ∈ faceMask (⟨263, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0264 :
    faceAnchor (⟨264, by decide⟩ : Fin 1069) ∈ faceMask (⟨264, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0265 :
    faceAnchor (⟨265, by decide⟩ : Fin 1069) ∈ faceMask (⟨265, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0266 :
    faceAnchor (⟨266, by decide⟩ : Fin 1069) ∈ faceMask (⟨266, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0267 :
    faceAnchor (⟨267, by decide⟩ : Fin 1069) ∈ faceMask (⟨267, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0268 :
    faceAnchor (⟨268, by decide⟩ : Fin 1069) ∈ faceMask (⟨268, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0269 :
    faceAnchor (⟨269, by decide⟩ : Fin 1069) ∈ faceMask (⟨269, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0270 :
    faceAnchor (⟨270, by decide⟩ : Fin 1069) ∈ faceMask (⟨270, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0271 :
    faceAnchor (⟨271, by decide⟩ : Fin 1069) ∈ faceMask (⟨271, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0272 :
    faceAnchor (⟨272, by decide⟩ : Fin 1069) ∈ faceMask (⟨272, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0273 :
    faceAnchor (⟨273, by decide⟩ : Fin 1069) ∈ faceMask (⟨273, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0274 :
    faceAnchor (⟨274, by decide⟩ : Fin 1069) ∈ faceMask (⟨274, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0275 :
    faceAnchor (⟨275, by decide⟩ : Fin 1069) ∈ faceMask (⟨275, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0276 :
    faceAnchor (⟨276, by decide⟩ : Fin 1069) ∈ faceMask (⟨276, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0277 :
    faceAnchor (⟨277, by decide⟩ : Fin 1069) ∈ faceMask (⟨277, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0278 :
    faceAnchor (⟨278, by decide⟩ : Fin 1069) ∈ faceMask (⟨278, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0279 :
    faceAnchor (⟨279, by decide⟩ : Fin 1069) ∈ faceMask (⟨279, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0280 :
    faceAnchor (⟨280, by decide⟩ : Fin 1069) ∈ faceMask (⟨280, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0281 :
    faceAnchor (⟨281, by decide⟩ : Fin 1069) ∈ faceMask (⟨281, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0282 :
    faceAnchor (⟨282, by decide⟩ : Fin 1069) ∈ faceMask (⟨282, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0283 :
    faceAnchor (⟨283, by decide⟩ : Fin 1069) ∈ faceMask (⟨283, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0284 :
    faceAnchor (⟨284, by decide⟩ : Fin 1069) ∈ faceMask (⟨284, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0285 :
    faceAnchor (⟨285, by decide⟩ : Fin 1069) ∈ faceMask (⟨285, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0286 :
    faceAnchor (⟨286, by decide⟩ : Fin 1069) ∈ faceMask (⟨286, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0287 :
    faceAnchor (⟨287, by decide⟩ : Fin 1069) ∈ faceMask (⟨287, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0288 :
    faceAnchor (⟨288, by decide⟩ : Fin 1069) ∈ faceMask (⟨288, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0289 :
    faceAnchor (⟨289, by decide⟩ : Fin 1069) ∈ faceMask (⟨289, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0290 :
    faceAnchor (⟨290, by decide⟩ : Fin 1069) ∈ faceMask (⟨290, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0291 :
    faceAnchor (⟨291, by decide⟩ : Fin 1069) ∈ faceMask (⟨291, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0292 :
    faceAnchor (⟨292, by decide⟩ : Fin 1069) ∈ faceMask (⟨292, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0293 :
    faceAnchor (⟨293, by decide⟩ : Fin 1069) ∈ faceMask (⟨293, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0294 :
    faceAnchor (⟨294, by decide⟩ : Fin 1069) ∈ faceMask (⟨294, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0295 :
    faceAnchor (⟨295, by decide⟩ : Fin 1069) ∈ faceMask (⟨295, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0296 :
    faceAnchor (⟨296, by decide⟩ : Fin 1069) ∈ faceMask (⟨296, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0297 :
    faceAnchor (⟨297, by decide⟩ : Fin 1069) ∈ faceMask (⟨297, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0298 :
    faceAnchor (⟨298, by decide⟩ : Fin 1069) ∈ faceMask (⟨298, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0299 :
    faceAnchor (⟨299, by decide⟩ : Fin 1069) ∈ faceMask (⟨299, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0300 :
    faceAnchor (⟨300, by decide⟩ : Fin 1069) ∈ faceMask (⟨300, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0301 :
    faceAnchor (⟨301, by decide⟩ : Fin 1069) ∈ faceMask (⟨301, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0302 :
    faceAnchor (⟨302, by decide⟩ : Fin 1069) ∈ faceMask (⟨302, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0303 :
    faceAnchor (⟨303, by decide⟩ : Fin 1069) ∈ faceMask (⟨303, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0304 :
    faceAnchor (⟨304, by decide⟩ : Fin 1069) ∈ faceMask (⟨304, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0305 :
    faceAnchor (⟨305, by decide⟩ : Fin 1069) ∈ faceMask (⟨305, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0306 :
    faceAnchor (⟨306, by decide⟩ : Fin 1069) ∈ faceMask (⟨306, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0307 :
    faceAnchor (⟨307, by decide⟩ : Fin 1069) ∈ faceMask (⟨307, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0308 :
    faceAnchor (⟨308, by decide⟩ : Fin 1069) ∈ faceMask (⟨308, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0309 :
    faceAnchor (⟨309, by decide⟩ : Fin 1069) ∈ faceMask (⟨309, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0310 :
    faceAnchor (⟨310, by decide⟩ : Fin 1069) ∈ faceMask (⟨310, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0311 :
    faceAnchor (⟨311, by decide⟩ : Fin 1069) ∈ faceMask (⟨311, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0312 :
    faceAnchor (⟨312, by decide⟩ : Fin 1069) ∈ faceMask (⟨312, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0313 :
    faceAnchor (⟨313, by decide⟩ : Fin 1069) ∈ faceMask (⟨313, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0314 :
    faceAnchor (⟨314, by decide⟩ : Fin 1069) ∈ faceMask (⟨314, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0315 :
    faceAnchor (⟨315, by decide⟩ : Fin 1069) ∈ faceMask (⟨315, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0316 :
    faceAnchor (⟨316, by decide⟩ : Fin 1069) ∈ faceMask (⟨316, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0317 :
    faceAnchor (⟨317, by decide⟩ : Fin 1069) ∈ faceMask (⟨317, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0318 :
    faceAnchor (⟨318, by decide⟩ : Fin 1069) ∈ faceMask (⟨318, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0319 :
    faceAnchor (⟨319, by decide⟩ : Fin 1069) ∈ faceMask (⟨319, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0320 :
    faceAnchor (⟨320, by decide⟩ : Fin 1069) ∈ faceMask (⟨320, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0321 :
    faceAnchor (⟨321, by decide⟩ : Fin 1069) ∈ faceMask (⟨321, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0322 :
    faceAnchor (⟨322, by decide⟩ : Fin 1069) ∈ faceMask (⟨322, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0323 :
    faceAnchor (⟨323, by decide⟩ : Fin 1069) ∈ faceMask (⟨323, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0324 :
    faceAnchor (⟨324, by decide⟩ : Fin 1069) ∈ faceMask (⟨324, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0325 :
    faceAnchor (⟨325, by decide⟩ : Fin 1069) ∈ faceMask (⟨325, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0326 :
    faceAnchor (⟨326, by decide⟩ : Fin 1069) ∈ faceMask (⟨326, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0327 :
    faceAnchor (⟨327, by decide⟩ : Fin 1069) ∈ faceMask (⟨327, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0328 :
    faceAnchor (⟨328, by decide⟩ : Fin 1069) ∈ faceMask (⟨328, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0329 :
    faceAnchor (⟨329, by decide⟩ : Fin 1069) ∈ faceMask (⟨329, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0330 :
    faceAnchor (⟨330, by decide⟩ : Fin 1069) ∈ faceMask (⟨330, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0331 :
    faceAnchor (⟨331, by decide⟩ : Fin 1069) ∈ faceMask (⟨331, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0332 :
    faceAnchor (⟨332, by decide⟩ : Fin 1069) ∈ faceMask (⟨332, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0333 :
    faceAnchor (⟨333, by decide⟩ : Fin 1069) ∈ faceMask (⟨333, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0334 :
    faceAnchor (⟨334, by decide⟩ : Fin 1069) ∈ faceMask (⟨334, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0335 :
    faceAnchor (⟨335, by decide⟩ : Fin 1069) ∈ faceMask (⟨335, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0336 :
    faceAnchor (⟨336, by decide⟩ : Fin 1069) ∈ faceMask (⟨336, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0337 :
    faceAnchor (⟨337, by decide⟩ : Fin 1069) ∈ faceMask (⟨337, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0338 :
    faceAnchor (⟨338, by decide⟩ : Fin 1069) ∈ faceMask (⟨338, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0339 :
    faceAnchor (⟨339, by decide⟩ : Fin 1069) ∈ faceMask (⟨339, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0340 :
    faceAnchor (⟨340, by decide⟩ : Fin 1069) ∈ faceMask (⟨340, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0341 :
    faceAnchor (⟨341, by decide⟩ : Fin 1069) ∈ faceMask (⟨341, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0342 :
    faceAnchor (⟨342, by decide⟩ : Fin 1069) ∈ faceMask (⟨342, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0343 :
    faceAnchor (⟨343, by decide⟩ : Fin 1069) ∈ faceMask (⟨343, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0344 :
    faceAnchor (⟨344, by decide⟩ : Fin 1069) ∈ faceMask (⟨344, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0345 :
    faceAnchor (⟨345, by decide⟩ : Fin 1069) ∈ faceMask (⟨345, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0346 :
    faceAnchor (⟨346, by decide⟩ : Fin 1069) ∈ faceMask (⟨346, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0347 :
    faceAnchor (⟨347, by decide⟩ : Fin 1069) ∈ faceMask (⟨347, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0348 :
    faceAnchor (⟨348, by decide⟩ : Fin 1069) ∈ faceMask (⟨348, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0349 :
    faceAnchor (⟨349, by decide⟩ : Fin 1069) ∈ faceMask (⟨349, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0350 :
    faceAnchor (⟨350, by decide⟩ : Fin 1069) ∈ faceMask (⟨350, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0351 :
    faceAnchor (⟨351, by decide⟩ : Fin 1069) ∈ faceMask (⟨351, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0352 :
    faceAnchor (⟨352, by decide⟩ : Fin 1069) ∈ faceMask (⟨352, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0353 :
    faceAnchor (⟨353, by decide⟩ : Fin 1069) ∈ faceMask (⟨353, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0354 :
    faceAnchor (⟨354, by decide⟩ : Fin 1069) ∈ faceMask (⟨354, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0355 :
    faceAnchor (⟨355, by decide⟩ : Fin 1069) ∈ faceMask (⟨355, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0356 :
    faceAnchor (⟨356, by decide⟩ : Fin 1069) ∈ faceMask (⟨356, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0357 :
    faceAnchor (⟨357, by decide⟩ : Fin 1069) ∈ faceMask (⟨357, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0358 :
    faceAnchor (⟨358, by decide⟩ : Fin 1069) ∈ faceMask (⟨358, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0359 :
    faceAnchor (⟨359, by decide⟩ : Fin 1069) ∈ faceMask (⟨359, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0360 :
    faceAnchor (⟨360, by decide⟩ : Fin 1069) ∈ faceMask (⟨360, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0361 :
    faceAnchor (⟨361, by decide⟩ : Fin 1069) ∈ faceMask (⟨361, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0362 :
    faceAnchor (⟨362, by decide⟩ : Fin 1069) ∈ faceMask (⟨362, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0363 :
    faceAnchor (⟨363, by decide⟩ : Fin 1069) ∈ faceMask (⟨363, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0364 :
    faceAnchor (⟨364, by decide⟩ : Fin 1069) ∈ faceMask (⟨364, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0365 :
    faceAnchor (⟨365, by decide⟩ : Fin 1069) ∈ faceMask (⟨365, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0366 :
    faceAnchor (⟨366, by decide⟩ : Fin 1069) ∈ faceMask (⟨366, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0367 :
    faceAnchor (⟨367, by decide⟩ : Fin 1069) ∈ faceMask (⟨367, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0368 :
    faceAnchor (⟨368, by decide⟩ : Fin 1069) ∈ faceMask (⟨368, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0369 :
    faceAnchor (⟨369, by decide⟩ : Fin 1069) ∈ faceMask (⟨369, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0370 :
    faceAnchor (⟨370, by decide⟩ : Fin 1069) ∈ faceMask (⟨370, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0371 :
    faceAnchor (⟨371, by decide⟩ : Fin 1069) ∈ faceMask (⟨371, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0372 :
    faceAnchor (⟨372, by decide⟩ : Fin 1069) ∈ faceMask (⟨372, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0373 :
    faceAnchor (⟨373, by decide⟩ : Fin 1069) ∈ faceMask (⟨373, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0374 :
    faceAnchor (⟨374, by decide⟩ : Fin 1069) ∈ faceMask (⟨374, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0375 :
    faceAnchor (⟨375, by decide⟩ : Fin 1069) ∈ faceMask (⟨375, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0376 :
    faceAnchor (⟨376, by decide⟩ : Fin 1069) ∈ faceMask (⟨376, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0377 :
    faceAnchor (⟨377, by decide⟩ : Fin 1069) ∈ faceMask (⟨377, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0378 :
    faceAnchor (⟨378, by decide⟩ : Fin 1069) ∈ faceMask (⟨378, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0379 :
    faceAnchor (⟨379, by decide⟩ : Fin 1069) ∈ faceMask (⟨379, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0380 :
    faceAnchor (⟨380, by decide⟩ : Fin 1069) ∈ faceMask (⟨380, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0381 :
    faceAnchor (⟨381, by decide⟩ : Fin 1069) ∈ faceMask (⟨381, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0382 :
    faceAnchor (⟨382, by decide⟩ : Fin 1069) ∈ faceMask (⟨382, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0383 :
    faceAnchor (⟨383, by decide⟩ : Fin 1069) ∈ faceMask (⟨383, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0384 :
    faceAnchor (⟨384, by decide⟩ : Fin 1069) ∈ faceMask (⟨384, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0385 :
    faceAnchor (⟨385, by decide⟩ : Fin 1069) ∈ faceMask (⟨385, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0386 :
    faceAnchor (⟨386, by decide⟩ : Fin 1069) ∈ faceMask (⟨386, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0387 :
    faceAnchor (⟨387, by decide⟩ : Fin 1069) ∈ faceMask (⟨387, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0388 :
    faceAnchor (⟨388, by decide⟩ : Fin 1069) ∈ faceMask (⟨388, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0389 :
    faceAnchor (⟨389, by decide⟩ : Fin 1069) ∈ faceMask (⟨389, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0390 :
    faceAnchor (⟨390, by decide⟩ : Fin 1069) ∈ faceMask (⟨390, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0391 :
    faceAnchor (⟨391, by decide⟩ : Fin 1069) ∈ faceMask (⟨391, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0392 :
    faceAnchor (⟨392, by decide⟩ : Fin 1069) ∈ faceMask (⟨392, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0393 :
    faceAnchor (⟨393, by decide⟩ : Fin 1069) ∈ faceMask (⟨393, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0394 :
    faceAnchor (⟨394, by decide⟩ : Fin 1069) ∈ faceMask (⟨394, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0395 :
    faceAnchor (⟨395, by decide⟩ : Fin 1069) ∈ faceMask (⟨395, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0396 :
    faceAnchor (⟨396, by decide⟩ : Fin 1069) ∈ faceMask (⟨396, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0397 :
    faceAnchor (⟨397, by decide⟩ : Fin 1069) ∈ faceMask (⟨397, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0398 :
    faceAnchor (⟨398, by decide⟩ : Fin 1069) ∈ faceMask (⟨398, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0399 :
    faceAnchor (⟨399, by decide⟩ : Fin 1069) ∈ faceMask (⟨399, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0400 :
    faceAnchor (⟨400, by decide⟩ : Fin 1069) ∈ faceMask (⟨400, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0401 :
    faceAnchor (⟨401, by decide⟩ : Fin 1069) ∈ faceMask (⟨401, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0402 :
    faceAnchor (⟨402, by decide⟩ : Fin 1069) ∈ faceMask (⟨402, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0403 :
    faceAnchor (⟨403, by decide⟩ : Fin 1069) ∈ faceMask (⟨403, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0404 :
    faceAnchor (⟨404, by decide⟩ : Fin 1069) ∈ faceMask (⟨404, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0405 :
    faceAnchor (⟨405, by decide⟩ : Fin 1069) ∈ faceMask (⟨405, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0406 :
    faceAnchor (⟨406, by decide⟩ : Fin 1069) ∈ faceMask (⟨406, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0407 :
    faceAnchor (⟨407, by decide⟩ : Fin 1069) ∈ faceMask (⟨407, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0408 :
    faceAnchor (⟨408, by decide⟩ : Fin 1069) ∈ faceMask (⟨408, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0409 :
    faceAnchor (⟨409, by decide⟩ : Fin 1069) ∈ faceMask (⟨409, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0410 :
    faceAnchor (⟨410, by decide⟩ : Fin 1069) ∈ faceMask (⟨410, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0411 :
    faceAnchor (⟨411, by decide⟩ : Fin 1069) ∈ faceMask (⟨411, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0412 :
    faceAnchor (⟨412, by decide⟩ : Fin 1069) ∈ faceMask (⟨412, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0413 :
    faceAnchor (⟨413, by decide⟩ : Fin 1069) ∈ faceMask (⟨413, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0414 :
    faceAnchor (⟨414, by decide⟩ : Fin 1069) ∈ faceMask (⟨414, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0415 :
    faceAnchor (⟨415, by decide⟩ : Fin 1069) ∈ faceMask (⟨415, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0416 :
    faceAnchor (⟨416, by decide⟩ : Fin 1069) ∈ faceMask (⟨416, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0417 :
    faceAnchor (⟨417, by decide⟩ : Fin 1069) ∈ faceMask (⟨417, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0418 :
    faceAnchor (⟨418, by decide⟩ : Fin 1069) ∈ faceMask (⟨418, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0419 :
    faceAnchor (⟨419, by decide⟩ : Fin 1069) ∈ faceMask (⟨419, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0420 :
    faceAnchor (⟨420, by decide⟩ : Fin 1069) ∈ faceMask (⟨420, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0421 :
    faceAnchor (⟨421, by decide⟩ : Fin 1069) ∈ faceMask (⟨421, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0422 :
    faceAnchor (⟨422, by decide⟩ : Fin 1069) ∈ faceMask (⟨422, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0423 :
    faceAnchor (⟨423, by decide⟩ : Fin 1069) ∈ faceMask (⟨423, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0424 :
    faceAnchor (⟨424, by decide⟩ : Fin 1069) ∈ faceMask (⟨424, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0425 :
    faceAnchor (⟨425, by decide⟩ : Fin 1069) ∈ faceMask (⟨425, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0426 :
    faceAnchor (⟨426, by decide⟩ : Fin 1069) ∈ faceMask (⟨426, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0427 :
    faceAnchor (⟨427, by decide⟩ : Fin 1069) ∈ faceMask (⟨427, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0428 :
    faceAnchor (⟨428, by decide⟩ : Fin 1069) ∈ faceMask (⟨428, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0429 :
    faceAnchor (⟨429, by decide⟩ : Fin 1069) ∈ faceMask (⟨429, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0430 :
    faceAnchor (⟨430, by decide⟩ : Fin 1069) ∈ faceMask (⟨430, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0431 :
    faceAnchor (⟨431, by decide⟩ : Fin 1069) ∈ faceMask (⟨431, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0432 :
    faceAnchor (⟨432, by decide⟩ : Fin 1069) ∈ faceMask (⟨432, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0433 :
    faceAnchor (⟨433, by decide⟩ : Fin 1069) ∈ faceMask (⟨433, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0434 :
    faceAnchor (⟨434, by decide⟩ : Fin 1069) ∈ faceMask (⟨434, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0435 :
    faceAnchor (⟨435, by decide⟩ : Fin 1069) ∈ faceMask (⟨435, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0436 :
    faceAnchor (⟨436, by decide⟩ : Fin 1069) ∈ faceMask (⟨436, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0437 :
    faceAnchor (⟨437, by decide⟩ : Fin 1069) ∈ faceMask (⟨437, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0438 :
    faceAnchor (⟨438, by decide⟩ : Fin 1069) ∈ faceMask (⟨438, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0439 :
    faceAnchor (⟨439, by decide⟩ : Fin 1069) ∈ faceMask (⟨439, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0440 :
    faceAnchor (⟨440, by decide⟩ : Fin 1069) ∈ faceMask (⟨440, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0441 :
    faceAnchor (⟨441, by decide⟩ : Fin 1069) ∈ faceMask (⟨441, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0442 :
    faceAnchor (⟨442, by decide⟩ : Fin 1069) ∈ faceMask (⟨442, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0443 :
    faceAnchor (⟨443, by decide⟩ : Fin 1069) ∈ faceMask (⟨443, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0444 :
    faceAnchor (⟨444, by decide⟩ : Fin 1069) ∈ faceMask (⟨444, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0445 :
    faceAnchor (⟨445, by decide⟩ : Fin 1069) ∈ faceMask (⟨445, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0446 :
    faceAnchor (⟨446, by decide⟩ : Fin 1069) ∈ faceMask (⟨446, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0447 :
    faceAnchor (⟨447, by decide⟩ : Fin 1069) ∈ faceMask (⟨447, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0448 :
    faceAnchor (⟨448, by decide⟩ : Fin 1069) ∈ faceMask (⟨448, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0449 :
    faceAnchor (⟨449, by decide⟩ : Fin 1069) ∈ faceMask (⟨449, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0450 :
    faceAnchor (⟨450, by decide⟩ : Fin 1069) ∈ faceMask (⟨450, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0451 :
    faceAnchor (⟨451, by decide⟩ : Fin 1069) ∈ faceMask (⟨451, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0452 :
    faceAnchor (⟨452, by decide⟩ : Fin 1069) ∈ faceMask (⟨452, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0453 :
    faceAnchor (⟨453, by decide⟩ : Fin 1069) ∈ faceMask (⟨453, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0454 :
    faceAnchor (⟨454, by decide⟩ : Fin 1069) ∈ faceMask (⟨454, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0455 :
    faceAnchor (⟨455, by decide⟩ : Fin 1069) ∈ faceMask (⟨455, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0456 :
    faceAnchor (⟨456, by decide⟩ : Fin 1069) ∈ faceMask (⟨456, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0457 :
    faceAnchor (⟨457, by decide⟩ : Fin 1069) ∈ faceMask (⟨457, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0458 :
    faceAnchor (⟨458, by decide⟩ : Fin 1069) ∈ faceMask (⟨458, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0459 :
    faceAnchor (⟨459, by decide⟩ : Fin 1069) ∈ faceMask (⟨459, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0460 :
    faceAnchor (⟨460, by decide⟩ : Fin 1069) ∈ faceMask (⟨460, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0461 :
    faceAnchor (⟨461, by decide⟩ : Fin 1069) ∈ faceMask (⟨461, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0462 :
    faceAnchor (⟨462, by decide⟩ : Fin 1069) ∈ faceMask (⟨462, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0463 :
    faceAnchor (⟨463, by decide⟩ : Fin 1069) ∈ faceMask (⟨463, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0464 :
    faceAnchor (⟨464, by decide⟩ : Fin 1069) ∈ faceMask (⟨464, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0465 :
    faceAnchor (⟨465, by decide⟩ : Fin 1069) ∈ faceMask (⟨465, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0466 :
    faceAnchor (⟨466, by decide⟩ : Fin 1069) ∈ faceMask (⟨466, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0467 :
    faceAnchor (⟨467, by decide⟩ : Fin 1069) ∈ faceMask (⟨467, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0468 :
    faceAnchor (⟨468, by decide⟩ : Fin 1069) ∈ faceMask (⟨468, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0469 :
    faceAnchor (⟨469, by decide⟩ : Fin 1069) ∈ faceMask (⟨469, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0470 :
    faceAnchor (⟨470, by decide⟩ : Fin 1069) ∈ faceMask (⟨470, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0471 :
    faceAnchor (⟨471, by decide⟩ : Fin 1069) ∈ faceMask (⟨471, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0472 :
    faceAnchor (⟨472, by decide⟩ : Fin 1069) ∈ faceMask (⟨472, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0473 :
    faceAnchor (⟨473, by decide⟩ : Fin 1069) ∈ faceMask (⟨473, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0474 :
    faceAnchor (⟨474, by decide⟩ : Fin 1069) ∈ faceMask (⟨474, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0475 :
    faceAnchor (⟨475, by decide⟩ : Fin 1069) ∈ faceMask (⟨475, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0476 :
    faceAnchor (⟨476, by decide⟩ : Fin 1069) ∈ faceMask (⟨476, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0477 :
    faceAnchor (⟨477, by decide⟩ : Fin 1069) ∈ faceMask (⟨477, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0478 :
    faceAnchor (⟨478, by decide⟩ : Fin 1069) ∈ faceMask (⟨478, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0479 :
    faceAnchor (⟨479, by decide⟩ : Fin 1069) ∈ faceMask (⟨479, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0480 :
    faceAnchor (⟨480, by decide⟩ : Fin 1069) ∈ faceMask (⟨480, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0481 :
    faceAnchor (⟨481, by decide⟩ : Fin 1069) ∈ faceMask (⟨481, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0482 :
    faceAnchor (⟨482, by decide⟩ : Fin 1069) ∈ faceMask (⟨482, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0483 :
    faceAnchor (⟨483, by decide⟩ : Fin 1069) ∈ faceMask (⟨483, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0484 :
    faceAnchor (⟨484, by decide⟩ : Fin 1069) ∈ faceMask (⟨484, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0485 :
    faceAnchor (⟨485, by decide⟩ : Fin 1069) ∈ faceMask (⟨485, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0486 :
    faceAnchor (⟨486, by decide⟩ : Fin 1069) ∈ faceMask (⟨486, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0487 :
    faceAnchor (⟨487, by decide⟩ : Fin 1069) ∈ faceMask (⟨487, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0488 :
    faceAnchor (⟨488, by decide⟩ : Fin 1069) ∈ faceMask (⟨488, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0489 :
    faceAnchor (⟨489, by decide⟩ : Fin 1069) ∈ faceMask (⟨489, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0490 :
    faceAnchor (⟨490, by decide⟩ : Fin 1069) ∈ faceMask (⟨490, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0491 :
    faceAnchor (⟨491, by decide⟩ : Fin 1069) ∈ faceMask (⟨491, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0492 :
    faceAnchor (⟨492, by decide⟩ : Fin 1069) ∈ faceMask (⟨492, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0493 :
    faceAnchor (⟨493, by decide⟩ : Fin 1069) ∈ faceMask (⟨493, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0494 :
    faceAnchor (⟨494, by decide⟩ : Fin 1069) ∈ faceMask (⟨494, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0495 :
    faceAnchor (⟨495, by decide⟩ : Fin 1069) ∈ faceMask (⟨495, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0496 :
    faceAnchor (⟨496, by decide⟩ : Fin 1069) ∈ faceMask (⟨496, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0497 :
    faceAnchor (⟨497, by decide⟩ : Fin 1069) ∈ faceMask (⟨497, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0498 :
    faceAnchor (⟨498, by decide⟩ : Fin 1069) ∈ faceMask (⟨498, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0499 :
    faceAnchor (⟨499, by decide⟩ : Fin 1069) ∈ faceMask (⟨499, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0500 :
    faceAnchor (⟨500, by decide⟩ : Fin 1069) ∈ faceMask (⟨500, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0501 :
    faceAnchor (⟨501, by decide⟩ : Fin 1069) ∈ faceMask (⟨501, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0502 :
    faceAnchor (⟨502, by decide⟩ : Fin 1069) ∈ faceMask (⟨502, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0503 :
    faceAnchor (⟨503, by decide⟩ : Fin 1069) ∈ faceMask (⟨503, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0504 :
    faceAnchor (⟨504, by decide⟩ : Fin 1069) ∈ faceMask (⟨504, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0505 :
    faceAnchor (⟨505, by decide⟩ : Fin 1069) ∈ faceMask (⟨505, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0506 :
    faceAnchor (⟨506, by decide⟩ : Fin 1069) ∈ faceMask (⟨506, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0507 :
    faceAnchor (⟨507, by decide⟩ : Fin 1069) ∈ faceMask (⟨507, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0508 :
    faceAnchor (⟨508, by decide⟩ : Fin 1069) ∈ faceMask (⟨508, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0509 :
    faceAnchor (⟨509, by decide⟩ : Fin 1069) ∈ faceMask (⟨509, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0510 :
    faceAnchor (⟨510, by decide⟩ : Fin 1069) ∈ faceMask (⟨510, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0511 :
    faceAnchor (⟨511, by decide⟩ : Fin 1069) ∈ faceMask (⟨511, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0512 :
    faceAnchor (⟨512, by decide⟩ : Fin 1069) ∈ faceMask (⟨512, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0513 :
    faceAnchor (⟨513, by decide⟩ : Fin 1069) ∈ faceMask (⟨513, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0514 :
    faceAnchor (⟨514, by decide⟩ : Fin 1069) ∈ faceMask (⟨514, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0515 :
    faceAnchor (⟨515, by decide⟩ : Fin 1069) ∈ faceMask (⟨515, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0516 :
    faceAnchor (⟨516, by decide⟩ : Fin 1069) ∈ faceMask (⟨516, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0517 :
    faceAnchor (⟨517, by decide⟩ : Fin 1069) ∈ faceMask (⟨517, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0518 :
    faceAnchor (⟨518, by decide⟩ : Fin 1069) ∈ faceMask (⟨518, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0519 :
    faceAnchor (⟨519, by decide⟩ : Fin 1069) ∈ faceMask (⟨519, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0520 :
    faceAnchor (⟨520, by decide⟩ : Fin 1069) ∈ faceMask (⟨520, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0521 :
    faceAnchor (⟨521, by decide⟩ : Fin 1069) ∈ faceMask (⟨521, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0522 :
    faceAnchor (⟨522, by decide⟩ : Fin 1069) ∈ faceMask (⟨522, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0523 :
    faceAnchor (⟨523, by decide⟩ : Fin 1069) ∈ faceMask (⟨523, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0524 :
    faceAnchor (⟨524, by decide⟩ : Fin 1069) ∈ faceMask (⟨524, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0525 :
    faceAnchor (⟨525, by decide⟩ : Fin 1069) ∈ faceMask (⟨525, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0526 :
    faceAnchor (⟨526, by decide⟩ : Fin 1069) ∈ faceMask (⟨526, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0527 :
    faceAnchor (⟨527, by decide⟩ : Fin 1069) ∈ faceMask (⟨527, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0528 :
    faceAnchor (⟨528, by decide⟩ : Fin 1069) ∈ faceMask (⟨528, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0529 :
    faceAnchor (⟨529, by decide⟩ : Fin 1069) ∈ faceMask (⟨529, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0530 :
    faceAnchor (⟨530, by decide⟩ : Fin 1069) ∈ faceMask (⟨530, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0531 :
    faceAnchor (⟨531, by decide⟩ : Fin 1069) ∈ faceMask (⟨531, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0532 :
    faceAnchor (⟨532, by decide⟩ : Fin 1069) ∈ faceMask (⟨532, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0533 :
    faceAnchor (⟨533, by decide⟩ : Fin 1069) ∈ faceMask (⟨533, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0534 :
    faceAnchor (⟨534, by decide⟩ : Fin 1069) ∈ faceMask (⟨534, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0535 :
    faceAnchor (⟨535, by decide⟩ : Fin 1069) ∈ faceMask (⟨535, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0536 :
    faceAnchor (⟨536, by decide⟩ : Fin 1069) ∈ faceMask (⟨536, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0537 :
    faceAnchor (⟨537, by decide⟩ : Fin 1069) ∈ faceMask (⟨537, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0538 :
    faceAnchor (⟨538, by decide⟩ : Fin 1069) ∈ faceMask (⟨538, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0539 :
    faceAnchor (⟨539, by decide⟩ : Fin 1069) ∈ faceMask (⟨539, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0540 :
    faceAnchor (⟨540, by decide⟩ : Fin 1069) ∈ faceMask (⟨540, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0541 :
    faceAnchor (⟨541, by decide⟩ : Fin 1069) ∈ faceMask (⟨541, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0542 :
    faceAnchor (⟨542, by decide⟩ : Fin 1069) ∈ faceMask (⟨542, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0543 :
    faceAnchor (⟨543, by decide⟩ : Fin 1069) ∈ faceMask (⟨543, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0544 :
    faceAnchor (⟨544, by decide⟩ : Fin 1069) ∈ faceMask (⟨544, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0545 :
    faceAnchor (⟨545, by decide⟩ : Fin 1069) ∈ faceMask (⟨545, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0546 :
    faceAnchor (⟨546, by decide⟩ : Fin 1069) ∈ faceMask (⟨546, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0547 :
    faceAnchor (⟨547, by decide⟩ : Fin 1069) ∈ faceMask (⟨547, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0548 :
    faceAnchor (⟨548, by decide⟩ : Fin 1069) ∈ faceMask (⟨548, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0549 :
    faceAnchor (⟨549, by decide⟩ : Fin 1069) ∈ faceMask (⟨549, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0550 :
    faceAnchor (⟨550, by decide⟩ : Fin 1069) ∈ faceMask (⟨550, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0551 :
    faceAnchor (⟨551, by decide⟩ : Fin 1069) ∈ faceMask (⟨551, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0552 :
    faceAnchor (⟨552, by decide⟩ : Fin 1069) ∈ faceMask (⟨552, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0553 :
    faceAnchor (⟨553, by decide⟩ : Fin 1069) ∈ faceMask (⟨553, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0554 :
    faceAnchor (⟨554, by decide⟩ : Fin 1069) ∈ faceMask (⟨554, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0555 :
    faceAnchor (⟨555, by decide⟩ : Fin 1069) ∈ faceMask (⟨555, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0556 :
    faceAnchor (⟨556, by decide⟩ : Fin 1069) ∈ faceMask (⟨556, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0557 :
    faceAnchor (⟨557, by decide⟩ : Fin 1069) ∈ faceMask (⟨557, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0558 :
    faceAnchor (⟨558, by decide⟩ : Fin 1069) ∈ faceMask (⟨558, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0559 :
    faceAnchor (⟨559, by decide⟩ : Fin 1069) ∈ faceMask (⟨559, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0560 :
    faceAnchor (⟨560, by decide⟩ : Fin 1069) ∈ faceMask (⟨560, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0561 :
    faceAnchor (⟨561, by decide⟩ : Fin 1069) ∈ faceMask (⟨561, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0562 :
    faceAnchor (⟨562, by decide⟩ : Fin 1069) ∈ faceMask (⟨562, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0563 :
    faceAnchor (⟨563, by decide⟩ : Fin 1069) ∈ faceMask (⟨563, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0564 :
    faceAnchor (⟨564, by decide⟩ : Fin 1069) ∈ faceMask (⟨564, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0565 :
    faceAnchor (⟨565, by decide⟩ : Fin 1069) ∈ faceMask (⟨565, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0566 :
    faceAnchor (⟨566, by decide⟩ : Fin 1069) ∈ faceMask (⟨566, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0567 :
    faceAnchor (⟨567, by decide⟩ : Fin 1069) ∈ faceMask (⟨567, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0568 :
    faceAnchor (⟨568, by decide⟩ : Fin 1069) ∈ faceMask (⟨568, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0569 :
    faceAnchor (⟨569, by decide⟩ : Fin 1069) ∈ faceMask (⟨569, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0570 :
    faceAnchor (⟨570, by decide⟩ : Fin 1069) ∈ faceMask (⟨570, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0571 :
    faceAnchor (⟨571, by decide⟩ : Fin 1069) ∈ faceMask (⟨571, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0572 :
    faceAnchor (⟨572, by decide⟩ : Fin 1069) ∈ faceMask (⟨572, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0573 :
    faceAnchor (⟨573, by decide⟩ : Fin 1069) ∈ faceMask (⟨573, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0574 :
    faceAnchor (⟨574, by decide⟩ : Fin 1069) ∈ faceMask (⟨574, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0575 :
    faceAnchor (⟨575, by decide⟩ : Fin 1069) ∈ faceMask (⟨575, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0576 :
    faceAnchor (⟨576, by decide⟩ : Fin 1069) ∈ faceMask (⟨576, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0577 :
    faceAnchor (⟨577, by decide⟩ : Fin 1069) ∈ faceMask (⟨577, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0578 :
    faceAnchor (⟨578, by decide⟩ : Fin 1069) ∈ faceMask (⟨578, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0579 :
    faceAnchor (⟨579, by decide⟩ : Fin 1069) ∈ faceMask (⟨579, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0580 :
    faceAnchor (⟨580, by decide⟩ : Fin 1069) ∈ faceMask (⟨580, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0581 :
    faceAnchor (⟨581, by decide⟩ : Fin 1069) ∈ faceMask (⟨581, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0582 :
    faceAnchor (⟨582, by decide⟩ : Fin 1069) ∈ faceMask (⟨582, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0583 :
    faceAnchor (⟨583, by decide⟩ : Fin 1069) ∈ faceMask (⟨583, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0584 :
    faceAnchor (⟨584, by decide⟩ : Fin 1069) ∈ faceMask (⟨584, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0585 :
    faceAnchor (⟨585, by decide⟩ : Fin 1069) ∈ faceMask (⟨585, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0586 :
    faceAnchor (⟨586, by decide⟩ : Fin 1069) ∈ faceMask (⟨586, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0587 :
    faceAnchor (⟨587, by decide⟩ : Fin 1069) ∈ faceMask (⟨587, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0588 :
    faceAnchor (⟨588, by decide⟩ : Fin 1069) ∈ faceMask (⟨588, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0589 :
    faceAnchor (⟨589, by decide⟩ : Fin 1069) ∈ faceMask (⟨589, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0590 :
    faceAnchor (⟨590, by decide⟩ : Fin 1069) ∈ faceMask (⟨590, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0591 :
    faceAnchor (⟨591, by decide⟩ : Fin 1069) ∈ faceMask (⟨591, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0592 :
    faceAnchor (⟨592, by decide⟩ : Fin 1069) ∈ faceMask (⟨592, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0593 :
    faceAnchor (⟨593, by decide⟩ : Fin 1069) ∈ faceMask (⟨593, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0594 :
    faceAnchor (⟨594, by decide⟩ : Fin 1069) ∈ faceMask (⟨594, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0595 :
    faceAnchor (⟨595, by decide⟩ : Fin 1069) ∈ faceMask (⟨595, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0596 :
    faceAnchor (⟨596, by decide⟩ : Fin 1069) ∈ faceMask (⟨596, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0597 :
    faceAnchor (⟨597, by decide⟩ : Fin 1069) ∈ faceMask (⟨597, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0598 :
    faceAnchor (⟨598, by decide⟩ : Fin 1069) ∈ faceMask (⟨598, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0599 :
    faceAnchor (⟨599, by decide⟩ : Fin 1069) ∈ faceMask (⟨599, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0600 :
    faceAnchor (⟨600, by decide⟩ : Fin 1069) ∈ faceMask (⟨600, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0601 :
    faceAnchor (⟨601, by decide⟩ : Fin 1069) ∈ faceMask (⟨601, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0602 :
    faceAnchor (⟨602, by decide⟩ : Fin 1069) ∈ faceMask (⟨602, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0603 :
    faceAnchor (⟨603, by decide⟩ : Fin 1069) ∈ faceMask (⟨603, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0604 :
    faceAnchor (⟨604, by decide⟩ : Fin 1069) ∈ faceMask (⟨604, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0605 :
    faceAnchor (⟨605, by decide⟩ : Fin 1069) ∈ faceMask (⟨605, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0606 :
    faceAnchor (⟨606, by decide⟩ : Fin 1069) ∈ faceMask (⟨606, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0607 :
    faceAnchor (⟨607, by decide⟩ : Fin 1069) ∈ faceMask (⟨607, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0608 :
    faceAnchor (⟨608, by decide⟩ : Fin 1069) ∈ faceMask (⟨608, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0609 :
    faceAnchor (⟨609, by decide⟩ : Fin 1069) ∈ faceMask (⟨609, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0610 :
    faceAnchor (⟨610, by decide⟩ : Fin 1069) ∈ faceMask (⟨610, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0611 :
    faceAnchor (⟨611, by decide⟩ : Fin 1069) ∈ faceMask (⟨611, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0612 :
    faceAnchor (⟨612, by decide⟩ : Fin 1069) ∈ faceMask (⟨612, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0613 :
    faceAnchor (⟨613, by decide⟩ : Fin 1069) ∈ faceMask (⟨613, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0614 :
    faceAnchor (⟨614, by decide⟩ : Fin 1069) ∈ faceMask (⟨614, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0615 :
    faceAnchor (⟨615, by decide⟩ : Fin 1069) ∈ faceMask (⟨615, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0616 :
    faceAnchor (⟨616, by decide⟩ : Fin 1069) ∈ faceMask (⟨616, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0617 :
    faceAnchor (⟨617, by decide⟩ : Fin 1069) ∈ faceMask (⟨617, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0618 :
    faceAnchor (⟨618, by decide⟩ : Fin 1069) ∈ faceMask (⟨618, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0619 :
    faceAnchor (⟨619, by decide⟩ : Fin 1069) ∈ faceMask (⟨619, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0620 :
    faceAnchor (⟨620, by decide⟩ : Fin 1069) ∈ faceMask (⟨620, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0621 :
    faceAnchor (⟨621, by decide⟩ : Fin 1069) ∈ faceMask (⟨621, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0622 :
    faceAnchor (⟨622, by decide⟩ : Fin 1069) ∈ faceMask (⟨622, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0623 :
    faceAnchor (⟨623, by decide⟩ : Fin 1069) ∈ faceMask (⟨623, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0624 :
    faceAnchor (⟨624, by decide⟩ : Fin 1069) ∈ faceMask (⟨624, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0625 :
    faceAnchor (⟨625, by decide⟩ : Fin 1069) ∈ faceMask (⟨625, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0626 :
    faceAnchor (⟨626, by decide⟩ : Fin 1069) ∈ faceMask (⟨626, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0627 :
    faceAnchor (⟨627, by decide⟩ : Fin 1069) ∈ faceMask (⟨627, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0628 :
    faceAnchor (⟨628, by decide⟩ : Fin 1069) ∈ faceMask (⟨628, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0629 :
    faceAnchor (⟨629, by decide⟩ : Fin 1069) ∈ faceMask (⟨629, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0630 :
    faceAnchor (⟨630, by decide⟩ : Fin 1069) ∈ faceMask (⟨630, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0631 :
    faceAnchor (⟨631, by decide⟩ : Fin 1069) ∈ faceMask (⟨631, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0632 :
    faceAnchor (⟨632, by decide⟩ : Fin 1069) ∈ faceMask (⟨632, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0633 :
    faceAnchor (⟨633, by decide⟩ : Fin 1069) ∈ faceMask (⟨633, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0634 :
    faceAnchor (⟨634, by decide⟩ : Fin 1069) ∈ faceMask (⟨634, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0635 :
    faceAnchor (⟨635, by decide⟩ : Fin 1069) ∈ faceMask (⟨635, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0636 :
    faceAnchor (⟨636, by decide⟩ : Fin 1069) ∈ faceMask (⟨636, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0637 :
    faceAnchor (⟨637, by decide⟩ : Fin 1069) ∈ faceMask (⟨637, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0638 :
    faceAnchor (⟨638, by decide⟩ : Fin 1069) ∈ faceMask (⟨638, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0639 :
    faceAnchor (⟨639, by decide⟩ : Fin 1069) ∈ faceMask (⟨639, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0640 :
    faceAnchor (⟨640, by decide⟩ : Fin 1069) ∈ faceMask (⟨640, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0641 :
    faceAnchor (⟨641, by decide⟩ : Fin 1069) ∈ faceMask (⟨641, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0642 :
    faceAnchor (⟨642, by decide⟩ : Fin 1069) ∈ faceMask (⟨642, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0643 :
    faceAnchor (⟨643, by decide⟩ : Fin 1069) ∈ faceMask (⟨643, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0644 :
    faceAnchor (⟨644, by decide⟩ : Fin 1069) ∈ faceMask (⟨644, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0645 :
    faceAnchor (⟨645, by decide⟩ : Fin 1069) ∈ faceMask (⟨645, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0646 :
    faceAnchor (⟨646, by decide⟩ : Fin 1069) ∈ faceMask (⟨646, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0647 :
    faceAnchor (⟨647, by decide⟩ : Fin 1069) ∈ faceMask (⟨647, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0648 :
    faceAnchor (⟨648, by decide⟩ : Fin 1069) ∈ faceMask (⟨648, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0649 :
    faceAnchor (⟨649, by decide⟩ : Fin 1069) ∈ faceMask (⟨649, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0650 :
    faceAnchor (⟨650, by decide⟩ : Fin 1069) ∈ faceMask (⟨650, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0651 :
    faceAnchor (⟨651, by decide⟩ : Fin 1069) ∈ faceMask (⟨651, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0652 :
    faceAnchor (⟨652, by decide⟩ : Fin 1069) ∈ faceMask (⟨652, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0653 :
    faceAnchor (⟨653, by decide⟩ : Fin 1069) ∈ faceMask (⟨653, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0654 :
    faceAnchor (⟨654, by decide⟩ : Fin 1069) ∈ faceMask (⟨654, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0655 :
    faceAnchor (⟨655, by decide⟩ : Fin 1069) ∈ faceMask (⟨655, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0656 :
    faceAnchor (⟨656, by decide⟩ : Fin 1069) ∈ faceMask (⟨656, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0657 :
    faceAnchor (⟨657, by decide⟩ : Fin 1069) ∈ faceMask (⟨657, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0658 :
    faceAnchor (⟨658, by decide⟩ : Fin 1069) ∈ faceMask (⟨658, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0659 :
    faceAnchor (⟨659, by decide⟩ : Fin 1069) ∈ faceMask (⟨659, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0660 :
    faceAnchor (⟨660, by decide⟩ : Fin 1069) ∈ faceMask (⟨660, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0661 :
    faceAnchor (⟨661, by decide⟩ : Fin 1069) ∈ faceMask (⟨661, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0662 :
    faceAnchor (⟨662, by decide⟩ : Fin 1069) ∈ faceMask (⟨662, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0663 :
    faceAnchor (⟨663, by decide⟩ : Fin 1069) ∈ faceMask (⟨663, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0664 :
    faceAnchor (⟨664, by decide⟩ : Fin 1069) ∈ faceMask (⟨664, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0665 :
    faceAnchor (⟨665, by decide⟩ : Fin 1069) ∈ faceMask (⟨665, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0666 :
    faceAnchor (⟨666, by decide⟩ : Fin 1069) ∈ faceMask (⟨666, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0667 :
    faceAnchor (⟨667, by decide⟩ : Fin 1069) ∈ faceMask (⟨667, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0668 :
    faceAnchor (⟨668, by decide⟩ : Fin 1069) ∈ faceMask (⟨668, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0669 :
    faceAnchor (⟨669, by decide⟩ : Fin 1069) ∈ faceMask (⟨669, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0670 :
    faceAnchor (⟨670, by decide⟩ : Fin 1069) ∈ faceMask (⟨670, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0671 :
    faceAnchor (⟨671, by decide⟩ : Fin 1069) ∈ faceMask (⟨671, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0672 :
    faceAnchor (⟨672, by decide⟩ : Fin 1069) ∈ faceMask (⟨672, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0673 :
    faceAnchor (⟨673, by decide⟩ : Fin 1069) ∈ faceMask (⟨673, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0674 :
    faceAnchor (⟨674, by decide⟩ : Fin 1069) ∈ faceMask (⟨674, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0675 :
    faceAnchor (⟨675, by decide⟩ : Fin 1069) ∈ faceMask (⟨675, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0676 :
    faceAnchor (⟨676, by decide⟩ : Fin 1069) ∈ faceMask (⟨676, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0677 :
    faceAnchor (⟨677, by decide⟩ : Fin 1069) ∈ faceMask (⟨677, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0678 :
    faceAnchor (⟨678, by decide⟩ : Fin 1069) ∈ faceMask (⟨678, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0679 :
    faceAnchor (⟨679, by decide⟩ : Fin 1069) ∈ faceMask (⟨679, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0680 :
    faceAnchor (⟨680, by decide⟩ : Fin 1069) ∈ faceMask (⟨680, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0681 :
    faceAnchor (⟨681, by decide⟩ : Fin 1069) ∈ faceMask (⟨681, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0682 :
    faceAnchor (⟨682, by decide⟩ : Fin 1069) ∈ faceMask (⟨682, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0683 :
    faceAnchor (⟨683, by decide⟩ : Fin 1069) ∈ faceMask (⟨683, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0684 :
    faceAnchor (⟨684, by decide⟩ : Fin 1069) ∈ faceMask (⟨684, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0685 :
    faceAnchor (⟨685, by decide⟩ : Fin 1069) ∈ faceMask (⟨685, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0686 :
    faceAnchor (⟨686, by decide⟩ : Fin 1069) ∈ faceMask (⟨686, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0687 :
    faceAnchor (⟨687, by decide⟩ : Fin 1069) ∈ faceMask (⟨687, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0688 :
    faceAnchor (⟨688, by decide⟩ : Fin 1069) ∈ faceMask (⟨688, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0689 :
    faceAnchor (⟨689, by decide⟩ : Fin 1069) ∈ faceMask (⟨689, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0690 :
    faceAnchor (⟨690, by decide⟩ : Fin 1069) ∈ faceMask (⟨690, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0691 :
    faceAnchor (⟨691, by decide⟩ : Fin 1069) ∈ faceMask (⟨691, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0692 :
    faceAnchor (⟨692, by decide⟩ : Fin 1069) ∈ faceMask (⟨692, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0693 :
    faceAnchor (⟨693, by decide⟩ : Fin 1069) ∈ faceMask (⟨693, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0694 :
    faceAnchor (⟨694, by decide⟩ : Fin 1069) ∈ faceMask (⟨694, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0695 :
    faceAnchor (⟨695, by decide⟩ : Fin 1069) ∈ faceMask (⟨695, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0696 :
    faceAnchor (⟨696, by decide⟩ : Fin 1069) ∈ faceMask (⟨696, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0697 :
    faceAnchor (⟨697, by decide⟩ : Fin 1069) ∈ faceMask (⟨697, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0698 :
    faceAnchor (⟨698, by decide⟩ : Fin 1069) ∈ faceMask (⟨698, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0699 :
    faceAnchor (⟨699, by decide⟩ : Fin 1069) ∈ faceMask (⟨699, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0700 :
    faceAnchor (⟨700, by decide⟩ : Fin 1069) ∈ faceMask (⟨700, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0701 :
    faceAnchor (⟨701, by decide⟩ : Fin 1069) ∈ faceMask (⟨701, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0702 :
    faceAnchor (⟨702, by decide⟩ : Fin 1069) ∈ faceMask (⟨702, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0703 :
    faceAnchor (⟨703, by decide⟩ : Fin 1069) ∈ faceMask (⟨703, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0704 :
    faceAnchor (⟨704, by decide⟩ : Fin 1069) ∈ faceMask (⟨704, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0705 :
    faceAnchor (⟨705, by decide⟩ : Fin 1069) ∈ faceMask (⟨705, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0706 :
    faceAnchor (⟨706, by decide⟩ : Fin 1069) ∈ faceMask (⟨706, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0707 :
    faceAnchor (⟨707, by decide⟩ : Fin 1069) ∈ faceMask (⟨707, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0708 :
    faceAnchor (⟨708, by decide⟩ : Fin 1069) ∈ faceMask (⟨708, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0709 :
    faceAnchor (⟨709, by decide⟩ : Fin 1069) ∈ faceMask (⟨709, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0710 :
    faceAnchor (⟨710, by decide⟩ : Fin 1069) ∈ faceMask (⟨710, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0711 :
    faceAnchor (⟨711, by decide⟩ : Fin 1069) ∈ faceMask (⟨711, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0712 :
    faceAnchor (⟨712, by decide⟩ : Fin 1069) ∈ faceMask (⟨712, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0713 :
    faceAnchor (⟨713, by decide⟩ : Fin 1069) ∈ faceMask (⟨713, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0714 :
    faceAnchor (⟨714, by decide⟩ : Fin 1069) ∈ faceMask (⟨714, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0715 :
    faceAnchor (⟨715, by decide⟩ : Fin 1069) ∈ faceMask (⟨715, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0716 :
    faceAnchor (⟨716, by decide⟩ : Fin 1069) ∈ faceMask (⟨716, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0717 :
    faceAnchor (⟨717, by decide⟩ : Fin 1069) ∈ faceMask (⟨717, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0718 :
    faceAnchor (⟨718, by decide⟩ : Fin 1069) ∈ faceMask (⟨718, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0719 :
    faceAnchor (⟨719, by decide⟩ : Fin 1069) ∈ faceMask (⟨719, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0720 :
    faceAnchor (⟨720, by decide⟩ : Fin 1069) ∈ faceMask (⟨720, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0721 :
    faceAnchor (⟨721, by decide⟩ : Fin 1069) ∈ faceMask (⟨721, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0722 :
    faceAnchor (⟨722, by decide⟩ : Fin 1069) ∈ faceMask (⟨722, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0723 :
    faceAnchor (⟨723, by decide⟩ : Fin 1069) ∈ faceMask (⟨723, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0724 :
    faceAnchor (⟨724, by decide⟩ : Fin 1069) ∈ faceMask (⟨724, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0725 :
    faceAnchor (⟨725, by decide⟩ : Fin 1069) ∈ faceMask (⟨725, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0726 :
    faceAnchor (⟨726, by decide⟩ : Fin 1069) ∈ faceMask (⟨726, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0727 :
    faceAnchor (⟨727, by decide⟩ : Fin 1069) ∈ faceMask (⟨727, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0728 :
    faceAnchor (⟨728, by decide⟩ : Fin 1069) ∈ faceMask (⟨728, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0729 :
    faceAnchor (⟨729, by decide⟩ : Fin 1069) ∈ faceMask (⟨729, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0730 :
    faceAnchor (⟨730, by decide⟩ : Fin 1069) ∈ faceMask (⟨730, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0731 :
    faceAnchor (⟨731, by decide⟩ : Fin 1069) ∈ faceMask (⟨731, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0732 :
    faceAnchor (⟨732, by decide⟩ : Fin 1069) ∈ faceMask (⟨732, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0733 :
    faceAnchor (⟨733, by decide⟩ : Fin 1069) ∈ faceMask (⟨733, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0734 :
    faceAnchor (⟨734, by decide⟩ : Fin 1069) ∈ faceMask (⟨734, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0735 :
    faceAnchor (⟨735, by decide⟩ : Fin 1069) ∈ faceMask (⟨735, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0736 :
    faceAnchor (⟨736, by decide⟩ : Fin 1069) ∈ faceMask (⟨736, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0737 :
    faceAnchor (⟨737, by decide⟩ : Fin 1069) ∈ faceMask (⟨737, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0738 :
    faceAnchor (⟨738, by decide⟩ : Fin 1069) ∈ faceMask (⟨738, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0739 :
    faceAnchor (⟨739, by decide⟩ : Fin 1069) ∈ faceMask (⟨739, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0740 :
    faceAnchor (⟨740, by decide⟩ : Fin 1069) ∈ faceMask (⟨740, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0741 :
    faceAnchor (⟨741, by decide⟩ : Fin 1069) ∈ faceMask (⟨741, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0742 :
    faceAnchor (⟨742, by decide⟩ : Fin 1069) ∈ faceMask (⟨742, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0743 :
    faceAnchor (⟨743, by decide⟩ : Fin 1069) ∈ faceMask (⟨743, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0744 :
    faceAnchor (⟨744, by decide⟩ : Fin 1069) ∈ faceMask (⟨744, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0745 :
    faceAnchor (⟨745, by decide⟩ : Fin 1069) ∈ faceMask (⟨745, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0746 :
    faceAnchor (⟨746, by decide⟩ : Fin 1069) ∈ faceMask (⟨746, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0747 :
    faceAnchor (⟨747, by decide⟩ : Fin 1069) ∈ faceMask (⟨747, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0748 :
    faceAnchor (⟨748, by decide⟩ : Fin 1069) ∈ faceMask (⟨748, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0749 :
    faceAnchor (⟨749, by decide⟩ : Fin 1069) ∈ faceMask (⟨749, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0750 :
    faceAnchor (⟨750, by decide⟩ : Fin 1069) ∈ faceMask (⟨750, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0751 :
    faceAnchor (⟨751, by decide⟩ : Fin 1069) ∈ faceMask (⟨751, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0752 :
    faceAnchor (⟨752, by decide⟩ : Fin 1069) ∈ faceMask (⟨752, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0753 :
    faceAnchor (⟨753, by decide⟩ : Fin 1069) ∈ faceMask (⟨753, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0754 :
    faceAnchor (⟨754, by decide⟩ : Fin 1069) ∈ faceMask (⟨754, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0755 :
    faceAnchor (⟨755, by decide⟩ : Fin 1069) ∈ faceMask (⟨755, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0756 :
    faceAnchor (⟨756, by decide⟩ : Fin 1069) ∈ faceMask (⟨756, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0757 :
    faceAnchor (⟨757, by decide⟩ : Fin 1069) ∈ faceMask (⟨757, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0758 :
    faceAnchor (⟨758, by decide⟩ : Fin 1069) ∈ faceMask (⟨758, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0759 :
    faceAnchor (⟨759, by decide⟩ : Fin 1069) ∈ faceMask (⟨759, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0760 :
    faceAnchor (⟨760, by decide⟩ : Fin 1069) ∈ faceMask (⟨760, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0761 :
    faceAnchor (⟨761, by decide⟩ : Fin 1069) ∈ faceMask (⟨761, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0762 :
    faceAnchor (⟨762, by decide⟩ : Fin 1069) ∈ faceMask (⟨762, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0763 :
    faceAnchor (⟨763, by decide⟩ : Fin 1069) ∈ faceMask (⟨763, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0764 :
    faceAnchor (⟨764, by decide⟩ : Fin 1069) ∈ faceMask (⟨764, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0765 :
    faceAnchor (⟨765, by decide⟩ : Fin 1069) ∈ faceMask (⟨765, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0766 :
    faceAnchor (⟨766, by decide⟩ : Fin 1069) ∈ faceMask (⟨766, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0767 :
    faceAnchor (⟨767, by decide⟩ : Fin 1069) ∈ faceMask (⟨767, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0768 :
    faceAnchor (⟨768, by decide⟩ : Fin 1069) ∈ faceMask (⟨768, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0769 :
    faceAnchor (⟨769, by decide⟩ : Fin 1069) ∈ faceMask (⟨769, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0770 :
    faceAnchor (⟨770, by decide⟩ : Fin 1069) ∈ faceMask (⟨770, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0771 :
    faceAnchor (⟨771, by decide⟩ : Fin 1069) ∈ faceMask (⟨771, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0772 :
    faceAnchor (⟨772, by decide⟩ : Fin 1069) ∈ faceMask (⟨772, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0773 :
    faceAnchor (⟨773, by decide⟩ : Fin 1069) ∈ faceMask (⟨773, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0774 :
    faceAnchor (⟨774, by decide⟩ : Fin 1069) ∈ faceMask (⟨774, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0775 :
    faceAnchor (⟨775, by decide⟩ : Fin 1069) ∈ faceMask (⟨775, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0776 :
    faceAnchor (⟨776, by decide⟩ : Fin 1069) ∈ faceMask (⟨776, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0777 :
    faceAnchor (⟨777, by decide⟩ : Fin 1069) ∈ faceMask (⟨777, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0778 :
    faceAnchor (⟨778, by decide⟩ : Fin 1069) ∈ faceMask (⟨778, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0779 :
    faceAnchor (⟨779, by decide⟩ : Fin 1069) ∈ faceMask (⟨779, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0780 :
    faceAnchor (⟨780, by decide⟩ : Fin 1069) ∈ faceMask (⟨780, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0781 :
    faceAnchor (⟨781, by decide⟩ : Fin 1069) ∈ faceMask (⟨781, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0782 :
    faceAnchor (⟨782, by decide⟩ : Fin 1069) ∈ faceMask (⟨782, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0783 :
    faceAnchor (⟨783, by decide⟩ : Fin 1069) ∈ faceMask (⟨783, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0784 :
    faceAnchor (⟨784, by decide⟩ : Fin 1069) ∈ faceMask (⟨784, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0785 :
    faceAnchor (⟨785, by decide⟩ : Fin 1069) ∈ faceMask (⟨785, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0786 :
    faceAnchor (⟨786, by decide⟩ : Fin 1069) ∈ faceMask (⟨786, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0787 :
    faceAnchor (⟨787, by decide⟩ : Fin 1069) ∈ faceMask (⟨787, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0788 :
    faceAnchor (⟨788, by decide⟩ : Fin 1069) ∈ faceMask (⟨788, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0789 :
    faceAnchor (⟨789, by decide⟩ : Fin 1069) ∈ faceMask (⟨789, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0790 :
    faceAnchor (⟨790, by decide⟩ : Fin 1069) ∈ faceMask (⟨790, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0791 :
    faceAnchor (⟨791, by decide⟩ : Fin 1069) ∈ faceMask (⟨791, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0792 :
    faceAnchor (⟨792, by decide⟩ : Fin 1069) ∈ faceMask (⟨792, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0793 :
    faceAnchor (⟨793, by decide⟩ : Fin 1069) ∈ faceMask (⟨793, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0794 :
    faceAnchor (⟨794, by decide⟩ : Fin 1069) ∈ faceMask (⟨794, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0795 :
    faceAnchor (⟨795, by decide⟩ : Fin 1069) ∈ faceMask (⟨795, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0796 :
    faceAnchor (⟨796, by decide⟩ : Fin 1069) ∈ faceMask (⟨796, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0797 :
    faceAnchor (⟨797, by decide⟩ : Fin 1069) ∈ faceMask (⟨797, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0798 :
    faceAnchor (⟨798, by decide⟩ : Fin 1069) ∈ faceMask (⟨798, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0799 :
    faceAnchor (⟨799, by decide⟩ : Fin 1069) ∈ faceMask (⟨799, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0800 :
    faceAnchor (⟨800, by decide⟩ : Fin 1069) ∈ faceMask (⟨800, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0801 :
    faceAnchor (⟨801, by decide⟩ : Fin 1069) ∈ faceMask (⟨801, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0802 :
    faceAnchor (⟨802, by decide⟩ : Fin 1069) ∈ faceMask (⟨802, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0803 :
    faceAnchor (⟨803, by decide⟩ : Fin 1069) ∈ faceMask (⟨803, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0804 :
    faceAnchor (⟨804, by decide⟩ : Fin 1069) ∈ faceMask (⟨804, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0805 :
    faceAnchor (⟨805, by decide⟩ : Fin 1069) ∈ faceMask (⟨805, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0806 :
    faceAnchor (⟨806, by decide⟩ : Fin 1069) ∈ faceMask (⟨806, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0807 :
    faceAnchor (⟨807, by decide⟩ : Fin 1069) ∈ faceMask (⟨807, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0808 :
    faceAnchor (⟨808, by decide⟩ : Fin 1069) ∈ faceMask (⟨808, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0809 :
    faceAnchor (⟨809, by decide⟩ : Fin 1069) ∈ faceMask (⟨809, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0810 :
    faceAnchor (⟨810, by decide⟩ : Fin 1069) ∈ faceMask (⟨810, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0811 :
    faceAnchor (⟨811, by decide⟩ : Fin 1069) ∈ faceMask (⟨811, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0812 :
    faceAnchor (⟨812, by decide⟩ : Fin 1069) ∈ faceMask (⟨812, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0813 :
    faceAnchor (⟨813, by decide⟩ : Fin 1069) ∈ faceMask (⟨813, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0814 :
    faceAnchor (⟨814, by decide⟩ : Fin 1069) ∈ faceMask (⟨814, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0815 :
    faceAnchor (⟨815, by decide⟩ : Fin 1069) ∈ faceMask (⟨815, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0816 :
    faceAnchor (⟨816, by decide⟩ : Fin 1069) ∈ faceMask (⟨816, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0817 :
    faceAnchor (⟨817, by decide⟩ : Fin 1069) ∈ faceMask (⟨817, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0818 :
    faceAnchor (⟨818, by decide⟩ : Fin 1069) ∈ faceMask (⟨818, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0819 :
    faceAnchor (⟨819, by decide⟩ : Fin 1069) ∈ faceMask (⟨819, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0820 :
    faceAnchor (⟨820, by decide⟩ : Fin 1069) ∈ faceMask (⟨820, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0821 :
    faceAnchor (⟨821, by decide⟩ : Fin 1069) ∈ faceMask (⟨821, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0822 :
    faceAnchor (⟨822, by decide⟩ : Fin 1069) ∈ faceMask (⟨822, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0823 :
    faceAnchor (⟨823, by decide⟩ : Fin 1069) ∈ faceMask (⟨823, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0824 :
    faceAnchor (⟨824, by decide⟩ : Fin 1069) ∈ faceMask (⟨824, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0825 :
    faceAnchor (⟨825, by decide⟩ : Fin 1069) ∈ faceMask (⟨825, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0826 :
    faceAnchor (⟨826, by decide⟩ : Fin 1069) ∈ faceMask (⟨826, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0827 :
    faceAnchor (⟨827, by decide⟩ : Fin 1069) ∈ faceMask (⟨827, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0828 :
    faceAnchor (⟨828, by decide⟩ : Fin 1069) ∈ faceMask (⟨828, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0829 :
    faceAnchor (⟨829, by decide⟩ : Fin 1069) ∈ faceMask (⟨829, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0830 :
    faceAnchor (⟨830, by decide⟩ : Fin 1069) ∈ faceMask (⟨830, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0831 :
    faceAnchor (⟨831, by decide⟩ : Fin 1069) ∈ faceMask (⟨831, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0832 :
    faceAnchor (⟨832, by decide⟩ : Fin 1069) ∈ faceMask (⟨832, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0833 :
    faceAnchor (⟨833, by decide⟩ : Fin 1069) ∈ faceMask (⟨833, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0834 :
    faceAnchor (⟨834, by decide⟩ : Fin 1069) ∈ faceMask (⟨834, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0835 :
    faceAnchor (⟨835, by decide⟩ : Fin 1069) ∈ faceMask (⟨835, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0836 :
    faceAnchor (⟨836, by decide⟩ : Fin 1069) ∈ faceMask (⟨836, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0837 :
    faceAnchor (⟨837, by decide⟩ : Fin 1069) ∈ faceMask (⟨837, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0838 :
    faceAnchor (⟨838, by decide⟩ : Fin 1069) ∈ faceMask (⟨838, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0839 :
    faceAnchor (⟨839, by decide⟩ : Fin 1069) ∈ faceMask (⟨839, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0840 :
    faceAnchor (⟨840, by decide⟩ : Fin 1069) ∈ faceMask (⟨840, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0841 :
    faceAnchor (⟨841, by decide⟩ : Fin 1069) ∈ faceMask (⟨841, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0842 :
    faceAnchor (⟨842, by decide⟩ : Fin 1069) ∈ faceMask (⟨842, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0843 :
    faceAnchor (⟨843, by decide⟩ : Fin 1069) ∈ faceMask (⟨843, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0844 :
    faceAnchor (⟨844, by decide⟩ : Fin 1069) ∈ faceMask (⟨844, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0845 :
    faceAnchor (⟨845, by decide⟩ : Fin 1069) ∈ faceMask (⟨845, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0846 :
    faceAnchor (⟨846, by decide⟩ : Fin 1069) ∈ faceMask (⟨846, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0847 :
    faceAnchor (⟨847, by decide⟩ : Fin 1069) ∈ faceMask (⟨847, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0848 :
    faceAnchor (⟨848, by decide⟩ : Fin 1069) ∈ faceMask (⟨848, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0849 :
    faceAnchor (⟨849, by decide⟩ : Fin 1069) ∈ faceMask (⟨849, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0850 :
    faceAnchor (⟨850, by decide⟩ : Fin 1069) ∈ faceMask (⟨850, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0851 :
    faceAnchor (⟨851, by decide⟩ : Fin 1069) ∈ faceMask (⟨851, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0852 :
    faceAnchor (⟨852, by decide⟩ : Fin 1069) ∈ faceMask (⟨852, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0853 :
    faceAnchor (⟨853, by decide⟩ : Fin 1069) ∈ faceMask (⟨853, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0854 :
    faceAnchor (⟨854, by decide⟩ : Fin 1069) ∈ faceMask (⟨854, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0855 :
    faceAnchor (⟨855, by decide⟩ : Fin 1069) ∈ faceMask (⟨855, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0856 :
    faceAnchor (⟨856, by decide⟩ : Fin 1069) ∈ faceMask (⟨856, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0857 :
    faceAnchor (⟨857, by decide⟩ : Fin 1069) ∈ faceMask (⟨857, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0858 :
    faceAnchor (⟨858, by decide⟩ : Fin 1069) ∈ faceMask (⟨858, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0859 :
    faceAnchor (⟨859, by decide⟩ : Fin 1069) ∈ faceMask (⟨859, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0860 :
    faceAnchor (⟨860, by decide⟩ : Fin 1069) ∈ faceMask (⟨860, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0861 :
    faceAnchor (⟨861, by decide⟩ : Fin 1069) ∈ faceMask (⟨861, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0862 :
    faceAnchor (⟨862, by decide⟩ : Fin 1069) ∈ faceMask (⟨862, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0863 :
    faceAnchor (⟨863, by decide⟩ : Fin 1069) ∈ faceMask (⟨863, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0864 :
    faceAnchor (⟨864, by decide⟩ : Fin 1069) ∈ faceMask (⟨864, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0865 :
    faceAnchor (⟨865, by decide⟩ : Fin 1069) ∈ faceMask (⟨865, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0866 :
    faceAnchor (⟨866, by decide⟩ : Fin 1069) ∈ faceMask (⟨866, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0867 :
    faceAnchor (⟨867, by decide⟩ : Fin 1069) ∈ faceMask (⟨867, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0868 :
    faceAnchor (⟨868, by decide⟩ : Fin 1069) ∈ faceMask (⟨868, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0869 :
    faceAnchor (⟨869, by decide⟩ : Fin 1069) ∈ faceMask (⟨869, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0870 :
    faceAnchor (⟨870, by decide⟩ : Fin 1069) ∈ faceMask (⟨870, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0871 :
    faceAnchor (⟨871, by decide⟩ : Fin 1069) ∈ faceMask (⟨871, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0872 :
    faceAnchor (⟨872, by decide⟩ : Fin 1069) ∈ faceMask (⟨872, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0873 :
    faceAnchor (⟨873, by decide⟩ : Fin 1069) ∈ faceMask (⟨873, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0874 :
    faceAnchor (⟨874, by decide⟩ : Fin 1069) ∈ faceMask (⟨874, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0875 :
    faceAnchor (⟨875, by decide⟩ : Fin 1069) ∈ faceMask (⟨875, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0876 :
    faceAnchor (⟨876, by decide⟩ : Fin 1069) ∈ faceMask (⟨876, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0877 :
    faceAnchor (⟨877, by decide⟩ : Fin 1069) ∈ faceMask (⟨877, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0878 :
    faceAnchor (⟨878, by decide⟩ : Fin 1069) ∈ faceMask (⟨878, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0879 :
    faceAnchor (⟨879, by decide⟩ : Fin 1069) ∈ faceMask (⟨879, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0880 :
    faceAnchor (⟨880, by decide⟩ : Fin 1069) ∈ faceMask (⟨880, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0881 :
    faceAnchor (⟨881, by decide⟩ : Fin 1069) ∈ faceMask (⟨881, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0882 :
    faceAnchor (⟨882, by decide⟩ : Fin 1069) ∈ faceMask (⟨882, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0883 :
    faceAnchor (⟨883, by decide⟩ : Fin 1069) ∈ faceMask (⟨883, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0884 :
    faceAnchor (⟨884, by decide⟩ : Fin 1069) ∈ faceMask (⟨884, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0885 :
    faceAnchor (⟨885, by decide⟩ : Fin 1069) ∈ faceMask (⟨885, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0886 :
    faceAnchor (⟨886, by decide⟩ : Fin 1069) ∈ faceMask (⟨886, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0887 :
    faceAnchor (⟨887, by decide⟩ : Fin 1069) ∈ faceMask (⟨887, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0888 :
    faceAnchor (⟨888, by decide⟩ : Fin 1069) ∈ faceMask (⟨888, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0889 :
    faceAnchor (⟨889, by decide⟩ : Fin 1069) ∈ faceMask (⟨889, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0890 :
    faceAnchor (⟨890, by decide⟩ : Fin 1069) ∈ faceMask (⟨890, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0891 :
    faceAnchor (⟨891, by decide⟩ : Fin 1069) ∈ faceMask (⟨891, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0892 :
    faceAnchor (⟨892, by decide⟩ : Fin 1069) ∈ faceMask (⟨892, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0893 :
    faceAnchor (⟨893, by decide⟩ : Fin 1069) ∈ faceMask (⟨893, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0894 :
    faceAnchor (⟨894, by decide⟩ : Fin 1069) ∈ faceMask (⟨894, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0895 :
    faceAnchor (⟨895, by decide⟩ : Fin 1069) ∈ faceMask (⟨895, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0896 :
    faceAnchor (⟨896, by decide⟩ : Fin 1069) ∈ faceMask (⟨896, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0897 :
    faceAnchor (⟨897, by decide⟩ : Fin 1069) ∈ faceMask (⟨897, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0898 :
    faceAnchor (⟨898, by decide⟩ : Fin 1069) ∈ faceMask (⟨898, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0899 :
    faceAnchor (⟨899, by decide⟩ : Fin 1069) ∈ faceMask (⟨899, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0900 :
    faceAnchor (⟨900, by decide⟩ : Fin 1069) ∈ faceMask (⟨900, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0901 :
    faceAnchor (⟨901, by decide⟩ : Fin 1069) ∈ faceMask (⟨901, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0902 :
    faceAnchor (⟨902, by decide⟩ : Fin 1069) ∈ faceMask (⟨902, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0903 :
    faceAnchor (⟨903, by decide⟩ : Fin 1069) ∈ faceMask (⟨903, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0904 :
    faceAnchor (⟨904, by decide⟩ : Fin 1069) ∈ faceMask (⟨904, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0905 :
    faceAnchor (⟨905, by decide⟩ : Fin 1069) ∈ faceMask (⟨905, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0906 :
    faceAnchor (⟨906, by decide⟩ : Fin 1069) ∈ faceMask (⟨906, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0907 :
    faceAnchor (⟨907, by decide⟩ : Fin 1069) ∈ faceMask (⟨907, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0908 :
    faceAnchor (⟨908, by decide⟩ : Fin 1069) ∈ faceMask (⟨908, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0909 :
    faceAnchor (⟨909, by decide⟩ : Fin 1069) ∈ faceMask (⟨909, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0910 :
    faceAnchor (⟨910, by decide⟩ : Fin 1069) ∈ faceMask (⟨910, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0911 :
    faceAnchor (⟨911, by decide⟩ : Fin 1069) ∈ faceMask (⟨911, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0912 :
    faceAnchor (⟨912, by decide⟩ : Fin 1069) ∈ faceMask (⟨912, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0913 :
    faceAnchor (⟨913, by decide⟩ : Fin 1069) ∈ faceMask (⟨913, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0914 :
    faceAnchor (⟨914, by decide⟩ : Fin 1069) ∈ faceMask (⟨914, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0915 :
    faceAnchor (⟨915, by decide⟩ : Fin 1069) ∈ faceMask (⟨915, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0916 :
    faceAnchor (⟨916, by decide⟩ : Fin 1069) ∈ faceMask (⟨916, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0917 :
    faceAnchor (⟨917, by decide⟩ : Fin 1069) ∈ faceMask (⟨917, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0918 :
    faceAnchor (⟨918, by decide⟩ : Fin 1069) ∈ faceMask (⟨918, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0919 :
    faceAnchor (⟨919, by decide⟩ : Fin 1069) ∈ faceMask (⟨919, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0920 :
    faceAnchor (⟨920, by decide⟩ : Fin 1069) ∈ faceMask (⟨920, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0921 :
    faceAnchor (⟨921, by decide⟩ : Fin 1069) ∈ faceMask (⟨921, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0922 :
    faceAnchor (⟨922, by decide⟩ : Fin 1069) ∈ faceMask (⟨922, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0923 :
    faceAnchor (⟨923, by decide⟩ : Fin 1069) ∈ faceMask (⟨923, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0924 :
    faceAnchor (⟨924, by decide⟩ : Fin 1069) ∈ faceMask (⟨924, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0925 :
    faceAnchor (⟨925, by decide⟩ : Fin 1069) ∈ faceMask (⟨925, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0926 :
    faceAnchor (⟨926, by decide⟩ : Fin 1069) ∈ faceMask (⟨926, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0927 :
    faceAnchor (⟨927, by decide⟩ : Fin 1069) ∈ faceMask (⟨927, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0928 :
    faceAnchor (⟨928, by decide⟩ : Fin 1069) ∈ faceMask (⟨928, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0929 :
    faceAnchor (⟨929, by decide⟩ : Fin 1069) ∈ faceMask (⟨929, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0930 :
    faceAnchor (⟨930, by decide⟩ : Fin 1069) ∈ faceMask (⟨930, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0931 :
    faceAnchor (⟨931, by decide⟩ : Fin 1069) ∈ faceMask (⟨931, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0932 :
    faceAnchor (⟨932, by decide⟩ : Fin 1069) ∈ faceMask (⟨932, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0933 :
    faceAnchor (⟨933, by decide⟩ : Fin 1069) ∈ faceMask (⟨933, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0934 :
    faceAnchor (⟨934, by decide⟩ : Fin 1069) ∈ faceMask (⟨934, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0935 :
    faceAnchor (⟨935, by decide⟩ : Fin 1069) ∈ faceMask (⟨935, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0936 :
    faceAnchor (⟨936, by decide⟩ : Fin 1069) ∈ faceMask (⟨936, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0937 :
    faceAnchor (⟨937, by decide⟩ : Fin 1069) ∈ faceMask (⟨937, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0938 :
    faceAnchor (⟨938, by decide⟩ : Fin 1069) ∈ faceMask (⟨938, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0939 :
    faceAnchor (⟨939, by decide⟩ : Fin 1069) ∈ faceMask (⟨939, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0940 :
    faceAnchor (⟨940, by decide⟩ : Fin 1069) ∈ faceMask (⟨940, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0941 :
    faceAnchor (⟨941, by decide⟩ : Fin 1069) ∈ faceMask (⟨941, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0942 :
    faceAnchor (⟨942, by decide⟩ : Fin 1069) ∈ faceMask (⟨942, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0943 :
    faceAnchor (⟨943, by decide⟩ : Fin 1069) ∈ faceMask (⟨943, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0944 :
    faceAnchor (⟨944, by decide⟩ : Fin 1069) ∈ faceMask (⟨944, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0945 :
    faceAnchor (⟨945, by decide⟩ : Fin 1069) ∈ faceMask (⟨945, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0946 :
    faceAnchor (⟨946, by decide⟩ : Fin 1069) ∈ faceMask (⟨946, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0947 :
    faceAnchor (⟨947, by decide⟩ : Fin 1069) ∈ faceMask (⟨947, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0948 :
    faceAnchor (⟨948, by decide⟩ : Fin 1069) ∈ faceMask (⟨948, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0949 :
    faceAnchor (⟨949, by decide⟩ : Fin 1069) ∈ faceMask (⟨949, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0950 :
    faceAnchor (⟨950, by decide⟩ : Fin 1069) ∈ faceMask (⟨950, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0951 :
    faceAnchor (⟨951, by decide⟩ : Fin 1069) ∈ faceMask (⟨951, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0952 :
    faceAnchor (⟨952, by decide⟩ : Fin 1069) ∈ faceMask (⟨952, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0953 :
    faceAnchor (⟨953, by decide⟩ : Fin 1069) ∈ faceMask (⟨953, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0954 :
    faceAnchor (⟨954, by decide⟩ : Fin 1069) ∈ faceMask (⟨954, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0955 :
    faceAnchor (⟨955, by decide⟩ : Fin 1069) ∈ faceMask (⟨955, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0956 :
    faceAnchor (⟨956, by decide⟩ : Fin 1069) ∈ faceMask (⟨956, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0957 :
    faceAnchor (⟨957, by decide⟩ : Fin 1069) ∈ faceMask (⟨957, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0958 :
    faceAnchor (⟨958, by decide⟩ : Fin 1069) ∈ faceMask (⟨958, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0959 :
    faceAnchor (⟨959, by decide⟩ : Fin 1069) ∈ faceMask (⟨959, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0960 :
    faceAnchor (⟨960, by decide⟩ : Fin 1069) ∈ faceMask (⟨960, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0961 :
    faceAnchor (⟨961, by decide⟩ : Fin 1069) ∈ faceMask (⟨961, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0962 :
    faceAnchor (⟨962, by decide⟩ : Fin 1069) ∈ faceMask (⟨962, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0963 :
    faceAnchor (⟨963, by decide⟩ : Fin 1069) ∈ faceMask (⟨963, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0964 :
    faceAnchor (⟨964, by decide⟩ : Fin 1069) ∈ faceMask (⟨964, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0965 :
    faceAnchor (⟨965, by decide⟩ : Fin 1069) ∈ faceMask (⟨965, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0966 :
    faceAnchor (⟨966, by decide⟩ : Fin 1069) ∈ faceMask (⟨966, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0967 :
    faceAnchor (⟨967, by decide⟩ : Fin 1069) ∈ faceMask (⟨967, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0968 :
    faceAnchor (⟨968, by decide⟩ : Fin 1069) ∈ faceMask (⟨968, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0969 :
    faceAnchor (⟨969, by decide⟩ : Fin 1069) ∈ faceMask (⟨969, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0970 :
    faceAnchor (⟨970, by decide⟩ : Fin 1069) ∈ faceMask (⟨970, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0971 :
    faceAnchor (⟨971, by decide⟩ : Fin 1069) ∈ faceMask (⟨971, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0972 :
    faceAnchor (⟨972, by decide⟩ : Fin 1069) ∈ faceMask (⟨972, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0973 :
    faceAnchor (⟨973, by decide⟩ : Fin 1069) ∈ faceMask (⟨973, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0974 :
    faceAnchor (⟨974, by decide⟩ : Fin 1069) ∈ faceMask (⟨974, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0975 :
    faceAnchor (⟨975, by decide⟩ : Fin 1069) ∈ faceMask (⟨975, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0976 :
    faceAnchor (⟨976, by decide⟩ : Fin 1069) ∈ faceMask (⟨976, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0977 :
    faceAnchor (⟨977, by decide⟩ : Fin 1069) ∈ faceMask (⟨977, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0978 :
    faceAnchor (⟨978, by decide⟩ : Fin 1069) ∈ faceMask (⟨978, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0979 :
    faceAnchor (⟨979, by decide⟩ : Fin 1069) ∈ faceMask (⟨979, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0980 :
    faceAnchor (⟨980, by decide⟩ : Fin 1069) ∈ faceMask (⟨980, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0981 :
    faceAnchor (⟨981, by decide⟩ : Fin 1069) ∈ faceMask (⟨981, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0982 :
    faceAnchor (⟨982, by decide⟩ : Fin 1069) ∈ faceMask (⟨982, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0983 :
    faceAnchor (⟨983, by decide⟩ : Fin 1069) ∈ faceMask (⟨983, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0984 :
    faceAnchor (⟨984, by decide⟩ : Fin 1069) ∈ faceMask (⟨984, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0985 :
    faceAnchor (⟨985, by decide⟩ : Fin 1069) ∈ faceMask (⟨985, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0986 :
    faceAnchor (⟨986, by decide⟩ : Fin 1069) ∈ faceMask (⟨986, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0987 :
    faceAnchor (⟨987, by decide⟩ : Fin 1069) ∈ faceMask (⟨987, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0988 :
    faceAnchor (⟨988, by decide⟩ : Fin 1069) ∈ faceMask (⟨988, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0989 :
    faceAnchor (⟨989, by decide⟩ : Fin 1069) ∈ faceMask (⟨989, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0990 :
    faceAnchor (⟨990, by decide⟩ : Fin 1069) ∈ faceMask (⟨990, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0991 :
    faceAnchor (⟨991, by decide⟩ : Fin 1069) ∈ faceMask (⟨991, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0992 :
    faceAnchor (⟨992, by decide⟩ : Fin 1069) ∈ faceMask (⟨992, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0993 :
    faceAnchor (⟨993, by decide⟩ : Fin 1069) ∈ faceMask (⟨993, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0994 :
    faceAnchor (⟨994, by decide⟩ : Fin 1069) ∈ faceMask (⟨994, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0995 :
    faceAnchor (⟨995, by decide⟩ : Fin 1069) ∈ faceMask (⟨995, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0996 :
    faceAnchor (⟨996, by decide⟩ : Fin 1069) ∈ faceMask (⟨996, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0997 :
    faceAnchor (⟨997, by decide⟩ : Fin 1069) ∈ faceMask (⟨997, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0998 :
    faceAnchor (⟨998, by decide⟩ : Fin 1069) ∈ faceMask (⟨998, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor0999 :
    faceAnchor (⟨999, by decide⟩ : Fin 1069) ∈ faceMask (⟨999, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1000 :
    faceAnchor (⟨1000, by decide⟩ : Fin 1069) ∈ faceMask (⟨1000, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1001 :
    faceAnchor (⟨1001, by decide⟩ : Fin 1069) ∈ faceMask (⟨1001, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1002 :
    faceAnchor (⟨1002, by decide⟩ : Fin 1069) ∈ faceMask (⟨1002, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1003 :
    faceAnchor (⟨1003, by decide⟩ : Fin 1069) ∈ faceMask (⟨1003, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1004 :
    faceAnchor (⟨1004, by decide⟩ : Fin 1069) ∈ faceMask (⟨1004, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1005 :
    faceAnchor (⟨1005, by decide⟩ : Fin 1069) ∈ faceMask (⟨1005, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1006 :
    faceAnchor (⟨1006, by decide⟩ : Fin 1069) ∈ faceMask (⟨1006, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1007 :
    faceAnchor (⟨1007, by decide⟩ : Fin 1069) ∈ faceMask (⟨1007, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1008 :
    faceAnchor (⟨1008, by decide⟩ : Fin 1069) ∈ faceMask (⟨1008, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1009 :
    faceAnchor (⟨1009, by decide⟩ : Fin 1069) ∈ faceMask (⟨1009, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1010 :
    faceAnchor (⟨1010, by decide⟩ : Fin 1069) ∈ faceMask (⟨1010, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1011 :
    faceAnchor (⟨1011, by decide⟩ : Fin 1069) ∈ faceMask (⟨1011, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1012 :
    faceAnchor (⟨1012, by decide⟩ : Fin 1069) ∈ faceMask (⟨1012, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1013 :
    faceAnchor (⟨1013, by decide⟩ : Fin 1069) ∈ faceMask (⟨1013, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1014 :
    faceAnchor (⟨1014, by decide⟩ : Fin 1069) ∈ faceMask (⟨1014, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1015 :
    faceAnchor (⟨1015, by decide⟩ : Fin 1069) ∈ faceMask (⟨1015, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1016 :
    faceAnchor (⟨1016, by decide⟩ : Fin 1069) ∈ faceMask (⟨1016, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1017 :
    faceAnchor (⟨1017, by decide⟩ : Fin 1069) ∈ faceMask (⟨1017, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1018 :
    faceAnchor (⟨1018, by decide⟩ : Fin 1069) ∈ faceMask (⟨1018, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1019 :
    faceAnchor (⟨1019, by decide⟩ : Fin 1069) ∈ faceMask (⟨1019, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1020 :
    faceAnchor (⟨1020, by decide⟩ : Fin 1069) ∈ faceMask (⟨1020, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1021 :
    faceAnchor (⟨1021, by decide⟩ : Fin 1069) ∈ faceMask (⟨1021, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1022 :
    faceAnchor (⟨1022, by decide⟩ : Fin 1069) ∈ faceMask (⟨1022, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1023 :
    faceAnchor (⟨1023, by decide⟩ : Fin 1069) ∈ faceMask (⟨1023, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1024 :
    faceAnchor (⟨1024, by decide⟩ : Fin 1069) ∈ faceMask (⟨1024, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1025 :
    faceAnchor (⟨1025, by decide⟩ : Fin 1069) ∈ faceMask (⟨1025, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1026 :
    faceAnchor (⟨1026, by decide⟩ : Fin 1069) ∈ faceMask (⟨1026, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1027 :
    faceAnchor (⟨1027, by decide⟩ : Fin 1069) ∈ faceMask (⟨1027, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1028 :
    faceAnchor (⟨1028, by decide⟩ : Fin 1069) ∈ faceMask (⟨1028, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1029 :
    faceAnchor (⟨1029, by decide⟩ : Fin 1069) ∈ faceMask (⟨1029, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1030 :
    faceAnchor (⟨1030, by decide⟩ : Fin 1069) ∈ faceMask (⟨1030, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1031 :
    faceAnchor (⟨1031, by decide⟩ : Fin 1069) ∈ faceMask (⟨1031, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1032 :
    faceAnchor (⟨1032, by decide⟩ : Fin 1069) ∈ faceMask (⟨1032, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1033 :
    faceAnchor (⟨1033, by decide⟩ : Fin 1069) ∈ faceMask (⟨1033, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1034 :
    faceAnchor (⟨1034, by decide⟩ : Fin 1069) ∈ faceMask (⟨1034, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1035 :
    faceAnchor (⟨1035, by decide⟩ : Fin 1069) ∈ faceMask (⟨1035, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1036 :
    faceAnchor (⟨1036, by decide⟩ : Fin 1069) ∈ faceMask (⟨1036, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1037 :
    faceAnchor (⟨1037, by decide⟩ : Fin 1069) ∈ faceMask (⟨1037, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1038 :
    faceAnchor (⟨1038, by decide⟩ : Fin 1069) ∈ faceMask (⟨1038, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1039 :
    faceAnchor (⟨1039, by decide⟩ : Fin 1069) ∈ faceMask (⟨1039, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1040 :
    faceAnchor (⟨1040, by decide⟩ : Fin 1069) ∈ faceMask (⟨1040, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1041 :
    faceAnchor (⟨1041, by decide⟩ : Fin 1069) ∈ faceMask (⟨1041, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1042 :
    faceAnchor (⟨1042, by decide⟩ : Fin 1069) ∈ faceMask (⟨1042, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1043 :
    faceAnchor (⟨1043, by decide⟩ : Fin 1069) ∈ faceMask (⟨1043, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1044 :
    faceAnchor (⟨1044, by decide⟩ : Fin 1069) ∈ faceMask (⟨1044, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1045 :
    faceAnchor (⟨1045, by decide⟩ : Fin 1069) ∈ faceMask (⟨1045, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1046 :
    faceAnchor (⟨1046, by decide⟩ : Fin 1069) ∈ faceMask (⟨1046, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1047 :
    faceAnchor (⟨1047, by decide⟩ : Fin 1069) ∈ faceMask (⟨1047, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1048 :
    faceAnchor (⟨1048, by decide⟩ : Fin 1069) ∈ faceMask (⟨1048, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1049 :
    faceAnchor (⟨1049, by decide⟩ : Fin 1069) ∈ faceMask (⟨1049, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1050 :
    faceAnchor (⟨1050, by decide⟩ : Fin 1069) ∈ faceMask (⟨1050, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1051 :
    faceAnchor (⟨1051, by decide⟩ : Fin 1069) ∈ faceMask (⟨1051, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1052 :
    faceAnchor (⟨1052, by decide⟩ : Fin 1069) ∈ faceMask (⟨1052, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1053 :
    faceAnchor (⟨1053, by decide⟩ : Fin 1069) ∈ faceMask (⟨1053, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1054 :
    faceAnchor (⟨1054, by decide⟩ : Fin 1069) ∈ faceMask (⟨1054, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1055 :
    faceAnchor (⟨1055, by decide⟩ : Fin 1069) ∈ faceMask (⟨1055, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1056 :
    faceAnchor (⟨1056, by decide⟩ : Fin 1069) ∈ faceMask (⟨1056, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1057 :
    faceAnchor (⟨1057, by decide⟩ : Fin 1069) ∈ faceMask (⟨1057, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1058 :
    faceAnchor (⟨1058, by decide⟩ : Fin 1069) ∈ faceMask (⟨1058, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1059 :
    faceAnchor (⟨1059, by decide⟩ : Fin 1069) ∈ faceMask (⟨1059, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1060 :
    faceAnchor (⟨1060, by decide⟩ : Fin 1069) ∈ faceMask (⟨1060, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1061 :
    faceAnchor (⟨1061, by decide⟩ : Fin 1069) ∈ faceMask (⟨1061, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1062 :
    faceAnchor (⟨1062, by decide⟩ : Fin 1069) ∈ faceMask (⟨1062, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1063 :
    faceAnchor (⟨1063, by decide⟩ : Fin 1069) ∈ faceMask (⟨1063, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1064 :
    faceAnchor (⟨1064, by decide⟩ : Fin 1069) ∈ faceMask (⟨1064, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1065 :
    faceAnchor (⟨1065, by decide⟩ : Fin 1069) ∈ faceMask (⟨1065, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1066 :
    faceAnchor (⟨1066, by decide⟩ : Fin 1069) ∈ faceMask (⟨1066, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1067 :
    faceAnchor (⟨1067, by decide⟩ : Fin 1069) ∈ faceMask (⟨1067, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchor1068 :
    faceAnchor (⟨1068, by decide⟩ : Fin 1069) ∈ faceMask (⟨1068, by decide⟩ : Fin 1069) := by decide +kernel

private theorem anchorGroup0000 (i : Fin 1069)
    (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h16 : i.val < 16
  ·
    by_cases h8 : i.val < 8
    ·
      by_cases h4 : i.val < 4
      ·
        by_cases h2 : i.val < 2
        ·
          by_cases h1 : i.val < 1
          ·
            have he : (⟨0, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 0 = i.val
              omega
            simpa only [he] using anchor0000
          ·
            have he : (⟨1, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using anchor0001
        ·
          by_cases h3 : i.val < 3
          ·
            have he : (⟨2, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using anchor0002
          ·
            have he : (⟨3, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 3 = i.val
              omega
            simpa only [he] using anchor0003
      ·
        by_cases h6 : i.val < 6
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using anchor0004
          ·
            have he : (⟨5, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using anchor0005
        ·
          by_cases h7 : i.val < 7
          ·
            have he : (⟨6, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 6 = i.val
              omega
            simpa only [he] using anchor0006
          ·
            have he : (⟨7, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using anchor0007
    ·
      by_cases h12 : i.val < 12
      ·
        by_cases h10 : i.val < 10
        ·
          by_cases h9 : i.val < 9
          ·
            have he : (⟨8, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 8 = i.val
              omega
            simpa only [he] using anchor0008
          ·
            have he : (⟨9, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 9 = i.val
              omega
            simpa only [he] using anchor0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using anchor0010
          ·
            have he : (⟨11, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using anchor0011
      ·
        by_cases h14 : i.val < 14
        ·
          by_cases h13 : i.val < 13
          ·
            have he : (⟨12, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 12 = i.val
              omega
            simpa only [he] using anchor0012
          ·
            have he : (⟨13, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using anchor0013
        ·
          by_cases h15 : i.val < 15
          ·
            have he : (⟨14, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using anchor0014
          ·
            have he : (⟨15, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 15 = i.val
              omega
            simpa only [he] using anchor0015
  ·
    by_cases h24 : i.val < 24
    ·
      by_cases h20 : i.val < 20
      ·
        by_cases h18 : i.val < 18
        ·
          by_cases h17 : i.val < 17
          ·
            have he : (⟨16, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 16 = i.val
              omega
            simpa only [he] using anchor0016
          ·
            have he : (⟨17, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using anchor0017
        ·
          by_cases h19 : i.val < 19
          ·
            have he : (⟨18, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 18 = i.val
              omega
            simpa only [he] using anchor0018
          ·
            have he : (⟨19, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using anchor0019
      ·
        by_cases h22 : i.val < 22
        ·
          by_cases h21 : i.val < 21
          ·
            have he : (⟨20, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using anchor0020
          ·
            have he : (⟨21, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 21 = i.val
              omega
            simpa only [he] using anchor0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using anchor0022
          ·
            have he : (⟨23, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using anchor0023
    ·
      by_cases h28 : i.val < 28
      ·
        by_cases h26 : i.val < 26
        ·
          by_cases h25 : i.val < 25
          ·
            have he : (⟨24, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 24 = i.val
              omega
            simpa only [he] using anchor0024
          ·
            have he : (⟨25, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 25 = i.val
              omega
            simpa only [he] using anchor0025
        ·
          by_cases h27 : i.val < 27
          ·
            have he : (⟨26, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 26 = i.val
              omega
            simpa only [he] using anchor0026
          ·
            have he : (⟨27, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 27 = i.val
              omega
            simpa only [he] using anchor0027
      ·
        by_cases h30 : i.val < 30
        ·
          by_cases h29 : i.val < 29
          ·
            have he : (⟨28, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 28 = i.val
              omega
            simpa only [he] using anchor0028
          ·
            have he : (⟨29, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 29 = i.val
              omega
            simpa only [he] using anchor0029
        ·
          by_cases h31 : i.val < 31
          ·
            have he : (⟨30, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 30 = i.val
              omega
            simpa only [he] using anchor0030
          ·
            have he : (⟨31, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 31 = i.val
              omega
            simpa only [he] using anchor0031

private theorem anchorGroup0001 (i : Fin 1069)
    (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h48 : i.val < 48
  ·
    by_cases h40 : i.val < 40
    ·
      by_cases h36 : i.val < 36
      ·
        by_cases h34 : i.val < 34
        ·
          by_cases h33 : i.val < 33
          ·
            have he : (⟨32, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 32 = i.val
              omega
            simpa only [he] using anchor0032
          ·
            have he : (⟨33, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 33 = i.val
              omega
            simpa only [he] using anchor0033
        ·
          by_cases h35 : i.val < 35
          ·
            have he : (⟨34, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 34 = i.val
              omega
            simpa only [he] using anchor0034
          ·
            have he : (⟨35, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 35 = i.val
              omega
            simpa only [he] using anchor0035
      ·
        by_cases h38 : i.val < 38
        ·
          by_cases h37 : i.val < 37
          ·
            have he : (⟨36, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 36 = i.val
              omega
            simpa only [he] using anchor0036
          ·
            have he : (⟨37, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 37 = i.val
              omega
            simpa only [he] using anchor0037
        ·
          by_cases h39 : i.val < 39
          ·
            have he : (⟨38, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 38 = i.val
              omega
            simpa only [he] using anchor0038
          ·
            have he : (⟨39, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 39 = i.val
              omega
            simpa only [he] using anchor0039
    ·
      by_cases h44 : i.val < 44
      ·
        by_cases h42 : i.val < 42
        ·
          by_cases h41 : i.val < 41
          ·
            have he : (⟨40, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 40 = i.val
              omega
            simpa only [he] using anchor0040
          ·
            have he : (⟨41, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 41 = i.val
              omega
            simpa only [he] using anchor0041
        ·
          by_cases h43 : i.val < 43
          ·
            have he : (⟨42, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 42 = i.val
              omega
            simpa only [he] using anchor0042
          ·
            have he : (⟨43, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 43 = i.val
              omega
            simpa only [he] using anchor0043
      ·
        by_cases h46 : i.val < 46
        ·
          by_cases h45 : i.val < 45
          ·
            have he : (⟨44, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 44 = i.val
              omega
            simpa only [he] using anchor0044
          ·
            have he : (⟨45, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 45 = i.val
              omega
            simpa only [he] using anchor0045
        ·
          by_cases h47 : i.val < 47
          ·
            have he : (⟨46, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 46 = i.val
              omega
            simpa only [he] using anchor0046
          ·
            have he : (⟨47, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 47 = i.val
              omega
            simpa only [he] using anchor0047
  ·
    by_cases h56 : i.val < 56
    ·
      by_cases h52 : i.val < 52
      ·
        by_cases h50 : i.val < 50
        ·
          by_cases h49 : i.val < 49
          ·
            have he : (⟨48, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 48 = i.val
              omega
            simpa only [he] using anchor0048
          ·
            have he : (⟨49, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 49 = i.val
              omega
            simpa only [he] using anchor0049
        ·
          by_cases h51 : i.val < 51
          ·
            have he : (⟨50, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 50 = i.val
              omega
            simpa only [he] using anchor0050
          ·
            have he : (⟨51, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 51 = i.val
              omega
            simpa only [he] using anchor0051
      ·
        by_cases h54 : i.val < 54
        ·
          by_cases h53 : i.val < 53
          ·
            have he : (⟨52, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 52 = i.val
              omega
            simpa only [he] using anchor0052
          ·
            have he : (⟨53, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 53 = i.val
              omega
            simpa only [he] using anchor0053
        ·
          by_cases h55 : i.val < 55
          ·
            have he : (⟨54, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 54 = i.val
              omega
            simpa only [he] using anchor0054
          ·
            have he : (⟨55, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 55 = i.val
              omega
            simpa only [he] using anchor0055
    ·
      by_cases h60 : i.val < 60
      ·
        by_cases h58 : i.val < 58
        ·
          by_cases h57 : i.val < 57
          ·
            have he : (⟨56, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 56 = i.val
              omega
            simpa only [he] using anchor0056
          ·
            have he : (⟨57, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 57 = i.val
              omega
            simpa only [he] using anchor0057
        ·
          by_cases h59 : i.val < 59
          ·
            have he : (⟨58, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 58 = i.val
              omega
            simpa only [he] using anchor0058
          ·
            have he : (⟨59, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 59 = i.val
              omega
            simpa only [he] using anchor0059
      ·
        by_cases h62 : i.val < 62
        ·
          by_cases h61 : i.val < 61
          ·
            have he : (⟨60, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 60 = i.val
              omega
            simpa only [he] using anchor0060
          ·
            have he : (⟨61, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 61 = i.val
              omega
            simpa only [he] using anchor0061
        ·
          by_cases h63 : i.val < 63
          ·
            have he : (⟨62, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 62 = i.val
              omega
            simpa only [he] using anchor0062
          ·
            have he : (⟨63, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 63 = i.val
              omega
            simpa only [he] using anchor0063

private theorem anchorGroup0002 (i : Fin 1069)
    (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h80 : i.val < 80
  ·
    by_cases h72 : i.val < 72
    ·
      by_cases h68 : i.val < 68
      ·
        by_cases h66 : i.val < 66
        ·
          by_cases h65 : i.val < 65
          ·
            have he : (⟨64, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 64 = i.val
              omega
            simpa only [he] using anchor0064
          ·
            have he : (⟨65, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 65 = i.val
              omega
            simpa only [he] using anchor0065
        ·
          by_cases h67 : i.val < 67
          ·
            have he : (⟨66, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 66 = i.val
              omega
            simpa only [he] using anchor0066
          ·
            have he : (⟨67, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 67 = i.val
              omega
            simpa only [he] using anchor0067
      ·
        by_cases h70 : i.val < 70
        ·
          by_cases h69 : i.val < 69
          ·
            have he : (⟨68, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 68 = i.val
              omega
            simpa only [he] using anchor0068
          ·
            have he : (⟨69, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 69 = i.val
              omega
            simpa only [he] using anchor0069
        ·
          by_cases h71 : i.val < 71
          ·
            have he : (⟨70, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 70 = i.val
              omega
            simpa only [he] using anchor0070
          ·
            have he : (⟨71, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 71 = i.val
              omega
            simpa only [he] using anchor0071
    ·
      by_cases h76 : i.val < 76
      ·
        by_cases h74 : i.val < 74
        ·
          by_cases h73 : i.val < 73
          ·
            have he : (⟨72, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 72 = i.val
              omega
            simpa only [he] using anchor0072
          ·
            have he : (⟨73, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 73 = i.val
              omega
            simpa only [he] using anchor0073
        ·
          by_cases h75 : i.val < 75
          ·
            have he : (⟨74, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 74 = i.val
              omega
            simpa only [he] using anchor0074
          ·
            have he : (⟨75, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 75 = i.val
              omega
            simpa only [he] using anchor0075
      ·
        by_cases h78 : i.val < 78
        ·
          by_cases h77 : i.val < 77
          ·
            have he : (⟨76, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 76 = i.val
              omega
            simpa only [he] using anchor0076
          ·
            have he : (⟨77, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 77 = i.val
              omega
            simpa only [he] using anchor0077
        ·
          by_cases h79 : i.val < 79
          ·
            have he : (⟨78, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 78 = i.val
              omega
            simpa only [he] using anchor0078
          ·
            have he : (⟨79, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 79 = i.val
              omega
            simpa only [he] using anchor0079
  ·
    by_cases h88 : i.val < 88
    ·
      by_cases h84 : i.val < 84
      ·
        by_cases h82 : i.val < 82
        ·
          by_cases h81 : i.val < 81
          ·
            have he : (⟨80, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 80 = i.val
              omega
            simpa only [he] using anchor0080
          ·
            have he : (⟨81, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 81 = i.val
              omega
            simpa only [he] using anchor0081
        ·
          by_cases h83 : i.val < 83
          ·
            have he : (⟨82, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 82 = i.val
              omega
            simpa only [he] using anchor0082
          ·
            have he : (⟨83, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 83 = i.val
              omega
            simpa only [he] using anchor0083
      ·
        by_cases h86 : i.val < 86
        ·
          by_cases h85 : i.val < 85
          ·
            have he : (⟨84, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 84 = i.val
              omega
            simpa only [he] using anchor0084
          ·
            have he : (⟨85, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 85 = i.val
              omega
            simpa only [he] using anchor0085
        ·
          by_cases h87 : i.val < 87
          ·
            have he : (⟨86, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 86 = i.val
              omega
            simpa only [he] using anchor0086
          ·
            have he : (⟨87, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 87 = i.val
              omega
            simpa only [he] using anchor0087
    ·
      by_cases h92 : i.val < 92
      ·
        by_cases h90 : i.val < 90
        ·
          by_cases h89 : i.val < 89
          ·
            have he : (⟨88, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 88 = i.val
              omega
            simpa only [he] using anchor0088
          ·
            have he : (⟨89, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 89 = i.val
              omega
            simpa only [he] using anchor0089
        ·
          by_cases h91 : i.val < 91
          ·
            have he : (⟨90, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 90 = i.val
              omega
            simpa only [he] using anchor0090
          ·
            have he : (⟨91, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 91 = i.val
              omega
            simpa only [he] using anchor0091
      ·
        by_cases h94 : i.val < 94
        ·
          by_cases h93 : i.val < 93
          ·
            have he : (⟨92, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 92 = i.val
              omega
            simpa only [he] using anchor0092
          ·
            have he : (⟨93, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 93 = i.val
              omega
            simpa only [he] using anchor0093
        ·
          by_cases h95 : i.val < 95
          ·
            have he : (⟨94, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 94 = i.val
              omega
            simpa only [he] using anchor0094
          ·
            have he : (⟨95, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 95 = i.val
              omega
            simpa only [he] using anchor0095

private theorem anchorGroup0003 (i : Fin 1069)
    (hlo : 96 ≤ i.val) (hhi : i.val < 128) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h112 : i.val < 112
  ·
    by_cases h104 : i.val < 104
    ·
      by_cases h100 : i.val < 100
      ·
        by_cases h98 : i.val < 98
        ·
          by_cases h97 : i.val < 97
          ·
            have he : (⟨96, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 96 = i.val
              omega
            simpa only [he] using anchor0096
          ·
            have he : (⟨97, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 97 = i.val
              omega
            simpa only [he] using anchor0097
        ·
          by_cases h99 : i.val < 99
          ·
            have he : (⟨98, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 98 = i.val
              omega
            simpa only [he] using anchor0098
          ·
            have he : (⟨99, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 99 = i.val
              omega
            simpa only [he] using anchor0099
      ·
        by_cases h102 : i.val < 102
        ·
          by_cases h101 : i.val < 101
          ·
            have he : (⟨100, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 100 = i.val
              omega
            simpa only [he] using anchor0100
          ·
            have he : (⟨101, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 101 = i.val
              omega
            simpa only [he] using anchor0101
        ·
          by_cases h103 : i.val < 103
          ·
            have he : (⟨102, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 102 = i.val
              omega
            simpa only [he] using anchor0102
          ·
            have he : (⟨103, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 103 = i.val
              omega
            simpa only [he] using anchor0103
    ·
      by_cases h108 : i.val < 108
      ·
        by_cases h106 : i.val < 106
        ·
          by_cases h105 : i.val < 105
          ·
            have he : (⟨104, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 104 = i.val
              omega
            simpa only [he] using anchor0104
          ·
            have he : (⟨105, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 105 = i.val
              omega
            simpa only [he] using anchor0105
        ·
          by_cases h107 : i.val < 107
          ·
            have he : (⟨106, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 106 = i.val
              omega
            simpa only [he] using anchor0106
          ·
            have he : (⟨107, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 107 = i.val
              omega
            simpa only [he] using anchor0107
      ·
        by_cases h110 : i.val < 110
        ·
          by_cases h109 : i.val < 109
          ·
            have he : (⟨108, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 108 = i.val
              omega
            simpa only [he] using anchor0108
          ·
            have he : (⟨109, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 109 = i.val
              omega
            simpa only [he] using anchor0109
        ·
          by_cases h111 : i.val < 111
          ·
            have he : (⟨110, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 110 = i.val
              omega
            simpa only [he] using anchor0110
          ·
            have he : (⟨111, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 111 = i.val
              omega
            simpa only [he] using anchor0111
  ·
    by_cases h120 : i.val < 120
    ·
      by_cases h116 : i.val < 116
      ·
        by_cases h114 : i.val < 114
        ·
          by_cases h113 : i.val < 113
          ·
            have he : (⟨112, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 112 = i.val
              omega
            simpa only [he] using anchor0112
          ·
            have he : (⟨113, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 113 = i.val
              omega
            simpa only [he] using anchor0113
        ·
          by_cases h115 : i.val < 115
          ·
            have he : (⟨114, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 114 = i.val
              omega
            simpa only [he] using anchor0114
          ·
            have he : (⟨115, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 115 = i.val
              omega
            simpa only [he] using anchor0115
      ·
        by_cases h118 : i.val < 118
        ·
          by_cases h117 : i.val < 117
          ·
            have he : (⟨116, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 116 = i.val
              omega
            simpa only [he] using anchor0116
          ·
            have he : (⟨117, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 117 = i.val
              omega
            simpa only [he] using anchor0117
        ·
          by_cases h119 : i.val < 119
          ·
            have he : (⟨118, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 118 = i.val
              omega
            simpa only [he] using anchor0118
          ·
            have he : (⟨119, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 119 = i.val
              omega
            simpa only [he] using anchor0119
    ·
      by_cases h124 : i.val < 124
      ·
        by_cases h122 : i.val < 122
        ·
          by_cases h121 : i.val < 121
          ·
            have he : (⟨120, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 120 = i.val
              omega
            simpa only [he] using anchor0120
          ·
            have he : (⟨121, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 121 = i.val
              omega
            simpa only [he] using anchor0121
        ·
          by_cases h123 : i.val < 123
          ·
            have he : (⟨122, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 122 = i.val
              omega
            simpa only [he] using anchor0122
          ·
            have he : (⟨123, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 123 = i.val
              omega
            simpa only [he] using anchor0123
      ·
        by_cases h126 : i.val < 126
        ·
          by_cases h125 : i.val < 125
          ·
            have he : (⟨124, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 124 = i.val
              omega
            simpa only [he] using anchor0124
          ·
            have he : (⟨125, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 125 = i.val
              omega
            simpa only [he] using anchor0125
        ·
          by_cases h127 : i.val < 127
          ·
            have he : (⟨126, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 126 = i.val
              omega
            simpa only [he] using anchor0126
          ·
            have he : (⟨127, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 127 = i.val
              omega
            simpa only [he] using anchor0127

private theorem anchorGroup0004 (i : Fin 1069)
    (hlo : 128 ≤ i.val) (hhi : i.val < 160) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h144 : i.val < 144
  ·
    by_cases h136 : i.val < 136
    ·
      by_cases h132 : i.val < 132
      ·
        by_cases h130 : i.val < 130
        ·
          by_cases h129 : i.val < 129
          ·
            have he : (⟨128, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 128 = i.val
              omega
            simpa only [he] using anchor0128
          ·
            have he : (⟨129, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 129 = i.val
              omega
            simpa only [he] using anchor0129
        ·
          by_cases h131 : i.val < 131
          ·
            have he : (⟨130, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 130 = i.val
              omega
            simpa only [he] using anchor0130
          ·
            have he : (⟨131, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 131 = i.val
              omega
            simpa only [he] using anchor0131
      ·
        by_cases h134 : i.val < 134
        ·
          by_cases h133 : i.val < 133
          ·
            have he : (⟨132, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 132 = i.val
              omega
            simpa only [he] using anchor0132
          ·
            have he : (⟨133, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 133 = i.val
              omega
            simpa only [he] using anchor0133
        ·
          by_cases h135 : i.val < 135
          ·
            have he : (⟨134, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 134 = i.val
              omega
            simpa only [he] using anchor0134
          ·
            have he : (⟨135, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 135 = i.val
              omega
            simpa only [he] using anchor0135
    ·
      by_cases h140 : i.val < 140
      ·
        by_cases h138 : i.val < 138
        ·
          by_cases h137 : i.val < 137
          ·
            have he : (⟨136, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 136 = i.val
              omega
            simpa only [he] using anchor0136
          ·
            have he : (⟨137, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 137 = i.val
              omega
            simpa only [he] using anchor0137
        ·
          by_cases h139 : i.val < 139
          ·
            have he : (⟨138, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 138 = i.val
              omega
            simpa only [he] using anchor0138
          ·
            have he : (⟨139, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 139 = i.val
              omega
            simpa only [he] using anchor0139
      ·
        by_cases h142 : i.val < 142
        ·
          by_cases h141 : i.val < 141
          ·
            have he : (⟨140, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 140 = i.val
              omega
            simpa only [he] using anchor0140
          ·
            have he : (⟨141, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 141 = i.val
              omega
            simpa only [he] using anchor0141
        ·
          by_cases h143 : i.val < 143
          ·
            have he : (⟨142, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 142 = i.val
              omega
            simpa only [he] using anchor0142
          ·
            have he : (⟨143, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 143 = i.val
              omega
            simpa only [he] using anchor0143
  ·
    by_cases h152 : i.val < 152
    ·
      by_cases h148 : i.val < 148
      ·
        by_cases h146 : i.val < 146
        ·
          by_cases h145 : i.val < 145
          ·
            have he : (⟨144, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 144 = i.val
              omega
            simpa only [he] using anchor0144
          ·
            have he : (⟨145, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 145 = i.val
              omega
            simpa only [he] using anchor0145
        ·
          by_cases h147 : i.val < 147
          ·
            have he : (⟨146, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 146 = i.val
              omega
            simpa only [he] using anchor0146
          ·
            have he : (⟨147, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 147 = i.val
              omega
            simpa only [he] using anchor0147
      ·
        by_cases h150 : i.val < 150
        ·
          by_cases h149 : i.val < 149
          ·
            have he : (⟨148, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 148 = i.val
              omega
            simpa only [he] using anchor0148
          ·
            have he : (⟨149, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 149 = i.val
              omega
            simpa only [he] using anchor0149
        ·
          by_cases h151 : i.val < 151
          ·
            have he : (⟨150, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 150 = i.val
              omega
            simpa only [he] using anchor0150
          ·
            have he : (⟨151, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 151 = i.val
              omega
            simpa only [he] using anchor0151
    ·
      by_cases h156 : i.val < 156
      ·
        by_cases h154 : i.val < 154
        ·
          by_cases h153 : i.val < 153
          ·
            have he : (⟨152, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 152 = i.val
              omega
            simpa only [he] using anchor0152
          ·
            have he : (⟨153, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 153 = i.val
              omega
            simpa only [he] using anchor0153
        ·
          by_cases h155 : i.val < 155
          ·
            have he : (⟨154, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 154 = i.val
              omega
            simpa only [he] using anchor0154
          ·
            have he : (⟨155, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 155 = i.val
              omega
            simpa only [he] using anchor0155
      ·
        by_cases h158 : i.val < 158
        ·
          by_cases h157 : i.val < 157
          ·
            have he : (⟨156, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 156 = i.val
              omega
            simpa only [he] using anchor0156
          ·
            have he : (⟨157, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 157 = i.val
              omega
            simpa only [he] using anchor0157
        ·
          by_cases h159 : i.val < 159
          ·
            have he : (⟨158, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 158 = i.val
              omega
            simpa only [he] using anchor0158
          ·
            have he : (⟨159, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 159 = i.val
              omega
            simpa only [he] using anchor0159

private theorem anchorGroup0005 (i : Fin 1069)
    (hlo : 160 ≤ i.val) (hhi : i.val < 192) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h176 : i.val < 176
  ·
    by_cases h168 : i.val < 168
    ·
      by_cases h164 : i.val < 164
      ·
        by_cases h162 : i.val < 162
        ·
          by_cases h161 : i.val < 161
          ·
            have he : (⟨160, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 160 = i.val
              omega
            simpa only [he] using anchor0160
          ·
            have he : (⟨161, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 161 = i.val
              omega
            simpa only [he] using anchor0161
        ·
          by_cases h163 : i.val < 163
          ·
            have he : (⟨162, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 162 = i.val
              omega
            simpa only [he] using anchor0162
          ·
            have he : (⟨163, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 163 = i.val
              omega
            simpa only [he] using anchor0163
      ·
        by_cases h166 : i.val < 166
        ·
          by_cases h165 : i.val < 165
          ·
            have he : (⟨164, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 164 = i.val
              omega
            simpa only [he] using anchor0164
          ·
            have he : (⟨165, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 165 = i.val
              omega
            simpa only [he] using anchor0165
        ·
          by_cases h167 : i.val < 167
          ·
            have he : (⟨166, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 166 = i.val
              omega
            simpa only [he] using anchor0166
          ·
            have he : (⟨167, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 167 = i.val
              omega
            simpa only [he] using anchor0167
    ·
      by_cases h172 : i.val < 172
      ·
        by_cases h170 : i.val < 170
        ·
          by_cases h169 : i.val < 169
          ·
            have he : (⟨168, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 168 = i.val
              omega
            simpa only [he] using anchor0168
          ·
            have he : (⟨169, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 169 = i.val
              omega
            simpa only [he] using anchor0169
        ·
          by_cases h171 : i.val < 171
          ·
            have he : (⟨170, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 170 = i.val
              omega
            simpa only [he] using anchor0170
          ·
            have he : (⟨171, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 171 = i.val
              omega
            simpa only [he] using anchor0171
      ·
        by_cases h174 : i.val < 174
        ·
          by_cases h173 : i.val < 173
          ·
            have he : (⟨172, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 172 = i.val
              omega
            simpa only [he] using anchor0172
          ·
            have he : (⟨173, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 173 = i.val
              omega
            simpa only [he] using anchor0173
        ·
          by_cases h175 : i.val < 175
          ·
            have he : (⟨174, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 174 = i.val
              omega
            simpa only [he] using anchor0174
          ·
            have he : (⟨175, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 175 = i.val
              omega
            simpa only [he] using anchor0175
  ·
    by_cases h184 : i.val < 184
    ·
      by_cases h180 : i.val < 180
      ·
        by_cases h178 : i.val < 178
        ·
          by_cases h177 : i.val < 177
          ·
            have he : (⟨176, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 176 = i.val
              omega
            simpa only [he] using anchor0176
          ·
            have he : (⟨177, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 177 = i.val
              omega
            simpa only [he] using anchor0177
        ·
          by_cases h179 : i.val < 179
          ·
            have he : (⟨178, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 178 = i.val
              omega
            simpa only [he] using anchor0178
          ·
            have he : (⟨179, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 179 = i.val
              omega
            simpa only [he] using anchor0179
      ·
        by_cases h182 : i.val < 182
        ·
          by_cases h181 : i.val < 181
          ·
            have he : (⟨180, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 180 = i.val
              omega
            simpa only [he] using anchor0180
          ·
            have he : (⟨181, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 181 = i.val
              omega
            simpa only [he] using anchor0181
        ·
          by_cases h183 : i.val < 183
          ·
            have he : (⟨182, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 182 = i.val
              omega
            simpa only [he] using anchor0182
          ·
            have he : (⟨183, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 183 = i.val
              omega
            simpa only [he] using anchor0183
    ·
      by_cases h188 : i.val < 188
      ·
        by_cases h186 : i.val < 186
        ·
          by_cases h185 : i.val < 185
          ·
            have he : (⟨184, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 184 = i.val
              omega
            simpa only [he] using anchor0184
          ·
            have he : (⟨185, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 185 = i.val
              omega
            simpa only [he] using anchor0185
        ·
          by_cases h187 : i.val < 187
          ·
            have he : (⟨186, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 186 = i.val
              omega
            simpa only [he] using anchor0186
          ·
            have he : (⟨187, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 187 = i.val
              omega
            simpa only [he] using anchor0187
      ·
        by_cases h190 : i.val < 190
        ·
          by_cases h189 : i.val < 189
          ·
            have he : (⟨188, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 188 = i.val
              omega
            simpa only [he] using anchor0188
          ·
            have he : (⟨189, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 189 = i.val
              omega
            simpa only [he] using anchor0189
        ·
          by_cases h191 : i.val < 191
          ·
            have he : (⟨190, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 190 = i.val
              omega
            simpa only [he] using anchor0190
          ·
            have he : (⟨191, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 191 = i.val
              omega
            simpa only [he] using anchor0191

private theorem anchorGroup0006 (i : Fin 1069)
    (hlo : 192 ≤ i.val) (hhi : i.val < 224) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h208 : i.val < 208
  ·
    by_cases h200 : i.val < 200
    ·
      by_cases h196 : i.val < 196
      ·
        by_cases h194 : i.val < 194
        ·
          by_cases h193 : i.val < 193
          ·
            have he : (⟨192, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 192 = i.val
              omega
            simpa only [he] using anchor0192
          ·
            have he : (⟨193, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 193 = i.val
              omega
            simpa only [he] using anchor0193
        ·
          by_cases h195 : i.val < 195
          ·
            have he : (⟨194, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 194 = i.val
              omega
            simpa only [he] using anchor0194
          ·
            have he : (⟨195, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 195 = i.val
              omega
            simpa only [he] using anchor0195
      ·
        by_cases h198 : i.val < 198
        ·
          by_cases h197 : i.val < 197
          ·
            have he : (⟨196, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 196 = i.val
              omega
            simpa only [he] using anchor0196
          ·
            have he : (⟨197, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 197 = i.val
              omega
            simpa only [he] using anchor0197
        ·
          by_cases h199 : i.val < 199
          ·
            have he : (⟨198, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 198 = i.val
              omega
            simpa only [he] using anchor0198
          ·
            have he : (⟨199, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 199 = i.val
              omega
            simpa only [he] using anchor0199
    ·
      by_cases h204 : i.val < 204
      ·
        by_cases h202 : i.val < 202
        ·
          by_cases h201 : i.val < 201
          ·
            have he : (⟨200, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 200 = i.val
              omega
            simpa only [he] using anchor0200
          ·
            have he : (⟨201, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 201 = i.val
              omega
            simpa only [he] using anchor0201
        ·
          by_cases h203 : i.val < 203
          ·
            have he : (⟨202, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 202 = i.val
              omega
            simpa only [he] using anchor0202
          ·
            have he : (⟨203, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 203 = i.val
              omega
            simpa only [he] using anchor0203
      ·
        by_cases h206 : i.val < 206
        ·
          by_cases h205 : i.val < 205
          ·
            have he : (⟨204, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 204 = i.val
              omega
            simpa only [he] using anchor0204
          ·
            have he : (⟨205, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 205 = i.val
              omega
            simpa only [he] using anchor0205
        ·
          by_cases h207 : i.val < 207
          ·
            have he : (⟨206, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 206 = i.val
              omega
            simpa only [he] using anchor0206
          ·
            have he : (⟨207, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 207 = i.val
              omega
            simpa only [he] using anchor0207
  ·
    by_cases h216 : i.val < 216
    ·
      by_cases h212 : i.val < 212
      ·
        by_cases h210 : i.val < 210
        ·
          by_cases h209 : i.val < 209
          ·
            have he : (⟨208, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 208 = i.val
              omega
            simpa only [he] using anchor0208
          ·
            have he : (⟨209, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 209 = i.val
              omega
            simpa only [he] using anchor0209
        ·
          by_cases h211 : i.val < 211
          ·
            have he : (⟨210, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 210 = i.val
              omega
            simpa only [he] using anchor0210
          ·
            have he : (⟨211, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 211 = i.val
              omega
            simpa only [he] using anchor0211
      ·
        by_cases h214 : i.val < 214
        ·
          by_cases h213 : i.val < 213
          ·
            have he : (⟨212, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 212 = i.val
              omega
            simpa only [he] using anchor0212
          ·
            have he : (⟨213, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 213 = i.val
              omega
            simpa only [he] using anchor0213
        ·
          by_cases h215 : i.val < 215
          ·
            have he : (⟨214, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 214 = i.val
              omega
            simpa only [he] using anchor0214
          ·
            have he : (⟨215, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 215 = i.val
              omega
            simpa only [he] using anchor0215
    ·
      by_cases h220 : i.val < 220
      ·
        by_cases h218 : i.val < 218
        ·
          by_cases h217 : i.val < 217
          ·
            have he : (⟨216, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 216 = i.val
              omega
            simpa only [he] using anchor0216
          ·
            have he : (⟨217, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 217 = i.val
              omega
            simpa only [he] using anchor0217
        ·
          by_cases h219 : i.val < 219
          ·
            have he : (⟨218, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 218 = i.val
              omega
            simpa only [he] using anchor0218
          ·
            have he : (⟨219, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 219 = i.val
              omega
            simpa only [he] using anchor0219
      ·
        by_cases h222 : i.val < 222
        ·
          by_cases h221 : i.val < 221
          ·
            have he : (⟨220, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 220 = i.val
              omega
            simpa only [he] using anchor0220
          ·
            have he : (⟨221, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 221 = i.val
              omega
            simpa only [he] using anchor0221
        ·
          by_cases h223 : i.val < 223
          ·
            have he : (⟨222, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 222 = i.val
              omega
            simpa only [he] using anchor0222
          ·
            have he : (⟨223, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 223 = i.val
              omega
            simpa only [he] using anchor0223

private theorem anchorGroup0007 (i : Fin 1069)
    (hlo : 224 ≤ i.val) (hhi : i.val < 256) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h240 : i.val < 240
  ·
    by_cases h232 : i.val < 232
    ·
      by_cases h228 : i.val < 228
      ·
        by_cases h226 : i.val < 226
        ·
          by_cases h225 : i.val < 225
          ·
            have he : (⟨224, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 224 = i.val
              omega
            simpa only [he] using anchor0224
          ·
            have he : (⟨225, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 225 = i.val
              omega
            simpa only [he] using anchor0225
        ·
          by_cases h227 : i.val < 227
          ·
            have he : (⟨226, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 226 = i.val
              omega
            simpa only [he] using anchor0226
          ·
            have he : (⟨227, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 227 = i.val
              omega
            simpa only [he] using anchor0227
      ·
        by_cases h230 : i.val < 230
        ·
          by_cases h229 : i.val < 229
          ·
            have he : (⟨228, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 228 = i.val
              omega
            simpa only [he] using anchor0228
          ·
            have he : (⟨229, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 229 = i.val
              omega
            simpa only [he] using anchor0229
        ·
          by_cases h231 : i.val < 231
          ·
            have he : (⟨230, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 230 = i.val
              omega
            simpa only [he] using anchor0230
          ·
            have he : (⟨231, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 231 = i.val
              omega
            simpa only [he] using anchor0231
    ·
      by_cases h236 : i.val < 236
      ·
        by_cases h234 : i.val < 234
        ·
          by_cases h233 : i.val < 233
          ·
            have he : (⟨232, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 232 = i.val
              omega
            simpa only [he] using anchor0232
          ·
            have he : (⟨233, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 233 = i.val
              omega
            simpa only [he] using anchor0233
        ·
          by_cases h235 : i.val < 235
          ·
            have he : (⟨234, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 234 = i.val
              omega
            simpa only [he] using anchor0234
          ·
            have he : (⟨235, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 235 = i.val
              omega
            simpa only [he] using anchor0235
      ·
        by_cases h238 : i.val < 238
        ·
          by_cases h237 : i.val < 237
          ·
            have he : (⟨236, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 236 = i.val
              omega
            simpa only [he] using anchor0236
          ·
            have he : (⟨237, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 237 = i.val
              omega
            simpa only [he] using anchor0237
        ·
          by_cases h239 : i.val < 239
          ·
            have he : (⟨238, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 238 = i.val
              omega
            simpa only [he] using anchor0238
          ·
            have he : (⟨239, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 239 = i.val
              omega
            simpa only [he] using anchor0239
  ·
    by_cases h248 : i.val < 248
    ·
      by_cases h244 : i.val < 244
      ·
        by_cases h242 : i.val < 242
        ·
          by_cases h241 : i.val < 241
          ·
            have he : (⟨240, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 240 = i.val
              omega
            simpa only [he] using anchor0240
          ·
            have he : (⟨241, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 241 = i.val
              omega
            simpa only [he] using anchor0241
        ·
          by_cases h243 : i.val < 243
          ·
            have he : (⟨242, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 242 = i.val
              omega
            simpa only [he] using anchor0242
          ·
            have he : (⟨243, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 243 = i.val
              omega
            simpa only [he] using anchor0243
      ·
        by_cases h246 : i.val < 246
        ·
          by_cases h245 : i.val < 245
          ·
            have he : (⟨244, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 244 = i.val
              omega
            simpa only [he] using anchor0244
          ·
            have he : (⟨245, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 245 = i.val
              omega
            simpa only [he] using anchor0245
        ·
          by_cases h247 : i.val < 247
          ·
            have he : (⟨246, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 246 = i.val
              omega
            simpa only [he] using anchor0246
          ·
            have he : (⟨247, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 247 = i.val
              omega
            simpa only [he] using anchor0247
    ·
      by_cases h252 : i.val < 252
      ·
        by_cases h250 : i.val < 250
        ·
          by_cases h249 : i.val < 249
          ·
            have he : (⟨248, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 248 = i.val
              omega
            simpa only [he] using anchor0248
          ·
            have he : (⟨249, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 249 = i.val
              omega
            simpa only [he] using anchor0249
        ·
          by_cases h251 : i.val < 251
          ·
            have he : (⟨250, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 250 = i.val
              omega
            simpa only [he] using anchor0250
          ·
            have he : (⟨251, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 251 = i.val
              omega
            simpa only [he] using anchor0251
      ·
        by_cases h254 : i.val < 254
        ·
          by_cases h253 : i.val < 253
          ·
            have he : (⟨252, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 252 = i.val
              omega
            simpa only [he] using anchor0252
          ·
            have he : (⟨253, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 253 = i.val
              omega
            simpa only [he] using anchor0253
        ·
          by_cases h255 : i.val < 255
          ·
            have he : (⟨254, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 254 = i.val
              omega
            simpa only [he] using anchor0254
          ·
            have he : (⟨255, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 255 = i.val
              omega
            simpa only [he] using anchor0255

private theorem anchorGroup0008 (i : Fin 1069)
    (hlo : 256 ≤ i.val) (hhi : i.val < 288) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h272 : i.val < 272
  ·
    by_cases h264 : i.val < 264
    ·
      by_cases h260 : i.val < 260
      ·
        by_cases h258 : i.val < 258
        ·
          by_cases h257 : i.val < 257
          ·
            have he : (⟨256, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 256 = i.val
              omega
            simpa only [he] using anchor0256
          ·
            have he : (⟨257, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 257 = i.val
              omega
            simpa only [he] using anchor0257
        ·
          by_cases h259 : i.val < 259
          ·
            have he : (⟨258, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 258 = i.val
              omega
            simpa only [he] using anchor0258
          ·
            have he : (⟨259, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 259 = i.val
              omega
            simpa only [he] using anchor0259
      ·
        by_cases h262 : i.val < 262
        ·
          by_cases h261 : i.val < 261
          ·
            have he : (⟨260, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 260 = i.val
              omega
            simpa only [he] using anchor0260
          ·
            have he : (⟨261, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 261 = i.val
              omega
            simpa only [he] using anchor0261
        ·
          by_cases h263 : i.val < 263
          ·
            have he : (⟨262, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 262 = i.val
              omega
            simpa only [he] using anchor0262
          ·
            have he : (⟨263, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 263 = i.val
              omega
            simpa only [he] using anchor0263
    ·
      by_cases h268 : i.val < 268
      ·
        by_cases h266 : i.val < 266
        ·
          by_cases h265 : i.val < 265
          ·
            have he : (⟨264, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 264 = i.val
              omega
            simpa only [he] using anchor0264
          ·
            have he : (⟨265, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 265 = i.val
              omega
            simpa only [he] using anchor0265
        ·
          by_cases h267 : i.val < 267
          ·
            have he : (⟨266, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 266 = i.val
              omega
            simpa only [he] using anchor0266
          ·
            have he : (⟨267, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 267 = i.val
              omega
            simpa only [he] using anchor0267
      ·
        by_cases h270 : i.val < 270
        ·
          by_cases h269 : i.val < 269
          ·
            have he : (⟨268, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 268 = i.val
              omega
            simpa only [he] using anchor0268
          ·
            have he : (⟨269, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 269 = i.val
              omega
            simpa only [he] using anchor0269
        ·
          by_cases h271 : i.val < 271
          ·
            have he : (⟨270, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 270 = i.val
              omega
            simpa only [he] using anchor0270
          ·
            have he : (⟨271, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 271 = i.val
              omega
            simpa only [he] using anchor0271
  ·
    by_cases h280 : i.val < 280
    ·
      by_cases h276 : i.val < 276
      ·
        by_cases h274 : i.val < 274
        ·
          by_cases h273 : i.val < 273
          ·
            have he : (⟨272, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 272 = i.val
              omega
            simpa only [he] using anchor0272
          ·
            have he : (⟨273, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 273 = i.val
              omega
            simpa only [he] using anchor0273
        ·
          by_cases h275 : i.val < 275
          ·
            have he : (⟨274, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 274 = i.val
              omega
            simpa only [he] using anchor0274
          ·
            have he : (⟨275, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 275 = i.val
              omega
            simpa only [he] using anchor0275
      ·
        by_cases h278 : i.val < 278
        ·
          by_cases h277 : i.val < 277
          ·
            have he : (⟨276, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 276 = i.val
              omega
            simpa only [he] using anchor0276
          ·
            have he : (⟨277, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 277 = i.val
              omega
            simpa only [he] using anchor0277
        ·
          by_cases h279 : i.val < 279
          ·
            have he : (⟨278, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 278 = i.val
              omega
            simpa only [he] using anchor0278
          ·
            have he : (⟨279, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 279 = i.val
              omega
            simpa only [he] using anchor0279
    ·
      by_cases h284 : i.val < 284
      ·
        by_cases h282 : i.val < 282
        ·
          by_cases h281 : i.val < 281
          ·
            have he : (⟨280, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 280 = i.val
              omega
            simpa only [he] using anchor0280
          ·
            have he : (⟨281, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 281 = i.val
              omega
            simpa only [he] using anchor0281
        ·
          by_cases h283 : i.val < 283
          ·
            have he : (⟨282, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 282 = i.val
              omega
            simpa only [he] using anchor0282
          ·
            have he : (⟨283, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 283 = i.val
              omega
            simpa only [he] using anchor0283
      ·
        by_cases h286 : i.val < 286
        ·
          by_cases h285 : i.val < 285
          ·
            have he : (⟨284, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 284 = i.val
              omega
            simpa only [he] using anchor0284
          ·
            have he : (⟨285, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 285 = i.val
              omega
            simpa only [he] using anchor0285
        ·
          by_cases h287 : i.val < 287
          ·
            have he : (⟨286, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 286 = i.val
              omega
            simpa only [he] using anchor0286
          ·
            have he : (⟨287, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 287 = i.val
              omega
            simpa only [he] using anchor0287

private theorem anchorGroup0009 (i : Fin 1069)
    (hlo : 288 ≤ i.val) (hhi : i.val < 320) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h304 : i.val < 304
  ·
    by_cases h296 : i.val < 296
    ·
      by_cases h292 : i.val < 292
      ·
        by_cases h290 : i.val < 290
        ·
          by_cases h289 : i.val < 289
          ·
            have he : (⟨288, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 288 = i.val
              omega
            simpa only [he] using anchor0288
          ·
            have he : (⟨289, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 289 = i.val
              omega
            simpa only [he] using anchor0289
        ·
          by_cases h291 : i.val < 291
          ·
            have he : (⟨290, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 290 = i.val
              omega
            simpa only [he] using anchor0290
          ·
            have he : (⟨291, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 291 = i.val
              omega
            simpa only [he] using anchor0291
      ·
        by_cases h294 : i.val < 294
        ·
          by_cases h293 : i.val < 293
          ·
            have he : (⟨292, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 292 = i.val
              omega
            simpa only [he] using anchor0292
          ·
            have he : (⟨293, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 293 = i.val
              omega
            simpa only [he] using anchor0293
        ·
          by_cases h295 : i.val < 295
          ·
            have he : (⟨294, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 294 = i.val
              omega
            simpa only [he] using anchor0294
          ·
            have he : (⟨295, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 295 = i.val
              omega
            simpa only [he] using anchor0295
    ·
      by_cases h300 : i.val < 300
      ·
        by_cases h298 : i.val < 298
        ·
          by_cases h297 : i.val < 297
          ·
            have he : (⟨296, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 296 = i.val
              omega
            simpa only [he] using anchor0296
          ·
            have he : (⟨297, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 297 = i.val
              omega
            simpa only [he] using anchor0297
        ·
          by_cases h299 : i.val < 299
          ·
            have he : (⟨298, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 298 = i.val
              omega
            simpa only [he] using anchor0298
          ·
            have he : (⟨299, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 299 = i.val
              omega
            simpa only [he] using anchor0299
      ·
        by_cases h302 : i.val < 302
        ·
          by_cases h301 : i.val < 301
          ·
            have he : (⟨300, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 300 = i.val
              omega
            simpa only [he] using anchor0300
          ·
            have he : (⟨301, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 301 = i.val
              omega
            simpa only [he] using anchor0301
        ·
          by_cases h303 : i.val < 303
          ·
            have he : (⟨302, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 302 = i.val
              omega
            simpa only [he] using anchor0302
          ·
            have he : (⟨303, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 303 = i.val
              omega
            simpa only [he] using anchor0303
  ·
    by_cases h312 : i.val < 312
    ·
      by_cases h308 : i.val < 308
      ·
        by_cases h306 : i.val < 306
        ·
          by_cases h305 : i.val < 305
          ·
            have he : (⟨304, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 304 = i.val
              omega
            simpa only [he] using anchor0304
          ·
            have he : (⟨305, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 305 = i.val
              omega
            simpa only [he] using anchor0305
        ·
          by_cases h307 : i.val < 307
          ·
            have he : (⟨306, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 306 = i.val
              omega
            simpa only [he] using anchor0306
          ·
            have he : (⟨307, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 307 = i.val
              omega
            simpa only [he] using anchor0307
      ·
        by_cases h310 : i.val < 310
        ·
          by_cases h309 : i.val < 309
          ·
            have he : (⟨308, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 308 = i.val
              omega
            simpa only [he] using anchor0308
          ·
            have he : (⟨309, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 309 = i.val
              omega
            simpa only [he] using anchor0309
        ·
          by_cases h311 : i.val < 311
          ·
            have he : (⟨310, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 310 = i.val
              omega
            simpa only [he] using anchor0310
          ·
            have he : (⟨311, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 311 = i.val
              omega
            simpa only [he] using anchor0311
    ·
      by_cases h316 : i.val < 316
      ·
        by_cases h314 : i.val < 314
        ·
          by_cases h313 : i.val < 313
          ·
            have he : (⟨312, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 312 = i.val
              omega
            simpa only [he] using anchor0312
          ·
            have he : (⟨313, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 313 = i.val
              omega
            simpa only [he] using anchor0313
        ·
          by_cases h315 : i.val < 315
          ·
            have he : (⟨314, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 314 = i.val
              omega
            simpa only [he] using anchor0314
          ·
            have he : (⟨315, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 315 = i.val
              omega
            simpa only [he] using anchor0315
      ·
        by_cases h318 : i.val < 318
        ·
          by_cases h317 : i.val < 317
          ·
            have he : (⟨316, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 316 = i.val
              omega
            simpa only [he] using anchor0316
          ·
            have he : (⟨317, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 317 = i.val
              omega
            simpa only [he] using anchor0317
        ·
          by_cases h319 : i.val < 319
          ·
            have he : (⟨318, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 318 = i.val
              omega
            simpa only [he] using anchor0318
          ·
            have he : (⟨319, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 319 = i.val
              omega
            simpa only [he] using anchor0319

private theorem anchorGroup0010 (i : Fin 1069)
    (hlo : 320 ≤ i.val) (hhi : i.val < 352) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h336 : i.val < 336
  ·
    by_cases h328 : i.val < 328
    ·
      by_cases h324 : i.val < 324
      ·
        by_cases h322 : i.val < 322
        ·
          by_cases h321 : i.val < 321
          ·
            have he : (⟨320, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 320 = i.val
              omega
            simpa only [he] using anchor0320
          ·
            have he : (⟨321, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 321 = i.val
              omega
            simpa only [he] using anchor0321
        ·
          by_cases h323 : i.val < 323
          ·
            have he : (⟨322, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 322 = i.val
              omega
            simpa only [he] using anchor0322
          ·
            have he : (⟨323, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 323 = i.val
              omega
            simpa only [he] using anchor0323
      ·
        by_cases h326 : i.val < 326
        ·
          by_cases h325 : i.val < 325
          ·
            have he : (⟨324, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 324 = i.val
              omega
            simpa only [he] using anchor0324
          ·
            have he : (⟨325, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 325 = i.val
              omega
            simpa only [he] using anchor0325
        ·
          by_cases h327 : i.val < 327
          ·
            have he : (⟨326, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 326 = i.val
              omega
            simpa only [he] using anchor0326
          ·
            have he : (⟨327, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 327 = i.val
              omega
            simpa only [he] using anchor0327
    ·
      by_cases h332 : i.val < 332
      ·
        by_cases h330 : i.val < 330
        ·
          by_cases h329 : i.val < 329
          ·
            have he : (⟨328, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 328 = i.val
              omega
            simpa only [he] using anchor0328
          ·
            have he : (⟨329, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 329 = i.val
              omega
            simpa only [he] using anchor0329
        ·
          by_cases h331 : i.val < 331
          ·
            have he : (⟨330, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 330 = i.val
              omega
            simpa only [he] using anchor0330
          ·
            have he : (⟨331, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 331 = i.val
              omega
            simpa only [he] using anchor0331
      ·
        by_cases h334 : i.val < 334
        ·
          by_cases h333 : i.val < 333
          ·
            have he : (⟨332, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 332 = i.val
              omega
            simpa only [he] using anchor0332
          ·
            have he : (⟨333, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 333 = i.val
              omega
            simpa only [he] using anchor0333
        ·
          by_cases h335 : i.val < 335
          ·
            have he : (⟨334, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 334 = i.val
              omega
            simpa only [he] using anchor0334
          ·
            have he : (⟨335, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 335 = i.val
              omega
            simpa only [he] using anchor0335
  ·
    by_cases h344 : i.val < 344
    ·
      by_cases h340 : i.val < 340
      ·
        by_cases h338 : i.val < 338
        ·
          by_cases h337 : i.val < 337
          ·
            have he : (⟨336, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 336 = i.val
              omega
            simpa only [he] using anchor0336
          ·
            have he : (⟨337, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 337 = i.val
              omega
            simpa only [he] using anchor0337
        ·
          by_cases h339 : i.val < 339
          ·
            have he : (⟨338, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 338 = i.val
              omega
            simpa only [he] using anchor0338
          ·
            have he : (⟨339, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 339 = i.val
              omega
            simpa only [he] using anchor0339
      ·
        by_cases h342 : i.val < 342
        ·
          by_cases h341 : i.val < 341
          ·
            have he : (⟨340, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 340 = i.val
              omega
            simpa only [he] using anchor0340
          ·
            have he : (⟨341, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 341 = i.val
              omega
            simpa only [he] using anchor0341
        ·
          by_cases h343 : i.val < 343
          ·
            have he : (⟨342, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 342 = i.val
              omega
            simpa only [he] using anchor0342
          ·
            have he : (⟨343, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 343 = i.val
              omega
            simpa only [he] using anchor0343
    ·
      by_cases h348 : i.val < 348
      ·
        by_cases h346 : i.val < 346
        ·
          by_cases h345 : i.val < 345
          ·
            have he : (⟨344, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 344 = i.val
              omega
            simpa only [he] using anchor0344
          ·
            have he : (⟨345, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 345 = i.val
              omega
            simpa only [he] using anchor0345
        ·
          by_cases h347 : i.val < 347
          ·
            have he : (⟨346, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 346 = i.val
              omega
            simpa only [he] using anchor0346
          ·
            have he : (⟨347, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 347 = i.val
              omega
            simpa only [he] using anchor0347
      ·
        by_cases h350 : i.val < 350
        ·
          by_cases h349 : i.val < 349
          ·
            have he : (⟨348, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 348 = i.val
              omega
            simpa only [he] using anchor0348
          ·
            have he : (⟨349, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 349 = i.val
              omega
            simpa only [he] using anchor0349
        ·
          by_cases h351 : i.val < 351
          ·
            have he : (⟨350, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 350 = i.val
              omega
            simpa only [he] using anchor0350
          ·
            have he : (⟨351, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 351 = i.val
              omega
            simpa only [he] using anchor0351

private theorem anchorGroup0011 (i : Fin 1069)
    (hlo : 352 ≤ i.val) (hhi : i.val < 384) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h368 : i.val < 368
  ·
    by_cases h360 : i.val < 360
    ·
      by_cases h356 : i.val < 356
      ·
        by_cases h354 : i.val < 354
        ·
          by_cases h353 : i.val < 353
          ·
            have he : (⟨352, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 352 = i.val
              omega
            simpa only [he] using anchor0352
          ·
            have he : (⟨353, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 353 = i.val
              omega
            simpa only [he] using anchor0353
        ·
          by_cases h355 : i.val < 355
          ·
            have he : (⟨354, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 354 = i.val
              omega
            simpa only [he] using anchor0354
          ·
            have he : (⟨355, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 355 = i.val
              omega
            simpa only [he] using anchor0355
      ·
        by_cases h358 : i.val < 358
        ·
          by_cases h357 : i.val < 357
          ·
            have he : (⟨356, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 356 = i.val
              omega
            simpa only [he] using anchor0356
          ·
            have he : (⟨357, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 357 = i.val
              omega
            simpa only [he] using anchor0357
        ·
          by_cases h359 : i.val < 359
          ·
            have he : (⟨358, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 358 = i.val
              omega
            simpa only [he] using anchor0358
          ·
            have he : (⟨359, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 359 = i.val
              omega
            simpa only [he] using anchor0359
    ·
      by_cases h364 : i.val < 364
      ·
        by_cases h362 : i.val < 362
        ·
          by_cases h361 : i.val < 361
          ·
            have he : (⟨360, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 360 = i.val
              omega
            simpa only [he] using anchor0360
          ·
            have he : (⟨361, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 361 = i.val
              omega
            simpa only [he] using anchor0361
        ·
          by_cases h363 : i.val < 363
          ·
            have he : (⟨362, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 362 = i.val
              omega
            simpa only [he] using anchor0362
          ·
            have he : (⟨363, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 363 = i.val
              omega
            simpa only [he] using anchor0363
      ·
        by_cases h366 : i.val < 366
        ·
          by_cases h365 : i.val < 365
          ·
            have he : (⟨364, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 364 = i.val
              omega
            simpa only [he] using anchor0364
          ·
            have he : (⟨365, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 365 = i.val
              omega
            simpa only [he] using anchor0365
        ·
          by_cases h367 : i.val < 367
          ·
            have he : (⟨366, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 366 = i.val
              omega
            simpa only [he] using anchor0366
          ·
            have he : (⟨367, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 367 = i.val
              omega
            simpa only [he] using anchor0367
  ·
    by_cases h376 : i.val < 376
    ·
      by_cases h372 : i.val < 372
      ·
        by_cases h370 : i.val < 370
        ·
          by_cases h369 : i.val < 369
          ·
            have he : (⟨368, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 368 = i.val
              omega
            simpa only [he] using anchor0368
          ·
            have he : (⟨369, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 369 = i.val
              omega
            simpa only [he] using anchor0369
        ·
          by_cases h371 : i.val < 371
          ·
            have he : (⟨370, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 370 = i.val
              omega
            simpa only [he] using anchor0370
          ·
            have he : (⟨371, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 371 = i.val
              omega
            simpa only [he] using anchor0371
      ·
        by_cases h374 : i.val < 374
        ·
          by_cases h373 : i.val < 373
          ·
            have he : (⟨372, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 372 = i.val
              omega
            simpa only [he] using anchor0372
          ·
            have he : (⟨373, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 373 = i.val
              omega
            simpa only [he] using anchor0373
        ·
          by_cases h375 : i.val < 375
          ·
            have he : (⟨374, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 374 = i.val
              omega
            simpa only [he] using anchor0374
          ·
            have he : (⟨375, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 375 = i.val
              omega
            simpa only [he] using anchor0375
    ·
      by_cases h380 : i.val < 380
      ·
        by_cases h378 : i.val < 378
        ·
          by_cases h377 : i.val < 377
          ·
            have he : (⟨376, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 376 = i.val
              omega
            simpa only [he] using anchor0376
          ·
            have he : (⟨377, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 377 = i.val
              omega
            simpa only [he] using anchor0377
        ·
          by_cases h379 : i.val < 379
          ·
            have he : (⟨378, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 378 = i.val
              omega
            simpa only [he] using anchor0378
          ·
            have he : (⟨379, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 379 = i.val
              omega
            simpa only [he] using anchor0379
      ·
        by_cases h382 : i.val < 382
        ·
          by_cases h381 : i.val < 381
          ·
            have he : (⟨380, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 380 = i.val
              omega
            simpa only [he] using anchor0380
          ·
            have he : (⟨381, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 381 = i.val
              omega
            simpa only [he] using anchor0381
        ·
          by_cases h383 : i.val < 383
          ·
            have he : (⟨382, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 382 = i.val
              omega
            simpa only [he] using anchor0382
          ·
            have he : (⟨383, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 383 = i.val
              omega
            simpa only [he] using anchor0383

private theorem anchorGroup0012 (i : Fin 1069)
    (hlo : 384 ≤ i.val) (hhi : i.val < 416) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h400 : i.val < 400
  ·
    by_cases h392 : i.val < 392
    ·
      by_cases h388 : i.val < 388
      ·
        by_cases h386 : i.val < 386
        ·
          by_cases h385 : i.val < 385
          ·
            have he : (⟨384, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 384 = i.val
              omega
            simpa only [he] using anchor0384
          ·
            have he : (⟨385, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 385 = i.val
              omega
            simpa only [he] using anchor0385
        ·
          by_cases h387 : i.val < 387
          ·
            have he : (⟨386, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 386 = i.val
              omega
            simpa only [he] using anchor0386
          ·
            have he : (⟨387, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 387 = i.val
              omega
            simpa only [he] using anchor0387
      ·
        by_cases h390 : i.val < 390
        ·
          by_cases h389 : i.val < 389
          ·
            have he : (⟨388, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 388 = i.val
              omega
            simpa only [he] using anchor0388
          ·
            have he : (⟨389, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 389 = i.val
              omega
            simpa only [he] using anchor0389
        ·
          by_cases h391 : i.val < 391
          ·
            have he : (⟨390, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 390 = i.val
              omega
            simpa only [he] using anchor0390
          ·
            have he : (⟨391, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 391 = i.val
              omega
            simpa only [he] using anchor0391
    ·
      by_cases h396 : i.val < 396
      ·
        by_cases h394 : i.val < 394
        ·
          by_cases h393 : i.val < 393
          ·
            have he : (⟨392, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 392 = i.val
              omega
            simpa only [he] using anchor0392
          ·
            have he : (⟨393, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 393 = i.val
              omega
            simpa only [he] using anchor0393
        ·
          by_cases h395 : i.val < 395
          ·
            have he : (⟨394, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 394 = i.val
              omega
            simpa only [he] using anchor0394
          ·
            have he : (⟨395, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 395 = i.val
              omega
            simpa only [he] using anchor0395
      ·
        by_cases h398 : i.val < 398
        ·
          by_cases h397 : i.val < 397
          ·
            have he : (⟨396, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 396 = i.val
              omega
            simpa only [he] using anchor0396
          ·
            have he : (⟨397, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 397 = i.val
              omega
            simpa only [he] using anchor0397
        ·
          by_cases h399 : i.val < 399
          ·
            have he : (⟨398, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 398 = i.val
              omega
            simpa only [he] using anchor0398
          ·
            have he : (⟨399, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 399 = i.val
              omega
            simpa only [he] using anchor0399
  ·
    by_cases h408 : i.val < 408
    ·
      by_cases h404 : i.val < 404
      ·
        by_cases h402 : i.val < 402
        ·
          by_cases h401 : i.val < 401
          ·
            have he : (⟨400, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 400 = i.val
              omega
            simpa only [he] using anchor0400
          ·
            have he : (⟨401, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 401 = i.val
              omega
            simpa only [he] using anchor0401
        ·
          by_cases h403 : i.val < 403
          ·
            have he : (⟨402, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 402 = i.val
              omega
            simpa only [he] using anchor0402
          ·
            have he : (⟨403, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 403 = i.val
              omega
            simpa only [he] using anchor0403
      ·
        by_cases h406 : i.val < 406
        ·
          by_cases h405 : i.val < 405
          ·
            have he : (⟨404, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 404 = i.val
              omega
            simpa only [he] using anchor0404
          ·
            have he : (⟨405, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 405 = i.val
              omega
            simpa only [he] using anchor0405
        ·
          by_cases h407 : i.val < 407
          ·
            have he : (⟨406, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 406 = i.val
              omega
            simpa only [he] using anchor0406
          ·
            have he : (⟨407, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 407 = i.val
              omega
            simpa only [he] using anchor0407
    ·
      by_cases h412 : i.val < 412
      ·
        by_cases h410 : i.val < 410
        ·
          by_cases h409 : i.val < 409
          ·
            have he : (⟨408, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 408 = i.val
              omega
            simpa only [he] using anchor0408
          ·
            have he : (⟨409, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 409 = i.val
              omega
            simpa only [he] using anchor0409
        ·
          by_cases h411 : i.val < 411
          ·
            have he : (⟨410, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 410 = i.val
              omega
            simpa only [he] using anchor0410
          ·
            have he : (⟨411, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 411 = i.val
              omega
            simpa only [he] using anchor0411
      ·
        by_cases h414 : i.val < 414
        ·
          by_cases h413 : i.val < 413
          ·
            have he : (⟨412, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 412 = i.val
              omega
            simpa only [he] using anchor0412
          ·
            have he : (⟨413, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 413 = i.val
              omega
            simpa only [he] using anchor0413
        ·
          by_cases h415 : i.val < 415
          ·
            have he : (⟨414, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 414 = i.val
              omega
            simpa only [he] using anchor0414
          ·
            have he : (⟨415, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 415 = i.val
              omega
            simpa only [he] using anchor0415

private theorem anchorGroup0013 (i : Fin 1069)
    (hlo : 416 ≤ i.val) (hhi : i.val < 448) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h432 : i.val < 432
  ·
    by_cases h424 : i.val < 424
    ·
      by_cases h420 : i.val < 420
      ·
        by_cases h418 : i.val < 418
        ·
          by_cases h417 : i.val < 417
          ·
            have he : (⟨416, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 416 = i.val
              omega
            simpa only [he] using anchor0416
          ·
            have he : (⟨417, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 417 = i.val
              omega
            simpa only [he] using anchor0417
        ·
          by_cases h419 : i.val < 419
          ·
            have he : (⟨418, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 418 = i.val
              omega
            simpa only [he] using anchor0418
          ·
            have he : (⟨419, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 419 = i.val
              omega
            simpa only [he] using anchor0419
      ·
        by_cases h422 : i.val < 422
        ·
          by_cases h421 : i.val < 421
          ·
            have he : (⟨420, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 420 = i.val
              omega
            simpa only [he] using anchor0420
          ·
            have he : (⟨421, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 421 = i.val
              omega
            simpa only [he] using anchor0421
        ·
          by_cases h423 : i.val < 423
          ·
            have he : (⟨422, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 422 = i.val
              omega
            simpa only [he] using anchor0422
          ·
            have he : (⟨423, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 423 = i.val
              omega
            simpa only [he] using anchor0423
    ·
      by_cases h428 : i.val < 428
      ·
        by_cases h426 : i.val < 426
        ·
          by_cases h425 : i.val < 425
          ·
            have he : (⟨424, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 424 = i.val
              omega
            simpa only [he] using anchor0424
          ·
            have he : (⟨425, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 425 = i.val
              omega
            simpa only [he] using anchor0425
        ·
          by_cases h427 : i.val < 427
          ·
            have he : (⟨426, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 426 = i.val
              omega
            simpa only [he] using anchor0426
          ·
            have he : (⟨427, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 427 = i.val
              omega
            simpa only [he] using anchor0427
      ·
        by_cases h430 : i.val < 430
        ·
          by_cases h429 : i.val < 429
          ·
            have he : (⟨428, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 428 = i.val
              omega
            simpa only [he] using anchor0428
          ·
            have he : (⟨429, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 429 = i.val
              omega
            simpa only [he] using anchor0429
        ·
          by_cases h431 : i.val < 431
          ·
            have he : (⟨430, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 430 = i.val
              omega
            simpa only [he] using anchor0430
          ·
            have he : (⟨431, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 431 = i.val
              omega
            simpa only [he] using anchor0431
  ·
    by_cases h440 : i.val < 440
    ·
      by_cases h436 : i.val < 436
      ·
        by_cases h434 : i.val < 434
        ·
          by_cases h433 : i.val < 433
          ·
            have he : (⟨432, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 432 = i.val
              omega
            simpa only [he] using anchor0432
          ·
            have he : (⟨433, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 433 = i.val
              omega
            simpa only [he] using anchor0433
        ·
          by_cases h435 : i.val < 435
          ·
            have he : (⟨434, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 434 = i.val
              omega
            simpa only [he] using anchor0434
          ·
            have he : (⟨435, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 435 = i.val
              omega
            simpa only [he] using anchor0435
      ·
        by_cases h438 : i.val < 438
        ·
          by_cases h437 : i.val < 437
          ·
            have he : (⟨436, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 436 = i.val
              omega
            simpa only [he] using anchor0436
          ·
            have he : (⟨437, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 437 = i.val
              omega
            simpa only [he] using anchor0437
        ·
          by_cases h439 : i.val < 439
          ·
            have he : (⟨438, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 438 = i.val
              omega
            simpa only [he] using anchor0438
          ·
            have he : (⟨439, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 439 = i.val
              omega
            simpa only [he] using anchor0439
    ·
      by_cases h444 : i.val < 444
      ·
        by_cases h442 : i.val < 442
        ·
          by_cases h441 : i.val < 441
          ·
            have he : (⟨440, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 440 = i.val
              omega
            simpa only [he] using anchor0440
          ·
            have he : (⟨441, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 441 = i.val
              omega
            simpa only [he] using anchor0441
        ·
          by_cases h443 : i.val < 443
          ·
            have he : (⟨442, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 442 = i.val
              omega
            simpa only [he] using anchor0442
          ·
            have he : (⟨443, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 443 = i.val
              omega
            simpa only [he] using anchor0443
      ·
        by_cases h446 : i.val < 446
        ·
          by_cases h445 : i.val < 445
          ·
            have he : (⟨444, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 444 = i.val
              omega
            simpa only [he] using anchor0444
          ·
            have he : (⟨445, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 445 = i.val
              omega
            simpa only [he] using anchor0445
        ·
          by_cases h447 : i.val < 447
          ·
            have he : (⟨446, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 446 = i.val
              omega
            simpa only [he] using anchor0446
          ·
            have he : (⟨447, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 447 = i.val
              omega
            simpa only [he] using anchor0447

private theorem anchorGroup0014 (i : Fin 1069)
    (hlo : 448 ≤ i.val) (hhi : i.val < 480) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h464 : i.val < 464
  ·
    by_cases h456 : i.val < 456
    ·
      by_cases h452 : i.val < 452
      ·
        by_cases h450 : i.val < 450
        ·
          by_cases h449 : i.val < 449
          ·
            have he : (⟨448, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 448 = i.val
              omega
            simpa only [he] using anchor0448
          ·
            have he : (⟨449, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 449 = i.val
              omega
            simpa only [he] using anchor0449
        ·
          by_cases h451 : i.val < 451
          ·
            have he : (⟨450, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 450 = i.val
              omega
            simpa only [he] using anchor0450
          ·
            have he : (⟨451, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 451 = i.val
              omega
            simpa only [he] using anchor0451
      ·
        by_cases h454 : i.val < 454
        ·
          by_cases h453 : i.val < 453
          ·
            have he : (⟨452, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 452 = i.val
              omega
            simpa only [he] using anchor0452
          ·
            have he : (⟨453, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 453 = i.val
              omega
            simpa only [he] using anchor0453
        ·
          by_cases h455 : i.val < 455
          ·
            have he : (⟨454, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 454 = i.val
              omega
            simpa only [he] using anchor0454
          ·
            have he : (⟨455, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 455 = i.val
              omega
            simpa only [he] using anchor0455
    ·
      by_cases h460 : i.val < 460
      ·
        by_cases h458 : i.val < 458
        ·
          by_cases h457 : i.val < 457
          ·
            have he : (⟨456, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 456 = i.val
              omega
            simpa only [he] using anchor0456
          ·
            have he : (⟨457, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 457 = i.val
              omega
            simpa only [he] using anchor0457
        ·
          by_cases h459 : i.val < 459
          ·
            have he : (⟨458, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 458 = i.val
              omega
            simpa only [he] using anchor0458
          ·
            have he : (⟨459, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 459 = i.val
              omega
            simpa only [he] using anchor0459
      ·
        by_cases h462 : i.val < 462
        ·
          by_cases h461 : i.val < 461
          ·
            have he : (⟨460, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 460 = i.val
              omega
            simpa only [he] using anchor0460
          ·
            have he : (⟨461, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 461 = i.val
              omega
            simpa only [he] using anchor0461
        ·
          by_cases h463 : i.val < 463
          ·
            have he : (⟨462, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 462 = i.val
              omega
            simpa only [he] using anchor0462
          ·
            have he : (⟨463, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 463 = i.val
              omega
            simpa only [he] using anchor0463
  ·
    by_cases h472 : i.val < 472
    ·
      by_cases h468 : i.val < 468
      ·
        by_cases h466 : i.val < 466
        ·
          by_cases h465 : i.val < 465
          ·
            have he : (⟨464, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 464 = i.val
              omega
            simpa only [he] using anchor0464
          ·
            have he : (⟨465, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 465 = i.val
              omega
            simpa only [he] using anchor0465
        ·
          by_cases h467 : i.val < 467
          ·
            have he : (⟨466, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 466 = i.val
              omega
            simpa only [he] using anchor0466
          ·
            have he : (⟨467, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 467 = i.val
              omega
            simpa only [he] using anchor0467
      ·
        by_cases h470 : i.val < 470
        ·
          by_cases h469 : i.val < 469
          ·
            have he : (⟨468, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 468 = i.val
              omega
            simpa only [he] using anchor0468
          ·
            have he : (⟨469, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 469 = i.val
              omega
            simpa only [he] using anchor0469
        ·
          by_cases h471 : i.val < 471
          ·
            have he : (⟨470, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 470 = i.val
              omega
            simpa only [he] using anchor0470
          ·
            have he : (⟨471, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 471 = i.val
              omega
            simpa only [he] using anchor0471
    ·
      by_cases h476 : i.val < 476
      ·
        by_cases h474 : i.val < 474
        ·
          by_cases h473 : i.val < 473
          ·
            have he : (⟨472, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 472 = i.val
              omega
            simpa only [he] using anchor0472
          ·
            have he : (⟨473, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 473 = i.val
              omega
            simpa only [he] using anchor0473
        ·
          by_cases h475 : i.val < 475
          ·
            have he : (⟨474, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 474 = i.val
              omega
            simpa only [he] using anchor0474
          ·
            have he : (⟨475, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 475 = i.val
              omega
            simpa only [he] using anchor0475
      ·
        by_cases h478 : i.val < 478
        ·
          by_cases h477 : i.val < 477
          ·
            have he : (⟨476, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 476 = i.val
              omega
            simpa only [he] using anchor0476
          ·
            have he : (⟨477, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 477 = i.val
              omega
            simpa only [he] using anchor0477
        ·
          by_cases h479 : i.val < 479
          ·
            have he : (⟨478, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 478 = i.val
              omega
            simpa only [he] using anchor0478
          ·
            have he : (⟨479, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 479 = i.val
              omega
            simpa only [he] using anchor0479

private theorem anchorGroup0015 (i : Fin 1069)
    (hlo : 480 ≤ i.val) (hhi : i.val < 512) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h496 : i.val < 496
  ·
    by_cases h488 : i.val < 488
    ·
      by_cases h484 : i.val < 484
      ·
        by_cases h482 : i.val < 482
        ·
          by_cases h481 : i.val < 481
          ·
            have he : (⟨480, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 480 = i.val
              omega
            simpa only [he] using anchor0480
          ·
            have he : (⟨481, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 481 = i.val
              omega
            simpa only [he] using anchor0481
        ·
          by_cases h483 : i.val < 483
          ·
            have he : (⟨482, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 482 = i.val
              omega
            simpa only [he] using anchor0482
          ·
            have he : (⟨483, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 483 = i.val
              omega
            simpa only [he] using anchor0483
      ·
        by_cases h486 : i.val < 486
        ·
          by_cases h485 : i.val < 485
          ·
            have he : (⟨484, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 484 = i.val
              omega
            simpa only [he] using anchor0484
          ·
            have he : (⟨485, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 485 = i.val
              omega
            simpa only [he] using anchor0485
        ·
          by_cases h487 : i.val < 487
          ·
            have he : (⟨486, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 486 = i.val
              omega
            simpa only [he] using anchor0486
          ·
            have he : (⟨487, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 487 = i.val
              omega
            simpa only [he] using anchor0487
    ·
      by_cases h492 : i.val < 492
      ·
        by_cases h490 : i.val < 490
        ·
          by_cases h489 : i.val < 489
          ·
            have he : (⟨488, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 488 = i.val
              omega
            simpa only [he] using anchor0488
          ·
            have he : (⟨489, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 489 = i.val
              omega
            simpa only [he] using anchor0489
        ·
          by_cases h491 : i.val < 491
          ·
            have he : (⟨490, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 490 = i.val
              omega
            simpa only [he] using anchor0490
          ·
            have he : (⟨491, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 491 = i.val
              omega
            simpa only [he] using anchor0491
      ·
        by_cases h494 : i.val < 494
        ·
          by_cases h493 : i.val < 493
          ·
            have he : (⟨492, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 492 = i.val
              omega
            simpa only [he] using anchor0492
          ·
            have he : (⟨493, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 493 = i.val
              omega
            simpa only [he] using anchor0493
        ·
          by_cases h495 : i.val < 495
          ·
            have he : (⟨494, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 494 = i.val
              omega
            simpa only [he] using anchor0494
          ·
            have he : (⟨495, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 495 = i.val
              omega
            simpa only [he] using anchor0495
  ·
    by_cases h504 : i.val < 504
    ·
      by_cases h500 : i.val < 500
      ·
        by_cases h498 : i.val < 498
        ·
          by_cases h497 : i.val < 497
          ·
            have he : (⟨496, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 496 = i.val
              omega
            simpa only [he] using anchor0496
          ·
            have he : (⟨497, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 497 = i.val
              omega
            simpa only [he] using anchor0497
        ·
          by_cases h499 : i.val < 499
          ·
            have he : (⟨498, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 498 = i.val
              omega
            simpa only [he] using anchor0498
          ·
            have he : (⟨499, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 499 = i.val
              omega
            simpa only [he] using anchor0499
      ·
        by_cases h502 : i.val < 502
        ·
          by_cases h501 : i.val < 501
          ·
            have he : (⟨500, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 500 = i.val
              omega
            simpa only [he] using anchor0500
          ·
            have he : (⟨501, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 501 = i.val
              omega
            simpa only [he] using anchor0501
        ·
          by_cases h503 : i.val < 503
          ·
            have he : (⟨502, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 502 = i.val
              omega
            simpa only [he] using anchor0502
          ·
            have he : (⟨503, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 503 = i.val
              omega
            simpa only [he] using anchor0503
    ·
      by_cases h508 : i.val < 508
      ·
        by_cases h506 : i.val < 506
        ·
          by_cases h505 : i.val < 505
          ·
            have he : (⟨504, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 504 = i.val
              omega
            simpa only [he] using anchor0504
          ·
            have he : (⟨505, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 505 = i.val
              omega
            simpa only [he] using anchor0505
        ·
          by_cases h507 : i.val < 507
          ·
            have he : (⟨506, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 506 = i.val
              omega
            simpa only [he] using anchor0506
          ·
            have he : (⟨507, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 507 = i.val
              omega
            simpa only [he] using anchor0507
      ·
        by_cases h510 : i.val < 510
        ·
          by_cases h509 : i.val < 509
          ·
            have he : (⟨508, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 508 = i.val
              omega
            simpa only [he] using anchor0508
          ·
            have he : (⟨509, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 509 = i.val
              omega
            simpa only [he] using anchor0509
        ·
          by_cases h511 : i.val < 511
          ·
            have he : (⟨510, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 510 = i.val
              omega
            simpa only [he] using anchor0510
          ·
            have he : (⟨511, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 511 = i.val
              omega
            simpa only [he] using anchor0511

private theorem anchorGroup0016 (i : Fin 1069)
    (hlo : 512 ≤ i.val) (hhi : i.val < 544) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h528 : i.val < 528
  ·
    by_cases h520 : i.val < 520
    ·
      by_cases h516 : i.val < 516
      ·
        by_cases h514 : i.val < 514
        ·
          by_cases h513 : i.val < 513
          ·
            have he : (⟨512, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 512 = i.val
              omega
            simpa only [he] using anchor0512
          ·
            have he : (⟨513, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 513 = i.val
              omega
            simpa only [he] using anchor0513
        ·
          by_cases h515 : i.val < 515
          ·
            have he : (⟨514, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 514 = i.val
              omega
            simpa only [he] using anchor0514
          ·
            have he : (⟨515, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 515 = i.val
              omega
            simpa only [he] using anchor0515
      ·
        by_cases h518 : i.val < 518
        ·
          by_cases h517 : i.val < 517
          ·
            have he : (⟨516, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 516 = i.val
              omega
            simpa only [he] using anchor0516
          ·
            have he : (⟨517, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 517 = i.val
              omega
            simpa only [he] using anchor0517
        ·
          by_cases h519 : i.val < 519
          ·
            have he : (⟨518, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 518 = i.val
              omega
            simpa only [he] using anchor0518
          ·
            have he : (⟨519, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 519 = i.val
              omega
            simpa only [he] using anchor0519
    ·
      by_cases h524 : i.val < 524
      ·
        by_cases h522 : i.val < 522
        ·
          by_cases h521 : i.val < 521
          ·
            have he : (⟨520, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 520 = i.val
              omega
            simpa only [he] using anchor0520
          ·
            have he : (⟨521, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 521 = i.val
              omega
            simpa only [he] using anchor0521
        ·
          by_cases h523 : i.val < 523
          ·
            have he : (⟨522, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 522 = i.val
              omega
            simpa only [he] using anchor0522
          ·
            have he : (⟨523, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 523 = i.val
              omega
            simpa only [he] using anchor0523
      ·
        by_cases h526 : i.val < 526
        ·
          by_cases h525 : i.val < 525
          ·
            have he : (⟨524, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 524 = i.val
              omega
            simpa only [he] using anchor0524
          ·
            have he : (⟨525, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 525 = i.val
              omega
            simpa only [he] using anchor0525
        ·
          by_cases h527 : i.val < 527
          ·
            have he : (⟨526, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 526 = i.val
              omega
            simpa only [he] using anchor0526
          ·
            have he : (⟨527, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 527 = i.val
              omega
            simpa only [he] using anchor0527
  ·
    by_cases h536 : i.val < 536
    ·
      by_cases h532 : i.val < 532
      ·
        by_cases h530 : i.val < 530
        ·
          by_cases h529 : i.val < 529
          ·
            have he : (⟨528, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 528 = i.val
              omega
            simpa only [he] using anchor0528
          ·
            have he : (⟨529, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 529 = i.val
              omega
            simpa only [he] using anchor0529
        ·
          by_cases h531 : i.val < 531
          ·
            have he : (⟨530, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 530 = i.val
              omega
            simpa only [he] using anchor0530
          ·
            have he : (⟨531, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 531 = i.val
              omega
            simpa only [he] using anchor0531
      ·
        by_cases h534 : i.val < 534
        ·
          by_cases h533 : i.val < 533
          ·
            have he : (⟨532, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 532 = i.val
              omega
            simpa only [he] using anchor0532
          ·
            have he : (⟨533, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 533 = i.val
              omega
            simpa only [he] using anchor0533
        ·
          by_cases h535 : i.val < 535
          ·
            have he : (⟨534, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 534 = i.val
              omega
            simpa only [he] using anchor0534
          ·
            have he : (⟨535, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 535 = i.val
              omega
            simpa only [he] using anchor0535
    ·
      by_cases h540 : i.val < 540
      ·
        by_cases h538 : i.val < 538
        ·
          by_cases h537 : i.val < 537
          ·
            have he : (⟨536, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 536 = i.val
              omega
            simpa only [he] using anchor0536
          ·
            have he : (⟨537, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 537 = i.val
              omega
            simpa only [he] using anchor0537
        ·
          by_cases h539 : i.val < 539
          ·
            have he : (⟨538, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 538 = i.val
              omega
            simpa only [he] using anchor0538
          ·
            have he : (⟨539, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 539 = i.val
              omega
            simpa only [he] using anchor0539
      ·
        by_cases h542 : i.val < 542
        ·
          by_cases h541 : i.val < 541
          ·
            have he : (⟨540, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 540 = i.val
              omega
            simpa only [he] using anchor0540
          ·
            have he : (⟨541, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 541 = i.val
              omega
            simpa only [he] using anchor0541
        ·
          by_cases h543 : i.val < 543
          ·
            have he : (⟨542, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 542 = i.val
              omega
            simpa only [he] using anchor0542
          ·
            have he : (⟨543, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 543 = i.val
              omega
            simpa only [he] using anchor0543

private theorem anchorGroup0017 (i : Fin 1069)
    (hlo : 544 ≤ i.val) (hhi : i.val < 576) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h560 : i.val < 560
  ·
    by_cases h552 : i.val < 552
    ·
      by_cases h548 : i.val < 548
      ·
        by_cases h546 : i.val < 546
        ·
          by_cases h545 : i.val < 545
          ·
            have he : (⟨544, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 544 = i.val
              omega
            simpa only [he] using anchor0544
          ·
            have he : (⟨545, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 545 = i.val
              omega
            simpa only [he] using anchor0545
        ·
          by_cases h547 : i.val < 547
          ·
            have he : (⟨546, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 546 = i.val
              omega
            simpa only [he] using anchor0546
          ·
            have he : (⟨547, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 547 = i.val
              omega
            simpa only [he] using anchor0547
      ·
        by_cases h550 : i.val < 550
        ·
          by_cases h549 : i.val < 549
          ·
            have he : (⟨548, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 548 = i.val
              omega
            simpa only [he] using anchor0548
          ·
            have he : (⟨549, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 549 = i.val
              omega
            simpa only [he] using anchor0549
        ·
          by_cases h551 : i.val < 551
          ·
            have he : (⟨550, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 550 = i.val
              omega
            simpa only [he] using anchor0550
          ·
            have he : (⟨551, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 551 = i.val
              omega
            simpa only [he] using anchor0551
    ·
      by_cases h556 : i.val < 556
      ·
        by_cases h554 : i.val < 554
        ·
          by_cases h553 : i.val < 553
          ·
            have he : (⟨552, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 552 = i.val
              omega
            simpa only [he] using anchor0552
          ·
            have he : (⟨553, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 553 = i.val
              omega
            simpa only [he] using anchor0553
        ·
          by_cases h555 : i.val < 555
          ·
            have he : (⟨554, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 554 = i.val
              omega
            simpa only [he] using anchor0554
          ·
            have he : (⟨555, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 555 = i.val
              omega
            simpa only [he] using anchor0555
      ·
        by_cases h558 : i.val < 558
        ·
          by_cases h557 : i.val < 557
          ·
            have he : (⟨556, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 556 = i.val
              omega
            simpa only [he] using anchor0556
          ·
            have he : (⟨557, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 557 = i.val
              omega
            simpa only [he] using anchor0557
        ·
          by_cases h559 : i.val < 559
          ·
            have he : (⟨558, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 558 = i.val
              omega
            simpa only [he] using anchor0558
          ·
            have he : (⟨559, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 559 = i.val
              omega
            simpa only [he] using anchor0559
  ·
    by_cases h568 : i.val < 568
    ·
      by_cases h564 : i.val < 564
      ·
        by_cases h562 : i.val < 562
        ·
          by_cases h561 : i.val < 561
          ·
            have he : (⟨560, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 560 = i.val
              omega
            simpa only [he] using anchor0560
          ·
            have he : (⟨561, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 561 = i.val
              omega
            simpa only [he] using anchor0561
        ·
          by_cases h563 : i.val < 563
          ·
            have he : (⟨562, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 562 = i.val
              omega
            simpa only [he] using anchor0562
          ·
            have he : (⟨563, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 563 = i.val
              omega
            simpa only [he] using anchor0563
      ·
        by_cases h566 : i.val < 566
        ·
          by_cases h565 : i.val < 565
          ·
            have he : (⟨564, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 564 = i.val
              omega
            simpa only [he] using anchor0564
          ·
            have he : (⟨565, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 565 = i.val
              omega
            simpa only [he] using anchor0565
        ·
          by_cases h567 : i.val < 567
          ·
            have he : (⟨566, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 566 = i.val
              omega
            simpa only [he] using anchor0566
          ·
            have he : (⟨567, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 567 = i.val
              omega
            simpa only [he] using anchor0567
    ·
      by_cases h572 : i.val < 572
      ·
        by_cases h570 : i.val < 570
        ·
          by_cases h569 : i.val < 569
          ·
            have he : (⟨568, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 568 = i.val
              omega
            simpa only [he] using anchor0568
          ·
            have he : (⟨569, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 569 = i.val
              omega
            simpa only [he] using anchor0569
        ·
          by_cases h571 : i.val < 571
          ·
            have he : (⟨570, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 570 = i.val
              omega
            simpa only [he] using anchor0570
          ·
            have he : (⟨571, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 571 = i.val
              omega
            simpa only [he] using anchor0571
      ·
        by_cases h574 : i.val < 574
        ·
          by_cases h573 : i.val < 573
          ·
            have he : (⟨572, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 572 = i.val
              omega
            simpa only [he] using anchor0572
          ·
            have he : (⟨573, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 573 = i.val
              omega
            simpa only [he] using anchor0573
        ·
          by_cases h575 : i.val < 575
          ·
            have he : (⟨574, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 574 = i.val
              omega
            simpa only [he] using anchor0574
          ·
            have he : (⟨575, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 575 = i.val
              omega
            simpa only [he] using anchor0575

private theorem anchorGroup0018 (i : Fin 1069)
    (hlo : 576 ≤ i.val) (hhi : i.val < 608) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h592 : i.val < 592
  ·
    by_cases h584 : i.val < 584
    ·
      by_cases h580 : i.val < 580
      ·
        by_cases h578 : i.val < 578
        ·
          by_cases h577 : i.val < 577
          ·
            have he : (⟨576, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 576 = i.val
              omega
            simpa only [he] using anchor0576
          ·
            have he : (⟨577, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 577 = i.val
              omega
            simpa only [he] using anchor0577
        ·
          by_cases h579 : i.val < 579
          ·
            have he : (⟨578, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 578 = i.val
              omega
            simpa only [he] using anchor0578
          ·
            have he : (⟨579, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 579 = i.val
              omega
            simpa only [he] using anchor0579
      ·
        by_cases h582 : i.val < 582
        ·
          by_cases h581 : i.val < 581
          ·
            have he : (⟨580, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 580 = i.val
              omega
            simpa only [he] using anchor0580
          ·
            have he : (⟨581, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 581 = i.val
              omega
            simpa only [he] using anchor0581
        ·
          by_cases h583 : i.val < 583
          ·
            have he : (⟨582, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 582 = i.val
              omega
            simpa only [he] using anchor0582
          ·
            have he : (⟨583, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 583 = i.val
              omega
            simpa only [he] using anchor0583
    ·
      by_cases h588 : i.val < 588
      ·
        by_cases h586 : i.val < 586
        ·
          by_cases h585 : i.val < 585
          ·
            have he : (⟨584, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 584 = i.val
              omega
            simpa only [he] using anchor0584
          ·
            have he : (⟨585, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 585 = i.val
              omega
            simpa only [he] using anchor0585
        ·
          by_cases h587 : i.val < 587
          ·
            have he : (⟨586, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 586 = i.val
              omega
            simpa only [he] using anchor0586
          ·
            have he : (⟨587, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 587 = i.val
              omega
            simpa only [he] using anchor0587
      ·
        by_cases h590 : i.val < 590
        ·
          by_cases h589 : i.val < 589
          ·
            have he : (⟨588, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 588 = i.val
              omega
            simpa only [he] using anchor0588
          ·
            have he : (⟨589, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 589 = i.val
              omega
            simpa only [he] using anchor0589
        ·
          by_cases h591 : i.val < 591
          ·
            have he : (⟨590, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 590 = i.val
              omega
            simpa only [he] using anchor0590
          ·
            have he : (⟨591, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 591 = i.val
              omega
            simpa only [he] using anchor0591
  ·
    by_cases h600 : i.val < 600
    ·
      by_cases h596 : i.val < 596
      ·
        by_cases h594 : i.val < 594
        ·
          by_cases h593 : i.val < 593
          ·
            have he : (⟨592, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 592 = i.val
              omega
            simpa only [he] using anchor0592
          ·
            have he : (⟨593, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 593 = i.val
              omega
            simpa only [he] using anchor0593
        ·
          by_cases h595 : i.val < 595
          ·
            have he : (⟨594, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 594 = i.val
              omega
            simpa only [he] using anchor0594
          ·
            have he : (⟨595, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 595 = i.val
              omega
            simpa only [he] using anchor0595
      ·
        by_cases h598 : i.val < 598
        ·
          by_cases h597 : i.val < 597
          ·
            have he : (⟨596, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 596 = i.val
              omega
            simpa only [he] using anchor0596
          ·
            have he : (⟨597, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 597 = i.val
              omega
            simpa only [he] using anchor0597
        ·
          by_cases h599 : i.val < 599
          ·
            have he : (⟨598, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 598 = i.val
              omega
            simpa only [he] using anchor0598
          ·
            have he : (⟨599, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 599 = i.val
              omega
            simpa only [he] using anchor0599
    ·
      by_cases h604 : i.val < 604
      ·
        by_cases h602 : i.val < 602
        ·
          by_cases h601 : i.val < 601
          ·
            have he : (⟨600, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 600 = i.val
              omega
            simpa only [he] using anchor0600
          ·
            have he : (⟨601, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 601 = i.val
              omega
            simpa only [he] using anchor0601
        ·
          by_cases h603 : i.val < 603
          ·
            have he : (⟨602, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 602 = i.val
              omega
            simpa only [he] using anchor0602
          ·
            have he : (⟨603, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 603 = i.val
              omega
            simpa only [he] using anchor0603
      ·
        by_cases h606 : i.val < 606
        ·
          by_cases h605 : i.val < 605
          ·
            have he : (⟨604, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 604 = i.val
              omega
            simpa only [he] using anchor0604
          ·
            have he : (⟨605, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 605 = i.val
              omega
            simpa only [he] using anchor0605
        ·
          by_cases h607 : i.val < 607
          ·
            have he : (⟨606, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 606 = i.val
              omega
            simpa only [he] using anchor0606
          ·
            have he : (⟨607, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 607 = i.val
              omega
            simpa only [he] using anchor0607

private theorem anchorGroup0019 (i : Fin 1069)
    (hlo : 608 ≤ i.val) (hhi : i.val < 640) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h624 : i.val < 624
  ·
    by_cases h616 : i.val < 616
    ·
      by_cases h612 : i.val < 612
      ·
        by_cases h610 : i.val < 610
        ·
          by_cases h609 : i.val < 609
          ·
            have he : (⟨608, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 608 = i.val
              omega
            simpa only [he] using anchor0608
          ·
            have he : (⟨609, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 609 = i.val
              omega
            simpa only [he] using anchor0609
        ·
          by_cases h611 : i.val < 611
          ·
            have he : (⟨610, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 610 = i.val
              omega
            simpa only [he] using anchor0610
          ·
            have he : (⟨611, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 611 = i.val
              omega
            simpa only [he] using anchor0611
      ·
        by_cases h614 : i.val < 614
        ·
          by_cases h613 : i.val < 613
          ·
            have he : (⟨612, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 612 = i.val
              omega
            simpa only [he] using anchor0612
          ·
            have he : (⟨613, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 613 = i.val
              omega
            simpa only [he] using anchor0613
        ·
          by_cases h615 : i.val < 615
          ·
            have he : (⟨614, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 614 = i.val
              omega
            simpa only [he] using anchor0614
          ·
            have he : (⟨615, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 615 = i.val
              omega
            simpa only [he] using anchor0615
    ·
      by_cases h620 : i.val < 620
      ·
        by_cases h618 : i.val < 618
        ·
          by_cases h617 : i.val < 617
          ·
            have he : (⟨616, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 616 = i.val
              omega
            simpa only [he] using anchor0616
          ·
            have he : (⟨617, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 617 = i.val
              omega
            simpa only [he] using anchor0617
        ·
          by_cases h619 : i.val < 619
          ·
            have he : (⟨618, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 618 = i.val
              omega
            simpa only [he] using anchor0618
          ·
            have he : (⟨619, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 619 = i.val
              omega
            simpa only [he] using anchor0619
      ·
        by_cases h622 : i.val < 622
        ·
          by_cases h621 : i.val < 621
          ·
            have he : (⟨620, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 620 = i.val
              omega
            simpa only [he] using anchor0620
          ·
            have he : (⟨621, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 621 = i.val
              omega
            simpa only [he] using anchor0621
        ·
          by_cases h623 : i.val < 623
          ·
            have he : (⟨622, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 622 = i.val
              omega
            simpa only [he] using anchor0622
          ·
            have he : (⟨623, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 623 = i.val
              omega
            simpa only [he] using anchor0623
  ·
    by_cases h632 : i.val < 632
    ·
      by_cases h628 : i.val < 628
      ·
        by_cases h626 : i.val < 626
        ·
          by_cases h625 : i.val < 625
          ·
            have he : (⟨624, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 624 = i.val
              omega
            simpa only [he] using anchor0624
          ·
            have he : (⟨625, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 625 = i.val
              omega
            simpa only [he] using anchor0625
        ·
          by_cases h627 : i.val < 627
          ·
            have he : (⟨626, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 626 = i.val
              omega
            simpa only [he] using anchor0626
          ·
            have he : (⟨627, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 627 = i.val
              omega
            simpa only [he] using anchor0627
      ·
        by_cases h630 : i.val < 630
        ·
          by_cases h629 : i.val < 629
          ·
            have he : (⟨628, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 628 = i.val
              omega
            simpa only [he] using anchor0628
          ·
            have he : (⟨629, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 629 = i.val
              omega
            simpa only [he] using anchor0629
        ·
          by_cases h631 : i.val < 631
          ·
            have he : (⟨630, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 630 = i.val
              omega
            simpa only [he] using anchor0630
          ·
            have he : (⟨631, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 631 = i.val
              omega
            simpa only [he] using anchor0631
    ·
      by_cases h636 : i.val < 636
      ·
        by_cases h634 : i.val < 634
        ·
          by_cases h633 : i.val < 633
          ·
            have he : (⟨632, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 632 = i.val
              omega
            simpa only [he] using anchor0632
          ·
            have he : (⟨633, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 633 = i.val
              omega
            simpa only [he] using anchor0633
        ·
          by_cases h635 : i.val < 635
          ·
            have he : (⟨634, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 634 = i.val
              omega
            simpa only [he] using anchor0634
          ·
            have he : (⟨635, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 635 = i.val
              omega
            simpa only [he] using anchor0635
      ·
        by_cases h638 : i.val < 638
        ·
          by_cases h637 : i.val < 637
          ·
            have he : (⟨636, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 636 = i.val
              omega
            simpa only [he] using anchor0636
          ·
            have he : (⟨637, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 637 = i.val
              omega
            simpa only [he] using anchor0637
        ·
          by_cases h639 : i.val < 639
          ·
            have he : (⟨638, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 638 = i.val
              omega
            simpa only [he] using anchor0638
          ·
            have he : (⟨639, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 639 = i.val
              omega
            simpa only [he] using anchor0639

private theorem anchorGroup0020 (i : Fin 1069)
    (hlo : 640 ≤ i.val) (hhi : i.val < 672) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h656 : i.val < 656
  ·
    by_cases h648 : i.val < 648
    ·
      by_cases h644 : i.val < 644
      ·
        by_cases h642 : i.val < 642
        ·
          by_cases h641 : i.val < 641
          ·
            have he : (⟨640, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 640 = i.val
              omega
            simpa only [he] using anchor0640
          ·
            have he : (⟨641, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 641 = i.val
              omega
            simpa only [he] using anchor0641
        ·
          by_cases h643 : i.val < 643
          ·
            have he : (⟨642, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 642 = i.val
              omega
            simpa only [he] using anchor0642
          ·
            have he : (⟨643, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 643 = i.val
              omega
            simpa only [he] using anchor0643
      ·
        by_cases h646 : i.val < 646
        ·
          by_cases h645 : i.val < 645
          ·
            have he : (⟨644, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 644 = i.val
              omega
            simpa only [he] using anchor0644
          ·
            have he : (⟨645, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 645 = i.val
              omega
            simpa only [he] using anchor0645
        ·
          by_cases h647 : i.val < 647
          ·
            have he : (⟨646, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 646 = i.val
              omega
            simpa only [he] using anchor0646
          ·
            have he : (⟨647, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 647 = i.val
              omega
            simpa only [he] using anchor0647
    ·
      by_cases h652 : i.val < 652
      ·
        by_cases h650 : i.val < 650
        ·
          by_cases h649 : i.val < 649
          ·
            have he : (⟨648, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 648 = i.val
              omega
            simpa only [he] using anchor0648
          ·
            have he : (⟨649, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 649 = i.val
              omega
            simpa only [he] using anchor0649
        ·
          by_cases h651 : i.val < 651
          ·
            have he : (⟨650, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 650 = i.val
              omega
            simpa only [he] using anchor0650
          ·
            have he : (⟨651, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 651 = i.val
              omega
            simpa only [he] using anchor0651
      ·
        by_cases h654 : i.val < 654
        ·
          by_cases h653 : i.val < 653
          ·
            have he : (⟨652, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 652 = i.val
              omega
            simpa only [he] using anchor0652
          ·
            have he : (⟨653, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 653 = i.val
              omega
            simpa only [he] using anchor0653
        ·
          by_cases h655 : i.val < 655
          ·
            have he : (⟨654, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 654 = i.val
              omega
            simpa only [he] using anchor0654
          ·
            have he : (⟨655, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 655 = i.val
              omega
            simpa only [he] using anchor0655
  ·
    by_cases h664 : i.val < 664
    ·
      by_cases h660 : i.val < 660
      ·
        by_cases h658 : i.val < 658
        ·
          by_cases h657 : i.val < 657
          ·
            have he : (⟨656, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 656 = i.val
              omega
            simpa only [he] using anchor0656
          ·
            have he : (⟨657, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 657 = i.val
              omega
            simpa only [he] using anchor0657
        ·
          by_cases h659 : i.val < 659
          ·
            have he : (⟨658, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 658 = i.val
              omega
            simpa only [he] using anchor0658
          ·
            have he : (⟨659, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 659 = i.val
              omega
            simpa only [he] using anchor0659
      ·
        by_cases h662 : i.val < 662
        ·
          by_cases h661 : i.val < 661
          ·
            have he : (⟨660, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 660 = i.val
              omega
            simpa only [he] using anchor0660
          ·
            have he : (⟨661, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 661 = i.val
              omega
            simpa only [he] using anchor0661
        ·
          by_cases h663 : i.val < 663
          ·
            have he : (⟨662, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 662 = i.val
              omega
            simpa only [he] using anchor0662
          ·
            have he : (⟨663, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 663 = i.val
              omega
            simpa only [he] using anchor0663
    ·
      by_cases h668 : i.val < 668
      ·
        by_cases h666 : i.val < 666
        ·
          by_cases h665 : i.val < 665
          ·
            have he : (⟨664, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 664 = i.val
              omega
            simpa only [he] using anchor0664
          ·
            have he : (⟨665, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 665 = i.val
              omega
            simpa only [he] using anchor0665
        ·
          by_cases h667 : i.val < 667
          ·
            have he : (⟨666, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 666 = i.val
              omega
            simpa only [he] using anchor0666
          ·
            have he : (⟨667, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 667 = i.val
              omega
            simpa only [he] using anchor0667
      ·
        by_cases h670 : i.val < 670
        ·
          by_cases h669 : i.val < 669
          ·
            have he : (⟨668, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 668 = i.val
              omega
            simpa only [he] using anchor0668
          ·
            have he : (⟨669, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 669 = i.val
              omega
            simpa only [he] using anchor0669
        ·
          by_cases h671 : i.val < 671
          ·
            have he : (⟨670, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 670 = i.val
              omega
            simpa only [he] using anchor0670
          ·
            have he : (⟨671, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 671 = i.val
              omega
            simpa only [he] using anchor0671

private theorem anchorGroup0021 (i : Fin 1069)
    (hlo : 672 ≤ i.val) (hhi : i.val < 704) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h688 : i.val < 688
  ·
    by_cases h680 : i.val < 680
    ·
      by_cases h676 : i.val < 676
      ·
        by_cases h674 : i.val < 674
        ·
          by_cases h673 : i.val < 673
          ·
            have he : (⟨672, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 672 = i.val
              omega
            simpa only [he] using anchor0672
          ·
            have he : (⟨673, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 673 = i.val
              omega
            simpa only [he] using anchor0673
        ·
          by_cases h675 : i.val < 675
          ·
            have he : (⟨674, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 674 = i.val
              omega
            simpa only [he] using anchor0674
          ·
            have he : (⟨675, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 675 = i.val
              omega
            simpa only [he] using anchor0675
      ·
        by_cases h678 : i.val < 678
        ·
          by_cases h677 : i.val < 677
          ·
            have he : (⟨676, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 676 = i.val
              omega
            simpa only [he] using anchor0676
          ·
            have he : (⟨677, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 677 = i.val
              omega
            simpa only [he] using anchor0677
        ·
          by_cases h679 : i.val < 679
          ·
            have he : (⟨678, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 678 = i.val
              omega
            simpa only [he] using anchor0678
          ·
            have he : (⟨679, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 679 = i.val
              omega
            simpa only [he] using anchor0679
    ·
      by_cases h684 : i.val < 684
      ·
        by_cases h682 : i.val < 682
        ·
          by_cases h681 : i.val < 681
          ·
            have he : (⟨680, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 680 = i.val
              omega
            simpa only [he] using anchor0680
          ·
            have he : (⟨681, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 681 = i.val
              omega
            simpa only [he] using anchor0681
        ·
          by_cases h683 : i.val < 683
          ·
            have he : (⟨682, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 682 = i.val
              omega
            simpa only [he] using anchor0682
          ·
            have he : (⟨683, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 683 = i.val
              omega
            simpa only [he] using anchor0683
      ·
        by_cases h686 : i.val < 686
        ·
          by_cases h685 : i.val < 685
          ·
            have he : (⟨684, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 684 = i.val
              omega
            simpa only [he] using anchor0684
          ·
            have he : (⟨685, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 685 = i.val
              omega
            simpa only [he] using anchor0685
        ·
          by_cases h687 : i.val < 687
          ·
            have he : (⟨686, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 686 = i.val
              omega
            simpa only [he] using anchor0686
          ·
            have he : (⟨687, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 687 = i.val
              omega
            simpa only [he] using anchor0687
  ·
    by_cases h696 : i.val < 696
    ·
      by_cases h692 : i.val < 692
      ·
        by_cases h690 : i.val < 690
        ·
          by_cases h689 : i.val < 689
          ·
            have he : (⟨688, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 688 = i.val
              omega
            simpa only [he] using anchor0688
          ·
            have he : (⟨689, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 689 = i.val
              omega
            simpa only [he] using anchor0689
        ·
          by_cases h691 : i.val < 691
          ·
            have he : (⟨690, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 690 = i.val
              omega
            simpa only [he] using anchor0690
          ·
            have he : (⟨691, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 691 = i.val
              omega
            simpa only [he] using anchor0691
      ·
        by_cases h694 : i.val < 694
        ·
          by_cases h693 : i.val < 693
          ·
            have he : (⟨692, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 692 = i.val
              omega
            simpa only [he] using anchor0692
          ·
            have he : (⟨693, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 693 = i.val
              omega
            simpa only [he] using anchor0693
        ·
          by_cases h695 : i.val < 695
          ·
            have he : (⟨694, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 694 = i.val
              omega
            simpa only [he] using anchor0694
          ·
            have he : (⟨695, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 695 = i.val
              omega
            simpa only [he] using anchor0695
    ·
      by_cases h700 : i.val < 700
      ·
        by_cases h698 : i.val < 698
        ·
          by_cases h697 : i.val < 697
          ·
            have he : (⟨696, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 696 = i.val
              omega
            simpa only [he] using anchor0696
          ·
            have he : (⟨697, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 697 = i.val
              omega
            simpa only [he] using anchor0697
        ·
          by_cases h699 : i.val < 699
          ·
            have he : (⟨698, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 698 = i.val
              omega
            simpa only [he] using anchor0698
          ·
            have he : (⟨699, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 699 = i.val
              omega
            simpa only [he] using anchor0699
      ·
        by_cases h702 : i.val < 702
        ·
          by_cases h701 : i.val < 701
          ·
            have he : (⟨700, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 700 = i.val
              omega
            simpa only [he] using anchor0700
          ·
            have he : (⟨701, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 701 = i.val
              omega
            simpa only [he] using anchor0701
        ·
          by_cases h703 : i.val < 703
          ·
            have he : (⟨702, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 702 = i.val
              omega
            simpa only [he] using anchor0702
          ·
            have he : (⟨703, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 703 = i.val
              omega
            simpa only [he] using anchor0703

private theorem anchorGroup0022 (i : Fin 1069)
    (hlo : 704 ≤ i.val) (hhi : i.val < 736) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h720 : i.val < 720
  ·
    by_cases h712 : i.val < 712
    ·
      by_cases h708 : i.val < 708
      ·
        by_cases h706 : i.val < 706
        ·
          by_cases h705 : i.val < 705
          ·
            have he : (⟨704, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 704 = i.val
              omega
            simpa only [he] using anchor0704
          ·
            have he : (⟨705, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 705 = i.val
              omega
            simpa only [he] using anchor0705
        ·
          by_cases h707 : i.val < 707
          ·
            have he : (⟨706, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 706 = i.val
              omega
            simpa only [he] using anchor0706
          ·
            have he : (⟨707, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 707 = i.val
              omega
            simpa only [he] using anchor0707
      ·
        by_cases h710 : i.val < 710
        ·
          by_cases h709 : i.val < 709
          ·
            have he : (⟨708, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 708 = i.val
              omega
            simpa only [he] using anchor0708
          ·
            have he : (⟨709, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 709 = i.val
              omega
            simpa only [he] using anchor0709
        ·
          by_cases h711 : i.val < 711
          ·
            have he : (⟨710, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 710 = i.val
              omega
            simpa only [he] using anchor0710
          ·
            have he : (⟨711, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 711 = i.val
              omega
            simpa only [he] using anchor0711
    ·
      by_cases h716 : i.val < 716
      ·
        by_cases h714 : i.val < 714
        ·
          by_cases h713 : i.val < 713
          ·
            have he : (⟨712, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 712 = i.val
              omega
            simpa only [he] using anchor0712
          ·
            have he : (⟨713, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 713 = i.val
              omega
            simpa only [he] using anchor0713
        ·
          by_cases h715 : i.val < 715
          ·
            have he : (⟨714, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 714 = i.val
              omega
            simpa only [he] using anchor0714
          ·
            have he : (⟨715, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 715 = i.val
              omega
            simpa only [he] using anchor0715
      ·
        by_cases h718 : i.val < 718
        ·
          by_cases h717 : i.val < 717
          ·
            have he : (⟨716, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 716 = i.val
              omega
            simpa only [he] using anchor0716
          ·
            have he : (⟨717, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 717 = i.val
              omega
            simpa only [he] using anchor0717
        ·
          by_cases h719 : i.val < 719
          ·
            have he : (⟨718, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 718 = i.val
              omega
            simpa only [he] using anchor0718
          ·
            have he : (⟨719, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 719 = i.val
              omega
            simpa only [he] using anchor0719
  ·
    by_cases h728 : i.val < 728
    ·
      by_cases h724 : i.val < 724
      ·
        by_cases h722 : i.val < 722
        ·
          by_cases h721 : i.val < 721
          ·
            have he : (⟨720, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 720 = i.val
              omega
            simpa only [he] using anchor0720
          ·
            have he : (⟨721, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 721 = i.val
              omega
            simpa only [he] using anchor0721
        ·
          by_cases h723 : i.val < 723
          ·
            have he : (⟨722, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 722 = i.val
              omega
            simpa only [he] using anchor0722
          ·
            have he : (⟨723, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 723 = i.val
              omega
            simpa only [he] using anchor0723
      ·
        by_cases h726 : i.val < 726
        ·
          by_cases h725 : i.val < 725
          ·
            have he : (⟨724, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 724 = i.val
              omega
            simpa only [he] using anchor0724
          ·
            have he : (⟨725, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 725 = i.val
              omega
            simpa only [he] using anchor0725
        ·
          by_cases h727 : i.val < 727
          ·
            have he : (⟨726, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 726 = i.val
              omega
            simpa only [he] using anchor0726
          ·
            have he : (⟨727, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 727 = i.val
              omega
            simpa only [he] using anchor0727
    ·
      by_cases h732 : i.val < 732
      ·
        by_cases h730 : i.val < 730
        ·
          by_cases h729 : i.val < 729
          ·
            have he : (⟨728, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 728 = i.val
              omega
            simpa only [he] using anchor0728
          ·
            have he : (⟨729, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 729 = i.val
              omega
            simpa only [he] using anchor0729
        ·
          by_cases h731 : i.val < 731
          ·
            have he : (⟨730, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 730 = i.val
              omega
            simpa only [he] using anchor0730
          ·
            have he : (⟨731, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 731 = i.val
              omega
            simpa only [he] using anchor0731
      ·
        by_cases h734 : i.val < 734
        ·
          by_cases h733 : i.val < 733
          ·
            have he : (⟨732, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 732 = i.val
              omega
            simpa only [he] using anchor0732
          ·
            have he : (⟨733, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 733 = i.val
              omega
            simpa only [he] using anchor0733
        ·
          by_cases h735 : i.val < 735
          ·
            have he : (⟨734, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 734 = i.val
              omega
            simpa only [he] using anchor0734
          ·
            have he : (⟨735, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 735 = i.val
              omega
            simpa only [he] using anchor0735

private theorem anchorGroup0023 (i : Fin 1069)
    (hlo : 736 ≤ i.val) (hhi : i.val < 768) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h752 : i.val < 752
  ·
    by_cases h744 : i.val < 744
    ·
      by_cases h740 : i.val < 740
      ·
        by_cases h738 : i.val < 738
        ·
          by_cases h737 : i.val < 737
          ·
            have he : (⟨736, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 736 = i.val
              omega
            simpa only [he] using anchor0736
          ·
            have he : (⟨737, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 737 = i.val
              omega
            simpa only [he] using anchor0737
        ·
          by_cases h739 : i.val < 739
          ·
            have he : (⟨738, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 738 = i.val
              omega
            simpa only [he] using anchor0738
          ·
            have he : (⟨739, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 739 = i.val
              omega
            simpa only [he] using anchor0739
      ·
        by_cases h742 : i.val < 742
        ·
          by_cases h741 : i.val < 741
          ·
            have he : (⟨740, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 740 = i.val
              omega
            simpa only [he] using anchor0740
          ·
            have he : (⟨741, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 741 = i.val
              omega
            simpa only [he] using anchor0741
        ·
          by_cases h743 : i.val < 743
          ·
            have he : (⟨742, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 742 = i.val
              omega
            simpa only [he] using anchor0742
          ·
            have he : (⟨743, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 743 = i.val
              omega
            simpa only [he] using anchor0743
    ·
      by_cases h748 : i.val < 748
      ·
        by_cases h746 : i.val < 746
        ·
          by_cases h745 : i.val < 745
          ·
            have he : (⟨744, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 744 = i.val
              omega
            simpa only [he] using anchor0744
          ·
            have he : (⟨745, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 745 = i.val
              omega
            simpa only [he] using anchor0745
        ·
          by_cases h747 : i.val < 747
          ·
            have he : (⟨746, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 746 = i.val
              omega
            simpa only [he] using anchor0746
          ·
            have he : (⟨747, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 747 = i.val
              omega
            simpa only [he] using anchor0747
      ·
        by_cases h750 : i.val < 750
        ·
          by_cases h749 : i.val < 749
          ·
            have he : (⟨748, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 748 = i.val
              omega
            simpa only [he] using anchor0748
          ·
            have he : (⟨749, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 749 = i.val
              omega
            simpa only [he] using anchor0749
        ·
          by_cases h751 : i.val < 751
          ·
            have he : (⟨750, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 750 = i.val
              omega
            simpa only [he] using anchor0750
          ·
            have he : (⟨751, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 751 = i.val
              omega
            simpa only [he] using anchor0751
  ·
    by_cases h760 : i.val < 760
    ·
      by_cases h756 : i.val < 756
      ·
        by_cases h754 : i.val < 754
        ·
          by_cases h753 : i.val < 753
          ·
            have he : (⟨752, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 752 = i.val
              omega
            simpa only [he] using anchor0752
          ·
            have he : (⟨753, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 753 = i.val
              omega
            simpa only [he] using anchor0753
        ·
          by_cases h755 : i.val < 755
          ·
            have he : (⟨754, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 754 = i.val
              omega
            simpa only [he] using anchor0754
          ·
            have he : (⟨755, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 755 = i.val
              omega
            simpa only [he] using anchor0755
      ·
        by_cases h758 : i.val < 758
        ·
          by_cases h757 : i.val < 757
          ·
            have he : (⟨756, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 756 = i.val
              omega
            simpa only [he] using anchor0756
          ·
            have he : (⟨757, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 757 = i.val
              omega
            simpa only [he] using anchor0757
        ·
          by_cases h759 : i.val < 759
          ·
            have he : (⟨758, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 758 = i.val
              omega
            simpa only [he] using anchor0758
          ·
            have he : (⟨759, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 759 = i.val
              omega
            simpa only [he] using anchor0759
    ·
      by_cases h764 : i.val < 764
      ·
        by_cases h762 : i.val < 762
        ·
          by_cases h761 : i.val < 761
          ·
            have he : (⟨760, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 760 = i.val
              omega
            simpa only [he] using anchor0760
          ·
            have he : (⟨761, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 761 = i.val
              omega
            simpa only [he] using anchor0761
        ·
          by_cases h763 : i.val < 763
          ·
            have he : (⟨762, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 762 = i.val
              omega
            simpa only [he] using anchor0762
          ·
            have he : (⟨763, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 763 = i.val
              omega
            simpa only [he] using anchor0763
      ·
        by_cases h766 : i.val < 766
        ·
          by_cases h765 : i.val < 765
          ·
            have he : (⟨764, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 764 = i.val
              omega
            simpa only [he] using anchor0764
          ·
            have he : (⟨765, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 765 = i.val
              omega
            simpa only [he] using anchor0765
        ·
          by_cases h767 : i.val < 767
          ·
            have he : (⟨766, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 766 = i.val
              omega
            simpa only [he] using anchor0766
          ·
            have he : (⟨767, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 767 = i.val
              omega
            simpa only [he] using anchor0767

private theorem anchorGroup0024 (i : Fin 1069)
    (hlo : 768 ≤ i.val) (hhi : i.val < 800) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h784 : i.val < 784
  ·
    by_cases h776 : i.val < 776
    ·
      by_cases h772 : i.val < 772
      ·
        by_cases h770 : i.val < 770
        ·
          by_cases h769 : i.val < 769
          ·
            have he : (⟨768, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 768 = i.val
              omega
            simpa only [he] using anchor0768
          ·
            have he : (⟨769, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 769 = i.val
              omega
            simpa only [he] using anchor0769
        ·
          by_cases h771 : i.val < 771
          ·
            have he : (⟨770, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 770 = i.val
              omega
            simpa only [he] using anchor0770
          ·
            have he : (⟨771, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 771 = i.val
              omega
            simpa only [he] using anchor0771
      ·
        by_cases h774 : i.val < 774
        ·
          by_cases h773 : i.val < 773
          ·
            have he : (⟨772, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 772 = i.val
              omega
            simpa only [he] using anchor0772
          ·
            have he : (⟨773, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 773 = i.val
              omega
            simpa only [he] using anchor0773
        ·
          by_cases h775 : i.val < 775
          ·
            have he : (⟨774, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 774 = i.val
              omega
            simpa only [he] using anchor0774
          ·
            have he : (⟨775, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 775 = i.val
              omega
            simpa only [he] using anchor0775
    ·
      by_cases h780 : i.val < 780
      ·
        by_cases h778 : i.val < 778
        ·
          by_cases h777 : i.val < 777
          ·
            have he : (⟨776, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 776 = i.val
              omega
            simpa only [he] using anchor0776
          ·
            have he : (⟨777, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 777 = i.val
              omega
            simpa only [he] using anchor0777
        ·
          by_cases h779 : i.val < 779
          ·
            have he : (⟨778, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 778 = i.val
              omega
            simpa only [he] using anchor0778
          ·
            have he : (⟨779, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 779 = i.val
              omega
            simpa only [he] using anchor0779
      ·
        by_cases h782 : i.val < 782
        ·
          by_cases h781 : i.val < 781
          ·
            have he : (⟨780, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 780 = i.val
              omega
            simpa only [he] using anchor0780
          ·
            have he : (⟨781, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 781 = i.val
              omega
            simpa only [he] using anchor0781
        ·
          by_cases h783 : i.val < 783
          ·
            have he : (⟨782, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 782 = i.val
              omega
            simpa only [he] using anchor0782
          ·
            have he : (⟨783, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 783 = i.val
              omega
            simpa only [he] using anchor0783
  ·
    by_cases h792 : i.val < 792
    ·
      by_cases h788 : i.val < 788
      ·
        by_cases h786 : i.val < 786
        ·
          by_cases h785 : i.val < 785
          ·
            have he : (⟨784, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 784 = i.val
              omega
            simpa only [he] using anchor0784
          ·
            have he : (⟨785, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 785 = i.val
              omega
            simpa only [he] using anchor0785
        ·
          by_cases h787 : i.val < 787
          ·
            have he : (⟨786, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 786 = i.val
              omega
            simpa only [he] using anchor0786
          ·
            have he : (⟨787, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 787 = i.val
              omega
            simpa only [he] using anchor0787
      ·
        by_cases h790 : i.val < 790
        ·
          by_cases h789 : i.val < 789
          ·
            have he : (⟨788, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 788 = i.val
              omega
            simpa only [he] using anchor0788
          ·
            have he : (⟨789, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 789 = i.val
              omega
            simpa only [he] using anchor0789
        ·
          by_cases h791 : i.val < 791
          ·
            have he : (⟨790, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 790 = i.val
              omega
            simpa only [he] using anchor0790
          ·
            have he : (⟨791, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 791 = i.val
              omega
            simpa only [he] using anchor0791
    ·
      by_cases h796 : i.val < 796
      ·
        by_cases h794 : i.val < 794
        ·
          by_cases h793 : i.val < 793
          ·
            have he : (⟨792, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 792 = i.val
              omega
            simpa only [he] using anchor0792
          ·
            have he : (⟨793, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 793 = i.val
              omega
            simpa only [he] using anchor0793
        ·
          by_cases h795 : i.val < 795
          ·
            have he : (⟨794, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 794 = i.val
              omega
            simpa only [he] using anchor0794
          ·
            have he : (⟨795, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 795 = i.val
              omega
            simpa only [he] using anchor0795
      ·
        by_cases h798 : i.val < 798
        ·
          by_cases h797 : i.val < 797
          ·
            have he : (⟨796, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 796 = i.val
              omega
            simpa only [he] using anchor0796
          ·
            have he : (⟨797, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 797 = i.val
              omega
            simpa only [he] using anchor0797
        ·
          by_cases h799 : i.val < 799
          ·
            have he : (⟨798, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 798 = i.val
              omega
            simpa only [he] using anchor0798
          ·
            have he : (⟨799, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 799 = i.val
              omega
            simpa only [he] using anchor0799

private theorem anchorGroup0025 (i : Fin 1069)
    (hlo : 800 ≤ i.val) (hhi : i.val < 832) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h816 : i.val < 816
  ·
    by_cases h808 : i.val < 808
    ·
      by_cases h804 : i.val < 804
      ·
        by_cases h802 : i.val < 802
        ·
          by_cases h801 : i.val < 801
          ·
            have he : (⟨800, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 800 = i.val
              omega
            simpa only [he] using anchor0800
          ·
            have he : (⟨801, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 801 = i.val
              omega
            simpa only [he] using anchor0801
        ·
          by_cases h803 : i.val < 803
          ·
            have he : (⟨802, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 802 = i.val
              omega
            simpa only [he] using anchor0802
          ·
            have he : (⟨803, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 803 = i.val
              omega
            simpa only [he] using anchor0803
      ·
        by_cases h806 : i.val < 806
        ·
          by_cases h805 : i.val < 805
          ·
            have he : (⟨804, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 804 = i.val
              omega
            simpa only [he] using anchor0804
          ·
            have he : (⟨805, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 805 = i.val
              omega
            simpa only [he] using anchor0805
        ·
          by_cases h807 : i.val < 807
          ·
            have he : (⟨806, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 806 = i.val
              omega
            simpa only [he] using anchor0806
          ·
            have he : (⟨807, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 807 = i.val
              omega
            simpa only [he] using anchor0807
    ·
      by_cases h812 : i.val < 812
      ·
        by_cases h810 : i.val < 810
        ·
          by_cases h809 : i.val < 809
          ·
            have he : (⟨808, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 808 = i.val
              omega
            simpa only [he] using anchor0808
          ·
            have he : (⟨809, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 809 = i.val
              omega
            simpa only [he] using anchor0809
        ·
          by_cases h811 : i.val < 811
          ·
            have he : (⟨810, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 810 = i.val
              omega
            simpa only [he] using anchor0810
          ·
            have he : (⟨811, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 811 = i.val
              omega
            simpa only [he] using anchor0811
      ·
        by_cases h814 : i.val < 814
        ·
          by_cases h813 : i.val < 813
          ·
            have he : (⟨812, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 812 = i.val
              omega
            simpa only [he] using anchor0812
          ·
            have he : (⟨813, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 813 = i.val
              omega
            simpa only [he] using anchor0813
        ·
          by_cases h815 : i.val < 815
          ·
            have he : (⟨814, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 814 = i.val
              omega
            simpa only [he] using anchor0814
          ·
            have he : (⟨815, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 815 = i.val
              omega
            simpa only [he] using anchor0815
  ·
    by_cases h824 : i.val < 824
    ·
      by_cases h820 : i.val < 820
      ·
        by_cases h818 : i.val < 818
        ·
          by_cases h817 : i.val < 817
          ·
            have he : (⟨816, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 816 = i.val
              omega
            simpa only [he] using anchor0816
          ·
            have he : (⟨817, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 817 = i.val
              omega
            simpa only [he] using anchor0817
        ·
          by_cases h819 : i.val < 819
          ·
            have he : (⟨818, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 818 = i.val
              omega
            simpa only [he] using anchor0818
          ·
            have he : (⟨819, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 819 = i.val
              omega
            simpa only [he] using anchor0819
      ·
        by_cases h822 : i.val < 822
        ·
          by_cases h821 : i.val < 821
          ·
            have he : (⟨820, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 820 = i.val
              omega
            simpa only [he] using anchor0820
          ·
            have he : (⟨821, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 821 = i.val
              omega
            simpa only [he] using anchor0821
        ·
          by_cases h823 : i.val < 823
          ·
            have he : (⟨822, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 822 = i.val
              omega
            simpa only [he] using anchor0822
          ·
            have he : (⟨823, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 823 = i.val
              omega
            simpa only [he] using anchor0823
    ·
      by_cases h828 : i.val < 828
      ·
        by_cases h826 : i.val < 826
        ·
          by_cases h825 : i.val < 825
          ·
            have he : (⟨824, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 824 = i.val
              omega
            simpa only [he] using anchor0824
          ·
            have he : (⟨825, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 825 = i.val
              omega
            simpa only [he] using anchor0825
        ·
          by_cases h827 : i.val < 827
          ·
            have he : (⟨826, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 826 = i.val
              omega
            simpa only [he] using anchor0826
          ·
            have he : (⟨827, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 827 = i.val
              omega
            simpa only [he] using anchor0827
      ·
        by_cases h830 : i.val < 830
        ·
          by_cases h829 : i.val < 829
          ·
            have he : (⟨828, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 828 = i.val
              omega
            simpa only [he] using anchor0828
          ·
            have he : (⟨829, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 829 = i.val
              omega
            simpa only [he] using anchor0829
        ·
          by_cases h831 : i.val < 831
          ·
            have he : (⟨830, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 830 = i.val
              omega
            simpa only [he] using anchor0830
          ·
            have he : (⟨831, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 831 = i.val
              omega
            simpa only [he] using anchor0831

private theorem anchorGroup0026 (i : Fin 1069)
    (hlo : 832 ≤ i.val) (hhi : i.val < 864) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h848 : i.val < 848
  ·
    by_cases h840 : i.val < 840
    ·
      by_cases h836 : i.val < 836
      ·
        by_cases h834 : i.val < 834
        ·
          by_cases h833 : i.val < 833
          ·
            have he : (⟨832, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 832 = i.val
              omega
            simpa only [he] using anchor0832
          ·
            have he : (⟨833, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 833 = i.val
              omega
            simpa only [he] using anchor0833
        ·
          by_cases h835 : i.val < 835
          ·
            have he : (⟨834, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 834 = i.val
              omega
            simpa only [he] using anchor0834
          ·
            have he : (⟨835, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 835 = i.val
              omega
            simpa only [he] using anchor0835
      ·
        by_cases h838 : i.val < 838
        ·
          by_cases h837 : i.val < 837
          ·
            have he : (⟨836, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 836 = i.val
              omega
            simpa only [he] using anchor0836
          ·
            have he : (⟨837, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 837 = i.val
              omega
            simpa only [he] using anchor0837
        ·
          by_cases h839 : i.val < 839
          ·
            have he : (⟨838, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 838 = i.val
              omega
            simpa only [he] using anchor0838
          ·
            have he : (⟨839, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 839 = i.val
              omega
            simpa only [he] using anchor0839
    ·
      by_cases h844 : i.val < 844
      ·
        by_cases h842 : i.val < 842
        ·
          by_cases h841 : i.val < 841
          ·
            have he : (⟨840, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 840 = i.val
              omega
            simpa only [he] using anchor0840
          ·
            have he : (⟨841, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 841 = i.val
              omega
            simpa only [he] using anchor0841
        ·
          by_cases h843 : i.val < 843
          ·
            have he : (⟨842, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 842 = i.val
              omega
            simpa only [he] using anchor0842
          ·
            have he : (⟨843, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 843 = i.val
              omega
            simpa only [he] using anchor0843
      ·
        by_cases h846 : i.val < 846
        ·
          by_cases h845 : i.val < 845
          ·
            have he : (⟨844, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 844 = i.val
              omega
            simpa only [he] using anchor0844
          ·
            have he : (⟨845, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 845 = i.val
              omega
            simpa only [he] using anchor0845
        ·
          by_cases h847 : i.val < 847
          ·
            have he : (⟨846, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 846 = i.val
              omega
            simpa only [he] using anchor0846
          ·
            have he : (⟨847, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 847 = i.val
              omega
            simpa only [he] using anchor0847
  ·
    by_cases h856 : i.val < 856
    ·
      by_cases h852 : i.val < 852
      ·
        by_cases h850 : i.val < 850
        ·
          by_cases h849 : i.val < 849
          ·
            have he : (⟨848, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 848 = i.val
              omega
            simpa only [he] using anchor0848
          ·
            have he : (⟨849, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 849 = i.val
              omega
            simpa only [he] using anchor0849
        ·
          by_cases h851 : i.val < 851
          ·
            have he : (⟨850, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 850 = i.val
              omega
            simpa only [he] using anchor0850
          ·
            have he : (⟨851, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 851 = i.val
              omega
            simpa only [he] using anchor0851
      ·
        by_cases h854 : i.val < 854
        ·
          by_cases h853 : i.val < 853
          ·
            have he : (⟨852, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 852 = i.val
              omega
            simpa only [he] using anchor0852
          ·
            have he : (⟨853, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 853 = i.val
              omega
            simpa only [he] using anchor0853
        ·
          by_cases h855 : i.val < 855
          ·
            have he : (⟨854, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 854 = i.val
              omega
            simpa only [he] using anchor0854
          ·
            have he : (⟨855, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 855 = i.val
              omega
            simpa only [he] using anchor0855
    ·
      by_cases h860 : i.val < 860
      ·
        by_cases h858 : i.val < 858
        ·
          by_cases h857 : i.val < 857
          ·
            have he : (⟨856, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 856 = i.val
              omega
            simpa only [he] using anchor0856
          ·
            have he : (⟨857, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 857 = i.val
              omega
            simpa only [he] using anchor0857
        ·
          by_cases h859 : i.val < 859
          ·
            have he : (⟨858, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 858 = i.val
              omega
            simpa only [he] using anchor0858
          ·
            have he : (⟨859, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 859 = i.val
              omega
            simpa only [he] using anchor0859
      ·
        by_cases h862 : i.val < 862
        ·
          by_cases h861 : i.val < 861
          ·
            have he : (⟨860, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 860 = i.val
              omega
            simpa only [he] using anchor0860
          ·
            have he : (⟨861, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 861 = i.val
              omega
            simpa only [he] using anchor0861
        ·
          by_cases h863 : i.val < 863
          ·
            have he : (⟨862, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 862 = i.val
              omega
            simpa only [he] using anchor0862
          ·
            have he : (⟨863, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 863 = i.val
              omega
            simpa only [he] using anchor0863

private theorem anchorGroup0027 (i : Fin 1069)
    (hlo : 864 ≤ i.val) (hhi : i.val < 896) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h880 : i.val < 880
  ·
    by_cases h872 : i.val < 872
    ·
      by_cases h868 : i.val < 868
      ·
        by_cases h866 : i.val < 866
        ·
          by_cases h865 : i.val < 865
          ·
            have he : (⟨864, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 864 = i.val
              omega
            simpa only [he] using anchor0864
          ·
            have he : (⟨865, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 865 = i.val
              omega
            simpa only [he] using anchor0865
        ·
          by_cases h867 : i.val < 867
          ·
            have he : (⟨866, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 866 = i.val
              omega
            simpa only [he] using anchor0866
          ·
            have he : (⟨867, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 867 = i.val
              omega
            simpa only [he] using anchor0867
      ·
        by_cases h870 : i.val < 870
        ·
          by_cases h869 : i.val < 869
          ·
            have he : (⟨868, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 868 = i.val
              omega
            simpa only [he] using anchor0868
          ·
            have he : (⟨869, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 869 = i.val
              omega
            simpa only [he] using anchor0869
        ·
          by_cases h871 : i.val < 871
          ·
            have he : (⟨870, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 870 = i.val
              omega
            simpa only [he] using anchor0870
          ·
            have he : (⟨871, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 871 = i.val
              omega
            simpa only [he] using anchor0871
    ·
      by_cases h876 : i.val < 876
      ·
        by_cases h874 : i.val < 874
        ·
          by_cases h873 : i.val < 873
          ·
            have he : (⟨872, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 872 = i.val
              omega
            simpa only [he] using anchor0872
          ·
            have he : (⟨873, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 873 = i.val
              omega
            simpa only [he] using anchor0873
        ·
          by_cases h875 : i.val < 875
          ·
            have he : (⟨874, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 874 = i.val
              omega
            simpa only [he] using anchor0874
          ·
            have he : (⟨875, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 875 = i.val
              omega
            simpa only [he] using anchor0875
      ·
        by_cases h878 : i.val < 878
        ·
          by_cases h877 : i.val < 877
          ·
            have he : (⟨876, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 876 = i.val
              omega
            simpa only [he] using anchor0876
          ·
            have he : (⟨877, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 877 = i.val
              omega
            simpa only [he] using anchor0877
        ·
          by_cases h879 : i.val < 879
          ·
            have he : (⟨878, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 878 = i.val
              omega
            simpa only [he] using anchor0878
          ·
            have he : (⟨879, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 879 = i.val
              omega
            simpa only [he] using anchor0879
  ·
    by_cases h888 : i.val < 888
    ·
      by_cases h884 : i.val < 884
      ·
        by_cases h882 : i.val < 882
        ·
          by_cases h881 : i.val < 881
          ·
            have he : (⟨880, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 880 = i.val
              omega
            simpa only [he] using anchor0880
          ·
            have he : (⟨881, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 881 = i.val
              omega
            simpa only [he] using anchor0881
        ·
          by_cases h883 : i.val < 883
          ·
            have he : (⟨882, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 882 = i.val
              omega
            simpa only [he] using anchor0882
          ·
            have he : (⟨883, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 883 = i.val
              omega
            simpa only [he] using anchor0883
      ·
        by_cases h886 : i.val < 886
        ·
          by_cases h885 : i.val < 885
          ·
            have he : (⟨884, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 884 = i.val
              omega
            simpa only [he] using anchor0884
          ·
            have he : (⟨885, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 885 = i.val
              omega
            simpa only [he] using anchor0885
        ·
          by_cases h887 : i.val < 887
          ·
            have he : (⟨886, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 886 = i.val
              omega
            simpa only [he] using anchor0886
          ·
            have he : (⟨887, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 887 = i.val
              omega
            simpa only [he] using anchor0887
    ·
      by_cases h892 : i.val < 892
      ·
        by_cases h890 : i.val < 890
        ·
          by_cases h889 : i.val < 889
          ·
            have he : (⟨888, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 888 = i.val
              omega
            simpa only [he] using anchor0888
          ·
            have he : (⟨889, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 889 = i.val
              omega
            simpa only [he] using anchor0889
        ·
          by_cases h891 : i.val < 891
          ·
            have he : (⟨890, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 890 = i.val
              omega
            simpa only [he] using anchor0890
          ·
            have he : (⟨891, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 891 = i.val
              omega
            simpa only [he] using anchor0891
      ·
        by_cases h894 : i.val < 894
        ·
          by_cases h893 : i.val < 893
          ·
            have he : (⟨892, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 892 = i.val
              omega
            simpa only [he] using anchor0892
          ·
            have he : (⟨893, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 893 = i.val
              omega
            simpa only [he] using anchor0893
        ·
          by_cases h895 : i.val < 895
          ·
            have he : (⟨894, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 894 = i.val
              omega
            simpa only [he] using anchor0894
          ·
            have he : (⟨895, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 895 = i.val
              omega
            simpa only [he] using anchor0895

private theorem anchorGroup0028 (i : Fin 1069)
    (hlo : 896 ≤ i.val) (hhi : i.val < 928) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h912 : i.val < 912
  ·
    by_cases h904 : i.val < 904
    ·
      by_cases h900 : i.val < 900
      ·
        by_cases h898 : i.val < 898
        ·
          by_cases h897 : i.val < 897
          ·
            have he : (⟨896, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 896 = i.val
              omega
            simpa only [he] using anchor0896
          ·
            have he : (⟨897, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 897 = i.val
              omega
            simpa only [he] using anchor0897
        ·
          by_cases h899 : i.val < 899
          ·
            have he : (⟨898, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 898 = i.val
              omega
            simpa only [he] using anchor0898
          ·
            have he : (⟨899, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 899 = i.val
              omega
            simpa only [he] using anchor0899
      ·
        by_cases h902 : i.val < 902
        ·
          by_cases h901 : i.val < 901
          ·
            have he : (⟨900, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 900 = i.val
              omega
            simpa only [he] using anchor0900
          ·
            have he : (⟨901, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 901 = i.val
              omega
            simpa only [he] using anchor0901
        ·
          by_cases h903 : i.val < 903
          ·
            have he : (⟨902, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 902 = i.val
              omega
            simpa only [he] using anchor0902
          ·
            have he : (⟨903, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 903 = i.val
              omega
            simpa only [he] using anchor0903
    ·
      by_cases h908 : i.val < 908
      ·
        by_cases h906 : i.val < 906
        ·
          by_cases h905 : i.val < 905
          ·
            have he : (⟨904, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 904 = i.val
              omega
            simpa only [he] using anchor0904
          ·
            have he : (⟨905, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 905 = i.val
              omega
            simpa only [he] using anchor0905
        ·
          by_cases h907 : i.val < 907
          ·
            have he : (⟨906, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 906 = i.val
              omega
            simpa only [he] using anchor0906
          ·
            have he : (⟨907, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 907 = i.val
              omega
            simpa only [he] using anchor0907
      ·
        by_cases h910 : i.val < 910
        ·
          by_cases h909 : i.val < 909
          ·
            have he : (⟨908, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 908 = i.val
              omega
            simpa only [he] using anchor0908
          ·
            have he : (⟨909, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 909 = i.val
              omega
            simpa only [he] using anchor0909
        ·
          by_cases h911 : i.val < 911
          ·
            have he : (⟨910, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 910 = i.val
              omega
            simpa only [he] using anchor0910
          ·
            have he : (⟨911, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 911 = i.val
              omega
            simpa only [he] using anchor0911
  ·
    by_cases h920 : i.val < 920
    ·
      by_cases h916 : i.val < 916
      ·
        by_cases h914 : i.val < 914
        ·
          by_cases h913 : i.val < 913
          ·
            have he : (⟨912, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 912 = i.val
              omega
            simpa only [he] using anchor0912
          ·
            have he : (⟨913, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 913 = i.val
              omega
            simpa only [he] using anchor0913
        ·
          by_cases h915 : i.val < 915
          ·
            have he : (⟨914, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 914 = i.val
              omega
            simpa only [he] using anchor0914
          ·
            have he : (⟨915, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 915 = i.val
              omega
            simpa only [he] using anchor0915
      ·
        by_cases h918 : i.val < 918
        ·
          by_cases h917 : i.val < 917
          ·
            have he : (⟨916, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 916 = i.val
              omega
            simpa only [he] using anchor0916
          ·
            have he : (⟨917, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 917 = i.val
              omega
            simpa only [he] using anchor0917
        ·
          by_cases h919 : i.val < 919
          ·
            have he : (⟨918, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 918 = i.val
              omega
            simpa only [he] using anchor0918
          ·
            have he : (⟨919, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 919 = i.val
              omega
            simpa only [he] using anchor0919
    ·
      by_cases h924 : i.val < 924
      ·
        by_cases h922 : i.val < 922
        ·
          by_cases h921 : i.val < 921
          ·
            have he : (⟨920, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 920 = i.val
              omega
            simpa only [he] using anchor0920
          ·
            have he : (⟨921, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 921 = i.val
              omega
            simpa only [he] using anchor0921
        ·
          by_cases h923 : i.val < 923
          ·
            have he : (⟨922, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 922 = i.val
              omega
            simpa only [he] using anchor0922
          ·
            have he : (⟨923, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 923 = i.val
              omega
            simpa only [he] using anchor0923
      ·
        by_cases h926 : i.val < 926
        ·
          by_cases h925 : i.val < 925
          ·
            have he : (⟨924, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 924 = i.val
              omega
            simpa only [he] using anchor0924
          ·
            have he : (⟨925, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 925 = i.val
              omega
            simpa only [he] using anchor0925
        ·
          by_cases h927 : i.val < 927
          ·
            have he : (⟨926, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 926 = i.val
              omega
            simpa only [he] using anchor0926
          ·
            have he : (⟨927, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 927 = i.val
              omega
            simpa only [he] using anchor0927

private theorem anchorGroup0029 (i : Fin 1069)
    (hlo : 928 ≤ i.val) (hhi : i.val < 960) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h944 : i.val < 944
  ·
    by_cases h936 : i.val < 936
    ·
      by_cases h932 : i.val < 932
      ·
        by_cases h930 : i.val < 930
        ·
          by_cases h929 : i.val < 929
          ·
            have he : (⟨928, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 928 = i.val
              omega
            simpa only [he] using anchor0928
          ·
            have he : (⟨929, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 929 = i.val
              omega
            simpa only [he] using anchor0929
        ·
          by_cases h931 : i.val < 931
          ·
            have he : (⟨930, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 930 = i.val
              omega
            simpa only [he] using anchor0930
          ·
            have he : (⟨931, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 931 = i.val
              omega
            simpa only [he] using anchor0931
      ·
        by_cases h934 : i.val < 934
        ·
          by_cases h933 : i.val < 933
          ·
            have he : (⟨932, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 932 = i.val
              omega
            simpa only [he] using anchor0932
          ·
            have he : (⟨933, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 933 = i.val
              omega
            simpa only [he] using anchor0933
        ·
          by_cases h935 : i.val < 935
          ·
            have he : (⟨934, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 934 = i.val
              omega
            simpa only [he] using anchor0934
          ·
            have he : (⟨935, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 935 = i.val
              omega
            simpa only [he] using anchor0935
    ·
      by_cases h940 : i.val < 940
      ·
        by_cases h938 : i.val < 938
        ·
          by_cases h937 : i.val < 937
          ·
            have he : (⟨936, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 936 = i.val
              omega
            simpa only [he] using anchor0936
          ·
            have he : (⟨937, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 937 = i.val
              omega
            simpa only [he] using anchor0937
        ·
          by_cases h939 : i.val < 939
          ·
            have he : (⟨938, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 938 = i.val
              omega
            simpa only [he] using anchor0938
          ·
            have he : (⟨939, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 939 = i.val
              omega
            simpa only [he] using anchor0939
      ·
        by_cases h942 : i.val < 942
        ·
          by_cases h941 : i.val < 941
          ·
            have he : (⟨940, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 940 = i.val
              omega
            simpa only [he] using anchor0940
          ·
            have he : (⟨941, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 941 = i.val
              omega
            simpa only [he] using anchor0941
        ·
          by_cases h943 : i.val < 943
          ·
            have he : (⟨942, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 942 = i.val
              omega
            simpa only [he] using anchor0942
          ·
            have he : (⟨943, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 943 = i.val
              omega
            simpa only [he] using anchor0943
  ·
    by_cases h952 : i.val < 952
    ·
      by_cases h948 : i.val < 948
      ·
        by_cases h946 : i.val < 946
        ·
          by_cases h945 : i.val < 945
          ·
            have he : (⟨944, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 944 = i.val
              omega
            simpa only [he] using anchor0944
          ·
            have he : (⟨945, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 945 = i.val
              omega
            simpa only [he] using anchor0945
        ·
          by_cases h947 : i.val < 947
          ·
            have he : (⟨946, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 946 = i.val
              omega
            simpa only [he] using anchor0946
          ·
            have he : (⟨947, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 947 = i.val
              omega
            simpa only [he] using anchor0947
      ·
        by_cases h950 : i.val < 950
        ·
          by_cases h949 : i.val < 949
          ·
            have he : (⟨948, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 948 = i.val
              omega
            simpa only [he] using anchor0948
          ·
            have he : (⟨949, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 949 = i.val
              omega
            simpa only [he] using anchor0949
        ·
          by_cases h951 : i.val < 951
          ·
            have he : (⟨950, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 950 = i.val
              omega
            simpa only [he] using anchor0950
          ·
            have he : (⟨951, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 951 = i.val
              omega
            simpa only [he] using anchor0951
    ·
      by_cases h956 : i.val < 956
      ·
        by_cases h954 : i.val < 954
        ·
          by_cases h953 : i.val < 953
          ·
            have he : (⟨952, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 952 = i.val
              omega
            simpa only [he] using anchor0952
          ·
            have he : (⟨953, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 953 = i.val
              omega
            simpa only [he] using anchor0953
        ·
          by_cases h955 : i.val < 955
          ·
            have he : (⟨954, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 954 = i.val
              omega
            simpa only [he] using anchor0954
          ·
            have he : (⟨955, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 955 = i.val
              omega
            simpa only [he] using anchor0955
      ·
        by_cases h958 : i.val < 958
        ·
          by_cases h957 : i.val < 957
          ·
            have he : (⟨956, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 956 = i.val
              omega
            simpa only [he] using anchor0956
          ·
            have he : (⟨957, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 957 = i.val
              omega
            simpa only [he] using anchor0957
        ·
          by_cases h959 : i.val < 959
          ·
            have he : (⟨958, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 958 = i.val
              omega
            simpa only [he] using anchor0958
          ·
            have he : (⟨959, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 959 = i.val
              omega
            simpa only [he] using anchor0959

private theorem anchorGroup0030 (i : Fin 1069)
    (hlo : 960 ≤ i.val) (hhi : i.val < 992) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h976 : i.val < 976
  ·
    by_cases h968 : i.val < 968
    ·
      by_cases h964 : i.val < 964
      ·
        by_cases h962 : i.val < 962
        ·
          by_cases h961 : i.val < 961
          ·
            have he : (⟨960, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 960 = i.val
              omega
            simpa only [he] using anchor0960
          ·
            have he : (⟨961, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 961 = i.val
              omega
            simpa only [he] using anchor0961
        ·
          by_cases h963 : i.val < 963
          ·
            have he : (⟨962, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 962 = i.val
              omega
            simpa only [he] using anchor0962
          ·
            have he : (⟨963, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 963 = i.val
              omega
            simpa only [he] using anchor0963
      ·
        by_cases h966 : i.val < 966
        ·
          by_cases h965 : i.val < 965
          ·
            have he : (⟨964, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 964 = i.val
              omega
            simpa only [he] using anchor0964
          ·
            have he : (⟨965, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 965 = i.val
              omega
            simpa only [he] using anchor0965
        ·
          by_cases h967 : i.val < 967
          ·
            have he : (⟨966, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 966 = i.val
              omega
            simpa only [he] using anchor0966
          ·
            have he : (⟨967, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 967 = i.val
              omega
            simpa only [he] using anchor0967
    ·
      by_cases h972 : i.val < 972
      ·
        by_cases h970 : i.val < 970
        ·
          by_cases h969 : i.val < 969
          ·
            have he : (⟨968, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 968 = i.val
              omega
            simpa only [he] using anchor0968
          ·
            have he : (⟨969, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 969 = i.val
              omega
            simpa only [he] using anchor0969
        ·
          by_cases h971 : i.val < 971
          ·
            have he : (⟨970, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 970 = i.val
              omega
            simpa only [he] using anchor0970
          ·
            have he : (⟨971, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 971 = i.val
              omega
            simpa only [he] using anchor0971
      ·
        by_cases h974 : i.val < 974
        ·
          by_cases h973 : i.val < 973
          ·
            have he : (⟨972, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 972 = i.val
              omega
            simpa only [he] using anchor0972
          ·
            have he : (⟨973, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 973 = i.val
              omega
            simpa only [he] using anchor0973
        ·
          by_cases h975 : i.val < 975
          ·
            have he : (⟨974, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 974 = i.val
              omega
            simpa only [he] using anchor0974
          ·
            have he : (⟨975, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 975 = i.val
              omega
            simpa only [he] using anchor0975
  ·
    by_cases h984 : i.val < 984
    ·
      by_cases h980 : i.val < 980
      ·
        by_cases h978 : i.val < 978
        ·
          by_cases h977 : i.val < 977
          ·
            have he : (⟨976, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 976 = i.val
              omega
            simpa only [he] using anchor0976
          ·
            have he : (⟨977, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 977 = i.val
              omega
            simpa only [he] using anchor0977
        ·
          by_cases h979 : i.val < 979
          ·
            have he : (⟨978, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 978 = i.val
              omega
            simpa only [he] using anchor0978
          ·
            have he : (⟨979, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 979 = i.val
              omega
            simpa only [he] using anchor0979
      ·
        by_cases h982 : i.val < 982
        ·
          by_cases h981 : i.val < 981
          ·
            have he : (⟨980, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 980 = i.val
              omega
            simpa only [he] using anchor0980
          ·
            have he : (⟨981, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 981 = i.val
              omega
            simpa only [he] using anchor0981
        ·
          by_cases h983 : i.val < 983
          ·
            have he : (⟨982, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 982 = i.val
              omega
            simpa only [he] using anchor0982
          ·
            have he : (⟨983, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 983 = i.val
              omega
            simpa only [he] using anchor0983
    ·
      by_cases h988 : i.val < 988
      ·
        by_cases h986 : i.val < 986
        ·
          by_cases h985 : i.val < 985
          ·
            have he : (⟨984, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 984 = i.val
              omega
            simpa only [he] using anchor0984
          ·
            have he : (⟨985, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 985 = i.val
              omega
            simpa only [he] using anchor0985
        ·
          by_cases h987 : i.val < 987
          ·
            have he : (⟨986, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 986 = i.val
              omega
            simpa only [he] using anchor0986
          ·
            have he : (⟨987, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 987 = i.val
              omega
            simpa only [he] using anchor0987
      ·
        by_cases h990 : i.val < 990
        ·
          by_cases h989 : i.val < 989
          ·
            have he : (⟨988, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 988 = i.val
              omega
            simpa only [he] using anchor0988
          ·
            have he : (⟨989, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 989 = i.val
              omega
            simpa only [he] using anchor0989
        ·
          by_cases h991 : i.val < 991
          ·
            have he : (⟨990, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 990 = i.val
              omega
            simpa only [he] using anchor0990
          ·
            have he : (⟨991, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 991 = i.val
              omega
            simpa only [he] using anchor0991

private theorem anchorGroup0031 (i : Fin 1069)
    (hlo : 992 ≤ i.val) (hhi : i.val < 1024) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h1008 : i.val < 1008
  ·
    by_cases h1000 : i.val < 1000
    ·
      by_cases h996 : i.val < 996
      ·
        by_cases h994 : i.val < 994
        ·
          by_cases h993 : i.val < 993
          ·
            have he : (⟨992, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 992 = i.val
              omega
            simpa only [he] using anchor0992
          ·
            have he : (⟨993, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 993 = i.val
              omega
            simpa only [he] using anchor0993
        ·
          by_cases h995 : i.val < 995
          ·
            have he : (⟨994, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 994 = i.val
              omega
            simpa only [he] using anchor0994
          ·
            have he : (⟨995, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 995 = i.val
              omega
            simpa only [he] using anchor0995
      ·
        by_cases h998 : i.val < 998
        ·
          by_cases h997 : i.val < 997
          ·
            have he : (⟨996, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 996 = i.val
              omega
            simpa only [he] using anchor0996
          ·
            have he : (⟨997, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 997 = i.val
              omega
            simpa only [he] using anchor0997
        ·
          by_cases h999 : i.val < 999
          ·
            have he : (⟨998, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 998 = i.val
              omega
            simpa only [he] using anchor0998
          ·
            have he : (⟨999, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 999 = i.val
              omega
            simpa only [he] using anchor0999
    ·
      by_cases h1004 : i.val < 1004
      ·
        by_cases h1002 : i.val < 1002
        ·
          by_cases h1001 : i.val < 1001
          ·
            have he : (⟨1000, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1000 = i.val
              omega
            simpa only [he] using anchor1000
          ·
            have he : (⟨1001, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1001 = i.val
              omega
            simpa only [he] using anchor1001
        ·
          by_cases h1003 : i.val < 1003
          ·
            have he : (⟨1002, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1002 = i.val
              omega
            simpa only [he] using anchor1002
          ·
            have he : (⟨1003, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1003 = i.val
              omega
            simpa only [he] using anchor1003
      ·
        by_cases h1006 : i.val < 1006
        ·
          by_cases h1005 : i.val < 1005
          ·
            have he : (⟨1004, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1004 = i.val
              omega
            simpa only [he] using anchor1004
          ·
            have he : (⟨1005, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1005 = i.val
              omega
            simpa only [he] using anchor1005
        ·
          by_cases h1007 : i.val < 1007
          ·
            have he : (⟨1006, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1006 = i.val
              omega
            simpa only [he] using anchor1006
          ·
            have he : (⟨1007, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1007 = i.val
              omega
            simpa only [he] using anchor1007
  ·
    by_cases h1016 : i.val < 1016
    ·
      by_cases h1012 : i.val < 1012
      ·
        by_cases h1010 : i.val < 1010
        ·
          by_cases h1009 : i.val < 1009
          ·
            have he : (⟨1008, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1008 = i.val
              omega
            simpa only [he] using anchor1008
          ·
            have he : (⟨1009, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1009 = i.val
              omega
            simpa only [he] using anchor1009
        ·
          by_cases h1011 : i.val < 1011
          ·
            have he : (⟨1010, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1010 = i.val
              omega
            simpa only [he] using anchor1010
          ·
            have he : (⟨1011, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1011 = i.val
              omega
            simpa only [he] using anchor1011
      ·
        by_cases h1014 : i.val < 1014
        ·
          by_cases h1013 : i.val < 1013
          ·
            have he : (⟨1012, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1012 = i.val
              omega
            simpa only [he] using anchor1012
          ·
            have he : (⟨1013, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1013 = i.val
              omega
            simpa only [he] using anchor1013
        ·
          by_cases h1015 : i.val < 1015
          ·
            have he : (⟨1014, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1014 = i.val
              omega
            simpa only [he] using anchor1014
          ·
            have he : (⟨1015, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1015 = i.val
              omega
            simpa only [he] using anchor1015
    ·
      by_cases h1020 : i.val < 1020
      ·
        by_cases h1018 : i.val < 1018
        ·
          by_cases h1017 : i.val < 1017
          ·
            have he : (⟨1016, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1016 = i.val
              omega
            simpa only [he] using anchor1016
          ·
            have he : (⟨1017, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1017 = i.val
              omega
            simpa only [he] using anchor1017
        ·
          by_cases h1019 : i.val < 1019
          ·
            have he : (⟨1018, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1018 = i.val
              omega
            simpa only [he] using anchor1018
          ·
            have he : (⟨1019, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1019 = i.val
              omega
            simpa only [he] using anchor1019
      ·
        by_cases h1022 : i.val < 1022
        ·
          by_cases h1021 : i.val < 1021
          ·
            have he : (⟨1020, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1020 = i.val
              omega
            simpa only [he] using anchor1020
          ·
            have he : (⟨1021, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1021 = i.val
              omega
            simpa only [he] using anchor1021
        ·
          by_cases h1023 : i.val < 1023
          ·
            have he : (⟨1022, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1022 = i.val
              omega
            simpa only [he] using anchor1022
          ·
            have he : (⟨1023, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1023 = i.val
              omega
            simpa only [he] using anchor1023

private theorem anchorGroup0032 (i : Fin 1069)
    (hlo : 1024 ≤ i.val) (hhi : i.val < 1056) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h1040 : i.val < 1040
  ·
    by_cases h1032 : i.val < 1032
    ·
      by_cases h1028 : i.val < 1028
      ·
        by_cases h1026 : i.val < 1026
        ·
          by_cases h1025 : i.val < 1025
          ·
            have he : (⟨1024, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1024 = i.val
              omega
            simpa only [he] using anchor1024
          ·
            have he : (⟨1025, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1025 = i.val
              omega
            simpa only [he] using anchor1025
        ·
          by_cases h1027 : i.val < 1027
          ·
            have he : (⟨1026, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1026 = i.val
              omega
            simpa only [he] using anchor1026
          ·
            have he : (⟨1027, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1027 = i.val
              omega
            simpa only [he] using anchor1027
      ·
        by_cases h1030 : i.val < 1030
        ·
          by_cases h1029 : i.val < 1029
          ·
            have he : (⟨1028, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1028 = i.val
              omega
            simpa only [he] using anchor1028
          ·
            have he : (⟨1029, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1029 = i.val
              omega
            simpa only [he] using anchor1029
        ·
          by_cases h1031 : i.val < 1031
          ·
            have he : (⟨1030, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1030 = i.val
              omega
            simpa only [he] using anchor1030
          ·
            have he : (⟨1031, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1031 = i.val
              omega
            simpa only [he] using anchor1031
    ·
      by_cases h1036 : i.val < 1036
      ·
        by_cases h1034 : i.val < 1034
        ·
          by_cases h1033 : i.val < 1033
          ·
            have he : (⟨1032, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1032 = i.val
              omega
            simpa only [he] using anchor1032
          ·
            have he : (⟨1033, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1033 = i.val
              omega
            simpa only [he] using anchor1033
        ·
          by_cases h1035 : i.val < 1035
          ·
            have he : (⟨1034, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1034 = i.val
              omega
            simpa only [he] using anchor1034
          ·
            have he : (⟨1035, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1035 = i.val
              omega
            simpa only [he] using anchor1035
      ·
        by_cases h1038 : i.val < 1038
        ·
          by_cases h1037 : i.val < 1037
          ·
            have he : (⟨1036, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1036 = i.val
              omega
            simpa only [he] using anchor1036
          ·
            have he : (⟨1037, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1037 = i.val
              omega
            simpa only [he] using anchor1037
        ·
          by_cases h1039 : i.val < 1039
          ·
            have he : (⟨1038, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1038 = i.val
              omega
            simpa only [he] using anchor1038
          ·
            have he : (⟨1039, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1039 = i.val
              omega
            simpa only [he] using anchor1039
  ·
    by_cases h1048 : i.val < 1048
    ·
      by_cases h1044 : i.val < 1044
      ·
        by_cases h1042 : i.val < 1042
        ·
          by_cases h1041 : i.val < 1041
          ·
            have he : (⟨1040, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1040 = i.val
              omega
            simpa only [he] using anchor1040
          ·
            have he : (⟨1041, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1041 = i.val
              omega
            simpa only [he] using anchor1041
        ·
          by_cases h1043 : i.val < 1043
          ·
            have he : (⟨1042, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1042 = i.val
              omega
            simpa only [he] using anchor1042
          ·
            have he : (⟨1043, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1043 = i.val
              omega
            simpa only [he] using anchor1043
      ·
        by_cases h1046 : i.val < 1046
        ·
          by_cases h1045 : i.val < 1045
          ·
            have he : (⟨1044, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1044 = i.val
              omega
            simpa only [he] using anchor1044
          ·
            have he : (⟨1045, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1045 = i.val
              omega
            simpa only [he] using anchor1045
        ·
          by_cases h1047 : i.val < 1047
          ·
            have he : (⟨1046, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1046 = i.val
              omega
            simpa only [he] using anchor1046
          ·
            have he : (⟨1047, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1047 = i.val
              omega
            simpa only [he] using anchor1047
    ·
      by_cases h1052 : i.val < 1052
      ·
        by_cases h1050 : i.val < 1050
        ·
          by_cases h1049 : i.val < 1049
          ·
            have he : (⟨1048, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1048 = i.val
              omega
            simpa only [he] using anchor1048
          ·
            have he : (⟨1049, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1049 = i.val
              omega
            simpa only [he] using anchor1049
        ·
          by_cases h1051 : i.val < 1051
          ·
            have he : (⟨1050, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1050 = i.val
              omega
            simpa only [he] using anchor1050
          ·
            have he : (⟨1051, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1051 = i.val
              omega
            simpa only [he] using anchor1051
      ·
        by_cases h1054 : i.val < 1054
        ·
          by_cases h1053 : i.val < 1053
          ·
            have he : (⟨1052, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1052 = i.val
              omega
            simpa only [he] using anchor1052
          ·
            have he : (⟨1053, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1053 = i.val
              omega
            simpa only [he] using anchor1053
        ·
          by_cases h1055 : i.val < 1055
          ·
            have he : (⟨1054, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1054 = i.val
              omega
            simpa only [he] using anchor1054
          ·
            have he : (⟨1055, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1055 = i.val
              omega
            simpa only [he] using anchor1055

private theorem anchorGroup0033 (i : Fin 1069)
    (hlo : 1056 ≤ i.val) (hhi : i.val < 1069) :
    faceAnchor i ∈ faceMask i := by
  have hi_bound := i.isLt
  by_cases h1062 : i.val < 1062
  ·
    by_cases h1059 : i.val < 1059
    ·
      by_cases h1057 : i.val < 1057
      ·
        have he : (⟨1056, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1056 = i.val
          omega
        simpa only [he] using anchor1056
      ·
        by_cases h1058 : i.val < 1058
        ·
          have he : (⟨1057, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1057 = i.val
            omega
          simpa only [he] using anchor1057
        ·
          have he : (⟨1058, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1058 = i.val
            omega
          simpa only [he] using anchor1058
    ·
      by_cases h1060 : i.val < 1060
      ·
        have he : (⟨1059, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1059 = i.val
          omega
        simpa only [he] using anchor1059
      ·
        by_cases h1061 : i.val < 1061
        ·
          have he : (⟨1060, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1060 = i.val
            omega
          simpa only [he] using anchor1060
        ·
          have he : (⟨1061, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1061 = i.val
            omega
          simpa only [he] using anchor1061
  ·
    by_cases h1065 : i.val < 1065
    ·
      by_cases h1063 : i.val < 1063
      ·
        have he : (⟨1062, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1062 = i.val
          omega
        simpa only [he] using anchor1062
      ·
        by_cases h1064 : i.val < 1064
        ·
          have he : (⟨1063, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1063 = i.val
            omega
          simpa only [he] using anchor1063
        ·
          have he : (⟨1064, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1064 = i.val
            omega
          simpa only [he] using anchor1064
    ·
      by_cases h1067 : i.val < 1067
      ·
        by_cases h1066 : i.val < 1066
        ·
          have he : (⟨1065, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1065 = i.val
            omega
          simpa only [he] using anchor1065
        ·
          have he : (⟨1066, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1066 = i.val
            omega
          simpa only [he] using anchor1066
      ·
        by_cases h1068 : i.val < 1068
        ·
          have he : (⟨1067, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1067 = i.val
            omega
          simpa only [he] using anchor1067
        ·
          have he : (⟨1068, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1068 = i.val
            omega
          simpa only [he] using anchor1068

theorem faceAnchor_mem : ∀ i : Fin 1069,
    faceAnchor i ∈ faceMask i := by
  intro i
  have hi_bound := i.isLt
  by_cases h544 : i.val < 544
  ·
    by_cases h256 : i.val < 256
    ·
      by_cases h128 : i.val < 128
      ·
        by_cases h64 : i.val < 64
        ·
          by_cases h32 : i.val < 32
          ·
            exact anchorGroup0000 i (by omega) (by omega)
          ·
            exact anchorGroup0001 i (by omega) (by omega)
        ·
          by_cases h96 : i.val < 96
          ·
            exact anchorGroup0002 i (by omega) (by omega)
          ·
            exact anchorGroup0003 i (by omega) (by omega)
      ·
        by_cases h192 : i.val < 192
        ·
          by_cases h160 : i.val < 160
          ·
            exact anchorGroup0004 i (by omega) (by omega)
          ·
            exact anchorGroup0005 i (by omega) (by omega)
        ·
          by_cases h224 : i.val < 224
          ·
            exact anchorGroup0006 i (by omega) (by omega)
          ·
            exact anchorGroup0007 i (by omega) (by omega)
    ·
      by_cases h384 : i.val < 384
      ·
        by_cases h320 : i.val < 320
        ·
          by_cases h288 : i.val < 288
          ·
            exact anchorGroup0008 i (by omega) (by omega)
          ·
            exact anchorGroup0009 i (by omega) (by omega)
        ·
          by_cases h352 : i.val < 352
          ·
            exact anchorGroup0010 i (by omega) (by omega)
          ·
            exact anchorGroup0011 i (by omega) (by omega)
      ·
        by_cases h448 : i.val < 448
        ·
          by_cases h416 : i.val < 416
          ·
            exact anchorGroup0012 i (by omega) (by omega)
          ·
            exact anchorGroup0013 i (by omega) (by omega)
        ·
          by_cases h480 : i.val < 480
          ·
            exact anchorGroup0014 i (by omega) (by omega)
          ·
            by_cases h512 : i.val < 512
            ·
              exact anchorGroup0015 i (by omega) (by omega)
            ·
              exact anchorGroup0016 i (by omega) (by omega)
  ·
    by_cases h800 : i.val < 800
    ·
      by_cases h672 : i.val < 672
      ·
        by_cases h608 : i.val < 608
        ·
          by_cases h576 : i.val < 576
          ·
            exact anchorGroup0017 i (by omega) (by omega)
          ·
            exact anchorGroup0018 i (by omega) (by omega)
        ·
          by_cases h640 : i.val < 640
          ·
            exact anchorGroup0019 i (by omega) (by omega)
          ·
            exact anchorGroup0020 i (by omega) (by omega)
      ·
        by_cases h736 : i.val < 736
        ·
          by_cases h704 : i.val < 704
          ·
            exact anchorGroup0021 i (by omega) (by omega)
          ·
            exact anchorGroup0022 i (by omega) (by omega)
        ·
          by_cases h768 : i.val < 768
          ·
            exact anchorGroup0023 i (by omega) (by omega)
          ·
            exact anchorGroup0024 i (by omega) (by omega)
    ·
      by_cases h928 : i.val < 928
      ·
        by_cases h864 : i.val < 864
        ·
          by_cases h832 : i.val < 832
          ·
            exact anchorGroup0025 i (by omega) (by omega)
          ·
            exact anchorGroup0026 i (by omega) (by omega)
        ·
          by_cases h896 : i.val < 896
          ·
            exact anchorGroup0027 i (by omega) (by omega)
          ·
            exact anchorGroup0028 i (by omega) (by omega)
      ·
        by_cases h992 : i.val < 992
        ·
          by_cases h960 : i.val < 960
          ·
            exact anchorGroup0029 i (by omega) (by omega)
          ·
            exact anchorGroup0030 i (by omega) (by omega)
        ·
          by_cases h1024 : i.val < 1024
          ·
            exact anchorGroup0031 i (by omega) (by omega)
          ·
            by_cases h1056 : i.val < 1056
            ·
              exact anchorGroup0032 i (by omega) (by omega)
            ·
              exact anchorGroup0033 i (by omega) (by omega)

end CubicalIndecomposability
