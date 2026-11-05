import cubical_indecomposability.face_data_checks.anchors
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Fin
import Lean.Elab.Tactic.Omega

/-!
# Sparse, exact finite certificates

The proposed finite data are checked by ordinary Lean kernel reduction.
The generic proof then recovers the full universally quantified statement.
Exhaustive case splits have at most 32 leaves per declaration.

Regenerate with `python3 scripts/sparse_supports_lower.py`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option autoImplicit false

namespace CubicalIndecomposability

/- A face of rank one less than `i` contained in `i` has its chosen
vertex in `i`. Thus these small buckets contain every possible lower face.
They may contain extra entries: the final rank/containment filter removes
those entries, and the equality certificate checks the resulting table. -/

private def anchoredFaces0 : ℕ → Finset (Fin 1069) :=
fun index =>
    if index < 72 then
      if index < 36 then
        if index < 18 then
          if index < 9 then
            if index < 4 then
              if index < 2 then
                if index < 1 then
                  {0}
                else
                  {1}
              else
                if index < 3 then
                  {2}
                else
                  {3}
            else
              if index < 6 then
                if index < 5 then
                  {4}
                else
                  {5}
              else
                if index < 7 then
                  {6}
                else
                  if index < 8 then
                    {7}
                  else
                    {8}
          else
            if index < 13 then
              if index < 11 then
                if index < 10 then
                  {9}
                else
                  {10}
              else
                if index < 12 then
                  {11}
                else
                  {12}
            else
              if index < 15 then
                if index < 14 then
                  {13}
                else
                  {14}
              else
                if index < 16 then
                  {15}
                else
                  if index < 17 then
                    {16}
                  else
                    {17}
        else
          if index < 27 then
            if index < 22 then
              if index < 20 then
                if index < 19 then
                  {18}
                else
                  {19}
              else
                if index < 21 then
                  {20}
                else
                  {21}
            else
              if index < 24 then
                if index < 23 then
                  {22}
                else
                  {23}
              else
                if index < 25 then
                  {24}
                else
                  if index < 26 then
                    {25}
                  else
                    {26}
          else
            if index < 31 then
              if index < 29 then
                if index < 28 then
                  {27}
                else
                  {28}
              else
                if index < 30 then
                  {29}
                else
                  {30}
            else
              if index < 33 then
                if index < 32 then
                  {31}
                else
                  {32}
              else
                if index < 34 then
                  {33}
                else
                  if index < 35 then
                    {34}
                  else
                    {35}
      else
        if index < 54 then
          if index < 45 then
            if index < 40 then
              if index < 38 then
                if index < 37 then
                  {36}
                else
                  {37}
              else
                if index < 39 then
                  {38}
                else
                  {39}
            else
              if index < 42 then
                if index < 41 then
                  {40}
                else
                  {41}
              else
                if index < 43 then
                  {42}
                else
                  if index < 44 then
                    {43}
                  else
                    {44}
          else
            if index < 49 then
              if index < 47 then
                if index < 46 then
                  {45}
                else
                  {46}
              else
                if index < 48 then
                  {47}
                else
                  {48}
            else
              if index < 51 then
                if index < 50 then
                  {49}
                else
                  {50}
              else
                if index < 52 then
                  {51}
                else
                  if index < 53 then
                    {52}
                  else
                    {53}
        else
          if index < 63 then
            if index < 58 then
              if index < 56 then
                if index < 55 then
                  {54}
                else
                  {55}
              else
                if index < 57 then
                  {56}
                else
                  {57}
            else
              if index < 60 then
                if index < 59 then
                  {58}
                else
                  {59}
              else
                if index < 61 then
                  {60}
                else
                  if index < 62 then
                    {61}
                  else
                    {62}
          else
            if index < 67 then
              if index < 65 then
                if index < 64 then
                  {63}
                else
                  {64}
              else
                if index < 66 then
                  {65}
                else
                  {66}
            else
              if index < 69 then
                if index < 68 then
                  {67}
                else
                  {68}
              else
                if index < 70 then
                  {69}
                else
                  if index < 71 then
                    {70}
                  else
                    {71}
    else
      if index < 108 then
        if index < 90 then
          if index < 81 then
            if index < 76 then
              if index < 74 then
                if index < 73 then
                  {72}
                else
                  {73}
              else
                if index < 75 then
                  {74}
                else
                  {75}
            else
              if index < 78 then
                if index < 77 then
                  {76}
                else
                  {77}
              else
                if index < 79 then
                  {78}
                else
                  if index < 80 then
                    {79}
                  else
                    {80}
          else
            if index < 85 then
              if index < 83 then
                if index < 82 then
                  {81}
                else
                  {82}
              else
                if index < 84 then
                  {83}
                else
                  {84}
            else
              if index < 87 then
                if index < 86 then
                  {85}
                else
                  {86}
              else
                if index < 88 then
                  {87}
                else
                  if index < 89 then
                    {88}
                  else
                    {89}
        else
          if index < 99 then
            if index < 94 then
              if index < 92 then
                if index < 91 then
                  {90}
                else
                  {91}
              else
                if index < 93 then
                  {92}
                else
                  {93}
            else
              if index < 96 then
                if index < 95 then
                  {94}
                else
                  {95}
              else
                if index < 97 then
                  {96}
                else
                  if index < 98 then
                    {97}
                  else
                    {98}
          else
            if index < 103 then
              if index < 101 then
                if index < 100 then
                  {99}
                else
                  {100}
              else
                if index < 102 then
                  {101}
                else
                  {102}
            else
              if index < 105 then
                if index < 104 then
                  {103}
                else
                  {104}
              else
                if index < 106 then
                  {105}
                else
                  if index < 107 then
                    {106}
                  else
                    {107}
      else
        if index < 126 then
          if index < 117 then
            if index < 112 then
              if index < 110 then
                if index < 109 then
                  {108}
                else
                  {109}
              else
                if index < 111 then
                  {110}
                else
                  {111}
            else
              if index < 114 then
                if index < 113 then
                  {112}
                else
                  {113}
              else
                if index < 115 then
                  {114}
                else
                  if index < 116 then
                    {115}
                  else
                    {116}
          else
            if index < 121 then
              if index < 119 then
                if index < 118 then
                  {117}
                else
                  {118}
              else
                if index < 120 then
                  {119}
                else
                  {120}
            else
              if index < 123 then
                if index < 122 then
                  {121}
                else
                  {122}
              else
                if index < 124 then
                  {123}
                else
                  if index < 125 then
                    {124}
                  else
                    {125}
        else
          if index < 135 then
            if index < 130 then
              if index < 128 then
                if index < 127 then
                  {126}
                else
                  {127}
              else
                if index < 129 then
                  {128}
                else
                  {129}
            else
              if index < 132 then
                if index < 131 then
                  {130}
                else
                  {131}
              else
                if index < 133 then
                  {132}
                else
                  if index < 134 then
                    {133}
                  else
                    {134}
          else
            if index < 139 then
              if index < 137 then
                if index < 136 then
                  {135}
                else
                  {136}
              else
                if index < 138 then
                  {137}
                else
                  {138}
            else
              if index < 141 then
                if index < 140 then
                  {139}
                else
                  {140}
              else
                if index < 142 then
                  {141}
                else
                  if index < 143 then
                    {142}
                  else
                    {143}

private def anchoredFaces1 : ℕ → Finset (Fin 1069) :=
fun index =>
    if index < 72 then
      if index < 36 then
        if index < 18 then
          if index < 9 then
            if index < 4 then
              if index < 2 then
                if index < 1 then
                  {144, 145, 146, 147, 148}
                else
                  {149, 150, 151, 152, 153, 154}
              else
                if index < 3 then
                  {155, 156, 157, 158}
                else
                  {159, 160, 161, 162, 163}
            else
              if index < 6 then
                if index < 5 then
                  {164, 165, 166, 167}
                else
                  {168, 169, 170, 171, 172}
              else
                if index < 7 then
                  {173, 174, 175}
                else
                  if index < 8 then
                    {176, 177, 178, 179}
                  else
                    {180, 181, 182, 183, 184, 185}
          else
            if index < 13 then
              if index < 11 then
                if index < 10 then
                  {186, 187, 188, 189, 190}
                else
                  {191, 192, 193, 194, 195}
              else
                if index < 12 then
                  {196, 197, 198, 199}
                else
                  {200, 201, 202, 203, 204}
            else
              if index < 15 then
                if index < 14 then
                  {205, 206, 207, 208}
                else
                  {209, 210, 211, 212}
              else
                if index < 16 then
                  {213, 214, 215}
                else
                  if index < 17 then
                    {216, 217, 218, 219}
                  else
                    {220, 221, 222}
        else
          if index < 27 then
            if index < 22 then
              if index < 20 then
                if index < 19 then
                  {223, 224, 225}
                else
                  {226, 227}
              else
                if index < 21 then
                  {228, 229, 230}
                else
                  {231, 232}
            else
              if index < 24 then
                if index < 23 then
                  {233, 234}
                else
                  {235}
              else
                if index < 25 then
                  {236, 237, 238, 239, 240, 241}
                else
                  if index < 26 then
                    {242, 243, 244, 245}
                  else
                    {246, 247, 248, 249, 250}
          else
            if index < 31 then
              if index < 29 then
                if index < 28 then
                  {251, 252, 253}
                else
                  {254, 255, 256, 257, 258}
              else
                if index < 30 then
                  {259, 260, 261}
                else
                  {262, 263, 264, 265}
            else
              if index < 33 then
                if index < 32 then
                  {266, 267}
                else
                  {268, 269, 270, 271, 272}
              else
                if index < 34 then
                  {273, 274, 275, 276}
                else
                  if index < 35 then
                    {277, 278, 279, 280}
                  else
                    {281, 282, 283}
      else
        if index < 54 then
          if index < 45 then
            if index < 40 then
              if index < 38 then
                if index < 37 then
                  {284, 285, 286, 287}
                else
                  {288, 289, 290}
              else
                if index < 39 then
                  {291, 292, 293}
                else
                  {294, 295}
            else
              if index < 42 then
                if index < 41 then
                  {296, 297, 298, 299, 300}
                else
                  {301, 302}
              else
                if index < 43 then
                  {303, 304, 305, 306}
                else
                  if index < 44 then
                    {307}
                  else
                    {308, 309, 310, 311}
          else
            if index < 49 then
              if index < 47 then
                if index < 46 then
                  {312}
                else
                  {313, 314, 315}
              else
                if index < 48 then
                  ∅
                else
                  {316, 317, 318}
            else
              if index < 51 then
                if index < 50 then
                  {319, 320}
                else
                  {321, 322}
              else
                if index < 52 then
                  {323}
                else
                  if index < 53 then
                    {324, 325}
                  else
                    {326}
        else
          if index < 63 then
            if index < 58 then
              if index < 56 then
                if index < 55 then
                  {327}
                else
                  ∅
              else
                if index < 57 then
                  {328, 329, 330, 331}
                else
                  {332, 333, 334, 335}
            else
              if index < 60 then
                if index < 59 then
                  {336, 337, 338}
                else
                  {339, 340, 341}
              else
                if index < 61 then
                  {342, 343, 344}
                else
                  if index < 62 then
                    {345, 346, 347}
                  else
                    {348, 349}
          else
            if index < 67 then
              if index < 65 then
                if index < 64 then
                  {350, 351}
                else
                  {352, 353}
              else
                if index < 66 then
                  {354}
                else
                  {355}
            else
              if index < 69 then
                if index < 68 then
                  ∅
                else
                  {356, 357, 358}
              else
                if index < 70 then
                  {359, 360}
                else
                  if index < 71 then
                    {361, 362}
                  else
                    {363}
    else
      if index < 108 then
        if index < 90 then
          if index < 81 then
            if index < 76 then
              if index < 74 then
                if index < 73 then
                  {364, 365}
                else
                  {366}
              else
                if index < 75 then
                  {367}
                else
                  ∅
            else
              if index < 78 then
                if index < 77 then
                  {368, 369, 370, 371}
                else
                  {372, 373, 374}
              else
                if index < 79 then
                  {375, 376, 377}
                else
                  if index < 80 then
                    {378, 379}
                  else
                    {380, 381, 382, 383, 384}
          else
            if index < 85 then
              if index < 83 then
                if index < 82 then
                  {385, 386, 387, 388}
                else
                  {389, 390, 391, 392}
              else
                if index < 84 then
                  {393, 394, 395}
                else
                  {396, 397, 398, 399}
            else
              if index < 87 then
                if index < 86 then
                  {400, 401, 402}
                else
                  {403, 404, 405}
              else
                if index < 88 then
                  {406, 407}
                else
                  if index < 89 then
                    {408, 409, 410}
                  else
                    {411, 412}
        else
          if index < 99 then
            if index < 94 then
              if index < 92 then
                if index < 91 then
                  {413, 414}
                else
                  {415}
              else
                if index < 93 then
                  {416, 417, 418, 419, 420, 421}
                else
                  {422, 423, 424, 425}
            else
              if index < 96 then
                if index < 95 then
                  {426, 427, 428, 429, 430}
                else
                  {431, 432, 433}
              else
                if index < 97 then
                  {434, 435, 436, 437, 438}
                else
                  if index < 98 then
                    {439, 440, 441}
                  else
                    {442, 443, 444, 445}
          else
            if index < 103 then
              if index < 101 then
                if index < 100 then
                  {446, 447}
                else
                  {448, 449, 450, 451, 452}
              else
                if index < 102 then
                  {453, 454, 455, 456}
                else
                  {457, 458, 459, 460}
            else
              if index < 105 then
                if index < 104 then
                  {461, 462, 463}
                else
                  {464, 465, 466, 467}
              else
                if index < 106 then
                  {468, 469, 470}
                else
                  if index < 107 then
                    {471, 472, 473}
                  else
                    {474, 475}
      else
        if index < 126 then
          if index < 117 then
            if index < 112 then
              if index < 110 then
                if index < 109 then
                  {476, 477, 478, 479, 480}
                else
                  {481, 482}
              else
                if index < 111 then
                  {483, 484, 485, 486}
                else
                  {487}
            else
              if index < 114 then
                if index < 113 then
                  {488, 489, 490, 491}
                else
                  {492}
              else
                if index < 115 then
                  {493, 494, 495}
                else
                  if index < 116 then
                    ∅
                  else
                    {496, 497, 498}
          else
            if index < 121 then
              if index < 119 then
                if index < 118 then
                  {499, 500}
                else
                  {501, 502}
              else
                if index < 120 then
                  {503}
                else
                  {504, 505}
            else
              if index < 123 then
                if index < 122 then
                  {506}
                else
                  {507}
              else
                if index < 124 then
                  ∅
                else
                  if index < 125 then
                    {508, 509, 510, 511}
                  else
                    {512, 513, 514, 515}
        else
          if index < 135 then
            if index < 130 then
              if index < 128 then
                if index < 127 then
                  {516, 517, 518}
                else
                  {519, 520, 521}
              else
                if index < 129 then
                  {522, 523, 524}
                else
                  {525, 526, 527}
            else
              if index < 132 then
                if index < 131 then
                  {528, 529}
                else
                  {530, 531}
              else
                if index < 133 then
                  {532, 533}
                else
                  if index < 134 then
                    {534}
                  else
                    {535}
          else
            if index < 139 then
              if index < 137 then
                if index < 136 then
                  ∅
                else
                  {536, 537, 538}
              else
                if index < 138 then
                  {539, 540}
                else
                  {541, 542}
            else
              if index < 141 then
                if index < 140 then
                  {543}
                else
                  {544, 545}
              else
                if index < 142 then
                  {546}
                else
                  if index < 143 then
                    {547}
                  else
                    ∅

private def anchoredFaces2 : ℕ → Finset (Fin 1069) :=
fun index =>
    if index < 72 then
      if index < 36 then
        if index < 18 then
          if index < 9 then
            if index < 4 then
              if index < 2 then
                if index < 1 then
                  {548, 549, 550, 551, 552, 553, 554, 555, 556}
                else
                  {557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568}
              else
                if index < 3 then
                  {569, 570, 571, 572, 573, 574}
                else
                  {575, 576, 577, 578, 579, 580, 581}
            else
              if index < 6 then
                if index < 5 then
                  {582, 583, 584, 585, 586}
                else
                  {587, 588, 589, 590, 591, 592, 593, 594}
              else
                if index < 7 then
                  {595, 596, 597}
                else
                  if index < 8 then
                    {598, 599, 600, 601}
                  else
                    {602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612}
          else
            if index < 13 then
              if index < 11 then
                if index < 10 then
                  {613, 614, 615, 616, 617, 618, 619}
                else
                  {620, 621, 622, 623, 624, 625, 626}
              else
                if index < 12 then
                  {627, 628, 629}
                else
                  {630, 631, 632, 633, 634, 635, 636}
            else
              if index < 15 then
                if index < 14 then
                  {637, 638, 639, 640}
                else
                  {641, 642, 643, 644}
              else
                if index < 16 then
                  {645}
                else
                  if index < 17 then
                    {646, 647, 648, 649, 650}
                  else
                    {651, 652}
        else
          if index < 27 then
            if index < 22 then
              if index < 20 then
                if index < 19 then
                  {653, 654}
                else
                  ∅
              else
                if index < 21 then
                  {655, 656, 657}
                else
                  {658}
            else
              if index < 24 then
                if index < 23 then
                  {659}
                else
                  ∅
              else
                if index < 25 then
                  {660, 661, 662, 663, 664, 665, 666, 667, 668, 669}
                else
                  if index < 26 then
                    {670, 671, 672, 673, 674}
                  else
                    {675, 676, 677, 678, 679, 680}
          else
            if index < 31 then
              if index < 29 then
                if index < 28 then
                  {681, 682, 683}
                else
                  {684, 685, 686, 687, 688, 689, 690, 691}
              else
                if index < 30 then
                  {692, 693}
                else
                  {694, 695, 696, 697}
            else
              if index < 33 then
                if index < 32 then
                  {698}
                else
                  {699, 700, 701, 702, 703, 704, 705, 706}
              else
                if index < 34 then
                  {707, 708, 709, 710, 711}
                else
                  if index < 35 then
                    {712, 713, 714, 715, 716}
                  else
                    {717, 718}
      else
        if index < 54 then
          if index < 45 then
            if index < 40 then
              if index < 38 then
                if index < 37 then
                  {719, 720, 721, 722}
                else
                  {723, 724}
              else
                if index < 39 then
                  {725, 726}
                else
                  ∅
            else
              if index < 42 then
                if index < 41 then
                  {727, 728, 729, 730, 731, 732}
                else
                  {733}
              else
                if index < 43 then
                  {734, 735, 736}
                else
                  if index < 44 then
                    ∅
                  else
                    {737, 738, 739}
          else
            if index < 49 then
              if index < 47 then
                if index < 46 then
                  ∅
                else
                  {740}
              else
                if index < 48 then
                  ∅
                else
                  {741, 742, 743}
            else
              if index < 51 then
                if index < 50 then
                  {744}
                else
                  {745}
              else
                if index < 52 then
                  ∅
                else
                  if index < 53 then
                    {746}
                  else
                    ∅
        else
          if index < 63 then
            if index < 58 then
              if index < 56 then
                if index < 55 then
                  ∅
                else
                  ∅
              else
                if index < 57 then
                  {747, 748, 749, 750, 751}
                else
                  {752, 753, 754, 755, 756}
            else
              if index < 60 then
                if index < 59 then
                  {757, 758, 759}
                else
                  {760, 761}
              else
                if index < 61 then
                  {762, 763}
                else
                  if index < 62 then
                    {764, 765}
                  else
                    {766}
          else
            if index < 67 then
              if index < 65 then
                if index < 64 then
                  ∅
                else
                  {767}
              else
                if index < 66 then
                  ∅
                else
                  ∅
            else
              if index < 69 then
                if index < 68 then
                  ∅
                else
                  {768, 769, 770}
              else
                if index < 70 then
                  {771}
                else
                  if index < 71 then
                    {772}
                  else
                    ∅
    else
      if index < 108 then
        if index < 90 then
          if index < 81 then
            if index < 76 then
              if index < 74 then
                if index < 73 then
                  {773}
                else
                  ∅
              else
                if index < 75 then
                  ∅
                else
                  ∅
            else
              if index < 78 then
                if index < 77 then
                  {774, 775, 776, 777, 778, 779}
                else
                  {780, 781, 782}
              else
                if index < 79 then
                  {783, 784, 785}
                else
                  if index < 80 then
                    {786}
                  else
                    {787, 788, 789, 790, 791, 792, 793, 794, 795}
          else
            if index < 85 then
              if index < 83 then
                if index < 82 then
                  {796, 797, 798, 799, 800}
                else
                  {801, 802, 803, 804, 805, 806}
              else
                if index < 84 then
                  {807, 808, 809}
                else
                  {810, 811, 812, 813, 814}
            else
              if index < 87 then
                if index < 86 then
                  {815, 816}
                else
                  {817, 818}
              else
                if index < 88 then
                  ∅
                else
                  if index < 89 then
                    {819, 820, 821}
                  else
                    {822}
        else
          if index < 99 then
            if index < 94 then
              if index < 92 then
                if index < 91 then
                  {823}
                else
                  ∅
              else
                if index < 93 then
                  {824, 825, 826, 827, 828, 829, 830, 831, 832, 833}
                else
                  {834, 835, 836, 837, 838}
            else
              if index < 96 then
                if index < 95 then
                  {839, 840, 841, 842, 843, 844}
                else
                  {845, 846, 847}
              else
                if index < 97 then
                  {848, 849, 850, 851, 852, 853, 854, 855}
                else
                  if index < 98 then
                    {856, 857}
                  else
                    {858, 859, 860, 861}
          else
            if index < 103 then
              if index < 101 then
                if index < 100 then
                  {862}
                else
                  {863, 864, 865, 866, 867, 868, 869, 870}
              else
                if index < 102 then
                  {871, 872, 873, 874, 875}
                else
                  {876, 877, 878, 879, 880}
            else
              if index < 105 then
                if index < 104 then
                  {881, 882}
                else
                  {883, 884, 885, 886}
              else
                if index < 106 then
                  {887, 888}
                else
                  if index < 107 then
                    {889, 890}
                  else
                    ∅
      else
        if index < 126 then
          if index < 117 then
            if index < 112 then
              if index < 110 then
                if index < 109 then
                  {891, 892, 893, 894, 895, 896}
                else
                  {897}
              else
                if index < 111 then
                  {898, 899, 900}
                else
                  ∅
            else
              if index < 114 then
                if index < 113 then
                  {901, 902, 903}
                else
                  ∅
              else
                if index < 115 then
                  {904}
                else
                  if index < 116 then
                    ∅
                  else
                    {905, 906, 907}
          else
            if index < 121 then
              if index < 119 then
                if index < 118 then
                  {908}
                else
                  {909}
              else
                if index < 120 then
                  ∅
                else
                  {910}
            else
              if index < 123 then
                if index < 122 then
                  ∅
                else
                  ∅
              else
                if index < 124 then
                  ∅
                else
                  if index < 125 then
                    {911, 912, 913, 914, 915}
                  else
                    {916, 917, 918, 919, 920}
        else
          if index < 135 then
            if index < 130 then
              if index < 128 then
                if index < 127 then
                  {921, 922, 923}
                else
                  {924, 925}
              else
                if index < 129 then
                  {926, 927}
                else
                  {928, 929}
            else
              if index < 132 then
                if index < 131 then
                  {930}
                else
                  ∅
              else
                if index < 133 then
                  {931}
                else
                  if index < 134 then
                    ∅
                  else
                    ∅
          else
            if index < 139 then
              if index < 137 then
                if index < 136 then
                  ∅
                else
                  {932, 933, 934}
              else
                if index < 138 then
                  {935}
                else
                  {936}
            else
              if index < 141 then
                if index < 140 then
                  ∅
                else
                  {937}
              else
                if index < 142 then
                  ∅
                else
                  if index < 143 then
                    ∅
                  else
                    ∅

private def anchoredFaces3 : ℕ → Finset (Fin 1069) :=
fun index =>
    if index < 72 then
      if index < 36 then
        if index < 18 then
          if index < 9 then
            if index < 4 then
              if index < 2 then
                if index < 1 then
                  {938, 939, 940, 941, 942, 943}
                else
                  {944, 945, 946, 947, 948, 949, 950}
              else
                if index < 3 then
                  {951, 952, 953}
                else
                  {954, 955}
            else
              if index < 6 then
                if index < 5 then
                  {956, 957}
                else
                  {958, 959, 960, 961}
              else
                if index < 7 then
                  {962}
                else
                  if index < 8 then
                    {963}
                  else
                    {964, 965, 966, 967, 968, 969}
          else
            if index < 13 then
              if index < 11 then
                if index < 10 then
                  {970, 971, 972}
                else
                  {973, 974, 975}
              else
                if index < 12 then
                  ∅
                else
                  {976, 977, 978}
            else
              if index < 15 then
                if index < 14 then
                  {979}
                else
                  {980}
              else
                if index < 16 then
                  ∅
                else
                  if index < 17 then
                    {981, 982}
                  else
                    ∅
        else
          if index < 27 then
            if index < 22 then
              if index < 20 then
                if index < 19 then
                  ∅
                else
                  ∅
              else
                if index < 21 then
                  {983}
                else
                  ∅
            else
              if index < 24 then
                if index < 23 then
                  ∅
                else
                  ∅
              else
                if index < 25 then
                  {984, 985, 986, 987, 988}
                else
                  if index < 26 then
                    {989, 990}
                  else
                    {991, 992}
          else
            if index < 31 then
              if index < 29 then
                if index < 28 then
                  {993}
                else
                  {994, 995, 996, 997}
              else
                if index < 30 then
                  ∅
                else
                  {998}
            else
              if index < 33 then
                if index < 32 then
                  ∅
                else
                  {999, 1000, 1001, 1002}
              else
                if index < 34 then
                  {1003, 1004}
                else
                  if index < 35 then
                    {1005, 1006}
                  else
                    ∅
      else
        if index < 54 then
          if index < 45 then
            if index < 40 then
              if index < 38 then
                if index < 37 then
                  ∅
                else
                  ∅
              else
                if index < 39 then
                  ∅
                else
                  ∅
            else
              if index < 42 then
                if index < 41 then
                  {1007, 1008}
                else
                  ∅
              else
                if index < 43 then
                  ∅
                else
                  if index < 44 then
                    ∅
                  else
                    {1009}
          else
            if index < 49 then
              if index < 47 then
                if index < 46 then
                  ∅
                else
                  ∅
              else
                if index < 48 then
                  ∅
                else
                  {1010}
            else
              if index < 51 then
                if index < 50 then
                  ∅
                else
                  ∅
              else
                if index < 52 then
                  ∅
                else
                  if index < 53 then
                    ∅
                  else
                    ∅
        else
          if index < 63 then
            if index < 58 then
              if index < 56 then
                if index < 55 then
                  ∅
                else
                  ∅
              else
                if index < 57 then
                  {1011, 1012}
                else
                  {1013, 1014}
            else
              if index < 60 then
                if index < 59 then
                  {1015}
                else
                  ∅
              else
                if index < 61 then
                  ∅
                else
                  if index < 62 then
                    ∅
                  else
                    ∅
          else
            if index < 67 then
              if index < 65 then
                if index < 64 then
                  ∅
                else
                  ∅
              else
                if index < 66 then
                  ∅
                else
                  ∅
            else
              if index < 69 then
                if index < 68 then
                  ∅
                else
                  {1016}
              else
                if index < 70 then
                  ∅
                else
                  if index < 71 then
                    ∅
                  else
                    ∅
    else
      if index < 108 then
        if index < 90 then
          if index < 81 then
            if index < 76 then
              if index < 74 then
                if index < 73 then
                  ∅
                else
                  ∅
              else
                if index < 75 then
                  ∅
                else
                  ∅
            else
              if index < 78 then
                if index < 77 then
                  {1017, 1018, 1019}
                else
                  ∅
              else
                if index < 79 then
                  {1020}
                else
                  if index < 80 then
                    ∅
                  else
                    {1021, 1022, 1023, 1024, 1025}
          else
            if index < 85 then
              if index < 83 then
                if index < 82 then
                  {1026, 1027}
                else
                  {1028, 1029, 1030}
              else
                if index < 84 then
                  {1031}
                else
                  {1032, 1033}
            else
              if index < 87 then
                if index < 86 then
                  ∅
                else
                  ∅
              else
                if index < 88 then
                  ∅
                else
                  if index < 89 then
                    {1034}
                  else
                    ∅
        else
          if index < 99 then
            if index < 94 then
              if index < 92 then
                if index < 91 then
                  ∅
                else
                  ∅
              else
                if index < 93 then
                  {1035, 1036, 1037, 1038, 1039}
                else
                  {1040, 1041}
            else
              if index < 96 then
                if index < 95 then
                  {1042, 1043}
                else
                  {1044}
              else
                if index < 97 then
                  {1045, 1046, 1047, 1048}
                else
                  if index < 98 then
                    ∅
                  else
                    {1049}
          else
            if index < 103 then
              if index < 101 then
                if index < 100 then
                  ∅
                else
                  {1050, 1051, 1052, 1053}
              else
                if index < 102 then
                  {1054, 1055}
                else
                  {1056, 1057}
            else
              if index < 105 then
                if index < 104 then
                  ∅
                else
                  ∅
              else
                if index < 106 then
                  ∅
                else
                  if index < 107 then
                    ∅
                  else
                    ∅
      else
        if index < 126 then
          if index < 117 then
            if index < 112 then
              if index < 110 then
                if index < 109 then
                  {1058, 1059}
                else
                  ∅
              else
                if index < 111 then
                  ∅
                else
                  ∅
            else
              if index < 114 then
                if index < 113 then
                  {1060}
                else
                  ∅
              else
                if index < 115 then
                  ∅
                else
                  if index < 116 then
                    ∅
                  else
                    {1061}
          else
            if index < 121 then
              if index < 119 then
                if index < 118 then
                  ∅
                else
                  ∅
              else
                if index < 120 then
                  ∅
                else
                  ∅
            else
              if index < 123 then
                if index < 122 then
                  ∅
                else
                  ∅
              else
                if index < 124 then
                  ∅
                else
                  if index < 125 then
                    {1062, 1063}
                  else
                    {1064, 1065}
        else
          if index < 135 then
            if index < 130 then
              if index < 128 then
                if index < 127 then
                  {1066}
                else
                  ∅
              else
                if index < 129 then
                  ∅
                else
                  ∅
            else
              if index < 132 then
                if index < 131 then
                  ∅
                else
                  ∅
              else
                if index < 133 then
                  ∅
                else
                  if index < 134 then
                    ∅
                  else
                    ∅
          else
            if index < 139 then
              if index < 137 then
                if index < 136 then
                  ∅
                else
                  {1067}
              else
                if index < 138 then
                  ∅
                else
                  ∅
            else
              if index < 141 then
                if index < 140 then
                  ∅
                else
                  ∅
              else
                if index < 142 then
                  ∅
                else
                  if index < 143 then
                    ∅
                  else
                    ∅

private def anchoredFaces4 : ℕ → Finset (Fin 1069) :=
fun index =>
    if index < 72 then
      if index < 36 then
        if index < 18 then
          if index < 9 then
            if index < 4 then
              if index < 2 then
                if index < 1 then
                  {1068}
                else
                  ∅
              else
                if index < 3 then
                  ∅
                else
                  ∅
            else
              if index < 6 then
                if index < 5 then
                  ∅
                else
                  ∅
              else
                if index < 7 then
                  ∅
                else
                  if index < 8 then
                    ∅
                  else
                    ∅
          else
            if index < 13 then
              if index < 11 then
                if index < 10 then
                  ∅
                else
                  ∅
              else
                if index < 12 then
                  ∅
                else
                  ∅
            else
              if index < 15 then
                if index < 14 then
                  ∅
                else
                  ∅
              else
                if index < 16 then
                  ∅
                else
                  if index < 17 then
                    ∅
                  else
                    ∅
        else
          if index < 27 then
            if index < 22 then
              if index < 20 then
                if index < 19 then
                  ∅
                else
                  ∅
              else
                if index < 21 then
                  ∅
                else
                  ∅
            else
              if index < 24 then
                if index < 23 then
                  ∅
                else
                  ∅
              else
                if index < 25 then
                  ∅
                else
                  if index < 26 then
                    ∅
                  else
                    ∅
          else
            if index < 31 then
              if index < 29 then
                if index < 28 then
                  ∅
                else
                  ∅
              else
                if index < 30 then
                  ∅
                else
                  ∅
            else
              if index < 33 then
                if index < 32 then
                  ∅
                else
                  ∅
              else
                if index < 34 then
                  ∅
                else
                  if index < 35 then
                    ∅
                  else
                    ∅
      else
        if index < 54 then
          if index < 45 then
            if index < 40 then
              if index < 38 then
                if index < 37 then
                  ∅
                else
                  ∅
              else
                if index < 39 then
                  ∅
                else
                  ∅
            else
              if index < 42 then
                if index < 41 then
                  ∅
                else
                  ∅
              else
                if index < 43 then
                  ∅
                else
                  if index < 44 then
                    ∅
                  else
                    ∅
          else
            if index < 49 then
              if index < 47 then
                if index < 46 then
                  ∅
                else
                  ∅
              else
                if index < 48 then
                  ∅
                else
                  ∅
            else
              if index < 51 then
                if index < 50 then
                  ∅
                else
                  ∅
              else
                if index < 52 then
                  ∅
                else
                  if index < 53 then
                    ∅
                  else
                    ∅
        else
          if index < 63 then
            if index < 58 then
              if index < 56 then
                if index < 55 then
                  ∅
                else
                  ∅
              else
                if index < 57 then
                  ∅
                else
                  ∅
            else
              if index < 60 then
                if index < 59 then
                  ∅
                else
                  ∅
              else
                if index < 61 then
                  ∅
                else
                  if index < 62 then
                    ∅
                  else
                    ∅
          else
            if index < 67 then
              if index < 65 then
                if index < 64 then
                  ∅
                else
                  ∅
              else
                if index < 66 then
                  ∅
                else
                  ∅
            else
              if index < 69 then
                if index < 68 then
                  ∅
                else
                  ∅
              else
                if index < 70 then
                  ∅
                else
                  if index < 71 then
                    ∅
                  else
                    ∅
    else
      if index < 108 then
        if index < 90 then
          if index < 81 then
            if index < 76 then
              if index < 74 then
                if index < 73 then
                  ∅
                else
                  ∅
              else
                if index < 75 then
                  ∅
                else
                  ∅
            else
              if index < 78 then
                if index < 77 then
                  ∅
                else
                  ∅
              else
                if index < 79 then
                  ∅
                else
                  if index < 80 then
                    ∅
                  else
                    ∅
          else
            if index < 85 then
              if index < 83 then
                if index < 82 then
                  ∅
                else
                  ∅
              else
                if index < 84 then
                  ∅
                else
                  ∅
            else
              if index < 87 then
                if index < 86 then
                  ∅
                else
                  ∅
              else
                if index < 88 then
                  ∅
                else
                  if index < 89 then
                    ∅
                  else
                    ∅
        else
          if index < 99 then
            if index < 94 then
              if index < 92 then
                if index < 91 then
                  ∅
                else
                  ∅
              else
                if index < 93 then
                  ∅
                else
                  ∅
            else
              if index < 96 then
                if index < 95 then
                  ∅
                else
                  ∅
              else
                if index < 97 then
                  ∅
                else
                  if index < 98 then
                    ∅
                  else
                    ∅
          else
            if index < 103 then
              if index < 101 then
                if index < 100 then
                  ∅
                else
                  ∅
              else
                if index < 102 then
                  ∅
                else
                  ∅
            else
              if index < 105 then
                if index < 104 then
                  ∅
                else
                  ∅
              else
                if index < 106 then
                  ∅
                else
                  if index < 107 then
                    ∅
                  else
                    ∅
      else
        if index < 126 then
          if index < 117 then
            if index < 112 then
              if index < 110 then
                if index < 109 then
                  ∅
                else
                  ∅
              else
                if index < 111 then
                  ∅
                else
                  ∅
            else
              if index < 114 then
                if index < 113 then
                  ∅
                else
                  ∅
              else
                if index < 115 then
                  ∅
                else
                  if index < 116 then
                    ∅
                  else
                    ∅
          else
            if index < 121 then
              if index < 119 then
                if index < 118 then
                  ∅
                else
                  ∅
              else
                if index < 120 then
                  ∅
                else
                  ∅
            else
              if index < 123 then
                if index < 122 then
                  ∅
                else
                  ∅
              else
                if index < 124 then
                  ∅
                else
                  if index < 125 then
                    ∅
                  else
                    ∅
        else
          if index < 135 then
            if index < 130 then
              if index < 128 then
                if index < 127 then
                  ∅
                else
                  ∅
              else
                if index < 129 then
                  ∅
                else
                  ∅
            else
              if index < 132 then
                if index < 131 then
                  ∅
                else
                  ∅
              else
                if index < 133 then
                  ∅
                else
                  if index < 134 then
                    ∅
                  else
                    ∅
          else
            if index < 139 then
              if index < 137 then
                if index < 136 then
                  ∅
                else
                  ∅
              else
                if index < 138 then
                  ∅
                else
                  ∅
            else
              if index < 141 then
                if index < 140 then
                  ∅
                else
                  ∅
              else
                if index < 142 then
                  ∅
                else
                  if index < 143 then
                    ∅
                  else
                    ∅

private def anchoredFaces (k : Fin 5) (v : Fin 144) : Finset (Fin 1069) :=
  if k.val = 0 then anchoredFaces0 v.val
  else if k.val = 1 then anchoredFaces1 v.val
  else if k.val = 2 then anchoredFaces2 v.val
  else if k.val = 3 then anchoredFaces3 v.val
  else anchoredFaces4 v.val

private theorem bucket0000 : (⟨0, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨0, by decide⟩ : Fin 1069)) (faceAnchor (⟨0, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0001 : (⟨1, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1, by decide⟩ : Fin 1069)) (faceAnchor (⟨1, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0002 : (⟨2, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨2, by decide⟩ : Fin 1069)) (faceAnchor (⟨2, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0003 : (⟨3, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨3, by decide⟩ : Fin 1069)) (faceAnchor (⟨3, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0004 : (⟨4, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨4, by decide⟩ : Fin 1069)) (faceAnchor (⟨4, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0005 : (⟨5, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨5, by decide⟩ : Fin 1069)) (faceAnchor (⟨5, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0006 : (⟨6, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨6, by decide⟩ : Fin 1069)) (faceAnchor (⟨6, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0007 : (⟨7, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨7, by decide⟩ : Fin 1069)) (faceAnchor (⟨7, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0008 : (⟨8, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨8, by decide⟩ : Fin 1069)) (faceAnchor (⟨8, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0009 : (⟨9, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨9, by decide⟩ : Fin 1069)) (faceAnchor (⟨9, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0010 : (⟨10, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨10, by decide⟩ : Fin 1069)) (faceAnchor (⟨10, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0011 : (⟨11, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨11, by decide⟩ : Fin 1069)) (faceAnchor (⟨11, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0012 : (⟨12, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨12, by decide⟩ : Fin 1069)) (faceAnchor (⟨12, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0013 : (⟨13, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨13, by decide⟩ : Fin 1069)) (faceAnchor (⟨13, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0014 : (⟨14, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨14, by decide⟩ : Fin 1069)) (faceAnchor (⟨14, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0015 : (⟨15, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨15, by decide⟩ : Fin 1069)) (faceAnchor (⟨15, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0016 : (⟨16, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨16, by decide⟩ : Fin 1069)) (faceAnchor (⟨16, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0017 : (⟨17, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨17, by decide⟩ : Fin 1069)) (faceAnchor (⟨17, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0018 : (⟨18, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨18, by decide⟩ : Fin 1069)) (faceAnchor (⟨18, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0019 : (⟨19, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨19, by decide⟩ : Fin 1069)) (faceAnchor (⟨19, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0020 : (⟨20, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨20, by decide⟩ : Fin 1069)) (faceAnchor (⟨20, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0021 : (⟨21, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨21, by decide⟩ : Fin 1069)) (faceAnchor (⟨21, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0022 : (⟨22, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨22, by decide⟩ : Fin 1069)) (faceAnchor (⟨22, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0023 : (⟨23, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨23, by decide⟩ : Fin 1069)) (faceAnchor (⟨23, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0024 : (⟨24, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨24, by decide⟩ : Fin 1069)) (faceAnchor (⟨24, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0025 : (⟨25, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨25, by decide⟩ : Fin 1069)) (faceAnchor (⟨25, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0026 : (⟨26, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨26, by decide⟩ : Fin 1069)) (faceAnchor (⟨26, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0027 : (⟨27, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨27, by decide⟩ : Fin 1069)) (faceAnchor (⟨27, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0028 : (⟨28, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨28, by decide⟩ : Fin 1069)) (faceAnchor (⟨28, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0029 : (⟨29, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨29, by decide⟩ : Fin 1069)) (faceAnchor (⟨29, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0030 : (⟨30, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨30, by decide⟩ : Fin 1069)) (faceAnchor (⟨30, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0031 : (⟨31, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨31, by decide⟩ : Fin 1069)) (faceAnchor (⟨31, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0032 : (⟨32, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨32, by decide⟩ : Fin 1069)) (faceAnchor (⟨32, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0033 : (⟨33, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨33, by decide⟩ : Fin 1069)) (faceAnchor (⟨33, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0034 : (⟨34, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨34, by decide⟩ : Fin 1069)) (faceAnchor (⟨34, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0035 : (⟨35, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨35, by decide⟩ : Fin 1069)) (faceAnchor (⟨35, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0036 : (⟨36, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨36, by decide⟩ : Fin 1069)) (faceAnchor (⟨36, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0037 : (⟨37, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨37, by decide⟩ : Fin 1069)) (faceAnchor (⟨37, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0038 : (⟨38, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨38, by decide⟩ : Fin 1069)) (faceAnchor (⟨38, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0039 : (⟨39, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨39, by decide⟩ : Fin 1069)) (faceAnchor (⟨39, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0040 : (⟨40, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨40, by decide⟩ : Fin 1069)) (faceAnchor (⟨40, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0041 : (⟨41, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨41, by decide⟩ : Fin 1069)) (faceAnchor (⟨41, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0042 : (⟨42, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨42, by decide⟩ : Fin 1069)) (faceAnchor (⟨42, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0043 : (⟨43, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨43, by decide⟩ : Fin 1069)) (faceAnchor (⟨43, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0044 : (⟨44, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨44, by decide⟩ : Fin 1069)) (faceAnchor (⟨44, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0045 : (⟨45, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨45, by decide⟩ : Fin 1069)) (faceAnchor (⟨45, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0046 : (⟨46, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨46, by decide⟩ : Fin 1069)) (faceAnchor (⟨46, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0047 : (⟨47, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨47, by decide⟩ : Fin 1069)) (faceAnchor (⟨47, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0048 : (⟨48, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨48, by decide⟩ : Fin 1069)) (faceAnchor (⟨48, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0049 : (⟨49, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨49, by decide⟩ : Fin 1069)) (faceAnchor (⟨49, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0050 : (⟨50, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨50, by decide⟩ : Fin 1069)) (faceAnchor (⟨50, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0051 : (⟨51, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨51, by decide⟩ : Fin 1069)) (faceAnchor (⟨51, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0052 : (⟨52, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨52, by decide⟩ : Fin 1069)) (faceAnchor (⟨52, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0053 : (⟨53, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨53, by decide⟩ : Fin 1069)) (faceAnchor (⟨53, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0054 : (⟨54, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨54, by decide⟩ : Fin 1069)) (faceAnchor (⟨54, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0055 : (⟨55, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨55, by decide⟩ : Fin 1069)) (faceAnchor (⟨55, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0056 : (⟨56, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨56, by decide⟩ : Fin 1069)) (faceAnchor (⟨56, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0057 : (⟨57, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨57, by decide⟩ : Fin 1069)) (faceAnchor (⟨57, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0058 : (⟨58, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨58, by decide⟩ : Fin 1069)) (faceAnchor (⟨58, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0059 : (⟨59, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨59, by decide⟩ : Fin 1069)) (faceAnchor (⟨59, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0060 : (⟨60, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨60, by decide⟩ : Fin 1069)) (faceAnchor (⟨60, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0061 : (⟨61, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨61, by decide⟩ : Fin 1069)) (faceAnchor (⟨61, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0062 : (⟨62, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨62, by decide⟩ : Fin 1069)) (faceAnchor (⟨62, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0063 : (⟨63, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨63, by decide⟩ : Fin 1069)) (faceAnchor (⟨63, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0064 : (⟨64, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨64, by decide⟩ : Fin 1069)) (faceAnchor (⟨64, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0065 : (⟨65, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨65, by decide⟩ : Fin 1069)) (faceAnchor (⟨65, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0066 : (⟨66, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨66, by decide⟩ : Fin 1069)) (faceAnchor (⟨66, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0067 : (⟨67, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨67, by decide⟩ : Fin 1069)) (faceAnchor (⟨67, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0068 : (⟨68, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨68, by decide⟩ : Fin 1069)) (faceAnchor (⟨68, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0069 : (⟨69, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨69, by decide⟩ : Fin 1069)) (faceAnchor (⟨69, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0070 : (⟨70, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨70, by decide⟩ : Fin 1069)) (faceAnchor (⟨70, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0071 : (⟨71, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨71, by decide⟩ : Fin 1069)) (faceAnchor (⟨71, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0072 : (⟨72, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨72, by decide⟩ : Fin 1069)) (faceAnchor (⟨72, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0073 : (⟨73, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨73, by decide⟩ : Fin 1069)) (faceAnchor (⟨73, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0074 : (⟨74, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨74, by decide⟩ : Fin 1069)) (faceAnchor (⟨74, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0075 : (⟨75, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨75, by decide⟩ : Fin 1069)) (faceAnchor (⟨75, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0076 : (⟨76, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨76, by decide⟩ : Fin 1069)) (faceAnchor (⟨76, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0077 : (⟨77, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨77, by decide⟩ : Fin 1069)) (faceAnchor (⟨77, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0078 : (⟨78, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨78, by decide⟩ : Fin 1069)) (faceAnchor (⟨78, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0079 : (⟨79, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨79, by decide⟩ : Fin 1069)) (faceAnchor (⟨79, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0080 : (⟨80, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨80, by decide⟩ : Fin 1069)) (faceAnchor (⟨80, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0081 : (⟨81, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨81, by decide⟩ : Fin 1069)) (faceAnchor (⟨81, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0082 : (⟨82, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨82, by decide⟩ : Fin 1069)) (faceAnchor (⟨82, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0083 : (⟨83, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨83, by decide⟩ : Fin 1069)) (faceAnchor (⟨83, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0084 : (⟨84, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨84, by decide⟩ : Fin 1069)) (faceAnchor (⟨84, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0085 : (⟨85, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨85, by decide⟩ : Fin 1069)) (faceAnchor (⟨85, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0086 : (⟨86, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨86, by decide⟩ : Fin 1069)) (faceAnchor (⟨86, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0087 : (⟨87, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨87, by decide⟩ : Fin 1069)) (faceAnchor (⟨87, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0088 : (⟨88, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨88, by decide⟩ : Fin 1069)) (faceAnchor (⟨88, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0089 : (⟨89, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨89, by decide⟩ : Fin 1069)) (faceAnchor (⟨89, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0090 : (⟨90, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨90, by decide⟩ : Fin 1069)) (faceAnchor (⟨90, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0091 : (⟨91, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨91, by decide⟩ : Fin 1069)) (faceAnchor (⟨91, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0092 : (⟨92, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨92, by decide⟩ : Fin 1069)) (faceAnchor (⟨92, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0093 : (⟨93, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨93, by decide⟩ : Fin 1069)) (faceAnchor (⟨93, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0094 : (⟨94, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨94, by decide⟩ : Fin 1069)) (faceAnchor (⟨94, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0095 : (⟨95, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨95, by decide⟩ : Fin 1069)) (faceAnchor (⟨95, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0096 : (⟨96, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨96, by decide⟩ : Fin 1069)) (faceAnchor (⟨96, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0097 : (⟨97, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨97, by decide⟩ : Fin 1069)) (faceAnchor (⟨97, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0098 : (⟨98, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨98, by decide⟩ : Fin 1069)) (faceAnchor (⟨98, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0099 : (⟨99, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨99, by decide⟩ : Fin 1069)) (faceAnchor (⟨99, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0100 : (⟨100, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨100, by decide⟩ : Fin 1069)) (faceAnchor (⟨100, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0101 : (⟨101, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨101, by decide⟩ : Fin 1069)) (faceAnchor (⟨101, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0102 : (⟨102, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨102, by decide⟩ : Fin 1069)) (faceAnchor (⟨102, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0103 : (⟨103, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨103, by decide⟩ : Fin 1069)) (faceAnchor (⟨103, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0104 : (⟨104, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨104, by decide⟩ : Fin 1069)) (faceAnchor (⟨104, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0105 : (⟨105, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨105, by decide⟩ : Fin 1069)) (faceAnchor (⟨105, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0106 : (⟨106, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨106, by decide⟩ : Fin 1069)) (faceAnchor (⟨106, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0107 : (⟨107, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨107, by decide⟩ : Fin 1069)) (faceAnchor (⟨107, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0108 : (⟨108, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨108, by decide⟩ : Fin 1069)) (faceAnchor (⟨108, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0109 : (⟨109, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨109, by decide⟩ : Fin 1069)) (faceAnchor (⟨109, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0110 : (⟨110, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨110, by decide⟩ : Fin 1069)) (faceAnchor (⟨110, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0111 : (⟨111, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨111, by decide⟩ : Fin 1069)) (faceAnchor (⟨111, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0112 : (⟨112, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨112, by decide⟩ : Fin 1069)) (faceAnchor (⟨112, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0113 : (⟨113, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨113, by decide⟩ : Fin 1069)) (faceAnchor (⟨113, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0114 : (⟨114, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨114, by decide⟩ : Fin 1069)) (faceAnchor (⟨114, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0115 : (⟨115, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨115, by decide⟩ : Fin 1069)) (faceAnchor (⟨115, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0116 : (⟨116, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨116, by decide⟩ : Fin 1069)) (faceAnchor (⟨116, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0117 : (⟨117, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨117, by decide⟩ : Fin 1069)) (faceAnchor (⟨117, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0118 : (⟨118, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨118, by decide⟩ : Fin 1069)) (faceAnchor (⟨118, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0119 : (⟨119, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨119, by decide⟩ : Fin 1069)) (faceAnchor (⟨119, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0120 : (⟨120, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨120, by decide⟩ : Fin 1069)) (faceAnchor (⟨120, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0121 : (⟨121, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨121, by decide⟩ : Fin 1069)) (faceAnchor (⟨121, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0122 : (⟨122, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨122, by decide⟩ : Fin 1069)) (faceAnchor (⟨122, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0123 : (⟨123, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨123, by decide⟩ : Fin 1069)) (faceAnchor (⟨123, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0124 : (⟨124, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨124, by decide⟩ : Fin 1069)) (faceAnchor (⟨124, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0125 : (⟨125, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨125, by decide⟩ : Fin 1069)) (faceAnchor (⟨125, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0126 : (⟨126, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨126, by decide⟩ : Fin 1069)) (faceAnchor (⟨126, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0127 : (⟨127, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨127, by decide⟩ : Fin 1069)) (faceAnchor (⟨127, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0128 : (⟨128, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨128, by decide⟩ : Fin 1069)) (faceAnchor (⟨128, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0129 : (⟨129, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨129, by decide⟩ : Fin 1069)) (faceAnchor (⟨129, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0130 : (⟨130, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨130, by decide⟩ : Fin 1069)) (faceAnchor (⟨130, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0131 : (⟨131, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨131, by decide⟩ : Fin 1069)) (faceAnchor (⟨131, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0132 : (⟨132, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨132, by decide⟩ : Fin 1069)) (faceAnchor (⟨132, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0133 : (⟨133, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨133, by decide⟩ : Fin 1069)) (faceAnchor (⟨133, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0134 : (⟨134, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨134, by decide⟩ : Fin 1069)) (faceAnchor (⟨134, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0135 : (⟨135, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨135, by decide⟩ : Fin 1069)) (faceAnchor (⟨135, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0136 : (⟨136, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨136, by decide⟩ : Fin 1069)) (faceAnchor (⟨136, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0137 : (⟨137, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨137, by decide⟩ : Fin 1069)) (faceAnchor (⟨137, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0138 : (⟨138, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨138, by decide⟩ : Fin 1069)) (faceAnchor (⟨138, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0139 : (⟨139, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨139, by decide⟩ : Fin 1069)) (faceAnchor (⟨139, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0140 : (⟨140, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨140, by decide⟩ : Fin 1069)) (faceAnchor (⟨140, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0141 : (⟨141, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨141, by decide⟩ : Fin 1069)) (faceAnchor (⟨141, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0142 : (⟨142, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨142, by decide⟩ : Fin 1069)) (faceAnchor (⟨142, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0143 : (⟨143, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨143, by decide⟩ : Fin 1069)) (faceAnchor (⟨143, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0144 : (⟨144, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨144, by decide⟩ : Fin 1069)) (faceAnchor (⟨144, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0145 : (⟨145, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨145, by decide⟩ : Fin 1069)) (faceAnchor (⟨145, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0146 : (⟨146, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨146, by decide⟩ : Fin 1069)) (faceAnchor (⟨146, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0147 : (⟨147, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨147, by decide⟩ : Fin 1069)) (faceAnchor (⟨147, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0148 : (⟨148, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨148, by decide⟩ : Fin 1069)) (faceAnchor (⟨148, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0149 : (⟨149, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨149, by decide⟩ : Fin 1069)) (faceAnchor (⟨149, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0150 : (⟨150, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨150, by decide⟩ : Fin 1069)) (faceAnchor (⟨150, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0151 : (⟨151, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨151, by decide⟩ : Fin 1069)) (faceAnchor (⟨151, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0152 : (⟨152, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨152, by decide⟩ : Fin 1069)) (faceAnchor (⟨152, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0153 : (⟨153, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨153, by decide⟩ : Fin 1069)) (faceAnchor (⟨153, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0154 : (⟨154, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨154, by decide⟩ : Fin 1069)) (faceAnchor (⟨154, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0155 : (⟨155, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨155, by decide⟩ : Fin 1069)) (faceAnchor (⟨155, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0156 : (⟨156, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨156, by decide⟩ : Fin 1069)) (faceAnchor (⟨156, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0157 : (⟨157, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨157, by decide⟩ : Fin 1069)) (faceAnchor (⟨157, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0158 : (⟨158, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨158, by decide⟩ : Fin 1069)) (faceAnchor (⟨158, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0159 : (⟨159, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨159, by decide⟩ : Fin 1069)) (faceAnchor (⟨159, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0160 : (⟨160, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨160, by decide⟩ : Fin 1069)) (faceAnchor (⟨160, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0161 : (⟨161, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨161, by decide⟩ : Fin 1069)) (faceAnchor (⟨161, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0162 : (⟨162, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨162, by decide⟩ : Fin 1069)) (faceAnchor (⟨162, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0163 : (⟨163, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨163, by decide⟩ : Fin 1069)) (faceAnchor (⟨163, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0164 : (⟨164, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨164, by decide⟩ : Fin 1069)) (faceAnchor (⟨164, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0165 : (⟨165, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨165, by decide⟩ : Fin 1069)) (faceAnchor (⟨165, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0166 : (⟨166, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨166, by decide⟩ : Fin 1069)) (faceAnchor (⟨166, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0167 : (⟨167, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨167, by decide⟩ : Fin 1069)) (faceAnchor (⟨167, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0168 : (⟨168, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨168, by decide⟩ : Fin 1069)) (faceAnchor (⟨168, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0169 : (⟨169, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨169, by decide⟩ : Fin 1069)) (faceAnchor (⟨169, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0170 : (⟨170, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨170, by decide⟩ : Fin 1069)) (faceAnchor (⟨170, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0171 : (⟨171, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨171, by decide⟩ : Fin 1069)) (faceAnchor (⟨171, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0172 : (⟨172, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨172, by decide⟩ : Fin 1069)) (faceAnchor (⟨172, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0173 : (⟨173, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨173, by decide⟩ : Fin 1069)) (faceAnchor (⟨173, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0174 : (⟨174, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨174, by decide⟩ : Fin 1069)) (faceAnchor (⟨174, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0175 : (⟨175, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨175, by decide⟩ : Fin 1069)) (faceAnchor (⟨175, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0176 : (⟨176, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨176, by decide⟩ : Fin 1069)) (faceAnchor (⟨176, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0177 : (⟨177, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨177, by decide⟩ : Fin 1069)) (faceAnchor (⟨177, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0178 : (⟨178, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨178, by decide⟩ : Fin 1069)) (faceAnchor (⟨178, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0179 : (⟨179, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨179, by decide⟩ : Fin 1069)) (faceAnchor (⟨179, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0180 : (⟨180, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨180, by decide⟩ : Fin 1069)) (faceAnchor (⟨180, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0181 : (⟨181, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨181, by decide⟩ : Fin 1069)) (faceAnchor (⟨181, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0182 : (⟨182, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨182, by decide⟩ : Fin 1069)) (faceAnchor (⟨182, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0183 : (⟨183, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨183, by decide⟩ : Fin 1069)) (faceAnchor (⟨183, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0184 : (⟨184, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨184, by decide⟩ : Fin 1069)) (faceAnchor (⟨184, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0185 : (⟨185, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨185, by decide⟩ : Fin 1069)) (faceAnchor (⟨185, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0186 : (⟨186, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨186, by decide⟩ : Fin 1069)) (faceAnchor (⟨186, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0187 : (⟨187, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨187, by decide⟩ : Fin 1069)) (faceAnchor (⟨187, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0188 : (⟨188, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨188, by decide⟩ : Fin 1069)) (faceAnchor (⟨188, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0189 : (⟨189, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨189, by decide⟩ : Fin 1069)) (faceAnchor (⟨189, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0190 : (⟨190, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨190, by decide⟩ : Fin 1069)) (faceAnchor (⟨190, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0191 : (⟨191, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨191, by decide⟩ : Fin 1069)) (faceAnchor (⟨191, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0192 : (⟨192, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨192, by decide⟩ : Fin 1069)) (faceAnchor (⟨192, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0193 : (⟨193, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨193, by decide⟩ : Fin 1069)) (faceAnchor (⟨193, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0194 : (⟨194, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨194, by decide⟩ : Fin 1069)) (faceAnchor (⟨194, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0195 : (⟨195, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨195, by decide⟩ : Fin 1069)) (faceAnchor (⟨195, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0196 : (⟨196, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨196, by decide⟩ : Fin 1069)) (faceAnchor (⟨196, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0197 : (⟨197, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨197, by decide⟩ : Fin 1069)) (faceAnchor (⟨197, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0198 : (⟨198, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨198, by decide⟩ : Fin 1069)) (faceAnchor (⟨198, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0199 : (⟨199, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨199, by decide⟩ : Fin 1069)) (faceAnchor (⟨199, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0200 : (⟨200, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨200, by decide⟩ : Fin 1069)) (faceAnchor (⟨200, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0201 : (⟨201, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨201, by decide⟩ : Fin 1069)) (faceAnchor (⟨201, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0202 : (⟨202, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨202, by decide⟩ : Fin 1069)) (faceAnchor (⟨202, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0203 : (⟨203, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨203, by decide⟩ : Fin 1069)) (faceAnchor (⟨203, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0204 : (⟨204, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨204, by decide⟩ : Fin 1069)) (faceAnchor (⟨204, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0205 : (⟨205, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨205, by decide⟩ : Fin 1069)) (faceAnchor (⟨205, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0206 : (⟨206, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨206, by decide⟩ : Fin 1069)) (faceAnchor (⟨206, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0207 : (⟨207, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨207, by decide⟩ : Fin 1069)) (faceAnchor (⟨207, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0208 : (⟨208, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨208, by decide⟩ : Fin 1069)) (faceAnchor (⟨208, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0209 : (⟨209, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨209, by decide⟩ : Fin 1069)) (faceAnchor (⟨209, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0210 : (⟨210, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨210, by decide⟩ : Fin 1069)) (faceAnchor (⟨210, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0211 : (⟨211, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨211, by decide⟩ : Fin 1069)) (faceAnchor (⟨211, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0212 : (⟨212, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨212, by decide⟩ : Fin 1069)) (faceAnchor (⟨212, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0213 : (⟨213, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨213, by decide⟩ : Fin 1069)) (faceAnchor (⟨213, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0214 : (⟨214, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨214, by decide⟩ : Fin 1069)) (faceAnchor (⟨214, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0215 : (⟨215, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨215, by decide⟩ : Fin 1069)) (faceAnchor (⟨215, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0216 : (⟨216, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨216, by decide⟩ : Fin 1069)) (faceAnchor (⟨216, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0217 : (⟨217, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨217, by decide⟩ : Fin 1069)) (faceAnchor (⟨217, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0218 : (⟨218, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨218, by decide⟩ : Fin 1069)) (faceAnchor (⟨218, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0219 : (⟨219, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨219, by decide⟩ : Fin 1069)) (faceAnchor (⟨219, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0220 : (⟨220, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨220, by decide⟩ : Fin 1069)) (faceAnchor (⟨220, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0221 : (⟨221, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨221, by decide⟩ : Fin 1069)) (faceAnchor (⟨221, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0222 : (⟨222, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨222, by decide⟩ : Fin 1069)) (faceAnchor (⟨222, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0223 : (⟨223, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨223, by decide⟩ : Fin 1069)) (faceAnchor (⟨223, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0224 : (⟨224, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨224, by decide⟩ : Fin 1069)) (faceAnchor (⟨224, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0225 : (⟨225, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨225, by decide⟩ : Fin 1069)) (faceAnchor (⟨225, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0226 : (⟨226, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨226, by decide⟩ : Fin 1069)) (faceAnchor (⟨226, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0227 : (⟨227, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨227, by decide⟩ : Fin 1069)) (faceAnchor (⟨227, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0228 : (⟨228, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨228, by decide⟩ : Fin 1069)) (faceAnchor (⟨228, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0229 : (⟨229, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨229, by decide⟩ : Fin 1069)) (faceAnchor (⟨229, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0230 : (⟨230, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨230, by decide⟩ : Fin 1069)) (faceAnchor (⟨230, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0231 : (⟨231, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨231, by decide⟩ : Fin 1069)) (faceAnchor (⟨231, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0232 : (⟨232, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨232, by decide⟩ : Fin 1069)) (faceAnchor (⟨232, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0233 : (⟨233, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨233, by decide⟩ : Fin 1069)) (faceAnchor (⟨233, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0234 : (⟨234, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨234, by decide⟩ : Fin 1069)) (faceAnchor (⟨234, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0235 : (⟨235, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨235, by decide⟩ : Fin 1069)) (faceAnchor (⟨235, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0236 : (⟨236, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨236, by decide⟩ : Fin 1069)) (faceAnchor (⟨236, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0237 : (⟨237, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨237, by decide⟩ : Fin 1069)) (faceAnchor (⟨237, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0238 : (⟨238, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨238, by decide⟩ : Fin 1069)) (faceAnchor (⟨238, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0239 : (⟨239, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨239, by decide⟩ : Fin 1069)) (faceAnchor (⟨239, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0240 : (⟨240, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨240, by decide⟩ : Fin 1069)) (faceAnchor (⟨240, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0241 : (⟨241, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨241, by decide⟩ : Fin 1069)) (faceAnchor (⟨241, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0242 : (⟨242, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨242, by decide⟩ : Fin 1069)) (faceAnchor (⟨242, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0243 : (⟨243, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨243, by decide⟩ : Fin 1069)) (faceAnchor (⟨243, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0244 : (⟨244, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨244, by decide⟩ : Fin 1069)) (faceAnchor (⟨244, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0245 : (⟨245, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨245, by decide⟩ : Fin 1069)) (faceAnchor (⟨245, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0246 : (⟨246, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨246, by decide⟩ : Fin 1069)) (faceAnchor (⟨246, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0247 : (⟨247, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨247, by decide⟩ : Fin 1069)) (faceAnchor (⟨247, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0248 : (⟨248, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨248, by decide⟩ : Fin 1069)) (faceAnchor (⟨248, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0249 : (⟨249, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨249, by decide⟩ : Fin 1069)) (faceAnchor (⟨249, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0250 : (⟨250, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨250, by decide⟩ : Fin 1069)) (faceAnchor (⟨250, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0251 : (⟨251, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨251, by decide⟩ : Fin 1069)) (faceAnchor (⟨251, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0252 : (⟨252, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨252, by decide⟩ : Fin 1069)) (faceAnchor (⟨252, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0253 : (⟨253, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨253, by decide⟩ : Fin 1069)) (faceAnchor (⟨253, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0254 : (⟨254, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨254, by decide⟩ : Fin 1069)) (faceAnchor (⟨254, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0255 : (⟨255, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨255, by decide⟩ : Fin 1069)) (faceAnchor (⟨255, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0256 : (⟨256, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨256, by decide⟩ : Fin 1069)) (faceAnchor (⟨256, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0257 : (⟨257, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨257, by decide⟩ : Fin 1069)) (faceAnchor (⟨257, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0258 : (⟨258, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨258, by decide⟩ : Fin 1069)) (faceAnchor (⟨258, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0259 : (⟨259, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨259, by decide⟩ : Fin 1069)) (faceAnchor (⟨259, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0260 : (⟨260, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨260, by decide⟩ : Fin 1069)) (faceAnchor (⟨260, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0261 : (⟨261, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨261, by decide⟩ : Fin 1069)) (faceAnchor (⟨261, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0262 : (⟨262, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨262, by decide⟩ : Fin 1069)) (faceAnchor (⟨262, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0263 : (⟨263, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨263, by decide⟩ : Fin 1069)) (faceAnchor (⟨263, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0264 : (⟨264, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨264, by decide⟩ : Fin 1069)) (faceAnchor (⟨264, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0265 : (⟨265, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨265, by decide⟩ : Fin 1069)) (faceAnchor (⟨265, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0266 : (⟨266, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨266, by decide⟩ : Fin 1069)) (faceAnchor (⟨266, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0267 : (⟨267, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨267, by decide⟩ : Fin 1069)) (faceAnchor (⟨267, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0268 : (⟨268, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨268, by decide⟩ : Fin 1069)) (faceAnchor (⟨268, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0269 : (⟨269, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨269, by decide⟩ : Fin 1069)) (faceAnchor (⟨269, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0270 : (⟨270, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨270, by decide⟩ : Fin 1069)) (faceAnchor (⟨270, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0271 : (⟨271, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨271, by decide⟩ : Fin 1069)) (faceAnchor (⟨271, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0272 : (⟨272, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨272, by decide⟩ : Fin 1069)) (faceAnchor (⟨272, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0273 : (⟨273, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨273, by decide⟩ : Fin 1069)) (faceAnchor (⟨273, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0274 : (⟨274, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨274, by decide⟩ : Fin 1069)) (faceAnchor (⟨274, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0275 : (⟨275, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨275, by decide⟩ : Fin 1069)) (faceAnchor (⟨275, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0276 : (⟨276, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨276, by decide⟩ : Fin 1069)) (faceAnchor (⟨276, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0277 : (⟨277, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨277, by decide⟩ : Fin 1069)) (faceAnchor (⟨277, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0278 : (⟨278, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨278, by decide⟩ : Fin 1069)) (faceAnchor (⟨278, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0279 : (⟨279, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨279, by decide⟩ : Fin 1069)) (faceAnchor (⟨279, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0280 : (⟨280, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨280, by decide⟩ : Fin 1069)) (faceAnchor (⟨280, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0281 : (⟨281, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨281, by decide⟩ : Fin 1069)) (faceAnchor (⟨281, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0282 : (⟨282, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨282, by decide⟩ : Fin 1069)) (faceAnchor (⟨282, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0283 : (⟨283, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨283, by decide⟩ : Fin 1069)) (faceAnchor (⟨283, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0284 : (⟨284, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨284, by decide⟩ : Fin 1069)) (faceAnchor (⟨284, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0285 : (⟨285, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨285, by decide⟩ : Fin 1069)) (faceAnchor (⟨285, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0286 : (⟨286, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨286, by decide⟩ : Fin 1069)) (faceAnchor (⟨286, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0287 : (⟨287, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨287, by decide⟩ : Fin 1069)) (faceAnchor (⟨287, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0288 : (⟨288, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨288, by decide⟩ : Fin 1069)) (faceAnchor (⟨288, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0289 : (⟨289, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨289, by decide⟩ : Fin 1069)) (faceAnchor (⟨289, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0290 : (⟨290, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨290, by decide⟩ : Fin 1069)) (faceAnchor (⟨290, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0291 : (⟨291, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨291, by decide⟩ : Fin 1069)) (faceAnchor (⟨291, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0292 : (⟨292, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨292, by decide⟩ : Fin 1069)) (faceAnchor (⟨292, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0293 : (⟨293, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨293, by decide⟩ : Fin 1069)) (faceAnchor (⟨293, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0294 : (⟨294, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨294, by decide⟩ : Fin 1069)) (faceAnchor (⟨294, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0295 : (⟨295, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨295, by decide⟩ : Fin 1069)) (faceAnchor (⟨295, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0296 : (⟨296, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨296, by decide⟩ : Fin 1069)) (faceAnchor (⟨296, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0297 : (⟨297, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨297, by decide⟩ : Fin 1069)) (faceAnchor (⟨297, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0298 : (⟨298, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨298, by decide⟩ : Fin 1069)) (faceAnchor (⟨298, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0299 : (⟨299, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨299, by decide⟩ : Fin 1069)) (faceAnchor (⟨299, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0300 : (⟨300, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨300, by decide⟩ : Fin 1069)) (faceAnchor (⟨300, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0301 : (⟨301, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨301, by decide⟩ : Fin 1069)) (faceAnchor (⟨301, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0302 : (⟨302, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨302, by decide⟩ : Fin 1069)) (faceAnchor (⟨302, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0303 : (⟨303, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨303, by decide⟩ : Fin 1069)) (faceAnchor (⟨303, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0304 : (⟨304, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨304, by decide⟩ : Fin 1069)) (faceAnchor (⟨304, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0305 : (⟨305, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨305, by decide⟩ : Fin 1069)) (faceAnchor (⟨305, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0306 : (⟨306, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨306, by decide⟩ : Fin 1069)) (faceAnchor (⟨306, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0307 : (⟨307, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨307, by decide⟩ : Fin 1069)) (faceAnchor (⟨307, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0308 : (⟨308, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨308, by decide⟩ : Fin 1069)) (faceAnchor (⟨308, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0309 : (⟨309, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨309, by decide⟩ : Fin 1069)) (faceAnchor (⟨309, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0310 : (⟨310, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨310, by decide⟩ : Fin 1069)) (faceAnchor (⟨310, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0311 : (⟨311, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨311, by decide⟩ : Fin 1069)) (faceAnchor (⟨311, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0312 : (⟨312, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨312, by decide⟩ : Fin 1069)) (faceAnchor (⟨312, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0313 : (⟨313, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨313, by decide⟩ : Fin 1069)) (faceAnchor (⟨313, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0314 : (⟨314, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨314, by decide⟩ : Fin 1069)) (faceAnchor (⟨314, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0315 : (⟨315, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨315, by decide⟩ : Fin 1069)) (faceAnchor (⟨315, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0316 : (⟨316, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨316, by decide⟩ : Fin 1069)) (faceAnchor (⟨316, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0317 : (⟨317, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨317, by decide⟩ : Fin 1069)) (faceAnchor (⟨317, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0318 : (⟨318, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨318, by decide⟩ : Fin 1069)) (faceAnchor (⟨318, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0319 : (⟨319, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨319, by decide⟩ : Fin 1069)) (faceAnchor (⟨319, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0320 : (⟨320, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨320, by decide⟩ : Fin 1069)) (faceAnchor (⟨320, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0321 : (⟨321, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨321, by decide⟩ : Fin 1069)) (faceAnchor (⟨321, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0322 : (⟨322, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨322, by decide⟩ : Fin 1069)) (faceAnchor (⟨322, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0323 : (⟨323, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨323, by decide⟩ : Fin 1069)) (faceAnchor (⟨323, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0324 : (⟨324, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨324, by decide⟩ : Fin 1069)) (faceAnchor (⟨324, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0325 : (⟨325, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨325, by decide⟩ : Fin 1069)) (faceAnchor (⟨325, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0326 : (⟨326, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨326, by decide⟩ : Fin 1069)) (faceAnchor (⟨326, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0327 : (⟨327, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨327, by decide⟩ : Fin 1069)) (faceAnchor (⟨327, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0328 : (⟨328, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨328, by decide⟩ : Fin 1069)) (faceAnchor (⟨328, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0329 : (⟨329, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨329, by decide⟩ : Fin 1069)) (faceAnchor (⟨329, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0330 : (⟨330, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨330, by decide⟩ : Fin 1069)) (faceAnchor (⟨330, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0331 : (⟨331, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨331, by decide⟩ : Fin 1069)) (faceAnchor (⟨331, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0332 : (⟨332, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨332, by decide⟩ : Fin 1069)) (faceAnchor (⟨332, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0333 : (⟨333, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨333, by decide⟩ : Fin 1069)) (faceAnchor (⟨333, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0334 : (⟨334, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨334, by decide⟩ : Fin 1069)) (faceAnchor (⟨334, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0335 : (⟨335, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨335, by decide⟩ : Fin 1069)) (faceAnchor (⟨335, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0336 : (⟨336, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨336, by decide⟩ : Fin 1069)) (faceAnchor (⟨336, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0337 : (⟨337, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨337, by decide⟩ : Fin 1069)) (faceAnchor (⟨337, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0338 : (⟨338, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨338, by decide⟩ : Fin 1069)) (faceAnchor (⟨338, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0339 : (⟨339, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨339, by decide⟩ : Fin 1069)) (faceAnchor (⟨339, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0340 : (⟨340, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨340, by decide⟩ : Fin 1069)) (faceAnchor (⟨340, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0341 : (⟨341, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨341, by decide⟩ : Fin 1069)) (faceAnchor (⟨341, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0342 : (⟨342, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨342, by decide⟩ : Fin 1069)) (faceAnchor (⟨342, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0343 : (⟨343, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨343, by decide⟩ : Fin 1069)) (faceAnchor (⟨343, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0344 : (⟨344, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨344, by decide⟩ : Fin 1069)) (faceAnchor (⟨344, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0345 : (⟨345, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨345, by decide⟩ : Fin 1069)) (faceAnchor (⟨345, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0346 : (⟨346, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨346, by decide⟩ : Fin 1069)) (faceAnchor (⟨346, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0347 : (⟨347, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨347, by decide⟩ : Fin 1069)) (faceAnchor (⟨347, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0348 : (⟨348, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨348, by decide⟩ : Fin 1069)) (faceAnchor (⟨348, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0349 : (⟨349, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨349, by decide⟩ : Fin 1069)) (faceAnchor (⟨349, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0350 : (⟨350, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨350, by decide⟩ : Fin 1069)) (faceAnchor (⟨350, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0351 : (⟨351, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨351, by decide⟩ : Fin 1069)) (faceAnchor (⟨351, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0352 : (⟨352, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨352, by decide⟩ : Fin 1069)) (faceAnchor (⟨352, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0353 : (⟨353, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨353, by decide⟩ : Fin 1069)) (faceAnchor (⟨353, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0354 : (⟨354, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨354, by decide⟩ : Fin 1069)) (faceAnchor (⟨354, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0355 : (⟨355, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨355, by decide⟩ : Fin 1069)) (faceAnchor (⟨355, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0356 : (⟨356, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨356, by decide⟩ : Fin 1069)) (faceAnchor (⟨356, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0357 : (⟨357, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨357, by decide⟩ : Fin 1069)) (faceAnchor (⟨357, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0358 : (⟨358, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨358, by decide⟩ : Fin 1069)) (faceAnchor (⟨358, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0359 : (⟨359, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨359, by decide⟩ : Fin 1069)) (faceAnchor (⟨359, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0360 : (⟨360, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨360, by decide⟩ : Fin 1069)) (faceAnchor (⟨360, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0361 : (⟨361, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨361, by decide⟩ : Fin 1069)) (faceAnchor (⟨361, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0362 : (⟨362, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨362, by decide⟩ : Fin 1069)) (faceAnchor (⟨362, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0363 : (⟨363, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨363, by decide⟩ : Fin 1069)) (faceAnchor (⟨363, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0364 : (⟨364, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨364, by decide⟩ : Fin 1069)) (faceAnchor (⟨364, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0365 : (⟨365, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨365, by decide⟩ : Fin 1069)) (faceAnchor (⟨365, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0366 : (⟨366, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨366, by decide⟩ : Fin 1069)) (faceAnchor (⟨366, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0367 : (⟨367, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨367, by decide⟩ : Fin 1069)) (faceAnchor (⟨367, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0368 : (⟨368, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨368, by decide⟩ : Fin 1069)) (faceAnchor (⟨368, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0369 : (⟨369, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨369, by decide⟩ : Fin 1069)) (faceAnchor (⟨369, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0370 : (⟨370, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨370, by decide⟩ : Fin 1069)) (faceAnchor (⟨370, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0371 : (⟨371, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨371, by decide⟩ : Fin 1069)) (faceAnchor (⟨371, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0372 : (⟨372, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨372, by decide⟩ : Fin 1069)) (faceAnchor (⟨372, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0373 : (⟨373, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨373, by decide⟩ : Fin 1069)) (faceAnchor (⟨373, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0374 : (⟨374, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨374, by decide⟩ : Fin 1069)) (faceAnchor (⟨374, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0375 : (⟨375, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨375, by decide⟩ : Fin 1069)) (faceAnchor (⟨375, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0376 : (⟨376, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨376, by decide⟩ : Fin 1069)) (faceAnchor (⟨376, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0377 : (⟨377, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨377, by decide⟩ : Fin 1069)) (faceAnchor (⟨377, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0378 : (⟨378, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨378, by decide⟩ : Fin 1069)) (faceAnchor (⟨378, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0379 : (⟨379, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨379, by decide⟩ : Fin 1069)) (faceAnchor (⟨379, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0380 : (⟨380, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨380, by decide⟩ : Fin 1069)) (faceAnchor (⟨380, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0381 : (⟨381, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨381, by decide⟩ : Fin 1069)) (faceAnchor (⟨381, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0382 : (⟨382, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨382, by decide⟩ : Fin 1069)) (faceAnchor (⟨382, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0383 : (⟨383, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨383, by decide⟩ : Fin 1069)) (faceAnchor (⟨383, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0384 : (⟨384, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨384, by decide⟩ : Fin 1069)) (faceAnchor (⟨384, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0385 : (⟨385, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨385, by decide⟩ : Fin 1069)) (faceAnchor (⟨385, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0386 : (⟨386, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨386, by decide⟩ : Fin 1069)) (faceAnchor (⟨386, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0387 : (⟨387, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨387, by decide⟩ : Fin 1069)) (faceAnchor (⟨387, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0388 : (⟨388, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨388, by decide⟩ : Fin 1069)) (faceAnchor (⟨388, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0389 : (⟨389, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨389, by decide⟩ : Fin 1069)) (faceAnchor (⟨389, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0390 : (⟨390, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨390, by decide⟩ : Fin 1069)) (faceAnchor (⟨390, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0391 : (⟨391, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨391, by decide⟩ : Fin 1069)) (faceAnchor (⟨391, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0392 : (⟨392, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨392, by decide⟩ : Fin 1069)) (faceAnchor (⟨392, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0393 : (⟨393, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨393, by decide⟩ : Fin 1069)) (faceAnchor (⟨393, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0394 : (⟨394, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨394, by decide⟩ : Fin 1069)) (faceAnchor (⟨394, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0395 : (⟨395, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨395, by decide⟩ : Fin 1069)) (faceAnchor (⟨395, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0396 : (⟨396, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨396, by decide⟩ : Fin 1069)) (faceAnchor (⟨396, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0397 : (⟨397, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨397, by decide⟩ : Fin 1069)) (faceAnchor (⟨397, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0398 : (⟨398, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨398, by decide⟩ : Fin 1069)) (faceAnchor (⟨398, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0399 : (⟨399, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨399, by decide⟩ : Fin 1069)) (faceAnchor (⟨399, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0400 : (⟨400, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨400, by decide⟩ : Fin 1069)) (faceAnchor (⟨400, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0401 : (⟨401, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨401, by decide⟩ : Fin 1069)) (faceAnchor (⟨401, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0402 : (⟨402, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨402, by decide⟩ : Fin 1069)) (faceAnchor (⟨402, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0403 : (⟨403, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨403, by decide⟩ : Fin 1069)) (faceAnchor (⟨403, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0404 : (⟨404, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨404, by decide⟩ : Fin 1069)) (faceAnchor (⟨404, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0405 : (⟨405, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨405, by decide⟩ : Fin 1069)) (faceAnchor (⟨405, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0406 : (⟨406, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨406, by decide⟩ : Fin 1069)) (faceAnchor (⟨406, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0407 : (⟨407, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨407, by decide⟩ : Fin 1069)) (faceAnchor (⟨407, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0408 : (⟨408, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨408, by decide⟩ : Fin 1069)) (faceAnchor (⟨408, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0409 : (⟨409, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨409, by decide⟩ : Fin 1069)) (faceAnchor (⟨409, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0410 : (⟨410, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨410, by decide⟩ : Fin 1069)) (faceAnchor (⟨410, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0411 : (⟨411, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨411, by decide⟩ : Fin 1069)) (faceAnchor (⟨411, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0412 : (⟨412, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨412, by decide⟩ : Fin 1069)) (faceAnchor (⟨412, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0413 : (⟨413, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨413, by decide⟩ : Fin 1069)) (faceAnchor (⟨413, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0414 : (⟨414, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨414, by decide⟩ : Fin 1069)) (faceAnchor (⟨414, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0415 : (⟨415, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨415, by decide⟩ : Fin 1069)) (faceAnchor (⟨415, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0416 : (⟨416, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨416, by decide⟩ : Fin 1069)) (faceAnchor (⟨416, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0417 : (⟨417, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨417, by decide⟩ : Fin 1069)) (faceAnchor (⟨417, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0418 : (⟨418, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨418, by decide⟩ : Fin 1069)) (faceAnchor (⟨418, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0419 : (⟨419, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨419, by decide⟩ : Fin 1069)) (faceAnchor (⟨419, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0420 : (⟨420, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨420, by decide⟩ : Fin 1069)) (faceAnchor (⟨420, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0421 : (⟨421, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨421, by decide⟩ : Fin 1069)) (faceAnchor (⟨421, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0422 : (⟨422, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨422, by decide⟩ : Fin 1069)) (faceAnchor (⟨422, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0423 : (⟨423, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨423, by decide⟩ : Fin 1069)) (faceAnchor (⟨423, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0424 : (⟨424, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨424, by decide⟩ : Fin 1069)) (faceAnchor (⟨424, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0425 : (⟨425, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨425, by decide⟩ : Fin 1069)) (faceAnchor (⟨425, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0426 : (⟨426, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨426, by decide⟩ : Fin 1069)) (faceAnchor (⟨426, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0427 : (⟨427, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨427, by decide⟩ : Fin 1069)) (faceAnchor (⟨427, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0428 : (⟨428, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨428, by decide⟩ : Fin 1069)) (faceAnchor (⟨428, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0429 : (⟨429, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨429, by decide⟩ : Fin 1069)) (faceAnchor (⟨429, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0430 : (⟨430, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨430, by decide⟩ : Fin 1069)) (faceAnchor (⟨430, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0431 : (⟨431, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨431, by decide⟩ : Fin 1069)) (faceAnchor (⟨431, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0432 : (⟨432, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨432, by decide⟩ : Fin 1069)) (faceAnchor (⟨432, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0433 : (⟨433, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨433, by decide⟩ : Fin 1069)) (faceAnchor (⟨433, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0434 : (⟨434, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨434, by decide⟩ : Fin 1069)) (faceAnchor (⟨434, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0435 : (⟨435, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨435, by decide⟩ : Fin 1069)) (faceAnchor (⟨435, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0436 : (⟨436, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨436, by decide⟩ : Fin 1069)) (faceAnchor (⟨436, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0437 : (⟨437, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨437, by decide⟩ : Fin 1069)) (faceAnchor (⟨437, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0438 : (⟨438, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨438, by decide⟩ : Fin 1069)) (faceAnchor (⟨438, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0439 : (⟨439, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨439, by decide⟩ : Fin 1069)) (faceAnchor (⟨439, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0440 : (⟨440, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨440, by decide⟩ : Fin 1069)) (faceAnchor (⟨440, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0441 : (⟨441, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨441, by decide⟩ : Fin 1069)) (faceAnchor (⟨441, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0442 : (⟨442, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨442, by decide⟩ : Fin 1069)) (faceAnchor (⟨442, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0443 : (⟨443, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨443, by decide⟩ : Fin 1069)) (faceAnchor (⟨443, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0444 : (⟨444, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨444, by decide⟩ : Fin 1069)) (faceAnchor (⟨444, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0445 : (⟨445, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨445, by decide⟩ : Fin 1069)) (faceAnchor (⟨445, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0446 : (⟨446, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨446, by decide⟩ : Fin 1069)) (faceAnchor (⟨446, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0447 : (⟨447, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨447, by decide⟩ : Fin 1069)) (faceAnchor (⟨447, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0448 : (⟨448, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨448, by decide⟩ : Fin 1069)) (faceAnchor (⟨448, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0449 : (⟨449, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨449, by decide⟩ : Fin 1069)) (faceAnchor (⟨449, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0450 : (⟨450, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨450, by decide⟩ : Fin 1069)) (faceAnchor (⟨450, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0451 : (⟨451, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨451, by decide⟩ : Fin 1069)) (faceAnchor (⟨451, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0452 : (⟨452, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨452, by decide⟩ : Fin 1069)) (faceAnchor (⟨452, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0453 : (⟨453, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨453, by decide⟩ : Fin 1069)) (faceAnchor (⟨453, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0454 : (⟨454, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨454, by decide⟩ : Fin 1069)) (faceAnchor (⟨454, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0455 : (⟨455, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨455, by decide⟩ : Fin 1069)) (faceAnchor (⟨455, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0456 : (⟨456, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨456, by decide⟩ : Fin 1069)) (faceAnchor (⟨456, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0457 : (⟨457, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨457, by decide⟩ : Fin 1069)) (faceAnchor (⟨457, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0458 : (⟨458, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨458, by decide⟩ : Fin 1069)) (faceAnchor (⟨458, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0459 : (⟨459, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨459, by decide⟩ : Fin 1069)) (faceAnchor (⟨459, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0460 : (⟨460, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨460, by decide⟩ : Fin 1069)) (faceAnchor (⟨460, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0461 : (⟨461, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨461, by decide⟩ : Fin 1069)) (faceAnchor (⟨461, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0462 : (⟨462, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨462, by decide⟩ : Fin 1069)) (faceAnchor (⟨462, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0463 : (⟨463, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨463, by decide⟩ : Fin 1069)) (faceAnchor (⟨463, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0464 : (⟨464, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨464, by decide⟩ : Fin 1069)) (faceAnchor (⟨464, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0465 : (⟨465, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨465, by decide⟩ : Fin 1069)) (faceAnchor (⟨465, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0466 : (⟨466, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨466, by decide⟩ : Fin 1069)) (faceAnchor (⟨466, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0467 : (⟨467, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨467, by decide⟩ : Fin 1069)) (faceAnchor (⟨467, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0468 : (⟨468, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨468, by decide⟩ : Fin 1069)) (faceAnchor (⟨468, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0469 : (⟨469, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨469, by decide⟩ : Fin 1069)) (faceAnchor (⟨469, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0470 : (⟨470, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨470, by decide⟩ : Fin 1069)) (faceAnchor (⟨470, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0471 : (⟨471, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨471, by decide⟩ : Fin 1069)) (faceAnchor (⟨471, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0472 : (⟨472, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨472, by decide⟩ : Fin 1069)) (faceAnchor (⟨472, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0473 : (⟨473, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨473, by decide⟩ : Fin 1069)) (faceAnchor (⟨473, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0474 : (⟨474, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨474, by decide⟩ : Fin 1069)) (faceAnchor (⟨474, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0475 : (⟨475, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨475, by decide⟩ : Fin 1069)) (faceAnchor (⟨475, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0476 : (⟨476, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨476, by decide⟩ : Fin 1069)) (faceAnchor (⟨476, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0477 : (⟨477, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨477, by decide⟩ : Fin 1069)) (faceAnchor (⟨477, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0478 : (⟨478, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨478, by decide⟩ : Fin 1069)) (faceAnchor (⟨478, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0479 : (⟨479, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨479, by decide⟩ : Fin 1069)) (faceAnchor (⟨479, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0480 : (⟨480, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨480, by decide⟩ : Fin 1069)) (faceAnchor (⟨480, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0481 : (⟨481, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨481, by decide⟩ : Fin 1069)) (faceAnchor (⟨481, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0482 : (⟨482, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨482, by decide⟩ : Fin 1069)) (faceAnchor (⟨482, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0483 : (⟨483, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨483, by decide⟩ : Fin 1069)) (faceAnchor (⟨483, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0484 : (⟨484, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨484, by decide⟩ : Fin 1069)) (faceAnchor (⟨484, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0485 : (⟨485, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨485, by decide⟩ : Fin 1069)) (faceAnchor (⟨485, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0486 : (⟨486, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨486, by decide⟩ : Fin 1069)) (faceAnchor (⟨486, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0487 : (⟨487, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨487, by decide⟩ : Fin 1069)) (faceAnchor (⟨487, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0488 : (⟨488, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨488, by decide⟩ : Fin 1069)) (faceAnchor (⟨488, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0489 : (⟨489, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨489, by decide⟩ : Fin 1069)) (faceAnchor (⟨489, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0490 : (⟨490, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨490, by decide⟩ : Fin 1069)) (faceAnchor (⟨490, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0491 : (⟨491, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨491, by decide⟩ : Fin 1069)) (faceAnchor (⟨491, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0492 : (⟨492, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨492, by decide⟩ : Fin 1069)) (faceAnchor (⟨492, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0493 : (⟨493, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨493, by decide⟩ : Fin 1069)) (faceAnchor (⟨493, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0494 : (⟨494, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨494, by decide⟩ : Fin 1069)) (faceAnchor (⟨494, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0495 : (⟨495, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨495, by decide⟩ : Fin 1069)) (faceAnchor (⟨495, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0496 : (⟨496, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨496, by decide⟩ : Fin 1069)) (faceAnchor (⟨496, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0497 : (⟨497, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨497, by decide⟩ : Fin 1069)) (faceAnchor (⟨497, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0498 : (⟨498, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨498, by decide⟩ : Fin 1069)) (faceAnchor (⟨498, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0499 : (⟨499, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨499, by decide⟩ : Fin 1069)) (faceAnchor (⟨499, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0500 : (⟨500, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨500, by decide⟩ : Fin 1069)) (faceAnchor (⟨500, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0501 : (⟨501, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨501, by decide⟩ : Fin 1069)) (faceAnchor (⟨501, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0502 : (⟨502, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨502, by decide⟩ : Fin 1069)) (faceAnchor (⟨502, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0503 : (⟨503, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨503, by decide⟩ : Fin 1069)) (faceAnchor (⟨503, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0504 : (⟨504, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨504, by decide⟩ : Fin 1069)) (faceAnchor (⟨504, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0505 : (⟨505, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨505, by decide⟩ : Fin 1069)) (faceAnchor (⟨505, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0506 : (⟨506, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨506, by decide⟩ : Fin 1069)) (faceAnchor (⟨506, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0507 : (⟨507, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨507, by decide⟩ : Fin 1069)) (faceAnchor (⟨507, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0508 : (⟨508, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨508, by decide⟩ : Fin 1069)) (faceAnchor (⟨508, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0509 : (⟨509, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨509, by decide⟩ : Fin 1069)) (faceAnchor (⟨509, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0510 : (⟨510, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨510, by decide⟩ : Fin 1069)) (faceAnchor (⟨510, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0511 : (⟨511, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨511, by decide⟩ : Fin 1069)) (faceAnchor (⟨511, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0512 : (⟨512, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨512, by decide⟩ : Fin 1069)) (faceAnchor (⟨512, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0513 : (⟨513, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨513, by decide⟩ : Fin 1069)) (faceAnchor (⟨513, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0514 : (⟨514, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨514, by decide⟩ : Fin 1069)) (faceAnchor (⟨514, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0515 : (⟨515, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨515, by decide⟩ : Fin 1069)) (faceAnchor (⟨515, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0516 : (⟨516, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨516, by decide⟩ : Fin 1069)) (faceAnchor (⟨516, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0517 : (⟨517, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨517, by decide⟩ : Fin 1069)) (faceAnchor (⟨517, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0518 : (⟨518, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨518, by decide⟩ : Fin 1069)) (faceAnchor (⟨518, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0519 : (⟨519, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨519, by decide⟩ : Fin 1069)) (faceAnchor (⟨519, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0520 : (⟨520, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨520, by decide⟩ : Fin 1069)) (faceAnchor (⟨520, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0521 : (⟨521, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨521, by decide⟩ : Fin 1069)) (faceAnchor (⟨521, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0522 : (⟨522, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨522, by decide⟩ : Fin 1069)) (faceAnchor (⟨522, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0523 : (⟨523, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨523, by decide⟩ : Fin 1069)) (faceAnchor (⟨523, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0524 : (⟨524, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨524, by decide⟩ : Fin 1069)) (faceAnchor (⟨524, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0525 : (⟨525, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨525, by decide⟩ : Fin 1069)) (faceAnchor (⟨525, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0526 : (⟨526, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨526, by decide⟩ : Fin 1069)) (faceAnchor (⟨526, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0527 : (⟨527, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨527, by decide⟩ : Fin 1069)) (faceAnchor (⟨527, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0528 : (⟨528, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨528, by decide⟩ : Fin 1069)) (faceAnchor (⟨528, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0529 : (⟨529, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨529, by decide⟩ : Fin 1069)) (faceAnchor (⟨529, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0530 : (⟨530, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨530, by decide⟩ : Fin 1069)) (faceAnchor (⟨530, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0531 : (⟨531, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨531, by decide⟩ : Fin 1069)) (faceAnchor (⟨531, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0532 : (⟨532, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨532, by decide⟩ : Fin 1069)) (faceAnchor (⟨532, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0533 : (⟨533, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨533, by decide⟩ : Fin 1069)) (faceAnchor (⟨533, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0534 : (⟨534, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨534, by decide⟩ : Fin 1069)) (faceAnchor (⟨534, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0535 : (⟨535, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨535, by decide⟩ : Fin 1069)) (faceAnchor (⟨535, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0536 : (⟨536, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨536, by decide⟩ : Fin 1069)) (faceAnchor (⟨536, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0537 : (⟨537, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨537, by decide⟩ : Fin 1069)) (faceAnchor (⟨537, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0538 : (⟨538, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨538, by decide⟩ : Fin 1069)) (faceAnchor (⟨538, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0539 : (⟨539, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨539, by decide⟩ : Fin 1069)) (faceAnchor (⟨539, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0540 : (⟨540, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨540, by decide⟩ : Fin 1069)) (faceAnchor (⟨540, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0541 : (⟨541, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨541, by decide⟩ : Fin 1069)) (faceAnchor (⟨541, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0542 : (⟨542, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨542, by decide⟩ : Fin 1069)) (faceAnchor (⟨542, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0543 : (⟨543, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨543, by decide⟩ : Fin 1069)) (faceAnchor (⟨543, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0544 : (⟨544, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨544, by decide⟩ : Fin 1069)) (faceAnchor (⟨544, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0545 : (⟨545, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨545, by decide⟩ : Fin 1069)) (faceAnchor (⟨545, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0546 : (⟨546, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨546, by decide⟩ : Fin 1069)) (faceAnchor (⟨546, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0547 : (⟨547, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨547, by decide⟩ : Fin 1069)) (faceAnchor (⟨547, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0548 : (⟨548, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨548, by decide⟩ : Fin 1069)) (faceAnchor (⟨548, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0549 : (⟨549, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨549, by decide⟩ : Fin 1069)) (faceAnchor (⟨549, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0550 : (⟨550, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨550, by decide⟩ : Fin 1069)) (faceAnchor (⟨550, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0551 : (⟨551, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨551, by decide⟩ : Fin 1069)) (faceAnchor (⟨551, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0552 : (⟨552, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨552, by decide⟩ : Fin 1069)) (faceAnchor (⟨552, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0553 : (⟨553, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨553, by decide⟩ : Fin 1069)) (faceAnchor (⟨553, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0554 : (⟨554, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨554, by decide⟩ : Fin 1069)) (faceAnchor (⟨554, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0555 : (⟨555, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨555, by decide⟩ : Fin 1069)) (faceAnchor (⟨555, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0556 : (⟨556, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨556, by decide⟩ : Fin 1069)) (faceAnchor (⟨556, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0557 : (⟨557, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨557, by decide⟩ : Fin 1069)) (faceAnchor (⟨557, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0558 : (⟨558, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨558, by decide⟩ : Fin 1069)) (faceAnchor (⟨558, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0559 : (⟨559, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨559, by decide⟩ : Fin 1069)) (faceAnchor (⟨559, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0560 : (⟨560, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨560, by decide⟩ : Fin 1069)) (faceAnchor (⟨560, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0561 : (⟨561, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨561, by decide⟩ : Fin 1069)) (faceAnchor (⟨561, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0562 : (⟨562, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨562, by decide⟩ : Fin 1069)) (faceAnchor (⟨562, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0563 : (⟨563, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨563, by decide⟩ : Fin 1069)) (faceAnchor (⟨563, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0564 : (⟨564, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨564, by decide⟩ : Fin 1069)) (faceAnchor (⟨564, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0565 : (⟨565, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨565, by decide⟩ : Fin 1069)) (faceAnchor (⟨565, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0566 : (⟨566, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨566, by decide⟩ : Fin 1069)) (faceAnchor (⟨566, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0567 : (⟨567, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨567, by decide⟩ : Fin 1069)) (faceAnchor (⟨567, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0568 : (⟨568, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨568, by decide⟩ : Fin 1069)) (faceAnchor (⟨568, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0569 : (⟨569, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨569, by decide⟩ : Fin 1069)) (faceAnchor (⟨569, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0570 : (⟨570, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨570, by decide⟩ : Fin 1069)) (faceAnchor (⟨570, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0571 : (⟨571, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨571, by decide⟩ : Fin 1069)) (faceAnchor (⟨571, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0572 : (⟨572, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨572, by decide⟩ : Fin 1069)) (faceAnchor (⟨572, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0573 : (⟨573, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨573, by decide⟩ : Fin 1069)) (faceAnchor (⟨573, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0574 : (⟨574, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨574, by decide⟩ : Fin 1069)) (faceAnchor (⟨574, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0575 : (⟨575, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨575, by decide⟩ : Fin 1069)) (faceAnchor (⟨575, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0576 : (⟨576, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨576, by decide⟩ : Fin 1069)) (faceAnchor (⟨576, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0577 : (⟨577, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨577, by decide⟩ : Fin 1069)) (faceAnchor (⟨577, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0578 : (⟨578, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨578, by decide⟩ : Fin 1069)) (faceAnchor (⟨578, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0579 : (⟨579, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨579, by decide⟩ : Fin 1069)) (faceAnchor (⟨579, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0580 : (⟨580, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨580, by decide⟩ : Fin 1069)) (faceAnchor (⟨580, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0581 : (⟨581, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨581, by decide⟩ : Fin 1069)) (faceAnchor (⟨581, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0582 : (⟨582, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨582, by decide⟩ : Fin 1069)) (faceAnchor (⟨582, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0583 : (⟨583, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨583, by decide⟩ : Fin 1069)) (faceAnchor (⟨583, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0584 : (⟨584, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨584, by decide⟩ : Fin 1069)) (faceAnchor (⟨584, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0585 : (⟨585, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨585, by decide⟩ : Fin 1069)) (faceAnchor (⟨585, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0586 : (⟨586, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨586, by decide⟩ : Fin 1069)) (faceAnchor (⟨586, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0587 : (⟨587, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨587, by decide⟩ : Fin 1069)) (faceAnchor (⟨587, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0588 : (⟨588, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨588, by decide⟩ : Fin 1069)) (faceAnchor (⟨588, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0589 : (⟨589, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨589, by decide⟩ : Fin 1069)) (faceAnchor (⟨589, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0590 : (⟨590, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨590, by decide⟩ : Fin 1069)) (faceAnchor (⟨590, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0591 : (⟨591, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨591, by decide⟩ : Fin 1069)) (faceAnchor (⟨591, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0592 : (⟨592, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨592, by decide⟩ : Fin 1069)) (faceAnchor (⟨592, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0593 : (⟨593, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨593, by decide⟩ : Fin 1069)) (faceAnchor (⟨593, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0594 : (⟨594, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨594, by decide⟩ : Fin 1069)) (faceAnchor (⟨594, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0595 : (⟨595, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨595, by decide⟩ : Fin 1069)) (faceAnchor (⟨595, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0596 : (⟨596, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨596, by decide⟩ : Fin 1069)) (faceAnchor (⟨596, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0597 : (⟨597, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨597, by decide⟩ : Fin 1069)) (faceAnchor (⟨597, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0598 : (⟨598, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨598, by decide⟩ : Fin 1069)) (faceAnchor (⟨598, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0599 : (⟨599, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨599, by decide⟩ : Fin 1069)) (faceAnchor (⟨599, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0600 : (⟨600, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨600, by decide⟩ : Fin 1069)) (faceAnchor (⟨600, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0601 : (⟨601, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨601, by decide⟩ : Fin 1069)) (faceAnchor (⟨601, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0602 : (⟨602, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨602, by decide⟩ : Fin 1069)) (faceAnchor (⟨602, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0603 : (⟨603, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨603, by decide⟩ : Fin 1069)) (faceAnchor (⟨603, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0604 : (⟨604, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨604, by decide⟩ : Fin 1069)) (faceAnchor (⟨604, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0605 : (⟨605, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨605, by decide⟩ : Fin 1069)) (faceAnchor (⟨605, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0606 : (⟨606, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨606, by decide⟩ : Fin 1069)) (faceAnchor (⟨606, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0607 : (⟨607, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨607, by decide⟩ : Fin 1069)) (faceAnchor (⟨607, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0608 : (⟨608, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨608, by decide⟩ : Fin 1069)) (faceAnchor (⟨608, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0609 : (⟨609, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨609, by decide⟩ : Fin 1069)) (faceAnchor (⟨609, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0610 : (⟨610, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨610, by decide⟩ : Fin 1069)) (faceAnchor (⟨610, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0611 : (⟨611, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨611, by decide⟩ : Fin 1069)) (faceAnchor (⟨611, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0612 : (⟨612, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨612, by decide⟩ : Fin 1069)) (faceAnchor (⟨612, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0613 : (⟨613, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨613, by decide⟩ : Fin 1069)) (faceAnchor (⟨613, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0614 : (⟨614, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨614, by decide⟩ : Fin 1069)) (faceAnchor (⟨614, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0615 : (⟨615, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨615, by decide⟩ : Fin 1069)) (faceAnchor (⟨615, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0616 : (⟨616, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨616, by decide⟩ : Fin 1069)) (faceAnchor (⟨616, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0617 : (⟨617, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨617, by decide⟩ : Fin 1069)) (faceAnchor (⟨617, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0618 : (⟨618, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨618, by decide⟩ : Fin 1069)) (faceAnchor (⟨618, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0619 : (⟨619, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨619, by decide⟩ : Fin 1069)) (faceAnchor (⟨619, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0620 : (⟨620, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨620, by decide⟩ : Fin 1069)) (faceAnchor (⟨620, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0621 : (⟨621, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨621, by decide⟩ : Fin 1069)) (faceAnchor (⟨621, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0622 : (⟨622, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨622, by decide⟩ : Fin 1069)) (faceAnchor (⟨622, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0623 : (⟨623, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨623, by decide⟩ : Fin 1069)) (faceAnchor (⟨623, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0624 : (⟨624, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨624, by decide⟩ : Fin 1069)) (faceAnchor (⟨624, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0625 : (⟨625, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨625, by decide⟩ : Fin 1069)) (faceAnchor (⟨625, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0626 : (⟨626, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨626, by decide⟩ : Fin 1069)) (faceAnchor (⟨626, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0627 : (⟨627, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨627, by decide⟩ : Fin 1069)) (faceAnchor (⟨627, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0628 : (⟨628, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨628, by decide⟩ : Fin 1069)) (faceAnchor (⟨628, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0629 : (⟨629, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨629, by decide⟩ : Fin 1069)) (faceAnchor (⟨629, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0630 : (⟨630, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨630, by decide⟩ : Fin 1069)) (faceAnchor (⟨630, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0631 : (⟨631, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨631, by decide⟩ : Fin 1069)) (faceAnchor (⟨631, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0632 : (⟨632, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨632, by decide⟩ : Fin 1069)) (faceAnchor (⟨632, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0633 : (⟨633, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨633, by decide⟩ : Fin 1069)) (faceAnchor (⟨633, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0634 : (⟨634, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨634, by decide⟩ : Fin 1069)) (faceAnchor (⟨634, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0635 : (⟨635, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨635, by decide⟩ : Fin 1069)) (faceAnchor (⟨635, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0636 : (⟨636, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨636, by decide⟩ : Fin 1069)) (faceAnchor (⟨636, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0637 : (⟨637, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨637, by decide⟩ : Fin 1069)) (faceAnchor (⟨637, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0638 : (⟨638, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨638, by decide⟩ : Fin 1069)) (faceAnchor (⟨638, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0639 : (⟨639, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨639, by decide⟩ : Fin 1069)) (faceAnchor (⟨639, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0640 : (⟨640, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨640, by decide⟩ : Fin 1069)) (faceAnchor (⟨640, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0641 : (⟨641, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨641, by decide⟩ : Fin 1069)) (faceAnchor (⟨641, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0642 : (⟨642, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨642, by decide⟩ : Fin 1069)) (faceAnchor (⟨642, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0643 : (⟨643, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨643, by decide⟩ : Fin 1069)) (faceAnchor (⟨643, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0644 : (⟨644, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨644, by decide⟩ : Fin 1069)) (faceAnchor (⟨644, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0645 : (⟨645, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨645, by decide⟩ : Fin 1069)) (faceAnchor (⟨645, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0646 : (⟨646, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨646, by decide⟩ : Fin 1069)) (faceAnchor (⟨646, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0647 : (⟨647, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨647, by decide⟩ : Fin 1069)) (faceAnchor (⟨647, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0648 : (⟨648, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨648, by decide⟩ : Fin 1069)) (faceAnchor (⟨648, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0649 : (⟨649, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨649, by decide⟩ : Fin 1069)) (faceAnchor (⟨649, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0650 : (⟨650, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨650, by decide⟩ : Fin 1069)) (faceAnchor (⟨650, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0651 : (⟨651, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨651, by decide⟩ : Fin 1069)) (faceAnchor (⟨651, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0652 : (⟨652, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨652, by decide⟩ : Fin 1069)) (faceAnchor (⟨652, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0653 : (⟨653, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨653, by decide⟩ : Fin 1069)) (faceAnchor (⟨653, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0654 : (⟨654, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨654, by decide⟩ : Fin 1069)) (faceAnchor (⟨654, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0655 : (⟨655, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨655, by decide⟩ : Fin 1069)) (faceAnchor (⟨655, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0656 : (⟨656, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨656, by decide⟩ : Fin 1069)) (faceAnchor (⟨656, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0657 : (⟨657, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨657, by decide⟩ : Fin 1069)) (faceAnchor (⟨657, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0658 : (⟨658, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨658, by decide⟩ : Fin 1069)) (faceAnchor (⟨658, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0659 : (⟨659, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨659, by decide⟩ : Fin 1069)) (faceAnchor (⟨659, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0660 : (⟨660, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨660, by decide⟩ : Fin 1069)) (faceAnchor (⟨660, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0661 : (⟨661, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨661, by decide⟩ : Fin 1069)) (faceAnchor (⟨661, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0662 : (⟨662, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨662, by decide⟩ : Fin 1069)) (faceAnchor (⟨662, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0663 : (⟨663, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨663, by decide⟩ : Fin 1069)) (faceAnchor (⟨663, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0664 : (⟨664, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨664, by decide⟩ : Fin 1069)) (faceAnchor (⟨664, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0665 : (⟨665, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨665, by decide⟩ : Fin 1069)) (faceAnchor (⟨665, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0666 : (⟨666, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨666, by decide⟩ : Fin 1069)) (faceAnchor (⟨666, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0667 : (⟨667, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨667, by decide⟩ : Fin 1069)) (faceAnchor (⟨667, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0668 : (⟨668, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨668, by decide⟩ : Fin 1069)) (faceAnchor (⟨668, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0669 : (⟨669, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨669, by decide⟩ : Fin 1069)) (faceAnchor (⟨669, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0670 : (⟨670, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨670, by decide⟩ : Fin 1069)) (faceAnchor (⟨670, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0671 : (⟨671, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨671, by decide⟩ : Fin 1069)) (faceAnchor (⟨671, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0672 : (⟨672, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨672, by decide⟩ : Fin 1069)) (faceAnchor (⟨672, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0673 : (⟨673, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨673, by decide⟩ : Fin 1069)) (faceAnchor (⟨673, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0674 : (⟨674, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨674, by decide⟩ : Fin 1069)) (faceAnchor (⟨674, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0675 : (⟨675, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨675, by decide⟩ : Fin 1069)) (faceAnchor (⟨675, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0676 : (⟨676, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨676, by decide⟩ : Fin 1069)) (faceAnchor (⟨676, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0677 : (⟨677, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨677, by decide⟩ : Fin 1069)) (faceAnchor (⟨677, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0678 : (⟨678, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨678, by decide⟩ : Fin 1069)) (faceAnchor (⟨678, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0679 : (⟨679, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨679, by decide⟩ : Fin 1069)) (faceAnchor (⟨679, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0680 : (⟨680, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨680, by decide⟩ : Fin 1069)) (faceAnchor (⟨680, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0681 : (⟨681, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨681, by decide⟩ : Fin 1069)) (faceAnchor (⟨681, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0682 : (⟨682, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨682, by decide⟩ : Fin 1069)) (faceAnchor (⟨682, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0683 : (⟨683, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨683, by decide⟩ : Fin 1069)) (faceAnchor (⟨683, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0684 : (⟨684, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨684, by decide⟩ : Fin 1069)) (faceAnchor (⟨684, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0685 : (⟨685, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨685, by decide⟩ : Fin 1069)) (faceAnchor (⟨685, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0686 : (⟨686, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨686, by decide⟩ : Fin 1069)) (faceAnchor (⟨686, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0687 : (⟨687, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨687, by decide⟩ : Fin 1069)) (faceAnchor (⟨687, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0688 : (⟨688, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨688, by decide⟩ : Fin 1069)) (faceAnchor (⟨688, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0689 : (⟨689, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨689, by decide⟩ : Fin 1069)) (faceAnchor (⟨689, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0690 : (⟨690, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨690, by decide⟩ : Fin 1069)) (faceAnchor (⟨690, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0691 : (⟨691, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨691, by decide⟩ : Fin 1069)) (faceAnchor (⟨691, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0692 : (⟨692, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨692, by decide⟩ : Fin 1069)) (faceAnchor (⟨692, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0693 : (⟨693, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨693, by decide⟩ : Fin 1069)) (faceAnchor (⟨693, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0694 : (⟨694, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨694, by decide⟩ : Fin 1069)) (faceAnchor (⟨694, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0695 : (⟨695, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨695, by decide⟩ : Fin 1069)) (faceAnchor (⟨695, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0696 : (⟨696, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨696, by decide⟩ : Fin 1069)) (faceAnchor (⟨696, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0697 : (⟨697, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨697, by decide⟩ : Fin 1069)) (faceAnchor (⟨697, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0698 : (⟨698, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨698, by decide⟩ : Fin 1069)) (faceAnchor (⟨698, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0699 : (⟨699, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨699, by decide⟩ : Fin 1069)) (faceAnchor (⟨699, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0700 : (⟨700, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨700, by decide⟩ : Fin 1069)) (faceAnchor (⟨700, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0701 : (⟨701, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨701, by decide⟩ : Fin 1069)) (faceAnchor (⟨701, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0702 : (⟨702, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨702, by decide⟩ : Fin 1069)) (faceAnchor (⟨702, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0703 : (⟨703, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨703, by decide⟩ : Fin 1069)) (faceAnchor (⟨703, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0704 : (⟨704, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨704, by decide⟩ : Fin 1069)) (faceAnchor (⟨704, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0705 : (⟨705, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨705, by decide⟩ : Fin 1069)) (faceAnchor (⟨705, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0706 : (⟨706, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨706, by decide⟩ : Fin 1069)) (faceAnchor (⟨706, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0707 : (⟨707, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨707, by decide⟩ : Fin 1069)) (faceAnchor (⟨707, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0708 : (⟨708, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨708, by decide⟩ : Fin 1069)) (faceAnchor (⟨708, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0709 : (⟨709, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨709, by decide⟩ : Fin 1069)) (faceAnchor (⟨709, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0710 : (⟨710, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨710, by decide⟩ : Fin 1069)) (faceAnchor (⟨710, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0711 : (⟨711, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨711, by decide⟩ : Fin 1069)) (faceAnchor (⟨711, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0712 : (⟨712, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨712, by decide⟩ : Fin 1069)) (faceAnchor (⟨712, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0713 : (⟨713, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨713, by decide⟩ : Fin 1069)) (faceAnchor (⟨713, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0714 : (⟨714, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨714, by decide⟩ : Fin 1069)) (faceAnchor (⟨714, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0715 : (⟨715, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨715, by decide⟩ : Fin 1069)) (faceAnchor (⟨715, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0716 : (⟨716, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨716, by decide⟩ : Fin 1069)) (faceAnchor (⟨716, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0717 : (⟨717, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨717, by decide⟩ : Fin 1069)) (faceAnchor (⟨717, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0718 : (⟨718, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨718, by decide⟩ : Fin 1069)) (faceAnchor (⟨718, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0719 : (⟨719, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨719, by decide⟩ : Fin 1069)) (faceAnchor (⟨719, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0720 : (⟨720, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨720, by decide⟩ : Fin 1069)) (faceAnchor (⟨720, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0721 : (⟨721, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨721, by decide⟩ : Fin 1069)) (faceAnchor (⟨721, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0722 : (⟨722, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨722, by decide⟩ : Fin 1069)) (faceAnchor (⟨722, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0723 : (⟨723, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨723, by decide⟩ : Fin 1069)) (faceAnchor (⟨723, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0724 : (⟨724, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨724, by decide⟩ : Fin 1069)) (faceAnchor (⟨724, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0725 : (⟨725, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨725, by decide⟩ : Fin 1069)) (faceAnchor (⟨725, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0726 : (⟨726, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨726, by decide⟩ : Fin 1069)) (faceAnchor (⟨726, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0727 : (⟨727, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨727, by decide⟩ : Fin 1069)) (faceAnchor (⟨727, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0728 : (⟨728, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨728, by decide⟩ : Fin 1069)) (faceAnchor (⟨728, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0729 : (⟨729, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨729, by decide⟩ : Fin 1069)) (faceAnchor (⟨729, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0730 : (⟨730, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨730, by decide⟩ : Fin 1069)) (faceAnchor (⟨730, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0731 : (⟨731, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨731, by decide⟩ : Fin 1069)) (faceAnchor (⟨731, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0732 : (⟨732, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨732, by decide⟩ : Fin 1069)) (faceAnchor (⟨732, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0733 : (⟨733, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨733, by decide⟩ : Fin 1069)) (faceAnchor (⟨733, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0734 : (⟨734, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨734, by decide⟩ : Fin 1069)) (faceAnchor (⟨734, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0735 : (⟨735, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨735, by decide⟩ : Fin 1069)) (faceAnchor (⟨735, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0736 : (⟨736, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨736, by decide⟩ : Fin 1069)) (faceAnchor (⟨736, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0737 : (⟨737, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨737, by decide⟩ : Fin 1069)) (faceAnchor (⟨737, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0738 : (⟨738, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨738, by decide⟩ : Fin 1069)) (faceAnchor (⟨738, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0739 : (⟨739, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨739, by decide⟩ : Fin 1069)) (faceAnchor (⟨739, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0740 : (⟨740, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨740, by decide⟩ : Fin 1069)) (faceAnchor (⟨740, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0741 : (⟨741, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨741, by decide⟩ : Fin 1069)) (faceAnchor (⟨741, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0742 : (⟨742, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨742, by decide⟩ : Fin 1069)) (faceAnchor (⟨742, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0743 : (⟨743, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨743, by decide⟩ : Fin 1069)) (faceAnchor (⟨743, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0744 : (⟨744, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨744, by decide⟩ : Fin 1069)) (faceAnchor (⟨744, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0745 : (⟨745, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨745, by decide⟩ : Fin 1069)) (faceAnchor (⟨745, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0746 : (⟨746, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨746, by decide⟩ : Fin 1069)) (faceAnchor (⟨746, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0747 : (⟨747, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨747, by decide⟩ : Fin 1069)) (faceAnchor (⟨747, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0748 : (⟨748, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨748, by decide⟩ : Fin 1069)) (faceAnchor (⟨748, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0749 : (⟨749, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨749, by decide⟩ : Fin 1069)) (faceAnchor (⟨749, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0750 : (⟨750, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨750, by decide⟩ : Fin 1069)) (faceAnchor (⟨750, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0751 : (⟨751, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨751, by decide⟩ : Fin 1069)) (faceAnchor (⟨751, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0752 : (⟨752, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨752, by decide⟩ : Fin 1069)) (faceAnchor (⟨752, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0753 : (⟨753, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨753, by decide⟩ : Fin 1069)) (faceAnchor (⟨753, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0754 : (⟨754, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨754, by decide⟩ : Fin 1069)) (faceAnchor (⟨754, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0755 : (⟨755, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨755, by decide⟩ : Fin 1069)) (faceAnchor (⟨755, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0756 : (⟨756, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨756, by decide⟩ : Fin 1069)) (faceAnchor (⟨756, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0757 : (⟨757, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨757, by decide⟩ : Fin 1069)) (faceAnchor (⟨757, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0758 : (⟨758, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨758, by decide⟩ : Fin 1069)) (faceAnchor (⟨758, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0759 : (⟨759, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨759, by decide⟩ : Fin 1069)) (faceAnchor (⟨759, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0760 : (⟨760, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨760, by decide⟩ : Fin 1069)) (faceAnchor (⟨760, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0761 : (⟨761, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨761, by decide⟩ : Fin 1069)) (faceAnchor (⟨761, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0762 : (⟨762, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨762, by decide⟩ : Fin 1069)) (faceAnchor (⟨762, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0763 : (⟨763, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨763, by decide⟩ : Fin 1069)) (faceAnchor (⟨763, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0764 : (⟨764, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨764, by decide⟩ : Fin 1069)) (faceAnchor (⟨764, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0765 : (⟨765, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨765, by decide⟩ : Fin 1069)) (faceAnchor (⟨765, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0766 : (⟨766, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨766, by decide⟩ : Fin 1069)) (faceAnchor (⟨766, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0767 : (⟨767, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨767, by decide⟩ : Fin 1069)) (faceAnchor (⟨767, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0768 : (⟨768, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨768, by decide⟩ : Fin 1069)) (faceAnchor (⟨768, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0769 : (⟨769, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨769, by decide⟩ : Fin 1069)) (faceAnchor (⟨769, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0770 : (⟨770, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨770, by decide⟩ : Fin 1069)) (faceAnchor (⟨770, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0771 : (⟨771, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨771, by decide⟩ : Fin 1069)) (faceAnchor (⟨771, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0772 : (⟨772, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨772, by decide⟩ : Fin 1069)) (faceAnchor (⟨772, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0773 : (⟨773, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨773, by decide⟩ : Fin 1069)) (faceAnchor (⟨773, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0774 : (⟨774, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨774, by decide⟩ : Fin 1069)) (faceAnchor (⟨774, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0775 : (⟨775, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨775, by decide⟩ : Fin 1069)) (faceAnchor (⟨775, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0776 : (⟨776, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨776, by decide⟩ : Fin 1069)) (faceAnchor (⟨776, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0777 : (⟨777, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨777, by decide⟩ : Fin 1069)) (faceAnchor (⟨777, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0778 : (⟨778, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨778, by decide⟩ : Fin 1069)) (faceAnchor (⟨778, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0779 : (⟨779, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨779, by decide⟩ : Fin 1069)) (faceAnchor (⟨779, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0780 : (⟨780, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨780, by decide⟩ : Fin 1069)) (faceAnchor (⟨780, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0781 : (⟨781, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨781, by decide⟩ : Fin 1069)) (faceAnchor (⟨781, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0782 : (⟨782, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨782, by decide⟩ : Fin 1069)) (faceAnchor (⟨782, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0783 : (⟨783, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨783, by decide⟩ : Fin 1069)) (faceAnchor (⟨783, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0784 : (⟨784, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨784, by decide⟩ : Fin 1069)) (faceAnchor (⟨784, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0785 : (⟨785, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨785, by decide⟩ : Fin 1069)) (faceAnchor (⟨785, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0786 : (⟨786, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨786, by decide⟩ : Fin 1069)) (faceAnchor (⟨786, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0787 : (⟨787, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨787, by decide⟩ : Fin 1069)) (faceAnchor (⟨787, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0788 : (⟨788, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨788, by decide⟩ : Fin 1069)) (faceAnchor (⟨788, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0789 : (⟨789, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨789, by decide⟩ : Fin 1069)) (faceAnchor (⟨789, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0790 : (⟨790, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨790, by decide⟩ : Fin 1069)) (faceAnchor (⟨790, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0791 : (⟨791, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨791, by decide⟩ : Fin 1069)) (faceAnchor (⟨791, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0792 : (⟨792, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨792, by decide⟩ : Fin 1069)) (faceAnchor (⟨792, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0793 : (⟨793, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨793, by decide⟩ : Fin 1069)) (faceAnchor (⟨793, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0794 : (⟨794, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨794, by decide⟩ : Fin 1069)) (faceAnchor (⟨794, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0795 : (⟨795, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨795, by decide⟩ : Fin 1069)) (faceAnchor (⟨795, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0796 : (⟨796, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨796, by decide⟩ : Fin 1069)) (faceAnchor (⟨796, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0797 : (⟨797, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨797, by decide⟩ : Fin 1069)) (faceAnchor (⟨797, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0798 : (⟨798, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨798, by decide⟩ : Fin 1069)) (faceAnchor (⟨798, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0799 : (⟨799, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨799, by decide⟩ : Fin 1069)) (faceAnchor (⟨799, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0800 : (⟨800, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨800, by decide⟩ : Fin 1069)) (faceAnchor (⟨800, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0801 : (⟨801, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨801, by decide⟩ : Fin 1069)) (faceAnchor (⟨801, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0802 : (⟨802, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨802, by decide⟩ : Fin 1069)) (faceAnchor (⟨802, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0803 : (⟨803, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨803, by decide⟩ : Fin 1069)) (faceAnchor (⟨803, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0804 : (⟨804, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨804, by decide⟩ : Fin 1069)) (faceAnchor (⟨804, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0805 : (⟨805, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨805, by decide⟩ : Fin 1069)) (faceAnchor (⟨805, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0806 : (⟨806, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨806, by decide⟩ : Fin 1069)) (faceAnchor (⟨806, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0807 : (⟨807, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨807, by decide⟩ : Fin 1069)) (faceAnchor (⟨807, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0808 : (⟨808, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨808, by decide⟩ : Fin 1069)) (faceAnchor (⟨808, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0809 : (⟨809, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨809, by decide⟩ : Fin 1069)) (faceAnchor (⟨809, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0810 : (⟨810, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨810, by decide⟩ : Fin 1069)) (faceAnchor (⟨810, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0811 : (⟨811, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨811, by decide⟩ : Fin 1069)) (faceAnchor (⟨811, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0812 : (⟨812, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨812, by decide⟩ : Fin 1069)) (faceAnchor (⟨812, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0813 : (⟨813, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨813, by decide⟩ : Fin 1069)) (faceAnchor (⟨813, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0814 : (⟨814, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨814, by decide⟩ : Fin 1069)) (faceAnchor (⟨814, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0815 : (⟨815, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨815, by decide⟩ : Fin 1069)) (faceAnchor (⟨815, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0816 : (⟨816, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨816, by decide⟩ : Fin 1069)) (faceAnchor (⟨816, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0817 : (⟨817, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨817, by decide⟩ : Fin 1069)) (faceAnchor (⟨817, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0818 : (⟨818, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨818, by decide⟩ : Fin 1069)) (faceAnchor (⟨818, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0819 : (⟨819, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨819, by decide⟩ : Fin 1069)) (faceAnchor (⟨819, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0820 : (⟨820, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨820, by decide⟩ : Fin 1069)) (faceAnchor (⟨820, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0821 : (⟨821, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨821, by decide⟩ : Fin 1069)) (faceAnchor (⟨821, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0822 : (⟨822, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨822, by decide⟩ : Fin 1069)) (faceAnchor (⟨822, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0823 : (⟨823, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨823, by decide⟩ : Fin 1069)) (faceAnchor (⟨823, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0824 : (⟨824, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨824, by decide⟩ : Fin 1069)) (faceAnchor (⟨824, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0825 : (⟨825, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨825, by decide⟩ : Fin 1069)) (faceAnchor (⟨825, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0826 : (⟨826, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨826, by decide⟩ : Fin 1069)) (faceAnchor (⟨826, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0827 : (⟨827, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨827, by decide⟩ : Fin 1069)) (faceAnchor (⟨827, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0828 : (⟨828, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨828, by decide⟩ : Fin 1069)) (faceAnchor (⟨828, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0829 : (⟨829, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨829, by decide⟩ : Fin 1069)) (faceAnchor (⟨829, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0830 : (⟨830, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨830, by decide⟩ : Fin 1069)) (faceAnchor (⟨830, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0831 : (⟨831, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨831, by decide⟩ : Fin 1069)) (faceAnchor (⟨831, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0832 : (⟨832, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨832, by decide⟩ : Fin 1069)) (faceAnchor (⟨832, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0833 : (⟨833, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨833, by decide⟩ : Fin 1069)) (faceAnchor (⟨833, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0834 : (⟨834, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨834, by decide⟩ : Fin 1069)) (faceAnchor (⟨834, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0835 : (⟨835, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨835, by decide⟩ : Fin 1069)) (faceAnchor (⟨835, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0836 : (⟨836, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨836, by decide⟩ : Fin 1069)) (faceAnchor (⟨836, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0837 : (⟨837, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨837, by decide⟩ : Fin 1069)) (faceAnchor (⟨837, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0838 : (⟨838, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨838, by decide⟩ : Fin 1069)) (faceAnchor (⟨838, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0839 : (⟨839, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨839, by decide⟩ : Fin 1069)) (faceAnchor (⟨839, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0840 : (⟨840, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨840, by decide⟩ : Fin 1069)) (faceAnchor (⟨840, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0841 : (⟨841, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨841, by decide⟩ : Fin 1069)) (faceAnchor (⟨841, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0842 : (⟨842, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨842, by decide⟩ : Fin 1069)) (faceAnchor (⟨842, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0843 : (⟨843, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨843, by decide⟩ : Fin 1069)) (faceAnchor (⟨843, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0844 : (⟨844, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨844, by decide⟩ : Fin 1069)) (faceAnchor (⟨844, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0845 : (⟨845, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨845, by decide⟩ : Fin 1069)) (faceAnchor (⟨845, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0846 : (⟨846, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨846, by decide⟩ : Fin 1069)) (faceAnchor (⟨846, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0847 : (⟨847, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨847, by decide⟩ : Fin 1069)) (faceAnchor (⟨847, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0848 : (⟨848, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨848, by decide⟩ : Fin 1069)) (faceAnchor (⟨848, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0849 : (⟨849, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨849, by decide⟩ : Fin 1069)) (faceAnchor (⟨849, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0850 : (⟨850, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨850, by decide⟩ : Fin 1069)) (faceAnchor (⟨850, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0851 : (⟨851, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨851, by decide⟩ : Fin 1069)) (faceAnchor (⟨851, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0852 : (⟨852, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨852, by decide⟩ : Fin 1069)) (faceAnchor (⟨852, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0853 : (⟨853, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨853, by decide⟩ : Fin 1069)) (faceAnchor (⟨853, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0854 : (⟨854, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨854, by decide⟩ : Fin 1069)) (faceAnchor (⟨854, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0855 : (⟨855, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨855, by decide⟩ : Fin 1069)) (faceAnchor (⟨855, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0856 : (⟨856, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨856, by decide⟩ : Fin 1069)) (faceAnchor (⟨856, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0857 : (⟨857, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨857, by decide⟩ : Fin 1069)) (faceAnchor (⟨857, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0858 : (⟨858, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨858, by decide⟩ : Fin 1069)) (faceAnchor (⟨858, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0859 : (⟨859, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨859, by decide⟩ : Fin 1069)) (faceAnchor (⟨859, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0860 : (⟨860, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨860, by decide⟩ : Fin 1069)) (faceAnchor (⟨860, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0861 : (⟨861, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨861, by decide⟩ : Fin 1069)) (faceAnchor (⟨861, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0862 : (⟨862, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨862, by decide⟩ : Fin 1069)) (faceAnchor (⟨862, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0863 : (⟨863, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨863, by decide⟩ : Fin 1069)) (faceAnchor (⟨863, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0864 : (⟨864, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨864, by decide⟩ : Fin 1069)) (faceAnchor (⟨864, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0865 : (⟨865, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨865, by decide⟩ : Fin 1069)) (faceAnchor (⟨865, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0866 : (⟨866, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨866, by decide⟩ : Fin 1069)) (faceAnchor (⟨866, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0867 : (⟨867, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨867, by decide⟩ : Fin 1069)) (faceAnchor (⟨867, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0868 : (⟨868, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨868, by decide⟩ : Fin 1069)) (faceAnchor (⟨868, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0869 : (⟨869, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨869, by decide⟩ : Fin 1069)) (faceAnchor (⟨869, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0870 : (⟨870, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨870, by decide⟩ : Fin 1069)) (faceAnchor (⟨870, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0871 : (⟨871, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨871, by decide⟩ : Fin 1069)) (faceAnchor (⟨871, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0872 : (⟨872, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨872, by decide⟩ : Fin 1069)) (faceAnchor (⟨872, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0873 : (⟨873, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨873, by decide⟩ : Fin 1069)) (faceAnchor (⟨873, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0874 : (⟨874, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨874, by decide⟩ : Fin 1069)) (faceAnchor (⟨874, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0875 : (⟨875, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨875, by decide⟩ : Fin 1069)) (faceAnchor (⟨875, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0876 : (⟨876, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨876, by decide⟩ : Fin 1069)) (faceAnchor (⟨876, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0877 : (⟨877, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨877, by decide⟩ : Fin 1069)) (faceAnchor (⟨877, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0878 : (⟨878, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨878, by decide⟩ : Fin 1069)) (faceAnchor (⟨878, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0879 : (⟨879, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨879, by decide⟩ : Fin 1069)) (faceAnchor (⟨879, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0880 : (⟨880, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨880, by decide⟩ : Fin 1069)) (faceAnchor (⟨880, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0881 : (⟨881, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨881, by decide⟩ : Fin 1069)) (faceAnchor (⟨881, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0882 : (⟨882, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨882, by decide⟩ : Fin 1069)) (faceAnchor (⟨882, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0883 : (⟨883, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨883, by decide⟩ : Fin 1069)) (faceAnchor (⟨883, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0884 : (⟨884, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨884, by decide⟩ : Fin 1069)) (faceAnchor (⟨884, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0885 : (⟨885, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨885, by decide⟩ : Fin 1069)) (faceAnchor (⟨885, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0886 : (⟨886, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨886, by decide⟩ : Fin 1069)) (faceAnchor (⟨886, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0887 : (⟨887, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨887, by decide⟩ : Fin 1069)) (faceAnchor (⟨887, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0888 : (⟨888, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨888, by decide⟩ : Fin 1069)) (faceAnchor (⟨888, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0889 : (⟨889, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨889, by decide⟩ : Fin 1069)) (faceAnchor (⟨889, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0890 : (⟨890, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨890, by decide⟩ : Fin 1069)) (faceAnchor (⟨890, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0891 : (⟨891, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨891, by decide⟩ : Fin 1069)) (faceAnchor (⟨891, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0892 : (⟨892, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨892, by decide⟩ : Fin 1069)) (faceAnchor (⟨892, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0893 : (⟨893, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨893, by decide⟩ : Fin 1069)) (faceAnchor (⟨893, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0894 : (⟨894, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨894, by decide⟩ : Fin 1069)) (faceAnchor (⟨894, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0895 : (⟨895, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨895, by decide⟩ : Fin 1069)) (faceAnchor (⟨895, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0896 : (⟨896, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨896, by decide⟩ : Fin 1069)) (faceAnchor (⟨896, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0897 : (⟨897, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨897, by decide⟩ : Fin 1069)) (faceAnchor (⟨897, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0898 : (⟨898, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨898, by decide⟩ : Fin 1069)) (faceAnchor (⟨898, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0899 : (⟨899, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨899, by decide⟩ : Fin 1069)) (faceAnchor (⟨899, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0900 : (⟨900, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨900, by decide⟩ : Fin 1069)) (faceAnchor (⟨900, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0901 : (⟨901, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨901, by decide⟩ : Fin 1069)) (faceAnchor (⟨901, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0902 : (⟨902, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨902, by decide⟩ : Fin 1069)) (faceAnchor (⟨902, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0903 : (⟨903, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨903, by decide⟩ : Fin 1069)) (faceAnchor (⟨903, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0904 : (⟨904, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨904, by decide⟩ : Fin 1069)) (faceAnchor (⟨904, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0905 : (⟨905, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨905, by decide⟩ : Fin 1069)) (faceAnchor (⟨905, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0906 : (⟨906, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨906, by decide⟩ : Fin 1069)) (faceAnchor (⟨906, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0907 : (⟨907, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨907, by decide⟩ : Fin 1069)) (faceAnchor (⟨907, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0908 : (⟨908, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨908, by decide⟩ : Fin 1069)) (faceAnchor (⟨908, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0909 : (⟨909, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨909, by decide⟩ : Fin 1069)) (faceAnchor (⟨909, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0910 : (⟨910, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨910, by decide⟩ : Fin 1069)) (faceAnchor (⟨910, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0911 : (⟨911, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨911, by decide⟩ : Fin 1069)) (faceAnchor (⟨911, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0912 : (⟨912, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨912, by decide⟩ : Fin 1069)) (faceAnchor (⟨912, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0913 : (⟨913, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨913, by decide⟩ : Fin 1069)) (faceAnchor (⟨913, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0914 : (⟨914, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨914, by decide⟩ : Fin 1069)) (faceAnchor (⟨914, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0915 : (⟨915, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨915, by decide⟩ : Fin 1069)) (faceAnchor (⟨915, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0916 : (⟨916, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨916, by decide⟩ : Fin 1069)) (faceAnchor (⟨916, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0917 : (⟨917, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨917, by decide⟩ : Fin 1069)) (faceAnchor (⟨917, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0918 : (⟨918, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨918, by decide⟩ : Fin 1069)) (faceAnchor (⟨918, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0919 : (⟨919, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨919, by decide⟩ : Fin 1069)) (faceAnchor (⟨919, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0920 : (⟨920, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨920, by decide⟩ : Fin 1069)) (faceAnchor (⟨920, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0921 : (⟨921, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨921, by decide⟩ : Fin 1069)) (faceAnchor (⟨921, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0922 : (⟨922, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨922, by decide⟩ : Fin 1069)) (faceAnchor (⟨922, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0923 : (⟨923, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨923, by decide⟩ : Fin 1069)) (faceAnchor (⟨923, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0924 : (⟨924, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨924, by decide⟩ : Fin 1069)) (faceAnchor (⟨924, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0925 : (⟨925, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨925, by decide⟩ : Fin 1069)) (faceAnchor (⟨925, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0926 : (⟨926, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨926, by decide⟩ : Fin 1069)) (faceAnchor (⟨926, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0927 : (⟨927, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨927, by decide⟩ : Fin 1069)) (faceAnchor (⟨927, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0928 : (⟨928, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨928, by decide⟩ : Fin 1069)) (faceAnchor (⟨928, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0929 : (⟨929, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨929, by decide⟩ : Fin 1069)) (faceAnchor (⟨929, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0930 : (⟨930, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨930, by decide⟩ : Fin 1069)) (faceAnchor (⟨930, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0931 : (⟨931, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨931, by decide⟩ : Fin 1069)) (faceAnchor (⟨931, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0932 : (⟨932, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨932, by decide⟩ : Fin 1069)) (faceAnchor (⟨932, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0933 : (⟨933, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨933, by decide⟩ : Fin 1069)) (faceAnchor (⟨933, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0934 : (⟨934, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨934, by decide⟩ : Fin 1069)) (faceAnchor (⟨934, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0935 : (⟨935, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨935, by decide⟩ : Fin 1069)) (faceAnchor (⟨935, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0936 : (⟨936, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨936, by decide⟩ : Fin 1069)) (faceAnchor (⟨936, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0937 : (⟨937, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨937, by decide⟩ : Fin 1069)) (faceAnchor (⟨937, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0938 : (⟨938, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨938, by decide⟩ : Fin 1069)) (faceAnchor (⟨938, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0939 : (⟨939, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨939, by decide⟩ : Fin 1069)) (faceAnchor (⟨939, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0940 : (⟨940, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨940, by decide⟩ : Fin 1069)) (faceAnchor (⟨940, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0941 : (⟨941, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨941, by decide⟩ : Fin 1069)) (faceAnchor (⟨941, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0942 : (⟨942, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨942, by decide⟩ : Fin 1069)) (faceAnchor (⟨942, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0943 : (⟨943, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨943, by decide⟩ : Fin 1069)) (faceAnchor (⟨943, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0944 : (⟨944, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨944, by decide⟩ : Fin 1069)) (faceAnchor (⟨944, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0945 : (⟨945, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨945, by decide⟩ : Fin 1069)) (faceAnchor (⟨945, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0946 : (⟨946, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨946, by decide⟩ : Fin 1069)) (faceAnchor (⟨946, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0947 : (⟨947, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨947, by decide⟩ : Fin 1069)) (faceAnchor (⟨947, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0948 : (⟨948, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨948, by decide⟩ : Fin 1069)) (faceAnchor (⟨948, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0949 : (⟨949, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨949, by decide⟩ : Fin 1069)) (faceAnchor (⟨949, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0950 : (⟨950, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨950, by decide⟩ : Fin 1069)) (faceAnchor (⟨950, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0951 : (⟨951, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨951, by decide⟩ : Fin 1069)) (faceAnchor (⟨951, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0952 : (⟨952, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨952, by decide⟩ : Fin 1069)) (faceAnchor (⟨952, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0953 : (⟨953, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨953, by decide⟩ : Fin 1069)) (faceAnchor (⟨953, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0954 : (⟨954, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨954, by decide⟩ : Fin 1069)) (faceAnchor (⟨954, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0955 : (⟨955, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨955, by decide⟩ : Fin 1069)) (faceAnchor (⟨955, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0956 : (⟨956, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨956, by decide⟩ : Fin 1069)) (faceAnchor (⟨956, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0957 : (⟨957, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨957, by decide⟩ : Fin 1069)) (faceAnchor (⟨957, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0958 : (⟨958, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨958, by decide⟩ : Fin 1069)) (faceAnchor (⟨958, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0959 : (⟨959, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨959, by decide⟩ : Fin 1069)) (faceAnchor (⟨959, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0960 : (⟨960, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨960, by decide⟩ : Fin 1069)) (faceAnchor (⟨960, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0961 : (⟨961, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨961, by decide⟩ : Fin 1069)) (faceAnchor (⟨961, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0962 : (⟨962, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨962, by decide⟩ : Fin 1069)) (faceAnchor (⟨962, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0963 : (⟨963, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨963, by decide⟩ : Fin 1069)) (faceAnchor (⟨963, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0964 : (⟨964, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨964, by decide⟩ : Fin 1069)) (faceAnchor (⟨964, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0965 : (⟨965, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨965, by decide⟩ : Fin 1069)) (faceAnchor (⟨965, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0966 : (⟨966, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨966, by decide⟩ : Fin 1069)) (faceAnchor (⟨966, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0967 : (⟨967, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨967, by decide⟩ : Fin 1069)) (faceAnchor (⟨967, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0968 : (⟨968, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨968, by decide⟩ : Fin 1069)) (faceAnchor (⟨968, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0969 : (⟨969, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨969, by decide⟩ : Fin 1069)) (faceAnchor (⟨969, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0970 : (⟨970, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨970, by decide⟩ : Fin 1069)) (faceAnchor (⟨970, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0971 : (⟨971, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨971, by decide⟩ : Fin 1069)) (faceAnchor (⟨971, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0972 : (⟨972, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨972, by decide⟩ : Fin 1069)) (faceAnchor (⟨972, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0973 : (⟨973, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨973, by decide⟩ : Fin 1069)) (faceAnchor (⟨973, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0974 : (⟨974, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨974, by decide⟩ : Fin 1069)) (faceAnchor (⟨974, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0975 : (⟨975, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨975, by decide⟩ : Fin 1069)) (faceAnchor (⟨975, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0976 : (⟨976, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨976, by decide⟩ : Fin 1069)) (faceAnchor (⟨976, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0977 : (⟨977, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨977, by decide⟩ : Fin 1069)) (faceAnchor (⟨977, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0978 : (⟨978, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨978, by decide⟩ : Fin 1069)) (faceAnchor (⟨978, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0979 : (⟨979, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨979, by decide⟩ : Fin 1069)) (faceAnchor (⟨979, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0980 : (⟨980, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨980, by decide⟩ : Fin 1069)) (faceAnchor (⟨980, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0981 : (⟨981, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨981, by decide⟩ : Fin 1069)) (faceAnchor (⟨981, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0982 : (⟨982, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨982, by decide⟩ : Fin 1069)) (faceAnchor (⟨982, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0983 : (⟨983, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨983, by decide⟩ : Fin 1069)) (faceAnchor (⟨983, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0984 : (⟨984, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨984, by decide⟩ : Fin 1069)) (faceAnchor (⟨984, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0985 : (⟨985, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨985, by decide⟩ : Fin 1069)) (faceAnchor (⟨985, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0986 : (⟨986, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨986, by decide⟩ : Fin 1069)) (faceAnchor (⟨986, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0987 : (⟨987, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨987, by decide⟩ : Fin 1069)) (faceAnchor (⟨987, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0988 : (⟨988, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨988, by decide⟩ : Fin 1069)) (faceAnchor (⟨988, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0989 : (⟨989, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨989, by decide⟩ : Fin 1069)) (faceAnchor (⟨989, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0990 : (⟨990, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨990, by decide⟩ : Fin 1069)) (faceAnchor (⟨990, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0991 : (⟨991, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨991, by decide⟩ : Fin 1069)) (faceAnchor (⟨991, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0992 : (⟨992, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨992, by decide⟩ : Fin 1069)) (faceAnchor (⟨992, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0993 : (⟨993, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨993, by decide⟩ : Fin 1069)) (faceAnchor (⟨993, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0994 : (⟨994, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨994, by decide⟩ : Fin 1069)) (faceAnchor (⟨994, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0995 : (⟨995, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨995, by decide⟩ : Fin 1069)) (faceAnchor (⟨995, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0996 : (⟨996, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨996, by decide⟩ : Fin 1069)) (faceAnchor (⟨996, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0997 : (⟨997, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨997, by decide⟩ : Fin 1069)) (faceAnchor (⟨997, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0998 : (⟨998, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨998, by decide⟩ : Fin 1069)) (faceAnchor (⟨998, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket0999 : (⟨999, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨999, by decide⟩ : Fin 1069)) (faceAnchor (⟨999, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1000 : (⟨1000, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1000, by decide⟩ : Fin 1069)) (faceAnchor (⟨1000, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1001 : (⟨1001, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1001, by decide⟩ : Fin 1069)) (faceAnchor (⟨1001, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1002 : (⟨1002, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1002, by decide⟩ : Fin 1069)) (faceAnchor (⟨1002, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1003 : (⟨1003, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1003, by decide⟩ : Fin 1069)) (faceAnchor (⟨1003, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1004 : (⟨1004, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1004, by decide⟩ : Fin 1069)) (faceAnchor (⟨1004, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1005 : (⟨1005, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1005, by decide⟩ : Fin 1069)) (faceAnchor (⟨1005, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1006 : (⟨1006, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1006, by decide⟩ : Fin 1069)) (faceAnchor (⟨1006, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1007 : (⟨1007, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1007, by decide⟩ : Fin 1069)) (faceAnchor (⟨1007, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1008 : (⟨1008, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1008, by decide⟩ : Fin 1069)) (faceAnchor (⟨1008, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1009 : (⟨1009, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1009, by decide⟩ : Fin 1069)) (faceAnchor (⟨1009, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1010 : (⟨1010, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1010, by decide⟩ : Fin 1069)) (faceAnchor (⟨1010, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1011 : (⟨1011, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1011, by decide⟩ : Fin 1069)) (faceAnchor (⟨1011, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1012 : (⟨1012, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1012, by decide⟩ : Fin 1069)) (faceAnchor (⟨1012, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1013 : (⟨1013, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1013, by decide⟩ : Fin 1069)) (faceAnchor (⟨1013, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1014 : (⟨1014, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1014, by decide⟩ : Fin 1069)) (faceAnchor (⟨1014, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1015 : (⟨1015, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1015, by decide⟩ : Fin 1069)) (faceAnchor (⟨1015, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1016 : (⟨1016, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1016, by decide⟩ : Fin 1069)) (faceAnchor (⟨1016, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1017 : (⟨1017, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1017, by decide⟩ : Fin 1069)) (faceAnchor (⟨1017, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1018 : (⟨1018, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1018, by decide⟩ : Fin 1069)) (faceAnchor (⟨1018, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1019 : (⟨1019, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1019, by decide⟩ : Fin 1069)) (faceAnchor (⟨1019, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1020 : (⟨1020, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1020, by decide⟩ : Fin 1069)) (faceAnchor (⟨1020, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1021 : (⟨1021, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1021, by decide⟩ : Fin 1069)) (faceAnchor (⟨1021, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1022 : (⟨1022, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1022, by decide⟩ : Fin 1069)) (faceAnchor (⟨1022, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1023 : (⟨1023, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1023, by decide⟩ : Fin 1069)) (faceAnchor (⟨1023, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1024 : (⟨1024, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1024, by decide⟩ : Fin 1069)) (faceAnchor (⟨1024, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1025 : (⟨1025, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1025, by decide⟩ : Fin 1069)) (faceAnchor (⟨1025, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1026 : (⟨1026, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1026, by decide⟩ : Fin 1069)) (faceAnchor (⟨1026, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1027 : (⟨1027, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1027, by decide⟩ : Fin 1069)) (faceAnchor (⟨1027, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1028 : (⟨1028, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1028, by decide⟩ : Fin 1069)) (faceAnchor (⟨1028, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1029 : (⟨1029, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1029, by decide⟩ : Fin 1069)) (faceAnchor (⟨1029, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1030 : (⟨1030, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1030, by decide⟩ : Fin 1069)) (faceAnchor (⟨1030, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1031 : (⟨1031, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1031, by decide⟩ : Fin 1069)) (faceAnchor (⟨1031, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1032 : (⟨1032, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1032, by decide⟩ : Fin 1069)) (faceAnchor (⟨1032, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1033 : (⟨1033, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1033, by decide⟩ : Fin 1069)) (faceAnchor (⟨1033, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1034 : (⟨1034, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1034, by decide⟩ : Fin 1069)) (faceAnchor (⟨1034, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1035 : (⟨1035, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1035, by decide⟩ : Fin 1069)) (faceAnchor (⟨1035, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1036 : (⟨1036, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1036, by decide⟩ : Fin 1069)) (faceAnchor (⟨1036, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1037 : (⟨1037, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1037, by decide⟩ : Fin 1069)) (faceAnchor (⟨1037, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1038 : (⟨1038, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1038, by decide⟩ : Fin 1069)) (faceAnchor (⟨1038, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1039 : (⟨1039, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1039, by decide⟩ : Fin 1069)) (faceAnchor (⟨1039, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1040 : (⟨1040, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1040, by decide⟩ : Fin 1069)) (faceAnchor (⟨1040, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1041 : (⟨1041, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1041, by decide⟩ : Fin 1069)) (faceAnchor (⟨1041, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1042 : (⟨1042, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1042, by decide⟩ : Fin 1069)) (faceAnchor (⟨1042, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1043 : (⟨1043, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1043, by decide⟩ : Fin 1069)) (faceAnchor (⟨1043, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1044 : (⟨1044, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1044, by decide⟩ : Fin 1069)) (faceAnchor (⟨1044, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1045 : (⟨1045, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1045, by decide⟩ : Fin 1069)) (faceAnchor (⟨1045, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1046 : (⟨1046, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1046, by decide⟩ : Fin 1069)) (faceAnchor (⟨1046, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1047 : (⟨1047, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1047, by decide⟩ : Fin 1069)) (faceAnchor (⟨1047, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1048 : (⟨1048, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1048, by decide⟩ : Fin 1069)) (faceAnchor (⟨1048, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1049 : (⟨1049, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1049, by decide⟩ : Fin 1069)) (faceAnchor (⟨1049, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1050 : (⟨1050, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1050, by decide⟩ : Fin 1069)) (faceAnchor (⟨1050, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1051 : (⟨1051, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1051, by decide⟩ : Fin 1069)) (faceAnchor (⟨1051, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1052 : (⟨1052, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1052, by decide⟩ : Fin 1069)) (faceAnchor (⟨1052, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1053 : (⟨1053, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1053, by decide⟩ : Fin 1069)) (faceAnchor (⟨1053, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1054 : (⟨1054, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1054, by decide⟩ : Fin 1069)) (faceAnchor (⟨1054, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1055 : (⟨1055, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1055, by decide⟩ : Fin 1069)) (faceAnchor (⟨1055, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1056 : (⟨1056, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1056, by decide⟩ : Fin 1069)) (faceAnchor (⟨1056, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1057 : (⟨1057, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1057, by decide⟩ : Fin 1069)) (faceAnchor (⟨1057, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1058 : (⟨1058, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1058, by decide⟩ : Fin 1069)) (faceAnchor (⟨1058, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1059 : (⟨1059, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1059, by decide⟩ : Fin 1069)) (faceAnchor (⟨1059, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1060 : (⟨1060, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1060, by decide⟩ : Fin 1069)) (faceAnchor (⟨1060, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1061 : (⟨1061, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1061, by decide⟩ : Fin 1069)) (faceAnchor (⟨1061, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1062 : (⟨1062, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1062, by decide⟩ : Fin 1069)) (faceAnchor (⟨1062, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1063 : (⟨1063, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1063, by decide⟩ : Fin 1069)) (faceAnchor (⟨1063, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1064 : (⟨1064, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1064, by decide⟩ : Fin 1069)) (faceAnchor (⟨1064, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1065 : (⟨1065, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1065, by decide⟩ : Fin 1069)) (faceAnchor (⟨1065, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1066 : (⟨1066, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1066, by decide⟩ : Fin 1069)) (faceAnchor (⟨1066, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1067 : (⟨1067, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1067, by decide⟩ : Fin 1069)) (faceAnchor (⟨1067, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucket1068 : (⟨1068, by decide⟩ : Fin 1069) ∈ anchoredFaces (faceRank (⟨1068, by decide⟩ : Fin 1069)) (faceAnchor (⟨1068, by decide⟩ : Fin 1069)) := by
  decide +kernel

private theorem bucketGroup0000 (i : Fin 1069)
    (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0000
          ·
            have he : (⟨1, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using bucket0001
        ·
          by_cases h3 : i.val < 3
          ·
            have he : (⟨2, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using bucket0002
          ·
            have he : (⟨3, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 3 = i.val
              omega
            simpa only [he] using bucket0003
      ·
        by_cases h6 : i.val < 6
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using bucket0004
          ·
            have he : (⟨5, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using bucket0005
        ·
          by_cases h7 : i.val < 7
          ·
            have he : (⟨6, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 6 = i.val
              omega
            simpa only [he] using bucket0006
          ·
            have he : (⟨7, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using bucket0007
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
            simpa only [he] using bucket0008
          ·
            have he : (⟨9, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 9 = i.val
              omega
            simpa only [he] using bucket0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using bucket0010
          ·
            have he : (⟨11, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using bucket0011
      ·
        by_cases h14 : i.val < 14
        ·
          by_cases h13 : i.val < 13
          ·
            have he : (⟨12, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 12 = i.val
              omega
            simpa only [he] using bucket0012
          ·
            have he : (⟨13, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using bucket0013
        ·
          by_cases h15 : i.val < 15
          ·
            have he : (⟨14, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using bucket0014
          ·
            have he : (⟨15, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 15 = i.val
              omega
            simpa only [he] using bucket0015
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
            simpa only [he] using bucket0016
          ·
            have he : (⟨17, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using bucket0017
        ·
          by_cases h19 : i.val < 19
          ·
            have he : (⟨18, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 18 = i.val
              omega
            simpa only [he] using bucket0018
          ·
            have he : (⟨19, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using bucket0019
      ·
        by_cases h22 : i.val < 22
        ·
          by_cases h21 : i.val < 21
          ·
            have he : (⟨20, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using bucket0020
          ·
            have he : (⟨21, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 21 = i.val
              omega
            simpa only [he] using bucket0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using bucket0022
          ·
            have he : (⟨23, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using bucket0023
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
            simpa only [he] using bucket0024
          ·
            have he : (⟨25, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 25 = i.val
              omega
            simpa only [he] using bucket0025
        ·
          by_cases h27 : i.val < 27
          ·
            have he : (⟨26, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 26 = i.val
              omega
            simpa only [he] using bucket0026
          ·
            have he : (⟨27, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 27 = i.val
              omega
            simpa only [he] using bucket0027
      ·
        by_cases h30 : i.val < 30
        ·
          by_cases h29 : i.val < 29
          ·
            have he : (⟨28, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 28 = i.val
              omega
            simpa only [he] using bucket0028
          ·
            have he : (⟨29, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 29 = i.val
              omega
            simpa only [he] using bucket0029
        ·
          by_cases h31 : i.val < 31
          ·
            have he : (⟨30, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 30 = i.val
              omega
            simpa only [he] using bucket0030
          ·
            have he : (⟨31, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 31 = i.val
              omega
            simpa only [he] using bucket0031

private theorem bucketGroup0001 (i : Fin 1069)
    (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0032
          ·
            have he : (⟨33, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 33 = i.val
              omega
            simpa only [he] using bucket0033
        ·
          by_cases h35 : i.val < 35
          ·
            have he : (⟨34, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 34 = i.val
              omega
            simpa only [he] using bucket0034
          ·
            have he : (⟨35, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 35 = i.val
              omega
            simpa only [he] using bucket0035
      ·
        by_cases h38 : i.val < 38
        ·
          by_cases h37 : i.val < 37
          ·
            have he : (⟨36, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 36 = i.val
              omega
            simpa only [he] using bucket0036
          ·
            have he : (⟨37, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 37 = i.val
              omega
            simpa only [he] using bucket0037
        ·
          by_cases h39 : i.val < 39
          ·
            have he : (⟨38, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 38 = i.val
              omega
            simpa only [he] using bucket0038
          ·
            have he : (⟨39, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 39 = i.val
              omega
            simpa only [he] using bucket0039
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
            simpa only [he] using bucket0040
          ·
            have he : (⟨41, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 41 = i.val
              omega
            simpa only [he] using bucket0041
        ·
          by_cases h43 : i.val < 43
          ·
            have he : (⟨42, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 42 = i.val
              omega
            simpa only [he] using bucket0042
          ·
            have he : (⟨43, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 43 = i.val
              omega
            simpa only [he] using bucket0043
      ·
        by_cases h46 : i.val < 46
        ·
          by_cases h45 : i.val < 45
          ·
            have he : (⟨44, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 44 = i.val
              omega
            simpa only [he] using bucket0044
          ·
            have he : (⟨45, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 45 = i.val
              omega
            simpa only [he] using bucket0045
        ·
          by_cases h47 : i.val < 47
          ·
            have he : (⟨46, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 46 = i.val
              omega
            simpa only [he] using bucket0046
          ·
            have he : (⟨47, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 47 = i.val
              omega
            simpa only [he] using bucket0047
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
            simpa only [he] using bucket0048
          ·
            have he : (⟨49, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 49 = i.val
              omega
            simpa only [he] using bucket0049
        ·
          by_cases h51 : i.val < 51
          ·
            have he : (⟨50, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 50 = i.val
              omega
            simpa only [he] using bucket0050
          ·
            have he : (⟨51, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 51 = i.val
              omega
            simpa only [he] using bucket0051
      ·
        by_cases h54 : i.val < 54
        ·
          by_cases h53 : i.val < 53
          ·
            have he : (⟨52, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 52 = i.val
              omega
            simpa only [he] using bucket0052
          ·
            have he : (⟨53, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 53 = i.val
              omega
            simpa only [he] using bucket0053
        ·
          by_cases h55 : i.val < 55
          ·
            have he : (⟨54, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 54 = i.val
              omega
            simpa only [he] using bucket0054
          ·
            have he : (⟨55, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 55 = i.val
              omega
            simpa only [he] using bucket0055
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
            simpa only [he] using bucket0056
          ·
            have he : (⟨57, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 57 = i.val
              omega
            simpa only [he] using bucket0057
        ·
          by_cases h59 : i.val < 59
          ·
            have he : (⟨58, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 58 = i.val
              omega
            simpa only [he] using bucket0058
          ·
            have he : (⟨59, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 59 = i.val
              omega
            simpa only [he] using bucket0059
      ·
        by_cases h62 : i.val < 62
        ·
          by_cases h61 : i.val < 61
          ·
            have he : (⟨60, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 60 = i.val
              omega
            simpa only [he] using bucket0060
          ·
            have he : (⟨61, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 61 = i.val
              omega
            simpa only [he] using bucket0061
        ·
          by_cases h63 : i.val < 63
          ·
            have he : (⟨62, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 62 = i.val
              omega
            simpa only [he] using bucket0062
          ·
            have he : (⟨63, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 63 = i.val
              omega
            simpa only [he] using bucket0063

private theorem bucketGroup0002 (i : Fin 1069)
    (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0064
          ·
            have he : (⟨65, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 65 = i.val
              omega
            simpa only [he] using bucket0065
        ·
          by_cases h67 : i.val < 67
          ·
            have he : (⟨66, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 66 = i.val
              omega
            simpa only [he] using bucket0066
          ·
            have he : (⟨67, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 67 = i.val
              omega
            simpa only [he] using bucket0067
      ·
        by_cases h70 : i.val < 70
        ·
          by_cases h69 : i.val < 69
          ·
            have he : (⟨68, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 68 = i.val
              omega
            simpa only [he] using bucket0068
          ·
            have he : (⟨69, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 69 = i.val
              omega
            simpa only [he] using bucket0069
        ·
          by_cases h71 : i.val < 71
          ·
            have he : (⟨70, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 70 = i.val
              omega
            simpa only [he] using bucket0070
          ·
            have he : (⟨71, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 71 = i.val
              omega
            simpa only [he] using bucket0071
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
            simpa only [he] using bucket0072
          ·
            have he : (⟨73, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 73 = i.val
              omega
            simpa only [he] using bucket0073
        ·
          by_cases h75 : i.val < 75
          ·
            have he : (⟨74, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 74 = i.val
              omega
            simpa only [he] using bucket0074
          ·
            have he : (⟨75, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 75 = i.val
              omega
            simpa only [he] using bucket0075
      ·
        by_cases h78 : i.val < 78
        ·
          by_cases h77 : i.val < 77
          ·
            have he : (⟨76, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 76 = i.val
              omega
            simpa only [he] using bucket0076
          ·
            have he : (⟨77, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 77 = i.val
              omega
            simpa only [he] using bucket0077
        ·
          by_cases h79 : i.val < 79
          ·
            have he : (⟨78, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 78 = i.val
              omega
            simpa only [he] using bucket0078
          ·
            have he : (⟨79, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 79 = i.val
              omega
            simpa only [he] using bucket0079
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
            simpa only [he] using bucket0080
          ·
            have he : (⟨81, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 81 = i.val
              omega
            simpa only [he] using bucket0081
        ·
          by_cases h83 : i.val < 83
          ·
            have he : (⟨82, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 82 = i.val
              omega
            simpa only [he] using bucket0082
          ·
            have he : (⟨83, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 83 = i.val
              omega
            simpa only [he] using bucket0083
      ·
        by_cases h86 : i.val < 86
        ·
          by_cases h85 : i.val < 85
          ·
            have he : (⟨84, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 84 = i.val
              omega
            simpa only [he] using bucket0084
          ·
            have he : (⟨85, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 85 = i.val
              omega
            simpa only [he] using bucket0085
        ·
          by_cases h87 : i.val < 87
          ·
            have he : (⟨86, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 86 = i.val
              omega
            simpa only [he] using bucket0086
          ·
            have he : (⟨87, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 87 = i.val
              omega
            simpa only [he] using bucket0087
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
            simpa only [he] using bucket0088
          ·
            have he : (⟨89, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 89 = i.val
              omega
            simpa only [he] using bucket0089
        ·
          by_cases h91 : i.val < 91
          ·
            have he : (⟨90, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 90 = i.val
              omega
            simpa only [he] using bucket0090
          ·
            have he : (⟨91, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 91 = i.val
              omega
            simpa only [he] using bucket0091
      ·
        by_cases h94 : i.val < 94
        ·
          by_cases h93 : i.val < 93
          ·
            have he : (⟨92, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 92 = i.val
              omega
            simpa only [he] using bucket0092
          ·
            have he : (⟨93, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 93 = i.val
              omega
            simpa only [he] using bucket0093
        ·
          by_cases h95 : i.val < 95
          ·
            have he : (⟨94, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 94 = i.val
              omega
            simpa only [he] using bucket0094
          ·
            have he : (⟨95, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 95 = i.val
              omega
            simpa only [he] using bucket0095

private theorem bucketGroup0003 (i : Fin 1069)
    (hlo : 96 ≤ i.val) (hhi : i.val < 128) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0096
          ·
            have he : (⟨97, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 97 = i.val
              omega
            simpa only [he] using bucket0097
        ·
          by_cases h99 : i.val < 99
          ·
            have he : (⟨98, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 98 = i.val
              omega
            simpa only [he] using bucket0098
          ·
            have he : (⟨99, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 99 = i.val
              omega
            simpa only [he] using bucket0099
      ·
        by_cases h102 : i.val < 102
        ·
          by_cases h101 : i.val < 101
          ·
            have he : (⟨100, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 100 = i.val
              omega
            simpa only [he] using bucket0100
          ·
            have he : (⟨101, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 101 = i.val
              omega
            simpa only [he] using bucket0101
        ·
          by_cases h103 : i.val < 103
          ·
            have he : (⟨102, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 102 = i.val
              omega
            simpa only [he] using bucket0102
          ·
            have he : (⟨103, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 103 = i.val
              omega
            simpa only [he] using bucket0103
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
            simpa only [he] using bucket0104
          ·
            have he : (⟨105, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 105 = i.val
              omega
            simpa only [he] using bucket0105
        ·
          by_cases h107 : i.val < 107
          ·
            have he : (⟨106, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 106 = i.val
              omega
            simpa only [he] using bucket0106
          ·
            have he : (⟨107, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 107 = i.val
              omega
            simpa only [he] using bucket0107
      ·
        by_cases h110 : i.val < 110
        ·
          by_cases h109 : i.val < 109
          ·
            have he : (⟨108, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 108 = i.val
              omega
            simpa only [he] using bucket0108
          ·
            have he : (⟨109, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 109 = i.val
              omega
            simpa only [he] using bucket0109
        ·
          by_cases h111 : i.val < 111
          ·
            have he : (⟨110, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 110 = i.val
              omega
            simpa only [he] using bucket0110
          ·
            have he : (⟨111, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 111 = i.val
              omega
            simpa only [he] using bucket0111
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
            simpa only [he] using bucket0112
          ·
            have he : (⟨113, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 113 = i.val
              omega
            simpa only [he] using bucket0113
        ·
          by_cases h115 : i.val < 115
          ·
            have he : (⟨114, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 114 = i.val
              omega
            simpa only [he] using bucket0114
          ·
            have he : (⟨115, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 115 = i.val
              omega
            simpa only [he] using bucket0115
      ·
        by_cases h118 : i.val < 118
        ·
          by_cases h117 : i.val < 117
          ·
            have he : (⟨116, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 116 = i.val
              omega
            simpa only [he] using bucket0116
          ·
            have he : (⟨117, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 117 = i.val
              omega
            simpa only [he] using bucket0117
        ·
          by_cases h119 : i.val < 119
          ·
            have he : (⟨118, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 118 = i.val
              omega
            simpa only [he] using bucket0118
          ·
            have he : (⟨119, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 119 = i.val
              omega
            simpa only [he] using bucket0119
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
            simpa only [he] using bucket0120
          ·
            have he : (⟨121, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 121 = i.val
              omega
            simpa only [he] using bucket0121
        ·
          by_cases h123 : i.val < 123
          ·
            have he : (⟨122, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 122 = i.val
              omega
            simpa only [he] using bucket0122
          ·
            have he : (⟨123, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 123 = i.val
              omega
            simpa only [he] using bucket0123
      ·
        by_cases h126 : i.val < 126
        ·
          by_cases h125 : i.val < 125
          ·
            have he : (⟨124, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 124 = i.val
              omega
            simpa only [he] using bucket0124
          ·
            have he : (⟨125, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 125 = i.val
              omega
            simpa only [he] using bucket0125
        ·
          by_cases h127 : i.val < 127
          ·
            have he : (⟨126, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 126 = i.val
              omega
            simpa only [he] using bucket0126
          ·
            have he : (⟨127, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 127 = i.val
              omega
            simpa only [he] using bucket0127

private theorem bucketGroup0004 (i : Fin 1069)
    (hlo : 128 ≤ i.val) (hhi : i.val < 160) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0128
          ·
            have he : (⟨129, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 129 = i.val
              omega
            simpa only [he] using bucket0129
        ·
          by_cases h131 : i.val < 131
          ·
            have he : (⟨130, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 130 = i.val
              omega
            simpa only [he] using bucket0130
          ·
            have he : (⟨131, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 131 = i.val
              omega
            simpa only [he] using bucket0131
      ·
        by_cases h134 : i.val < 134
        ·
          by_cases h133 : i.val < 133
          ·
            have he : (⟨132, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 132 = i.val
              omega
            simpa only [he] using bucket0132
          ·
            have he : (⟨133, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 133 = i.val
              omega
            simpa only [he] using bucket0133
        ·
          by_cases h135 : i.val < 135
          ·
            have he : (⟨134, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 134 = i.val
              omega
            simpa only [he] using bucket0134
          ·
            have he : (⟨135, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 135 = i.val
              omega
            simpa only [he] using bucket0135
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
            simpa only [he] using bucket0136
          ·
            have he : (⟨137, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 137 = i.val
              omega
            simpa only [he] using bucket0137
        ·
          by_cases h139 : i.val < 139
          ·
            have he : (⟨138, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 138 = i.val
              omega
            simpa only [he] using bucket0138
          ·
            have he : (⟨139, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 139 = i.val
              omega
            simpa only [he] using bucket0139
      ·
        by_cases h142 : i.val < 142
        ·
          by_cases h141 : i.val < 141
          ·
            have he : (⟨140, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 140 = i.val
              omega
            simpa only [he] using bucket0140
          ·
            have he : (⟨141, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 141 = i.val
              omega
            simpa only [he] using bucket0141
        ·
          by_cases h143 : i.val < 143
          ·
            have he : (⟨142, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 142 = i.val
              omega
            simpa only [he] using bucket0142
          ·
            have he : (⟨143, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 143 = i.val
              omega
            simpa only [he] using bucket0143
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
            simpa only [he] using bucket0144
          ·
            have he : (⟨145, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 145 = i.val
              omega
            simpa only [he] using bucket0145
        ·
          by_cases h147 : i.val < 147
          ·
            have he : (⟨146, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 146 = i.val
              omega
            simpa only [he] using bucket0146
          ·
            have he : (⟨147, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 147 = i.val
              omega
            simpa only [he] using bucket0147
      ·
        by_cases h150 : i.val < 150
        ·
          by_cases h149 : i.val < 149
          ·
            have he : (⟨148, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 148 = i.val
              omega
            simpa only [he] using bucket0148
          ·
            have he : (⟨149, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 149 = i.val
              omega
            simpa only [he] using bucket0149
        ·
          by_cases h151 : i.val < 151
          ·
            have he : (⟨150, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 150 = i.val
              omega
            simpa only [he] using bucket0150
          ·
            have he : (⟨151, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 151 = i.val
              omega
            simpa only [he] using bucket0151
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
            simpa only [he] using bucket0152
          ·
            have he : (⟨153, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 153 = i.val
              omega
            simpa only [he] using bucket0153
        ·
          by_cases h155 : i.val < 155
          ·
            have he : (⟨154, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 154 = i.val
              omega
            simpa only [he] using bucket0154
          ·
            have he : (⟨155, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 155 = i.val
              omega
            simpa only [he] using bucket0155
      ·
        by_cases h158 : i.val < 158
        ·
          by_cases h157 : i.val < 157
          ·
            have he : (⟨156, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 156 = i.val
              omega
            simpa only [he] using bucket0156
          ·
            have he : (⟨157, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 157 = i.val
              omega
            simpa only [he] using bucket0157
        ·
          by_cases h159 : i.val < 159
          ·
            have he : (⟨158, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 158 = i.val
              omega
            simpa only [he] using bucket0158
          ·
            have he : (⟨159, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 159 = i.val
              omega
            simpa only [he] using bucket0159

private theorem bucketGroup0005 (i : Fin 1069)
    (hlo : 160 ≤ i.val) (hhi : i.val < 192) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0160
          ·
            have he : (⟨161, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 161 = i.val
              omega
            simpa only [he] using bucket0161
        ·
          by_cases h163 : i.val < 163
          ·
            have he : (⟨162, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 162 = i.val
              omega
            simpa only [he] using bucket0162
          ·
            have he : (⟨163, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 163 = i.val
              omega
            simpa only [he] using bucket0163
      ·
        by_cases h166 : i.val < 166
        ·
          by_cases h165 : i.val < 165
          ·
            have he : (⟨164, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 164 = i.val
              omega
            simpa only [he] using bucket0164
          ·
            have he : (⟨165, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 165 = i.val
              omega
            simpa only [he] using bucket0165
        ·
          by_cases h167 : i.val < 167
          ·
            have he : (⟨166, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 166 = i.val
              omega
            simpa only [he] using bucket0166
          ·
            have he : (⟨167, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 167 = i.val
              omega
            simpa only [he] using bucket0167
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
            simpa only [he] using bucket0168
          ·
            have he : (⟨169, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 169 = i.val
              omega
            simpa only [he] using bucket0169
        ·
          by_cases h171 : i.val < 171
          ·
            have he : (⟨170, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 170 = i.val
              omega
            simpa only [he] using bucket0170
          ·
            have he : (⟨171, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 171 = i.val
              omega
            simpa only [he] using bucket0171
      ·
        by_cases h174 : i.val < 174
        ·
          by_cases h173 : i.val < 173
          ·
            have he : (⟨172, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 172 = i.val
              omega
            simpa only [he] using bucket0172
          ·
            have he : (⟨173, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 173 = i.val
              omega
            simpa only [he] using bucket0173
        ·
          by_cases h175 : i.val < 175
          ·
            have he : (⟨174, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 174 = i.val
              omega
            simpa only [he] using bucket0174
          ·
            have he : (⟨175, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 175 = i.val
              omega
            simpa only [he] using bucket0175
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
            simpa only [he] using bucket0176
          ·
            have he : (⟨177, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 177 = i.val
              omega
            simpa only [he] using bucket0177
        ·
          by_cases h179 : i.val < 179
          ·
            have he : (⟨178, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 178 = i.val
              omega
            simpa only [he] using bucket0178
          ·
            have he : (⟨179, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 179 = i.val
              omega
            simpa only [he] using bucket0179
      ·
        by_cases h182 : i.val < 182
        ·
          by_cases h181 : i.val < 181
          ·
            have he : (⟨180, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 180 = i.val
              omega
            simpa only [he] using bucket0180
          ·
            have he : (⟨181, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 181 = i.val
              omega
            simpa only [he] using bucket0181
        ·
          by_cases h183 : i.val < 183
          ·
            have he : (⟨182, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 182 = i.val
              omega
            simpa only [he] using bucket0182
          ·
            have he : (⟨183, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 183 = i.val
              omega
            simpa only [he] using bucket0183
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
            simpa only [he] using bucket0184
          ·
            have he : (⟨185, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 185 = i.val
              omega
            simpa only [he] using bucket0185
        ·
          by_cases h187 : i.val < 187
          ·
            have he : (⟨186, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 186 = i.val
              omega
            simpa only [he] using bucket0186
          ·
            have he : (⟨187, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 187 = i.val
              omega
            simpa only [he] using bucket0187
      ·
        by_cases h190 : i.val < 190
        ·
          by_cases h189 : i.val < 189
          ·
            have he : (⟨188, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 188 = i.val
              omega
            simpa only [he] using bucket0188
          ·
            have he : (⟨189, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 189 = i.val
              omega
            simpa only [he] using bucket0189
        ·
          by_cases h191 : i.val < 191
          ·
            have he : (⟨190, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 190 = i.val
              omega
            simpa only [he] using bucket0190
          ·
            have he : (⟨191, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 191 = i.val
              omega
            simpa only [he] using bucket0191

private theorem bucketGroup0006 (i : Fin 1069)
    (hlo : 192 ≤ i.val) (hhi : i.val < 224) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0192
          ·
            have he : (⟨193, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 193 = i.val
              omega
            simpa only [he] using bucket0193
        ·
          by_cases h195 : i.val < 195
          ·
            have he : (⟨194, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 194 = i.val
              omega
            simpa only [he] using bucket0194
          ·
            have he : (⟨195, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 195 = i.val
              omega
            simpa only [he] using bucket0195
      ·
        by_cases h198 : i.val < 198
        ·
          by_cases h197 : i.val < 197
          ·
            have he : (⟨196, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 196 = i.val
              omega
            simpa only [he] using bucket0196
          ·
            have he : (⟨197, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 197 = i.val
              omega
            simpa only [he] using bucket0197
        ·
          by_cases h199 : i.val < 199
          ·
            have he : (⟨198, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 198 = i.val
              omega
            simpa only [he] using bucket0198
          ·
            have he : (⟨199, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 199 = i.val
              omega
            simpa only [he] using bucket0199
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
            simpa only [he] using bucket0200
          ·
            have he : (⟨201, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 201 = i.val
              omega
            simpa only [he] using bucket0201
        ·
          by_cases h203 : i.val < 203
          ·
            have he : (⟨202, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 202 = i.val
              omega
            simpa only [he] using bucket0202
          ·
            have he : (⟨203, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 203 = i.val
              omega
            simpa only [he] using bucket0203
      ·
        by_cases h206 : i.val < 206
        ·
          by_cases h205 : i.val < 205
          ·
            have he : (⟨204, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 204 = i.val
              omega
            simpa only [he] using bucket0204
          ·
            have he : (⟨205, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 205 = i.val
              omega
            simpa only [he] using bucket0205
        ·
          by_cases h207 : i.val < 207
          ·
            have he : (⟨206, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 206 = i.val
              omega
            simpa only [he] using bucket0206
          ·
            have he : (⟨207, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 207 = i.val
              omega
            simpa only [he] using bucket0207
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
            simpa only [he] using bucket0208
          ·
            have he : (⟨209, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 209 = i.val
              omega
            simpa only [he] using bucket0209
        ·
          by_cases h211 : i.val < 211
          ·
            have he : (⟨210, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 210 = i.val
              omega
            simpa only [he] using bucket0210
          ·
            have he : (⟨211, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 211 = i.val
              omega
            simpa only [he] using bucket0211
      ·
        by_cases h214 : i.val < 214
        ·
          by_cases h213 : i.val < 213
          ·
            have he : (⟨212, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 212 = i.val
              omega
            simpa only [he] using bucket0212
          ·
            have he : (⟨213, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 213 = i.val
              omega
            simpa only [he] using bucket0213
        ·
          by_cases h215 : i.val < 215
          ·
            have he : (⟨214, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 214 = i.val
              omega
            simpa only [he] using bucket0214
          ·
            have he : (⟨215, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 215 = i.val
              omega
            simpa only [he] using bucket0215
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
            simpa only [he] using bucket0216
          ·
            have he : (⟨217, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 217 = i.val
              omega
            simpa only [he] using bucket0217
        ·
          by_cases h219 : i.val < 219
          ·
            have he : (⟨218, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 218 = i.val
              omega
            simpa only [he] using bucket0218
          ·
            have he : (⟨219, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 219 = i.val
              omega
            simpa only [he] using bucket0219
      ·
        by_cases h222 : i.val < 222
        ·
          by_cases h221 : i.val < 221
          ·
            have he : (⟨220, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 220 = i.val
              omega
            simpa only [he] using bucket0220
          ·
            have he : (⟨221, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 221 = i.val
              omega
            simpa only [he] using bucket0221
        ·
          by_cases h223 : i.val < 223
          ·
            have he : (⟨222, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 222 = i.val
              omega
            simpa only [he] using bucket0222
          ·
            have he : (⟨223, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 223 = i.val
              omega
            simpa only [he] using bucket0223

private theorem bucketGroup0007 (i : Fin 1069)
    (hlo : 224 ≤ i.val) (hhi : i.val < 256) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0224
          ·
            have he : (⟨225, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 225 = i.val
              omega
            simpa only [he] using bucket0225
        ·
          by_cases h227 : i.val < 227
          ·
            have he : (⟨226, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 226 = i.val
              omega
            simpa only [he] using bucket0226
          ·
            have he : (⟨227, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 227 = i.val
              omega
            simpa only [he] using bucket0227
      ·
        by_cases h230 : i.val < 230
        ·
          by_cases h229 : i.val < 229
          ·
            have he : (⟨228, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 228 = i.val
              omega
            simpa only [he] using bucket0228
          ·
            have he : (⟨229, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 229 = i.val
              omega
            simpa only [he] using bucket0229
        ·
          by_cases h231 : i.val < 231
          ·
            have he : (⟨230, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 230 = i.val
              omega
            simpa only [he] using bucket0230
          ·
            have he : (⟨231, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 231 = i.val
              omega
            simpa only [he] using bucket0231
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
            simpa only [he] using bucket0232
          ·
            have he : (⟨233, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 233 = i.val
              omega
            simpa only [he] using bucket0233
        ·
          by_cases h235 : i.val < 235
          ·
            have he : (⟨234, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 234 = i.val
              omega
            simpa only [he] using bucket0234
          ·
            have he : (⟨235, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 235 = i.val
              omega
            simpa only [he] using bucket0235
      ·
        by_cases h238 : i.val < 238
        ·
          by_cases h237 : i.val < 237
          ·
            have he : (⟨236, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 236 = i.val
              omega
            simpa only [he] using bucket0236
          ·
            have he : (⟨237, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 237 = i.val
              omega
            simpa only [he] using bucket0237
        ·
          by_cases h239 : i.val < 239
          ·
            have he : (⟨238, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 238 = i.val
              omega
            simpa only [he] using bucket0238
          ·
            have he : (⟨239, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 239 = i.val
              omega
            simpa only [he] using bucket0239
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
            simpa only [he] using bucket0240
          ·
            have he : (⟨241, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 241 = i.val
              omega
            simpa only [he] using bucket0241
        ·
          by_cases h243 : i.val < 243
          ·
            have he : (⟨242, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 242 = i.val
              omega
            simpa only [he] using bucket0242
          ·
            have he : (⟨243, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 243 = i.val
              omega
            simpa only [he] using bucket0243
      ·
        by_cases h246 : i.val < 246
        ·
          by_cases h245 : i.val < 245
          ·
            have he : (⟨244, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 244 = i.val
              omega
            simpa only [he] using bucket0244
          ·
            have he : (⟨245, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 245 = i.val
              omega
            simpa only [he] using bucket0245
        ·
          by_cases h247 : i.val < 247
          ·
            have he : (⟨246, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 246 = i.val
              omega
            simpa only [he] using bucket0246
          ·
            have he : (⟨247, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 247 = i.val
              omega
            simpa only [he] using bucket0247
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
            simpa only [he] using bucket0248
          ·
            have he : (⟨249, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 249 = i.val
              omega
            simpa only [he] using bucket0249
        ·
          by_cases h251 : i.val < 251
          ·
            have he : (⟨250, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 250 = i.val
              omega
            simpa only [he] using bucket0250
          ·
            have he : (⟨251, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 251 = i.val
              omega
            simpa only [he] using bucket0251
      ·
        by_cases h254 : i.val < 254
        ·
          by_cases h253 : i.val < 253
          ·
            have he : (⟨252, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 252 = i.val
              omega
            simpa only [he] using bucket0252
          ·
            have he : (⟨253, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 253 = i.val
              omega
            simpa only [he] using bucket0253
        ·
          by_cases h255 : i.val < 255
          ·
            have he : (⟨254, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 254 = i.val
              omega
            simpa only [he] using bucket0254
          ·
            have he : (⟨255, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 255 = i.val
              omega
            simpa only [he] using bucket0255

private theorem bucketGroup0008 (i : Fin 1069)
    (hlo : 256 ≤ i.val) (hhi : i.val < 288) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0256
          ·
            have he : (⟨257, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 257 = i.val
              omega
            simpa only [he] using bucket0257
        ·
          by_cases h259 : i.val < 259
          ·
            have he : (⟨258, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 258 = i.val
              omega
            simpa only [he] using bucket0258
          ·
            have he : (⟨259, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 259 = i.val
              omega
            simpa only [he] using bucket0259
      ·
        by_cases h262 : i.val < 262
        ·
          by_cases h261 : i.val < 261
          ·
            have he : (⟨260, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 260 = i.val
              omega
            simpa only [he] using bucket0260
          ·
            have he : (⟨261, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 261 = i.val
              omega
            simpa only [he] using bucket0261
        ·
          by_cases h263 : i.val < 263
          ·
            have he : (⟨262, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 262 = i.val
              omega
            simpa only [he] using bucket0262
          ·
            have he : (⟨263, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 263 = i.val
              omega
            simpa only [he] using bucket0263
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
            simpa only [he] using bucket0264
          ·
            have he : (⟨265, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 265 = i.val
              omega
            simpa only [he] using bucket0265
        ·
          by_cases h267 : i.val < 267
          ·
            have he : (⟨266, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 266 = i.val
              omega
            simpa only [he] using bucket0266
          ·
            have he : (⟨267, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 267 = i.val
              omega
            simpa only [he] using bucket0267
      ·
        by_cases h270 : i.val < 270
        ·
          by_cases h269 : i.val < 269
          ·
            have he : (⟨268, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 268 = i.val
              omega
            simpa only [he] using bucket0268
          ·
            have he : (⟨269, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 269 = i.val
              omega
            simpa only [he] using bucket0269
        ·
          by_cases h271 : i.val < 271
          ·
            have he : (⟨270, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 270 = i.val
              omega
            simpa only [he] using bucket0270
          ·
            have he : (⟨271, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 271 = i.val
              omega
            simpa only [he] using bucket0271
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
            simpa only [he] using bucket0272
          ·
            have he : (⟨273, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 273 = i.val
              omega
            simpa only [he] using bucket0273
        ·
          by_cases h275 : i.val < 275
          ·
            have he : (⟨274, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 274 = i.val
              omega
            simpa only [he] using bucket0274
          ·
            have he : (⟨275, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 275 = i.val
              omega
            simpa only [he] using bucket0275
      ·
        by_cases h278 : i.val < 278
        ·
          by_cases h277 : i.val < 277
          ·
            have he : (⟨276, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 276 = i.val
              omega
            simpa only [he] using bucket0276
          ·
            have he : (⟨277, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 277 = i.val
              omega
            simpa only [he] using bucket0277
        ·
          by_cases h279 : i.val < 279
          ·
            have he : (⟨278, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 278 = i.val
              omega
            simpa only [he] using bucket0278
          ·
            have he : (⟨279, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 279 = i.val
              omega
            simpa only [he] using bucket0279
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
            simpa only [he] using bucket0280
          ·
            have he : (⟨281, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 281 = i.val
              omega
            simpa only [he] using bucket0281
        ·
          by_cases h283 : i.val < 283
          ·
            have he : (⟨282, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 282 = i.val
              omega
            simpa only [he] using bucket0282
          ·
            have he : (⟨283, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 283 = i.val
              omega
            simpa only [he] using bucket0283
      ·
        by_cases h286 : i.val < 286
        ·
          by_cases h285 : i.val < 285
          ·
            have he : (⟨284, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 284 = i.val
              omega
            simpa only [he] using bucket0284
          ·
            have he : (⟨285, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 285 = i.val
              omega
            simpa only [he] using bucket0285
        ·
          by_cases h287 : i.val < 287
          ·
            have he : (⟨286, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 286 = i.val
              omega
            simpa only [he] using bucket0286
          ·
            have he : (⟨287, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 287 = i.val
              omega
            simpa only [he] using bucket0287

private theorem bucketGroup0009 (i : Fin 1069)
    (hlo : 288 ≤ i.val) (hhi : i.val < 320) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0288
          ·
            have he : (⟨289, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 289 = i.val
              omega
            simpa only [he] using bucket0289
        ·
          by_cases h291 : i.val < 291
          ·
            have he : (⟨290, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 290 = i.val
              omega
            simpa only [he] using bucket0290
          ·
            have he : (⟨291, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 291 = i.val
              omega
            simpa only [he] using bucket0291
      ·
        by_cases h294 : i.val < 294
        ·
          by_cases h293 : i.val < 293
          ·
            have he : (⟨292, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 292 = i.val
              omega
            simpa only [he] using bucket0292
          ·
            have he : (⟨293, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 293 = i.val
              omega
            simpa only [he] using bucket0293
        ·
          by_cases h295 : i.val < 295
          ·
            have he : (⟨294, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 294 = i.val
              omega
            simpa only [he] using bucket0294
          ·
            have he : (⟨295, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 295 = i.val
              omega
            simpa only [he] using bucket0295
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
            simpa only [he] using bucket0296
          ·
            have he : (⟨297, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 297 = i.val
              omega
            simpa only [he] using bucket0297
        ·
          by_cases h299 : i.val < 299
          ·
            have he : (⟨298, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 298 = i.val
              omega
            simpa only [he] using bucket0298
          ·
            have he : (⟨299, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 299 = i.val
              omega
            simpa only [he] using bucket0299
      ·
        by_cases h302 : i.val < 302
        ·
          by_cases h301 : i.val < 301
          ·
            have he : (⟨300, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 300 = i.val
              omega
            simpa only [he] using bucket0300
          ·
            have he : (⟨301, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 301 = i.val
              omega
            simpa only [he] using bucket0301
        ·
          by_cases h303 : i.val < 303
          ·
            have he : (⟨302, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 302 = i.val
              omega
            simpa only [he] using bucket0302
          ·
            have he : (⟨303, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 303 = i.val
              omega
            simpa only [he] using bucket0303
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
            simpa only [he] using bucket0304
          ·
            have he : (⟨305, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 305 = i.val
              omega
            simpa only [he] using bucket0305
        ·
          by_cases h307 : i.val < 307
          ·
            have he : (⟨306, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 306 = i.val
              omega
            simpa only [he] using bucket0306
          ·
            have he : (⟨307, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 307 = i.val
              omega
            simpa only [he] using bucket0307
      ·
        by_cases h310 : i.val < 310
        ·
          by_cases h309 : i.val < 309
          ·
            have he : (⟨308, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 308 = i.val
              omega
            simpa only [he] using bucket0308
          ·
            have he : (⟨309, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 309 = i.val
              omega
            simpa only [he] using bucket0309
        ·
          by_cases h311 : i.val < 311
          ·
            have he : (⟨310, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 310 = i.val
              omega
            simpa only [he] using bucket0310
          ·
            have he : (⟨311, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 311 = i.val
              omega
            simpa only [he] using bucket0311
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
            simpa only [he] using bucket0312
          ·
            have he : (⟨313, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 313 = i.val
              omega
            simpa only [he] using bucket0313
        ·
          by_cases h315 : i.val < 315
          ·
            have he : (⟨314, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 314 = i.val
              omega
            simpa only [he] using bucket0314
          ·
            have he : (⟨315, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 315 = i.val
              omega
            simpa only [he] using bucket0315
      ·
        by_cases h318 : i.val < 318
        ·
          by_cases h317 : i.val < 317
          ·
            have he : (⟨316, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 316 = i.val
              omega
            simpa only [he] using bucket0316
          ·
            have he : (⟨317, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 317 = i.val
              omega
            simpa only [he] using bucket0317
        ·
          by_cases h319 : i.val < 319
          ·
            have he : (⟨318, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 318 = i.val
              omega
            simpa only [he] using bucket0318
          ·
            have he : (⟨319, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 319 = i.val
              omega
            simpa only [he] using bucket0319

private theorem bucketGroup0010 (i : Fin 1069)
    (hlo : 320 ≤ i.val) (hhi : i.val < 352) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0320
          ·
            have he : (⟨321, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 321 = i.val
              omega
            simpa only [he] using bucket0321
        ·
          by_cases h323 : i.val < 323
          ·
            have he : (⟨322, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 322 = i.val
              omega
            simpa only [he] using bucket0322
          ·
            have he : (⟨323, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 323 = i.val
              omega
            simpa only [he] using bucket0323
      ·
        by_cases h326 : i.val < 326
        ·
          by_cases h325 : i.val < 325
          ·
            have he : (⟨324, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 324 = i.val
              omega
            simpa only [he] using bucket0324
          ·
            have he : (⟨325, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 325 = i.val
              omega
            simpa only [he] using bucket0325
        ·
          by_cases h327 : i.val < 327
          ·
            have he : (⟨326, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 326 = i.val
              omega
            simpa only [he] using bucket0326
          ·
            have he : (⟨327, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 327 = i.val
              omega
            simpa only [he] using bucket0327
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
            simpa only [he] using bucket0328
          ·
            have he : (⟨329, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 329 = i.val
              omega
            simpa only [he] using bucket0329
        ·
          by_cases h331 : i.val < 331
          ·
            have he : (⟨330, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 330 = i.val
              omega
            simpa only [he] using bucket0330
          ·
            have he : (⟨331, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 331 = i.val
              omega
            simpa only [he] using bucket0331
      ·
        by_cases h334 : i.val < 334
        ·
          by_cases h333 : i.val < 333
          ·
            have he : (⟨332, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 332 = i.val
              omega
            simpa only [he] using bucket0332
          ·
            have he : (⟨333, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 333 = i.val
              omega
            simpa only [he] using bucket0333
        ·
          by_cases h335 : i.val < 335
          ·
            have he : (⟨334, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 334 = i.val
              omega
            simpa only [he] using bucket0334
          ·
            have he : (⟨335, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 335 = i.val
              omega
            simpa only [he] using bucket0335
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
            simpa only [he] using bucket0336
          ·
            have he : (⟨337, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 337 = i.val
              omega
            simpa only [he] using bucket0337
        ·
          by_cases h339 : i.val < 339
          ·
            have he : (⟨338, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 338 = i.val
              omega
            simpa only [he] using bucket0338
          ·
            have he : (⟨339, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 339 = i.val
              omega
            simpa only [he] using bucket0339
      ·
        by_cases h342 : i.val < 342
        ·
          by_cases h341 : i.val < 341
          ·
            have he : (⟨340, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 340 = i.val
              omega
            simpa only [he] using bucket0340
          ·
            have he : (⟨341, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 341 = i.val
              omega
            simpa only [he] using bucket0341
        ·
          by_cases h343 : i.val < 343
          ·
            have he : (⟨342, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 342 = i.val
              omega
            simpa only [he] using bucket0342
          ·
            have he : (⟨343, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 343 = i.val
              omega
            simpa only [he] using bucket0343
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
            simpa only [he] using bucket0344
          ·
            have he : (⟨345, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 345 = i.val
              omega
            simpa only [he] using bucket0345
        ·
          by_cases h347 : i.val < 347
          ·
            have he : (⟨346, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 346 = i.val
              omega
            simpa only [he] using bucket0346
          ·
            have he : (⟨347, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 347 = i.val
              omega
            simpa only [he] using bucket0347
      ·
        by_cases h350 : i.val < 350
        ·
          by_cases h349 : i.val < 349
          ·
            have he : (⟨348, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 348 = i.val
              omega
            simpa only [he] using bucket0348
          ·
            have he : (⟨349, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 349 = i.val
              omega
            simpa only [he] using bucket0349
        ·
          by_cases h351 : i.val < 351
          ·
            have he : (⟨350, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 350 = i.val
              omega
            simpa only [he] using bucket0350
          ·
            have he : (⟨351, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 351 = i.val
              omega
            simpa only [he] using bucket0351

private theorem bucketGroup0011 (i : Fin 1069)
    (hlo : 352 ≤ i.val) (hhi : i.val < 384) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0352
          ·
            have he : (⟨353, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 353 = i.val
              omega
            simpa only [he] using bucket0353
        ·
          by_cases h355 : i.val < 355
          ·
            have he : (⟨354, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 354 = i.val
              omega
            simpa only [he] using bucket0354
          ·
            have he : (⟨355, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 355 = i.val
              omega
            simpa only [he] using bucket0355
      ·
        by_cases h358 : i.val < 358
        ·
          by_cases h357 : i.val < 357
          ·
            have he : (⟨356, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 356 = i.val
              omega
            simpa only [he] using bucket0356
          ·
            have he : (⟨357, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 357 = i.val
              omega
            simpa only [he] using bucket0357
        ·
          by_cases h359 : i.val < 359
          ·
            have he : (⟨358, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 358 = i.val
              omega
            simpa only [he] using bucket0358
          ·
            have he : (⟨359, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 359 = i.val
              omega
            simpa only [he] using bucket0359
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
            simpa only [he] using bucket0360
          ·
            have he : (⟨361, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 361 = i.val
              omega
            simpa only [he] using bucket0361
        ·
          by_cases h363 : i.val < 363
          ·
            have he : (⟨362, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 362 = i.val
              omega
            simpa only [he] using bucket0362
          ·
            have he : (⟨363, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 363 = i.val
              omega
            simpa only [he] using bucket0363
      ·
        by_cases h366 : i.val < 366
        ·
          by_cases h365 : i.val < 365
          ·
            have he : (⟨364, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 364 = i.val
              omega
            simpa only [he] using bucket0364
          ·
            have he : (⟨365, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 365 = i.val
              omega
            simpa only [he] using bucket0365
        ·
          by_cases h367 : i.val < 367
          ·
            have he : (⟨366, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 366 = i.val
              omega
            simpa only [he] using bucket0366
          ·
            have he : (⟨367, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 367 = i.val
              omega
            simpa only [he] using bucket0367
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
            simpa only [he] using bucket0368
          ·
            have he : (⟨369, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 369 = i.val
              omega
            simpa only [he] using bucket0369
        ·
          by_cases h371 : i.val < 371
          ·
            have he : (⟨370, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 370 = i.val
              omega
            simpa only [he] using bucket0370
          ·
            have he : (⟨371, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 371 = i.val
              omega
            simpa only [he] using bucket0371
      ·
        by_cases h374 : i.val < 374
        ·
          by_cases h373 : i.val < 373
          ·
            have he : (⟨372, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 372 = i.val
              omega
            simpa only [he] using bucket0372
          ·
            have he : (⟨373, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 373 = i.val
              omega
            simpa only [he] using bucket0373
        ·
          by_cases h375 : i.val < 375
          ·
            have he : (⟨374, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 374 = i.val
              omega
            simpa only [he] using bucket0374
          ·
            have he : (⟨375, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 375 = i.val
              omega
            simpa only [he] using bucket0375
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
            simpa only [he] using bucket0376
          ·
            have he : (⟨377, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 377 = i.val
              omega
            simpa only [he] using bucket0377
        ·
          by_cases h379 : i.val < 379
          ·
            have he : (⟨378, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 378 = i.val
              omega
            simpa only [he] using bucket0378
          ·
            have he : (⟨379, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 379 = i.val
              omega
            simpa only [he] using bucket0379
      ·
        by_cases h382 : i.val < 382
        ·
          by_cases h381 : i.val < 381
          ·
            have he : (⟨380, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 380 = i.val
              omega
            simpa only [he] using bucket0380
          ·
            have he : (⟨381, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 381 = i.val
              omega
            simpa only [he] using bucket0381
        ·
          by_cases h383 : i.val < 383
          ·
            have he : (⟨382, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 382 = i.val
              omega
            simpa only [he] using bucket0382
          ·
            have he : (⟨383, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 383 = i.val
              omega
            simpa only [he] using bucket0383

private theorem bucketGroup0012 (i : Fin 1069)
    (hlo : 384 ≤ i.val) (hhi : i.val < 416) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0384
          ·
            have he : (⟨385, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 385 = i.val
              omega
            simpa only [he] using bucket0385
        ·
          by_cases h387 : i.val < 387
          ·
            have he : (⟨386, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 386 = i.val
              omega
            simpa only [he] using bucket0386
          ·
            have he : (⟨387, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 387 = i.val
              omega
            simpa only [he] using bucket0387
      ·
        by_cases h390 : i.val < 390
        ·
          by_cases h389 : i.val < 389
          ·
            have he : (⟨388, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 388 = i.val
              omega
            simpa only [he] using bucket0388
          ·
            have he : (⟨389, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 389 = i.val
              omega
            simpa only [he] using bucket0389
        ·
          by_cases h391 : i.val < 391
          ·
            have he : (⟨390, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 390 = i.val
              omega
            simpa only [he] using bucket0390
          ·
            have he : (⟨391, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 391 = i.val
              omega
            simpa only [he] using bucket0391
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
            simpa only [he] using bucket0392
          ·
            have he : (⟨393, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 393 = i.val
              omega
            simpa only [he] using bucket0393
        ·
          by_cases h395 : i.val < 395
          ·
            have he : (⟨394, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 394 = i.val
              omega
            simpa only [he] using bucket0394
          ·
            have he : (⟨395, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 395 = i.val
              omega
            simpa only [he] using bucket0395
      ·
        by_cases h398 : i.val < 398
        ·
          by_cases h397 : i.val < 397
          ·
            have he : (⟨396, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 396 = i.val
              omega
            simpa only [he] using bucket0396
          ·
            have he : (⟨397, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 397 = i.val
              omega
            simpa only [he] using bucket0397
        ·
          by_cases h399 : i.val < 399
          ·
            have he : (⟨398, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 398 = i.val
              omega
            simpa only [he] using bucket0398
          ·
            have he : (⟨399, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 399 = i.val
              omega
            simpa only [he] using bucket0399
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
            simpa only [he] using bucket0400
          ·
            have he : (⟨401, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 401 = i.val
              omega
            simpa only [he] using bucket0401
        ·
          by_cases h403 : i.val < 403
          ·
            have he : (⟨402, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 402 = i.val
              omega
            simpa only [he] using bucket0402
          ·
            have he : (⟨403, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 403 = i.val
              omega
            simpa only [he] using bucket0403
      ·
        by_cases h406 : i.val < 406
        ·
          by_cases h405 : i.val < 405
          ·
            have he : (⟨404, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 404 = i.val
              omega
            simpa only [he] using bucket0404
          ·
            have he : (⟨405, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 405 = i.val
              omega
            simpa only [he] using bucket0405
        ·
          by_cases h407 : i.val < 407
          ·
            have he : (⟨406, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 406 = i.val
              omega
            simpa only [he] using bucket0406
          ·
            have he : (⟨407, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 407 = i.val
              omega
            simpa only [he] using bucket0407
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
            simpa only [he] using bucket0408
          ·
            have he : (⟨409, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 409 = i.val
              omega
            simpa only [he] using bucket0409
        ·
          by_cases h411 : i.val < 411
          ·
            have he : (⟨410, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 410 = i.val
              omega
            simpa only [he] using bucket0410
          ·
            have he : (⟨411, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 411 = i.val
              omega
            simpa only [he] using bucket0411
      ·
        by_cases h414 : i.val < 414
        ·
          by_cases h413 : i.val < 413
          ·
            have he : (⟨412, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 412 = i.val
              omega
            simpa only [he] using bucket0412
          ·
            have he : (⟨413, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 413 = i.val
              omega
            simpa only [he] using bucket0413
        ·
          by_cases h415 : i.val < 415
          ·
            have he : (⟨414, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 414 = i.val
              omega
            simpa only [he] using bucket0414
          ·
            have he : (⟨415, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 415 = i.val
              omega
            simpa only [he] using bucket0415

private theorem bucketGroup0013 (i : Fin 1069)
    (hlo : 416 ≤ i.val) (hhi : i.val < 448) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0416
          ·
            have he : (⟨417, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 417 = i.val
              omega
            simpa only [he] using bucket0417
        ·
          by_cases h419 : i.val < 419
          ·
            have he : (⟨418, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 418 = i.val
              omega
            simpa only [he] using bucket0418
          ·
            have he : (⟨419, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 419 = i.val
              omega
            simpa only [he] using bucket0419
      ·
        by_cases h422 : i.val < 422
        ·
          by_cases h421 : i.val < 421
          ·
            have he : (⟨420, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 420 = i.val
              omega
            simpa only [he] using bucket0420
          ·
            have he : (⟨421, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 421 = i.val
              omega
            simpa only [he] using bucket0421
        ·
          by_cases h423 : i.val < 423
          ·
            have he : (⟨422, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 422 = i.val
              omega
            simpa only [he] using bucket0422
          ·
            have he : (⟨423, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 423 = i.val
              omega
            simpa only [he] using bucket0423
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
            simpa only [he] using bucket0424
          ·
            have he : (⟨425, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 425 = i.val
              omega
            simpa only [he] using bucket0425
        ·
          by_cases h427 : i.val < 427
          ·
            have he : (⟨426, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 426 = i.val
              omega
            simpa only [he] using bucket0426
          ·
            have he : (⟨427, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 427 = i.val
              omega
            simpa only [he] using bucket0427
      ·
        by_cases h430 : i.val < 430
        ·
          by_cases h429 : i.val < 429
          ·
            have he : (⟨428, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 428 = i.val
              omega
            simpa only [he] using bucket0428
          ·
            have he : (⟨429, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 429 = i.val
              omega
            simpa only [he] using bucket0429
        ·
          by_cases h431 : i.val < 431
          ·
            have he : (⟨430, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 430 = i.val
              omega
            simpa only [he] using bucket0430
          ·
            have he : (⟨431, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 431 = i.val
              omega
            simpa only [he] using bucket0431
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
            simpa only [he] using bucket0432
          ·
            have he : (⟨433, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 433 = i.val
              omega
            simpa only [he] using bucket0433
        ·
          by_cases h435 : i.val < 435
          ·
            have he : (⟨434, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 434 = i.val
              omega
            simpa only [he] using bucket0434
          ·
            have he : (⟨435, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 435 = i.val
              omega
            simpa only [he] using bucket0435
      ·
        by_cases h438 : i.val < 438
        ·
          by_cases h437 : i.val < 437
          ·
            have he : (⟨436, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 436 = i.val
              omega
            simpa only [he] using bucket0436
          ·
            have he : (⟨437, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 437 = i.val
              omega
            simpa only [he] using bucket0437
        ·
          by_cases h439 : i.val < 439
          ·
            have he : (⟨438, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 438 = i.val
              omega
            simpa only [he] using bucket0438
          ·
            have he : (⟨439, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 439 = i.val
              omega
            simpa only [he] using bucket0439
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
            simpa only [he] using bucket0440
          ·
            have he : (⟨441, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 441 = i.val
              omega
            simpa only [he] using bucket0441
        ·
          by_cases h443 : i.val < 443
          ·
            have he : (⟨442, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 442 = i.val
              omega
            simpa only [he] using bucket0442
          ·
            have he : (⟨443, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 443 = i.val
              omega
            simpa only [he] using bucket0443
      ·
        by_cases h446 : i.val < 446
        ·
          by_cases h445 : i.val < 445
          ·
            have he : (⟨444, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 444 = i.val
              omega
            simpa only [he] using bucket0444
          ·
            have he : (⟨445, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 445 = i.val
              omega
            simpa only [he] using bucket0445
        ·
          by_cases h447 : i.val < 447
          ·
            have he : (⟨446, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 446 = i.val
              omega
            simpa only [he] using bucket0446
          ·
            have he : (⟨447, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 447 = i.val
              omega
            simpa only [he] using bucket0447

private theorem bucketGroup0014 (i : Fin 1069)
    (hlo : 448 ≤ i.val) (hhi : i.val < 480) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0448
          ·
            have he : (⟨449, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 449 = i.val
              omega
            simpa only [he] using bucket0449
        ·
          by_cases h451 : i.val < 451
          ·
            have he : (⟨450, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 450 = i.val
              omega
            simpa only [he] using bucket0450
          ·
            have he : (⟨451, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 451 = i.val
              omega
            simpa only [he] using bucket0451
      ·
        by_cases h454 : i.val < 454
        ·
          by_cases h453 : i.val < 453
          ·
            have he : (⟨452, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 452 = i.val
              omega
            simpa only [he] using bucket0452
          ·
            have he : (⟨453, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 453 = i.val
              omega
            simpa only [he] using bucket0453
        ·
          by_cases h455 : i.val < 455
          ·
            have he : (⟨454, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 454 = i.val
              omega
            simpa only [he] using bucket0454
          ·
            have he : (⟨455, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 455 = i.val
              omega
            simpa only [he] using bucket0455
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
            simpa only [he] using bucket0456
          ·
            have he : (⟨457, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 457 = i.val
              omega
            simpa only [he] using bucket0457
        ·
          by_cases h459 : i.val < 459
          ·
            have he : (⟨458, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 458 = i.val
              omega
            simpa only [he] using bucket0458
          ·
            have he : (⟨459, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 459 = i.val
              omega
            simpa only [he] using bucket0459
      ·
        by_cases h462 : i.val < 462
        ·
          by_cases h461 : i.val < 461
          ·
            have he : (⟨460, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 460 = i.val
              omega
            simpa only [he] using bucket0460
          ·
            have he : (⟨461, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 461 = i.val
              omega
            simpa only [he] using bucket0461
        ·
          by_cases h463 : i.val < 463
          ·
            have he : (⟨462, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 462 = i.val
              omega
            simpa only [he] using bucket0462
          ·
            have he : (⟨463, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 463 = i.val
              omega
            simpa only [he] using bucket0463
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
            simpa only [he] using bucket0464
          ·
            have he : (⟨465, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 465 = i.val
              omega
            simpa only [he] using bucket0465
        ·
          by_cases h467 : i.val < 467
          ·
            have he : (⟨466, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 466 = i.val
              omega
            simpa only [he] using bucket0466
          ·
            have he : (⟨467, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 467 = i.val
              omega
            simpa only [he] using bucket0467
      ·
        by_cases h470 : i.val < 470
        ·
          by_cases h469 : i.val < 469
          ·
            have he : (⟨468, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 468 = i.val
              omega
            simpa only [he] using bucket0468
          ·
            have he : (⟨469, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 469 = i.val
              omega
            simpa only [he] using bucket0469
        ·
          by_cases h471 : i.val < 471
          ·
            have he : (⟨470, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 470 = i.val
              omega
            simpa only [he] using bucket0470
          ·
            have he : (⟨471, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 471 = i.val
              omega
            simpa only [he] using bucket0471
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
            simpa only [he] using bucket0472
          ·
            have he : (⟨473, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 473 = i.val
              omega
            simpa only [he] using bucket0473
        ·
          by_cases h475 : i.val < 475
          ·
            have he : (⟨474, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 474 = i.val
              omega
            simpa only [he] using bucket0474
          ·
            have he : (⟨475, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 475 = i.val
              omega
            simpa only [he] using bucket0475
      ·
        by_cases h478 : i.val < 478
        ·
          by_cases h477 : i.val < 477
          ·
            have he : (⟨476, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 476 = i.val
              omega
            simpa only [he] using bucket0476
          ·
            have he : (⟨477, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 477 = i.val
              omega
            simpa only [he] using bucket0477
        ·
          by_cases h479 : i.val < 479
          ·
            have he : (⟨478, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 478 = i.val
              omega
            simpa only [he] using bucket0478
          ·
            have he : (⟨479, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 479 = i.val
              omega
            simpa only [he] using bucket0479

private theorem bucketGroup0015 (i : Fin 1069)
    (hlo : 480 ≤ i.val) (hhi : i.val < 512) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0480
          ·
            have he : (⟨481, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 481 = i.val
              omega
            simpa only [he] using bucket0481
        ·
          by_cases h483 : i.val < 483
          ·
            have he : (⟨482, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 482 = i.val
              omega
            simpa only [he] using bucket0482
          ·
            have he : (⟨483, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 483 = i.val
              omega
            simpa only [he] using bucket0483
      ·
        by_cases h486 : i.val < 486
        ·
          by_cases h485 : i.val < 485
          ·
            have he : (⟨484, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 484 = i.val
              omega
            simpa only [he] using bucket0484
          ·
            have he : (⟨485, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 485 = i.val
              omega
            simpa only [he] using bucket0485
        ·
          by_cases h487 : i.val < 487
          ·
            have he : (⟨486, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 486 = i.val
              omega
            simpa only [he] using bucket0486
          ·
            have he : (⟨487, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 487 = i.val
              omega
            simpa only [he] using bucket0487
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
            simpa only [he] using bucket0488
          ·
            have he : (⟨489, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 489 = i.val
              omega
            simpa only [he] using bucket0489
        ·
          by_cases h491 : i.val < 491
          ·
            have he : (⟨490, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 490 = i.val
              omega
            simpa only [he] using bucket0490
          ·
            have he : (⟨491, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 491 = i.val
              omega
            simpa only [he] using bucket0491
      ·
        by_cases h494 : i.val < 494
        ·
          by_cases h493 : i.val < 493
          ·
            have he : (⟨492, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 492 = i.val
              omega
            simpa only [he] using bucket0492
          ·
            have he : (⟨493, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 493 = i.val
              omega
            simpa only [he] using bucket0493
        ·
          by_cases h495 : i.val < 495
          ·
            have he : (⟨494, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 494 = i.val
              omega
            simpa only [he] using bucket0494
          ·
            have he : (⟨495, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 495 = i.val
              omega
            simpa only [he] using bucket0495
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
            simpa only [he] using bucket0496
          ·
            have he : (⟨497, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 497 = i.val
              omega
            simpa only [he] using bucket0497
        ·
          by_cases h499 : i.val < 499
          ·
            have he : (⟨498, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 498 = i.val
              omega
            simpa only [he] using bucket0498
          ·
            have he : (⟨499, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 499 = i.val
              omega
            simpa only [he] using bucket0499
      ·
        by_cases h502 : i.val < 502
        ·
          by_cases h501 : i.val < 501
          ·
            have he : (⟨500, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 500 = i.val
              omega
            simpa only [he] using bucket0500
          ·
            have he : (⟨501, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 501 = i.val
              omega
            simpa only [he] using bucket0501
        ·
          by_cases h503 : i.val < 503
          ·
            have he : (⟨502, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 502 = i.val
              omega
            simpa only [he] using bucket0502
          ·
            have he : (⟨503, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 503 = i.val
              omega
            simpa only [he] using bucket0503
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
            simpa only [he] using bucket0504
          ·
            have he : (⟨505, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 505 = i.val
              omega
            simpa only [he] using bucket0505
        ·
          by_cases h507 : i.val < 507
          ·
            have he : (⟨506, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 506 = i.val
              omega
            simpa only [he] using bucket0506
          ·
            have he : (⟨507, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 507 = i.val
              omega
            simpa only [he] using bucket0507
      ·
        by_cases h510 : i.val < 510
        ·
          by_cases h509 : i.val < 509
          ·
            have he : (⟨508, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 508 = i.val
              omega
            simpa only [he] using bucket0508
          ·
            have he : (⟨509, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 509 = i.val
              omega
            simpa only [he] using bucket0509
        ·
          by_cases h511 : i.val < 511
          ·
            have he : (⟨510, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 510 = i.val
              omega
            simpa only [he] using bucket0510
          ·
            have he : (⟨511, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 511 = i.val
              omega
            simpa only [he] using bucket0511

private theorem bucketGroup0016 (i : Fin 1069)
    (hlo : 512 ≤ i.val) (hhi : i.val < 544) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0512
          ·
            have he : (⟨513, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 513 = i.val
              omega
            simpa only [he] using bucket0513
        ·
          by_cases h515 : i.val < 515
          ·
            have he : (⟨514, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 514 = i.val
              omega
            simpa only [he] using bucket0514
          ·
            have he : (⟨515, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 515 = i.val
              omega
            simpa only [he] using bucket0515
      ·
        by_cases h518 : i.val < 518
        ·
          by_cases h517 : i.val < 517
          ·
            have he : (⟨516, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 516 = i.val
              omega
            simpa only [he] using bucket0516
          ·
            have he : (⟨517, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 517 = i.val
              omega
            simpa only [he] using bucket0517
        ·
          by_cases h519 : i.val < 519
          ·
            have he : (⟨518, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 518 = i.val
              omega
            simpa only [he] using bucket0518
          ·
            have he : (⟨519, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 519 = i.val
              omega
            simpa only [he] using bucket0519
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
            simpa only [he] using bucket0520
          ·
            have he : (⟨521, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 521 = i.val
              omega
            simpa only [he] using bucket0521
        ·
          by_cases h523 : i.val < 523
          ·
            have he : (⟨522, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 522 = i.val
              omega
            simpa only [he] using bucket0522
          ·
            have he : (⟨523, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 523 = i.val
              omega
            simpa only [he] using bucket0523
      ·
        by_cases h526 : i.val < 526
        ·
          by_cases h525 : i.val < 525
          ·
            have he : (⟨524, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 524 = i.val
              omega
            simpa only [he] using bucket0524
          ·
            have he : (⟨525, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 525 = i.val
              omega
            simpa only [he] using bucket0525
        ·
          by_cases h527 : i.val < 527
          ·
            have he : (⟨526, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 526 = i.val
              omega
            simpa only [he] using bucket0526
          ·
            have he : (⟨527, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 527 = i.val
              omega
            simpa only [he] using bucket0527
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
            simpa only [he] using bucket0528
          ·
            have he : (⟨529, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 529 = i.val
              omega
            simpa only [he] using bucket0529
        ·
          by_cases h531 : i.val < 531
          ·
            have he : (⟨530, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 530 = i.val
              omega
            simpa only [he] using bucket0530
          ·
            have he : (⟨531, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 531 = i.val
              omega
            simpa only [he] using bucket0531
      ·
        by_cases h534 : i.val < 534
        ·
          by_cases h533 : i.val < 533
          ·
            have he : (⟨532, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 532 = i.val
              omega
            simpa only [he] using bucket0532
          ·
            have he : (⟨533, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 533 = i.val
              omega
            simpa only [he] using bucket0533
        ·
          by_cases h535 : i.val < 535
          ·
            have he : (⟨534, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 534 = i.val
              omega
            simpa only [he] using bucket0534
          ·
            have he : (⟨535, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 535 = i.val
              omega
            simpa only [he] using bucket0535
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
            simpa only [he] using bucket0536
          ·
            have he : (⟨537, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 537 = i.val
              omega
            simpa only [he] using bucket0537
        ·
          by_cases h539 : i.val < 539
          ·
            have he : (⟨538, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 538 = i.val
              omega
            simpa only [he] using bucket0538
          ·
            have he : (⟨539, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 539 = i.val
              omega
            simpa only [he] using bucket0539
      ·
        by_cases h542 : i.val < 542
        ·
          by_cases h541 : i.val < 541
          ·
            have he : (⟨540, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 540 = i.val
              omega
            simpa only [he] using bucket0540
          ·
            have he : (⟨541, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 541 = i.val
              omega
            simpa only [he] using bucket0541
        ·
          by_cases h543 : i.val < 543
          ·
            have he : (⟨542, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 542 = i.val
              omega
            simpa only [he] using bucket0542
          ·
            have he : (⟨543, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 543 = i.val
              omega
            simpa only [he] using bucket0543

private theorem bucketGroup0017 (i : Fin 1069)
    (hlo : 544 ≤ i.val) (hhi : i.val < 576) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0544
          ·
            have he : (⟨545, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 545 = i.val
              omega
            simpa only [he] using bucket0545
        ·
          by_cases h547 : i.val < 547
          ·
            have he : (⟨546, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 546 = i.val
              omega
            simpa only [he] using bucket0546
          ·
            have he : (⟨547, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 547 = i.val
              omega
            simpa only [he] using bucket0547
      ·
        by_cases h550 : i.val < 550
        ·
          by_cases h549 : i.val < 549
          ·
            have he : (⟨548, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 548 = i.val
              omega
            simpa only [he] using bucket0548
          ·
            have he : (⟨549, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 549 = i.val
              omega
            simpa only [he] using bucket0549
        ·
          by_cases h551 : i.val < 551
          ·
            have he : (⟨550, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 550 = i.val
              omega
            simpa only [he] using bucket0550
          ·
            have he : (⟨551, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 551 = i.val
              omega
            simpa only [he] using bucket0551
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
            simpa only [he] using bucket0552
          ·
            have he : (⟨553, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 553 = i.val
              omega
            simpa only [he] using bucket0553
        ·
          by_cases h555 : i.val < 555
          ·
            have he : (⟨554, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 554 = i.val
              omega
            simpa only [he] using bucket0554
          ·
            have he : (⟨555, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 555 = i.val
              omega
            simpa only [he] using bucket0555
      ·
        by_cases h558 : i.val < 558
        ·
          by_cases h557 : i.val < 557
          ·
            have he : (⟨556, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 556 = i.val
              omega
            simpa only [he] using bucket0556
          ·
            have he : (⟨557, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 557 = i.val
              omega
            simpa only [he] using bucket0557
        ·
          by_cases h559 : i.val < 559
          ·
            have he : (⟨558, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 558 = i.val
              omega
            simpa only [he] using bucket0558
          ·
            have he : (⟨559, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 559 = i.val
              omega
            simpa only [he] using bucket0559
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
            simpa only [he] using bucket0560
          ·
            have he : (⟨561, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 561 = i.val
              omega
            simpa only [he] using bucket0561
        ·
          by_cases h563 : i.val < 563
          ·
            have he : (⟨562, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 562 = i.val
              omega
            simpa only [he] using bucket0562
          ·
            have he : (⟨563, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 563 = i.val
              omega
            simpa only [he] using bucket0563
      ·
        by_cases h566 : i.val < 566
        ·
          by_cases h565 : i.val < 565
          ·
            have he : (⟨564, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 564 = i.val
              omega
            simpa only [he] using bucket0564
          ·
            have he : (⟨565, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 565 = i.val
              omega
            simpa only [he] using bucket0565
        ·
          by_cases h567 : i.val < 567
          ·
            have he : (⟨566, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 566 = i.val
              omega
            simpa only [he] using bucket0566
          ·
            have he : (⟨567, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 567 = i.val
              omega
            simpa only [he] using bucket0567
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
            simpa only [he] using bucket0568
          ·
            have he : (⟨569, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 569 = i.val
              omega
            simpa only [he] using bucket0569
        ·
          by_cases h571 : i.val < 571
          ·
            have he : (⟨570, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 570 = i.val
              omega
            simpa only [he] using bucket0570
          ·
            have he : (⟨571, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 571 = i.val
              omega
            simpa only [he] using bucket0571
      ·
        by_cases h574 : i.val < 574
        ·
          by_cases h573 : i.val < 573
          ·
            have he : (⟨572, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 572 = i.val
              omega
            simpa only [he] using bucket0572
          ·
            have he : (⟨573, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 573 = i.val
              omega
            simpa only [he] using bucket0573
        ·
          by_cases h575 : i.val < 575
          ·
            have he : (⟨574, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 574 = i.val
              omega
            simpa only [he] using bucket0574
          ·
            have he : (⟨575, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 575 = i.val
              omega
            simpa only [he] using bucket0575

private theorem bucketGroup0018 (i : Fin 1069)
    (hlo : 576 ≤ i.val) (hhi : i.val < 608) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0576
          ·
            have he : (⟨577, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 577 = i.val
              omega
            simpa only [he] using bucket0577
        ·
          by_cases h579 : i.val < 579
          ·
            have he : (⟨578, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 578 = i.val
              omega
            simpa only [he] using bucket0578
          ·
            have he : (⟨579, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 579 = i.val
              omega
            simpa only [he] using bucket0579
      ·
        by_cases h582 : i.val < 582
        ·
          by_cases h581 : i.val < 581
          ·
            have he : (⟨580, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 580 = i.val
              omega
            simpa only [he] using bucket0580
          ·
            have he : (⟨581, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 581 = i.val
              omega
            simpa only [he] using bucket0581
        ·
          by_cases h583 : i.val < 583
          ·
            have he : (⟨582, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 582 = i.val
              omega
            simpa only [he] using bucket0582
          ·
            have he : (⟨583, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 583 = i.val
              omega
            simpa only [he] using bucket0583
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
            simpa only [he] using bucket0584
          ·
            have he : (⟨585, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 585 = i.val
              omega
            simpa only [he] using bucket0585
        ·
          by_cases h587 : i.val < 587
          ·
            have he : (⟨586, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 586 = i.val
              omega
            simpa only [he] using bucket0586
          ·
            have he : (⟨587, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 587 = i.val
              omega
            simpa only [he] using bucket0587
      ·
        by_cases h590 : i.val < 590
        ·
          by_cases h589 : i.val < 589
          ·
            have he : (⟨588, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 588 = i.val
              omega
            simpa only [he] using bucket0588
          ·
            have he : (⟨589, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 589 = i.val
              omega
            simpa only [he] using bucket0589
        ·
          by_cases h591 : i.val < 591
          ·
            have he : (⟨590, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 590 = i.val
              omega
            simpa only [he] using bucket0590
          ·
            have he : (⟨591, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 591 = i.val
              omega
            simpa only [he] using bucket0591
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
            simpa only [he] using bucket0592
          ·
            have he : (⟨593, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 593 = i.val
              omega
            simpa only [he] using bucket0593
        ·
          by_cases h595 : i.val < 595
          ·
            have he : (⟨594, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 594 = i.val
              omega
            simpa only [he] using bucket0594
          ·
            have he : (⟨595, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 595 = i.val
              omega
            simpa only [he] using bucket0595
      ·
        by_cases h598 : i.val < 598
        ·
          by_cases h597 : i.val < 597
          ·
            have he : (⟨596, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 596 = i.val
              omega
            simpa only [he] using bucket0596
          ·
            have he : (⟨597, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 597 = i.val
              omega
            simpa only [he] using bucket0597
        ·
          by_cases h599 : i.val < 599
          ·
            have he : (⟨598, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 598 = i.val
              omega
            simpa only [he] using bucket0598
          ·
            have he : (⟨599, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 599 = i.val
              omega
            simpa only [he] using bucket0599
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
            simpa only [he] using bucket0600
          ·
            have he : (⟨601, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 601 = i.val
              omega
            simpa only [he] using bucket0601
        ·
          by_cases h603 : i.val < 603
          ·
            have he : (⟨602, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 602 = i.val
              omega
            simpa only [he] using bucket0602
          ·
            have he : (⟨603, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 603 = i.val
              omega
            simpa only [he] using bucket0603
      ·
        by_cases h606 : i.val < 606
        ·
          by_cases h605 : i.val < 605
          ·
            have he : (⟨604, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 604 = i.val
              omega
            simpa only [he] using bucket0604
          ·
            have he : (⟨605, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 605 = i.val
              omega
            simpa only [he] using bucket0605
        ·
          by_cases h607 : i.val < 607
          ·
            have he : (⟨606, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 606 = i.val
              omega
            simpa only [he] using bucket0606
          ·
            have he : (⟨607, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 607 = i.val
              omega
            simpa only [he] using bucket0607

private theorem bucketGroup0019 (i : Fin 1069)
    (hlo : 608 ≤ i.val) (hhi : i.val < 640) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0608
          ·
            have he : (⟨609, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 609 = i.val
              omega
            simpa only [he] using bucket0609
        ·
          by_cases h611 : i.val < 611
          ·
            have he : (⟨610, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 610 = i.val
              omega
            simpa only [he] using bucket0610
          ·
            have he : (⟨611, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 611 = i.val
              omega
            simpa only [he] using bucket0611
      ·
        by_cases h614 : i.val < 614
        ·
          by_cases h613 : i.val < 613
          ·
            have he : (⟨612, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 612 = i.val
              omega
            simpa only [he] using bucket0612
          ·
            have he : (⟨613, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 613 = i.val
              omega
            simpa only [he] using bucket0613
        ·
          by_cases h615 : i.val < 615
          ·
            have he : (⟨614, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 614 = i.val
              omega
            simpa only [he] using bucket0614
          ·
            have he : (⟨615, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 615 = i.val
              omega
            simpa only [he] using bucket0615
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
            simpa only [he] using bucket0616
          ·
            have he : (⟨617, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 617 = i.val
              omega
            simpa only [he] using bucket0617
        ·
          by_cases h619 : i.val < 619
          ·
            have he : (⟨618, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 618 = i.val
              omega
            simpa only [he] using bucket0618
          ·
            have he : (⟨619, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 619 = i.val
              omega
            simpa only [he] using bucket0619
      ·
        by_cases h622 : i.val < 622
        ·
          by_cases h621 : i.val < 621
          ·
            have he : (⟨620, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 620 = i.val
              omega
            simpa only [he] using bucket0620
          ·
            have he : (⟨621, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 621 = i.val
              omega
            simpa only [he] using bucket0621
        ·
          by_cases h623 : i.val < 623
          ·
            have he : (⟨622, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 622 = i.val
              omega
            simpa only [he] using bucket0622
          ·
            have he : (⟨623, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 623 = i.val
              omega
            simpa only [he] using bucket0623
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
            simpa only [he] using bucket0624
          ·
            have he : (⟨625, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 625 = i.val
              omega
            simpa only [he] using bucket0625
        ·
          by_cases h627 : i.val < 627
          ·
            have he : (⟨626, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 626 = i.val
              omega
            simpa only [he] using bucket0626
          ·
            have he : (⟨627, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 627 = i.val
              omega
            simpa only [he] using bucket0627
      ·
        by_cases h630 : i.val < 630
        ·
          by_cases h629 : i.val < 629
          ·
            have he : (⟨628, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 628 = i.val
              omega
            simpa only [he] using bucket0628
          ·
            have he : (⟨629, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 629 = i.val
              omega
            simpa only [he] using bucket0629
        ·
          by_cases h631 : i.val < 631
          ·
            have he : (⟨630, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 630 = i.val
              omega
            simpa only [he] using bucket0630
          ·
            have he : (⟨631, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 631 = i.val
              omega
            simpa only [he] using bucket0631
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
            simpa only [he] using bucket0632
          ·
            have he : (⟨633, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 633 = i.val
              omega
            simpa only [he] using bucket0633
        ·
          by_cases h635 : i.val < 635
          ·
            have he : (⟨634, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 634 = i.val
              omega
            simpa only [he] using bucket0634
          ·
            have he : (⟨635, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 635 = i.val
              omega
            simpa only [he] using bucket0635
      ·
        by_cases h638 : i.val < 638
        ·
          by_cases h637 : i.val < 637
          ·
            have he : (⟨636, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 636 = i.val
              omega
            simpa only [he] using bucket0636
          ·
            have he : (⟨637, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 637 = i.val
              omega
            simpa only [he] using bucket0637
        ·
          by_cases h639 : i.val < 639
          ·
            have he : (⟨638, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 638 = i.val
              omega
            simpa only [he] using bucket0638
          ·
            have he : (⟨639, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 639 = i.val
              omega
            simpa only [he] using bucket0639

private theorem bucketGroup0020 (i : Fin 1069)
    (hlo : 640 ≤ i.val) (hhi : i.val < 672) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0640
          ·
            have he : (⟨641, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 641 = i.val
              omega
            simpa only [he] using bucket0641
        ·
          by_cases h643 : i.val < 643
          ·
            have he : (⟨642, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 642 = i.val
              omega
            simpa only [he] using bucket0642
          ·
            have he : (⟨643, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 643 = i.val
              omega
            simpa only [he] using bucket0643
      ·
        by_cases h646 : i.val < 646
        ·
          by_cases h645 : i.val < 645
          ·
            have he : (⟨644, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 644 = i.val
              omega
            simpa only [he] using bucket0644
          ·
            have he : (⟨645, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 645 = i.val
              omega
            simpa only [he] using bucket0645
        ·
          by_cases h647 : i.val < 647
          ·
            have he : (⟨646, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 646 = i.val
              omega
            simpa only [he] using bucket0646
          ·
            have he : (⟨647, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 647 = i.val
              omega
            simpa only [he] using bucket0647
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
            simpa only [he] using bucket0648
          ·
            have he : (⟨649, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 649 = i.val
              omega
            simpa only [he] using bucket0649
        ·
          by_cases h651 : i.val < 651
          ·
            have he : (⟨650, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 650 = i.val
              omega
            simpa only [he] using bucket0650
          ·
            have he : (⟨651, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 651 = i.val
              omega
            simpa only [he] using bucket0651
      ·
        by_cases h654 : i.val < 654
        ·
          by_cases h653 : i.val < 653
          ·
            have he : (⟨652, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 652 = i.val
              omega
            simpa only [he] using bucket0652
          ·
            have he : (⟨653, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 653 = i.val
              omega
            simpa only [he] using bucket0653
        ·
          by_cases h655 : i.val < 655
          ·
            have he : (⟨654, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 654 = i.val
              omega
            simpa only [he] using bucket0654
          ·
            have he : (⟨655, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 655 = i.val
              omega
            simpa only [he] using bucket0655
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
            simpa only [he] using bucket0656
          ·
            have he : (⟨657, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 657 = i.val
              omega
            simpa only [he] using bucket0657
        ·
          by_cases h659 : i.val < 659
          ·
            have he : (⟨658, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 658 = i.val
              omega
            simpa only [he] using bucket0658
          ·
            have he : (⟨659, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 659 = i.val
              omega
            simpa only [he] using bucket0659
      ·
        by_cases h662 : i.val < 662
        ·
          by_cases h661 : i.val < 661
          ·
            have he : (⟨660, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 660 = i.val
              omega
            simpa only [he] using bucket0660
          ·
            have he : (⟨661, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 661 = i.val
              omega
            simpa only [he] using bucket0661
        ·
          by_cases h663 : i.val < 663
          ·
            have he : (⟨662, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 662 = i.val
              omega
            simpa only [he] using bucket0662
          ·
            have he : (⟨663, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 663 = i.val
              omega
            simpa only [he] using bucket0663
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
            simpa only [he] using bucket0664
          ·
            have he : (⟨665, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 665 = i.val
              omega
            simpa only [he] using bucket0665
        ·
          by_cases h667 : i.val < 667
          ·
            have he : (⟨666, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 666 = i.val
              omega
            simpa only [he] using bucket0666
          ·
            have he : (⟨667, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 667 = i.val
              omega
            simpa only [he] using bucket0667
      ·
        by_cases h670 : i.val < 670
        ·
          by_cases h669 : i.val < 669
          ·
            have he : (⟨668, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 668 = i.val
              omega
            simpa only [he] using bucket0668
          ·
            have he : (⟨669, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 669 = i.val
              omega
            simpa only [he] using bucket0669
        ·
          by_cases h671 : i.val < 671
          ·
            have he : (⟨670, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 670 = i.val
              omega
            simpa only [he] using bucket0670
          ·
            have he : (⟨671, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 671 = i.val
              omega
            simpa only [he] using bucket0671

private theorem bucketGroup0021 (i : Fin 1069)
    (hlo : 672 ≤ i.val) (hhi : i.val < 704) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0672
          ·
            have he : (⟨673, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 673 = i.val
              omega
            simpa only [he] using bucket0673
        ·
          by_cases h675 : i.val < 675
          ·
            have he : (⟨674, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 674 = i.val
              omega
            simpa only [he] using bucket0674
          ·
            have he : (⟨675, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 675 = i.val
              omega
            simpa only [he] using bucket0675
      ·
        by_cases h678 : i.val < 678
        ·
          by_cases h677 : i.val < 677
          ·
            have he : (⟨676, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 676 = i.val
              omega
            simpa only [he] using bucket0676
          ·
            have he : (⟨677, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 677 = i.val
              omega
            simpa only [he] using bucket0677
        ·
          by_cases h679 : i.val < 679
          ·
            have he : (⟨678, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 678 = i.val
              omega
            simpa only [he] using bucket0678
          ·
            have he : (⟨679, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 679 = i.val
              omega
            simpa only [he] using bucket0679
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
            simpa only [he] using bucket0680
          ·
            have he : (⟨681, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 681 = i.val
              omega
            simpa only [he] using bucket0681
        ·
          by_cases h683 : i.val < 683
          ·
            have he : (⟨682, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 682 = i.val
              omega
            simpa only [he] using bucket0682
          ·
            have he : (⟨683, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 683 = i.val
              omega
            simpa only [he] using bucket0683
      ·
        by_cases h686 : i.val < 686
        ·
          by_cases h685 : i.val < 685
          ·
            have he : (⟨684, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 684 = i.val
              omega
            simpa only [he] using bucket0684
          ·
            have he : (⟨685, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 685 = i.val
              omega
            simpa only [he] using bucket0685
        ·
          by_cases h687 : i.val < 687
          ·
            have he : (⟨686, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 686 = i.val
              omega
            simpa only [he] using bucket0686
          ·
            have he : (⟨687, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 687 = i.val
              omega
            simpa only [he] using bucket0687
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
            simpa only [he] using bucket0688
          ·
            have he : (⟨689, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 689 = i.val
              omega
            simpa only [he] using bucket0689
        ·
          by_cases h691 : i.val < 691
          ·
            have he : (⟨690, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 690 = i.val
              omega
            simpa only [he] using bucket0690
          ·
            have he : (⟨691, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 691 = i.val
              omega
            simpa only [he] using bucket0691
      ·
        by_cases h694 : i.val < 694
        ·
          by_cases h693 : i.val < 693
          ·
            have he : (⟨692, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 692 = i.val
              omega
            simpa only [he] using bucket0692
          ·
            have he : (⟨693, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 693 = i.val
              omega
            simpa only [he] using bucket0693
        ·
          by_cases h695 : i.val < 695
          ·
            have he : (⟨694, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 694 = i.val
              omega
            simpa only [he] using bucket0694
          ·
            have he : (⟨695, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 695 = i.val
              omega
            simpa only [he] using bucket0695
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
            simpa only [he] using bucket0696
          ·
            have he : (⟨697, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 697 = i.val
              omega
            simpa only [he] using bucket0697
        ·
          by_cases h699 : i.val < 699
          ·
            have he : (⟨698, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 698 = i.val
              omega
            simpa only [he] using bucket0698
          ·
            have he : (⟨699, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 699 = i.val
              omega
            simpa only [he] using bucket0699
      ·
        by_cases h702 : i.val < 702
        ·
          by_cases h701 : i.val < 701
          ·
            have he : (⟨700, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 700 = i.val
              omega
            simpa only [he] using bucket0700
          ·
            have he : (⟨701, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 701 = i.val
              omega
            simpa only [he] using bucket0701
        ·
          by_cases h703 : i.val < 703
          ·
            have he : (⟨702, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 702 = i.val
              omega
            simpa only [he] using bucket0702
          ·
            have he : (⟨703, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 703 = i.val
              omega
            simpa only [he] using bucket0703

private theorem bucketGroup0022 (i : Fin 1069)
    (hlo : 704 ≤ i.val) (hhi : i.val < 736) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0704
          ·
            have he : (⟨705, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 705 = i.val
              omega
            simpa only [he] using bucket0705
        ·
          by_cases h707 : i.val < 707
          ·
            have he : (⟨706, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 706 = i.val
              omega
            simpa only [he] using bucket0706
          ·
            have he : (⟨707, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 707 = i.val
              omega
            simpa only [he] using bucket0707
      ·
        by_cases h710 : i.val < 710
        ·
          by_cases h709 : i.val < 709
          ·
            have he : (⟨708, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 708 = i.val
              omega
            simpa only [he] using bucket0708
          ·
            have he : (⟨709, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 709 = i.val
              omega
            simpa only [he] using bucket0709
        ·
          by_cases h711 : i.val < 711
          ·
            have he : (⟨710, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 710 = i.val
              omega
            simpa only [he] using bucket0710
          ·
            have he : (⟨711, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 711 = i.val
              omega
            simpa only [he] using bucket0711
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
            simpa only [he] using bucket0712
          ·
            have he : (⟨713, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 713 = i.val
              omega
            simpa only [he] using bucket0713
        ·
          by_cases h715 : i.val < 715
          ·
            have he : (⟨714, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 714 = i.val
              omega
            simpa only [he] using bucket0714
          ·
            have he : (⟨715, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 715 = i.val
              omega
            simpa only [he] using bucket0715
      ·
        by_cases h718 : i.val < 718
        ·
          by_cases h717 : i.val < 717
          ·
            have he : (⟨716, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 716 = i.val
              omega
            simpa only [he] using bucket0716
          ·
            have he : (⟨717, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 717 = i.val
              omega
            simpa only [he] using bucket0717
        ·
          by_cases h719 : i.val < 719
          ·
            have he : (⟨718, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 718 = i.val
              omega
            simpa only [he] using bucket0718
          ·
            have he : (⟨719, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 719 = i.val
              omega
            simpa only [he] using bucket0719
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
            simpa only [he] using bucket0720
          ·
            have he : (⟨721, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 721 = i.val
              omega
            simpa only [he] using bucket0721
        ·
          by_cases h723 : i.val < 723
          ·
            have he : (⟨722, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 722 = i.val
              omega
            simpa only [he] using bucket0722
          ·
            have he : (⟨723, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 723 = i.val
              omega
            simpa only [he] using bucket0723
      ·
        by_cases h726 : i.val < 726
        ·
          by_cases h725 : i.val < 725
          ·
            have he : (⟨724, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 724 = i.val
              omega
            simpa only [he] using bucket0724
          ·
            have he : (⟨725, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 725 = i.val
              omega
            simpa only [he] using bucket0725
        ·
          by_cases h727 : i.val < 727
          ·
            have he : (⟨726, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 726 = i.val
              omega
            simpa only [he] using bucket0726
          ·
            have he : (⟨727, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 727 = i.val
              omega
            simpa only [he] using bucket0727
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
            simpa only [he] using bucket0728
          ·
            have he : (⟨729, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 729 = i.val
              omega
            simpa only [he] using bucket0729
        ·
          by_cases h731 : i.val < 731
          ·
            have he : (⟨730, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 730 = i.val
              omega
            simpa only [he] using bucket0730
          ·
            have he : (⟨731, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 731 = i.val
              omega
            simpa only [he] using bucket0731
      ·
        by_cases h734 : i.val < 734
        ·
          by_cases h733 : i.val < 733
          ·
            have he : (⟨732, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 732 = i.val
              omega
            simpa only [he] using bucket0732
          ·
            have he : (⟨733, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 733 = i.val
              omega
            simpa only [he] using bucket0733
        ·
          by_cases h735 : i.val < 735
          ·
            have he : (⟨734, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 734 = i.val
              omega
            simpa only [he] using bucket0734
          ·
            have he : (⟨735, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 735 = i.val
              omega
            simpa only [he] using bucket0735

private theorem bucketGroup0023 (i : Fin 1069)
    (hlo : 736 ≤ i.val) (hhi : i.val < 768) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0736
          ·
            have he : (⟨737, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 737 = i.val
              omega
            simpa only [he] using bucket0737
        ·
          by_cases h739 : i.val < 739
          ·
            have he : (⟨738, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 738 = i.val
              omega
            simpa only [he] using bucket0738
          ·
            have he : (⟨739, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 739 = i.val
              omega
            simpa only [he] using bucket0739
      ·
        by_cases h742 : i.val < 742
        ·
          by_cases h741 : i.val < 741
          ·
            have he : (⟨740, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 740 = i.val
              omega
            simpa only [he] using bucket0740
          ·
            have he : (⟨741, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 741 = i.val
              omega
            simpa only [he] using bucket0741
        ·
          by_cases h743 : i.val < 743
          ·
            have he : (⟨742, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 742 = i.val
              omega
            simpa only [he] using bucket0742
          ·
            have he : (⟨743, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 743 = i.val
              omega
            simpa only [he] using bucket0743
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
            simpa only [he] using bucket0744
          ·
            have he : (⟨745, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 745 = i.val
              omega
            simpa only [he] using bucket0745
        ·
          by_cases h747 : i.val < 747
          ·
            have he : (⟨746, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 746 = i.val
              omega
            simpa only [he] using bucket0746
          ·
            have he : (⟨747, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 747 = i.val
              omega
            simpa only [he] using bucket0747
      ·
        by_cases h750 : i.val < 750
        ·
          by_cases h749 : i.val < 749
          ·
            have he : (⟨748, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 748 = i.val
              omega
            simpa only [he] using bucket0748
          ·
            have he : (⟨749, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 749 = i.val
              omega
            simpa only [he] using bucket0749
        ·
          by_cases h751 : i.val < 751
          ·
            have he : (⟨750, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 750 = i.val
              omega
            simpa only [he] using bucket0750
          ·
            have he : (⟨751, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 751 = i.val
              omega
            simpa only [he] using bucket0751
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
            simpa only [he] using bucket0752
          ·
            have he : (⟨753, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 753 = i.val
              omega
            simpa only [he] using bucket0753
        ·
          by_cases h755 : i.val < 755
          ·
            have he : (⟨754, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 754 = i.val
              omega
            simpa only [he] using bucket0754
          ·
            have he : (⟨755, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 755 = i.val
              omega
            simpa only [he] using bucket0755
      ·
        by_cases h758 : i.val < 758
        ·
          by_cases h757 : i.val < 757
          ·
            have he : (⟨756, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 756 = i.val
              omega
            simpa only [he] using bucket0756
          ·
            have he : (⟨757, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 757 = i.val
              omega
            simpa only [he] using bucket0757
        ·
          by_cases h759 : i.val < 759
          ·
            have he : (⟨758, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 758 = i.val
              omega
            simpa only [he] using bucket0758
          ·
            have he : (⟨759, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 759 = i.val
              omega
            simpa only [he] using bucket0759
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
            simpa only [he] using bucket0760
          ·
            have he : (⟨761, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 761 = i.val
              omega
            simpa only [he] using bucket0761
        ·
          by_cases h763 : i.val < 763
          ·
            have he : (⟨762, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 762 = i.val
              omega
            simpa only [he] using bucket0762
          ·
            have he : (⟨763, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 763 = i.val
              omega
            simpa only [he] using bucket0763
      ·
        by_cases h766 : i.val < 766
        ·
          by_cases h765 : i.val < 765
          ·
            have he : (⟨764, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 764 = i.val
              omega
            simpa only [he] using bucket0764
          ·
            have he : (⟨765, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 765 = i.val
              omega
            simpa only [he] using bucket0765
        ·
          by_cases h767 : i.val < 767
          ·
            have he : (⟨766, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 766 = i.val
              omega
            simpa only [he] using bucket0766
          ·
            have he : (⟨767, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 767 = i.val
              omega
            simpa only [he] using bucket0767

private theorem bucketGroup0024 (i : Fin 1069)
    (hlo : 768 ≤ i.val) (hhi : i.val < 800) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0768
          ·
            have he : (⟨769, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 769 = i.val
              omega
            simpa only [he] using bucket0769
        ·
          by_cases h771 : i.val < 771
          ·
            have he : (⟨770, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 770 = i.val
              omega
            simpa only [he] using bucket0770
          ·
            have he : (⟨771, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 771 = i.val
              omega
            simpa only [he] using bucket0771
      ·
        by_cases h774 : i.val < 774
        ·
          by_cases h773 : i.val < 773
          ·
            have he : (⟨772, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 772 = i.val
              omega
            simpa only [he] using bucket0772
          ·
            have he : (⟨773, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 773 = i.val
              omega
            simpa only [he] using bucket0773
        ·
          by_cases h775 : i.val < 775
          ·
            have he : (⟨774, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 774 = i.val
              omega
            simpa only [he] using bucket0774
          ·
            have he : (⟨775, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 775 = i.val
              omega
            simpa only [he] using bucket0775
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
            simpa only [he] using bucket0776
          ·
            have he : (⟨777, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 777 = i.val
              omega
            simpa only [he] using bucket0777
        ·
          by_cases h779 : i.val < 779
          ·
            have he : (⟨778, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 778 = i.val
              omega
            simpa only [he] using bucket0778
          ·
            have he : (⟨779, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 779 = i.val
              omega
            simpa only [he] using bucket0779
      ·
        by_cases h782 : i.val < 782
        ·
          by_cases h781 : i.val < 781
          ·
            have he : (⟨780, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 780 = i.val
              omega
            simpa only [he] using bucket0780
          ·
            have he : (⟨781, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 781 = i.val
              omega
            simpa only [he] using bucket0781
        ·
          by_cases h783 : i.val < 783
          ·
            have he : (⟨782, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 782 = i.val
              omega
            simpa only [he] using bucket0782
          ·
            have he : (⟨783, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 783 = i.val
              omega
            simpa only [he] using bucket0783
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
            simpa only [he] using bucket0784
          ·
            have he : (⟨785, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 785 = i.val
              omega
            simpa only [he] using bucket0785
        ·
          by_cases h787 : i.val < 787
          ·
            have he : (⟨786, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 786 = i.val
              omega
            simpa only [he] using bucket0786
          ·
            have he : (⟨787, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 787 = i.val
              omega
            simpa only [he] using bucket0787
      ·
        by_cases h790 : i.val < 790
        ·
          by_cases h789 : i.val < 789
          ·
            have he : (⟨788, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 788 = i.val
              omega
            simpa only [he] using bucket0788
          ·
            have he : (⟨789, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 789 = i.val
              omega
            simpa only [he] using bucket0789
        ·
          by_cases h791 : i.val < 791
          ·
            have he : (⟨790, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 790 = i.val
              omega
            simpa only [he] using bucket0790
          ·
            have he : (⟨791, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 791 = i.val
              omega
            simpa only [he] using bucket0791
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
            simpa only [he] using bucket0792
          ·
            have he : (⟨793, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 793 = i.val
              omega
            simpa only [he] using bucket0793
        ·
          by_cases h795 : i.val < 795
          ·
            have he : (⟨794, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 794 = i.val
              omega
            simpa only [he] using bucket0794
          ·
            have he : (⟨795, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 795 = i.val
              omega
            simpa only [he] using bucket0795
      ·
        by_cases h798 : i.val < 798
        ·
          by_cases h797 : i.val < 797
          ·
            have he : (⟨796, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 796 = i.val
              omega
            simpa only [he] using bucket0796
          ·
            have he : (⟨797, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 797 = i.val
              omega
            simpa only [he] using bucket0797
        ·
          by_cases h799 : i.val < 799
          ·
            have he : (⟨798, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 798 = i.val
              omega
            simpa only [he] using bucket0798
          ·
            have he : (⟨799, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 799 = i.val
              omega
            simpa only [he] using bucket0799

private theorem bucketGroup0025 (i : Fin 1069)
    (hlo : 800 ≤ i.val) (hhi : i.val < 832) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0800
          ·
            have he : (⟨801, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 801 = i.val
              omega
            simpa only [he] using bucket0801
        ·
          by_cases h803 : i.val < 803
          ·
            have he : (⟨802, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 802 = i.val
              omega
            simpa only [he] using bucket0802
          ·
            have he : (⟨803, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 803 = i.val
              omega
            simpa only [he] using bucket0803
      ·
        by_cases h806 : i.val < 806
        ·
          by_cases h805 : i.val < 805
          ·
            have he : (⟨804, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 804 = i.val
              omega
            simpa only [he] using bucket0804
          ·
            have he : (⟨805, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 805 = i.val
              omega
            simpa only [he] using bucket0805
        ·
          by_cases h807 : i.val < 807
          ·
            have he : (⟨806, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 806 = i.val
              omega
            simpa only [he] using bucket0806
          ·
            have he : (⟨807, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 807 = i.val
              omega
            simpa only [he] using bucket0807
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
            simpa only [he] using bucket0808
          ·
            have he : (⟨809, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 809 = i.val
              omega
            simpa only [he] using bucket0809
        ·
          by_cases h811 : i.val < 811
          ·
            have he : (⟨810, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 810 = i.val
              omega
            simpa only [he] using bucket0810
          ·
            have he : (⟨811, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 811 = i.val
              omega
            simpa only [he] using bucket0811
      ·
        by_cases h814 : i.val < 814
        ·
          by_cases h813 : i.val < 813
          ·
            have he : (⟨812, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 812 = i.val
              omega
            simpa only [he] using bucket0812
          ·
            have he : (⟨813, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 813 = i.val
              omega
            simpa only [he] using bucket0813
        ·
          by_cases h815 : i.val < 815
          ·
            have he : (⟨814, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 814 = i.val
              omega
            simpa only [he] using bucket0814
          ·
            have he : (⟨815, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 815 = i.val
              omega
            simpa only [he] using bucket0815
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
            simpa only [he] using bucket0816
          ·
            have he : (⟨817, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 817 = i.val
              omega
            simpa only [he] using bucket0817
        ·
          by_cases h819 : i.val < 819
          ·
            have he : (⟨818, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 818 = i.val
              omega
            simpa only [he] using bucket0818
          ·
            have he : (⟨819, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 819 = i.val
              omega
            simpa only [he] using bucket0819
      ·
        by_cases h822 : i.val < 822
        ·
          by_cases h821 : i.val < 821
          ·
            have he : (⟨820, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 820 = i.val
              omega
            simpa only [he] using bucket0820
          ·
            have he : (⟨821, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 821 = i.val
              omega
            simpa only [he] using bucket0821
        ·
          by_cases h823 : i.val < 823
          ·
            have he : (⟨822, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 822 = i.val
              omega
            simpa only [he] using bucket0822
          ·
            have he : (⟨823, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 823 = i.val
              omega
            simpa only [he] using bucket0823
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
            simpa only [he] using bucket0824
          ·
            have he : (⟨825, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 825 = i.val
              omega
            simpa only [he] using bucket0825
        ·
          by_cases h827 : i.val < 827
          ·
            have he : (⟨826, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 826 = i.val
              omega
            simpa only [he] using bucket0826
          ·
            have he : (⟨827, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 827 = i.val
              omega
            simpa only [he] using bucket0827
      ·
        by_cases h830 : i.val < 830
        ·
          by_cases h829 : i.val < 829
          ·
            have he : (⟨828, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 828 = i.val
              omega
            simpa only [he] using bucket0828
          ·
            have he : (⟨829, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 829 = i.val
              omega
            simpa only [he] using bucket0829
        ·
          by_cases h831 : i.val < 831
          ·
            have he : (⟨830, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 830 = i.val
              omega
            simpa only [he] using bucket0830
          ·
            have he : (⟨831, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 831 = i.val
              omega
            simpa only [he] using bucket0831

private theorem bucketGroup0026 (i : Fin 1069)
    (hlo : 832 ≤ i.val) (hhi : i.val < 864) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0832
          ·
            have he : (⟨833, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 833 = i.val
              omega
            simpa only [he] using bucket0833
        ·
          by_cases h835 : i.val < 835
          ·
            have he : (⟨834, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 834 = i.val
              omega
            simpa only [he] using bucket0834
          ·
            have he : (⟨835, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 835 = i.val
              omega
            simpa only [he] using bucket0835
      ·
        by_cases h838 : i.val < 838
        ·
          by_cases h837 : i.val < 837
          ·
            have he : (⟨836, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 836 = i.val
              omega
            simpa only [he] using bucket0836
          ·
            have he : (⟨837, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 837 = i.val
              omega
            simpa only [he] using bucket0837
        ·
          by_cases h839 : i.val < 839
          ·
            have he : (⟨838, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 838 = i.val
              omega
            simpa only [he] using bucket0838
          ·
            have he : (⟨839, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 839 = i.val
              omega
            simpa only [he] using bucket0839
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
            simpa only [he] using bucket0840
          ·
            have he : (⟨841, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 841 = i.val
              omega
            simpa only [he] using bucket0841
        ·
          by_cases h843 : i.val < 843
          ·
            have he : (⟨842, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 842 = i.val
              omega
            simpa only [he] using bucket0842
          ·
            have he : (⟨843, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 843 = i.val
              omega
            simpa only [he] using bucket0843
      ·
        by_cases h846 : i.val < 846
        ·
          by_cases h845 : i.val < 845
          ·
            have he : (⟨844, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 844 = i.val
              omega
            simpa only [he] using bucket0844
          ·
            have he : (⟨845, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 845 = i.val
              omega
            simpa only [he] using bucket0845
        ·
          by_cases h847 : i.val < 847
          ·
            have he : (⟨846, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 846 = i.val
              omega
            simpa only [he] using bucket0846
          ·
            have he : (⟨847, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 847 = i.val
              omega
            simpa only [he] using bucket0847
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
            simpa only [he] using bucket0848
          ·
            have he : (⟨849, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 849 = i.val
              omega
            simpa only [he] using bucket0849
        ·
          by_cases h851 : i.val < 851
          ·
            have he : (⟨850, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 850 = i.val
              omega
            simpa only [he] using bucket0850
          ·
            have he : (⟨851, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 851 = i.val
              omega
            simpa only [he] using bucket0851
      ·
        by_cases h854 : i.val < 854
        ·
          by_cases h853 : i.val < 853
          ·
            have he : (⟨852, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 852 = i.val
              omega
            simpa only [he] using bucket0852
          ·
            have he : (⟨853, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 853 = i.val
              omega
            simpa only [he] using bucket0853
        ·
          by_cases h855 : i.val < 855
          ·
            have he : (⟨854, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 854 = i.val
              omega
            simpa only [he] using bucket0854
          ·
            have he : (⟨855, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 855 = i.val
              omega
            simpa only [he] using bucket0855
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
            simpa only [he] using bucket0856
          ·
            have he : (⟨857, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 857 = i.val
              omega
            simpa only [he] using bucket0857
        ·
          by_cases h859 : i.val < 859
          ·
            have he : (⟨858, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 858 = i.val
              omega
            simpa only [he] using bucket0858
          ·
            have he : (⟨859, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 859 = i.val
              omega
            simpa only [he] using bucket0859
      ·
        by_cases h862 : i.val < 862
        ·
          by_cases h861 : i.val < 861
          ·
            have he : (⟨860, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 860 = i.val
              omega
            simpa only [he] using bucket0860
          ·
            have he : (⟨861, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 861 = i.val
              omega
            simpa only [he] using bucket0861
        ·
          by_cases h863 : i.val < 863
          ·
            have he : (⟨862, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 862 = i.val
              omega
            simpa only [he] using bucket0862
          ·
            have he : (⟨863, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 863 = i.val
              omega
            simpa only [he] using bucket0863

private theorem bucketGroup0027 (i : Fin 1069)
    (hlo : 864 ≤ i.val) (hhi : i.val < 896) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0864
          ·
            have he : (⟨865, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 865 = i.val
              omega
            simpa only [he] using bucket0865
        ·
          by_cases h867 : i.val < 867
          ·
            have he : (⟨866, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 866 = i.val
              omega
            simpa only [he] using bucket0866
          ·
            have he : (⟨867, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 867 = i.val
              omega
            simpa only [he] using bucket0867
      ·
        by_cases h870 : i.val < 870
        ·
          by_cases h869 : i.val < 869
          ·
            have he : (⟨868, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 868 = i.val
              omega
            simpa only [he] using bucket0868
          ·
            have he : (⟨869, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 869 = i.val
              omega
            simpa only [he] using bucket0869
        ·
          by_cases h871 : i.val < 871
          ·
            have he : (⟨870, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 870 = i.val
              omega
            simpa only [he] using bucket0870
          ·
            have he : (⟨871, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 871 = i.val
              omega
            simpa only [he] using bucket0871
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
            simpa only [he] using bucket0872
          ·
            have he : (⟨873, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 873 = i.val
              omega
            simpa only [he] using bucket0873
        ·
          by_cases h875 : i.val < 875
          ·
            have he : (⟨874, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 874 = i.val
              omega
            simpa only [he] using bucket0874
          ·
            have he : (⟨875, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 875 = i.val
              omega
            simpa only [he] using bucket0875
      ·
        by_cases h878 : i.val < 878
        ·
          by_cases h877 : i.val < 877
          ·
            have he : (⟨876, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 876 = i.val
              omega
            simpa only [he] using bucket0876
          ·
            have he : (⟨877, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 877 = i.val
              omega
            simpa only [he] using bucket0877
        ·
          by_cases h879 : i.val < 879
          ·
            have he : (⟨878, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 878 = i.val
              omega
            simpa only [he] using bucket0878
          ·
            have he : (⟨879, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 879 = i.val
              omega
            simpa only [he] using bucket0879
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
            simpa only [he] using bucket0880
          ·
            have he : (⟨881, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 881 = i.val
              omega
            simpa only [he] using bucket0881
        ·
          by_cases h883 : i.val < 883
          ·
            have he : (⟨882, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 882 = i.val
              omega
            simpa only [he] using bucket0882
          ·
            have he : (⟨883, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 883 = i.val
              omega
            simpa only [he] using bucket0883
      ·
        by_cases h886 : i.val < 886
        ·
          by_cases h885 : i.val < 885
          ·
            have he : (⟨884, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 884 = i.val
              omega
            simpa only [he] using bucket0884
          ·
            have he : (⟨885, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 885 = i.val
              omega
            simpa only [he] using bucket0885
        ·
          by_cases h887 : i.val < 887
          ·
            have he : (⟨886, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 886 = i.val
              omega
            simpa only [he] using bucket0886
          ·
            have he : (⟨887, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 887 = i.val
              omega
            simpa only [he] using bucket0887
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
            simpa only [he] using bucket0888
          ·
            have he : (⟨889, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 889 = i.val
              omega
            simpa only [he] using bucket0889
        ·
          by_cases h891 : i.val < 891
          ·
            have he : (⟨890, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 890 = i.val
              omega
            simpa only [he] using bucket0890
          ·
            have he : (⟨891, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 891 = i.val
              omega
            simpa only [he] using bucket0891
      ·
        by_cases h894 : i.val < 894
        ·
          by_cases h893 : i.val < 893
          ·
            have he : (⟨892, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 892 = i.val
              omega
            simpa only [he] using bucket0892
          ·
            have he : (⟨893, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 893 = i.val
              omega
            simpa only [he] using bucket0893
        ·
          by_cases h895 : i.val < 895
          ·
            have he : (⟨894, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 894 = i.val
              omega
            simpa only [he] using bucket0894
          ·
            have he : (⟨895, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 895 = i.val
              omega
            simpa only [he] using bucket0895

private theorem bucketGroup0028 (i : Fin 1069)
    (hlo : 896 ≤ i.val) (hhi : i.val < 928) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0896
          ·
            have he : (⟨897, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 897 = i.val
              omega
            simpa only [he] using bucket0897
        ·
          by_cases h899 : i.val < 899
          ·
            have he : (⟨898, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 898 = i.val
              omega
            simpa only [he] using bucket0898
          ·
            have he : (⟨899, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 899 = i.val
              omega
            simpa only [he] using bucket0899
      ·
        by_cases h902 : i.val < 902
        ·
          by_cases h901 : i.val < 901
          ·
            have he : (⟨900, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 900 = i.val
              omega
            simpa only [he] using bucket0900
          ·
            have he : (⟨901, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 901 = i.val
              omega
            simpa only [he] using bucket0901
        ·
          by_cases h903 : i.val < 903
          ·
            have he : (⟨902, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 902 = i.val
              omega
            simpa only [he] using bucket0902
          ·
            have he : (⟨903, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 903 = i.val
              omega
            simpa only [he] using bucket0903
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
            simpa only [he] using bucket0904
          ·
            have he : (⟨905, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 905 = i.val
              omega
            simpa only [he] using bucket0905
        ·
          by_cases h907 : i.val < 907
          ·
            have he : (⟨906, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 906 = i.val
              omega
            simpa only [he] using bucket0906
          ·
            have he : (⟨907, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 907 = i.val
              omega
            simpa only [he] using bucket0907
      ·
        by_cases h910 : i.val < 910
        ·
          by_cases h909 : i.val < 909
          ·
            have he : (⟨908, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 908 = i.val
              omega
            simpa only [he] using bucket0908
          ·
            have he : (⟨909, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 909 = i.val
              omega
            simpa only [he] using bucket0909
        ·
          by_cases h911 : i.val < 911
          ·
            have he : (⟨910, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 910 = i.val
              omega
            simpa only [he] using bucket0910
          ·
            have he : (⟨911, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 911 = i.val
              omega
            simpa only [he] using bucket0911
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
            simpa only [he] using bucket0912
          ·
            have he : (⟨913, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 913 = i.val
              omega
            simpa only [he] using bucket0913
        ·
          by_cases h915 : i.val < 915
          ·
            have he : (⟨914, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 914 = i.val
              omega
            simpa only [he] using bucket0914
          ·
            have he : (⟨915, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 915 = i.val
              omega
            simpa only [he] using bucket0915
      ·
        by_cases h918 : i.val < 918
        ·
          by_cases h917 : i.val < 917
          ·
            have he : (⟨916, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 916 = i.val
              omega
            simpa only [he] using bucket0916
          ·
            have he : (⟨917, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 917 = i.val
              omega
            simpa only [he] using bucket0917
        ·
          by_cases h919 : i.val < 919
          ·
            have he : (⟨918, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 918 = i.val
              omega
            simpa only [he] using bucket0918
          ·
            have he : (⟨919, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 919 = i.val
              omega
            simpa only [he] using bucket0919
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
            simpa only [he] using bucket0920
          ·
            have he : (⟨921, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 921 = i.val
              omega
            simpa only [he] using bucket0921
        ·
          by_cases h923 : i.val < 923
          ·
            have he : (⟨922, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 922 = i.val
              omega
            simpa only [he] using bucket0922
          ·
            have he : (⟨923, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 923 = i.val
              omega
            simpa only [he] using bucket0923
      ·
        by_cases h926 : i.val < 926
        ·
          by_cases h925 : i.val < 925
          ·
            have he : (⟨924, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 924 = i.val
              omega
            simpa only [he] using bucket0924
          ·
            have he : (⟨925, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 925 = i.val
              omega
            simpa only [he] using bucket0925
        ·
          by_cases h927 : i.val < 927
          ·
            have he : (⟨926, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 926 = i.val
              omega
            simpa only [he] using bucket0926
          ·
            have he : (⟨927, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 927 = i.val
              omega
            simpa only [he] using bucket0927

private theorem bucketGroup0029 (i : Fin 1069)
    (hlo : 928 ≤ i.val) (hhi : i.val < 960) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0928
          ·
            have he : (⟨929, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 929 = i.val
              omega
            simpa only [he] using bucket0929
        ·
          by_cases h931 : i.val < 931
          ·
            have he : (⟨930, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 930 = i.val
              omega
            simpa only [he] using bucket0930
          ·
            have he : (⟨931, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 931 = i.val
              omega
            simpa only [he] using bucket0931
      ·
        by_cases h934 : i.val < 934
        ·
          by_cases h933 : i.val < 933
          ·
            have he : (⟨932, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 932 = i.val
              omega
            simpa only [he] using bucket0932
          ·
            have he : (⟨933, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 933 = i.val
              omega
            simpa only [he] using bucket0933
        ·
          by_cases h935 : i.val < 935
          ·
            have he : (⟨934, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 934 = i.val
              omega
            simpa only [he] using bucket0934
          ·
            have he : (⟨935, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 935 = i.val
              omega
            simpa only [he] using bucket0935
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
            simpa only [he] using bucket0936
          ·
            have he : (⟨937, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 937 = i.val
              omega
            simpa only [he] using bucket0937
        ·
          by_cases h939 : i.val < 939
          ·
            have he : (⟨938, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 938 = i.val
              omega
            simpa only [he] using bucket0938
          ·
            have he : (⟨939, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 939 = i.val
              omega
            simpa only [he] using bucket0939
      ·
        by_cases h942 : i.val < 942
        ·
          by_cases h941 : i.val < 941
          ·
            have he : (⟨940, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 940 = i.val
              omega
            simpa only [he] using bucket0940
          ·
            have he : (⟨941, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 941 = i.val
              omega
            simpa only [he] using bucket0941
        ·
          by_cases h943 : i.val < 943
          ·
            have he : (⟨942, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 942 = i.val
              omega
            simpa only [he] using bucket0942
          ·
            have he : (⟨943, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 943 = i.val
              omega
            simpa only [he] using bucket0943
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
            simpa only [he] using bucket0944
          ·
            have he : (⟨945, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 945 = i.val
              omega
            simpa only [he] using bucket0945
        ·
          by_cases h947 : i.val < 947
          ·
            have he : (⟨946, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 946 = i.val
              omega
            simpa only [he] using bucket0946
          ·
            have he : (⟨947, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 947 = i.val
              omega
            simpa only [he] using bucket0947
      ·
        by_cases h950 : i.val < 950
        ·
          by_cases h949 : i.val < 949
          ·
            have he : (⟨948, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 948 = i.val
              omega
            simpa only [he] using bucket0948
          ·
            have he : (⟨949, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 949 = i.val
              omega
            simpa only [he] using bucket0949
        ·
          by_cases h951 : i.val < 951
          ·
            have he : (⟨950, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 950 = i.val
              omega
            simpa only [he] using bucket0950
          ·
            have he : (⟨951, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 951 = i.val
              omega
            simpa only [he] using bucket0951
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
            simpa only [he] using bucket0952
          ·
            have he : (⟨953, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 953 = i.val
              omega
            simpa only [he] using bucket0953
        ·
          by_cases h955 : i.val < 955
          ·
            have he : (⟨954, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 954 = i.val
              omega
            simpa only [he] using bucket0954
          ·
            have he : (⟨955, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 955 = i.val
              omega
            simpa only [he] using bucket0955
      ·
        by_cases h958 : i.val < 958
        ·
          by_cases h957 : i.val < 957
          ·
            have he : (⟨956, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 956 = i.val
              omega
            simpa only [he] using bucket0956
          ·
            have he : (⟨957, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 957 = i.val
              omega
            simpa only [he] using bucket0957
        ·
          by_cases h959 : i.val < 959
          ·
            have he : (⟨958, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 958 = i.val
              omega
            simpa only [he] using bucket0958
          ·
            have he : (⟨959, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 959 = i.val
              omega
            simpa only [he] using bucket0959

private theorem bucketGroup0030 (i : Fin 1069)
    (hlo : 960 ≤ i.val) (hhi : i.val < 992) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0960
          ·
            have he : (⟨961, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 961 = i.val
              omega
            simpa only [he] using bucket0961
        ·
          by_cases h963 : i.val < 963
          ·
            have he : (⟨962, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 962 = i.val
              omega
            simpa only [he] using bucket0962
          ·
            have he : (⟨963, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 963 = i.val
              omega
            simpa only [he] using bucket0963
      ·
        by_cases h966 : i.val < 966
        ·
          by_cases h965 : i.val < 965
          ·
            have he : (⟨964, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 964 = i.val
              omega
            simpa only [he] using bucket0964
          ·
            have he : (⟨965, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 965 = i.val
              omega
            simpa only [he] using bucket0965
        ·
          by_cases h967 : i.val < 967
          ·
            have he : (⟨966, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 966 = i.val
              omega
            simpa only [he] using bucket0966
          ·
            have he : (⟨967, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 967 = i.val
              omega
            simpa only [he] using bucket0967
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
            simpa only [he] using bucket0968
          ·
            have he : (⟨969, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 969 = i.val
              omega
            simpa only [he] using bucket0969
        ·
          by_cases h971 : i.val < 971
          ·
            have he : (⟨970, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 970 = i.val
              omega
            simpa only [he] using bucket0970
          ·
            have he : (⟨971, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 971 = i.val
              omega
            simpa only [he] using bucket0971
      ·
        by_cases h974 : i.val < 974
        ·
          by_cases h973 : i.val < 973
          ·
            have he : (⟨972, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 972 = i.val
              omega
            simpa only [he] using bucket0972
          ·
            have he : (⟨973, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 973 = i.val
              omega
            simpa only [he] using bucket0973
        ·
          by_cases h975 : i.val < 975
          ·
            have he : (⟨974, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 974 = i.val
              omega
            simpa only [he] using bucket0974
          ·
            have he : (⟨975, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 975 = i.val
              omega
            simpa only [he] using bucket0975
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
            simpa only [he] using bucket0976
          ·
            have he : (⟨977, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 977 = i.val
              omega
            simpa only [he] using bucket0977
        ·
          by_cases h979 : i.val < 979
          ·
            have he : (⟨978, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 978 = i.val
              omega
            simpa only [he] using bucket0978
          ·
            have he : (⟨979, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 979 = i.val
              omega
            simpa only [he] using bucket0979
      ·
        by_cases h982 : i.val < 982
        ·
          by_cases h981 : i.val < 981
          ·
            have he : (⟨980, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 980 = i.val
              omega
            simpa only [he] using bucket0980
          ·
            have he : (⟨981, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 981 = i.val
              omega
            simpa only [he] using bucket0981
        ·
          by_cases h983 : i.val < 983
          ·
            have he : (⟨982, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 982 = i.val
              omega
            simpa only [he] using bucket0982
          ·
            have he : (⟨983, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 983 = i.val
              omega
            simpa only [he] using bucket0983
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
            simpa only [he] using bucket0984
          ·
            have he : (⟨985, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 985 = i.val
              omega
            simpa only [he] using bucket0985
        ·
          by_cases h987 : i.val < 987
          ·
            have he : (⟨986, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 986 = i.val
              omega
            simpa only [he] using bucket0986
          ·
            have he : (⟨987, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 987 = i.val
              omega
            simpa only [he] using bucket0987
      ·
        by_cases h990 : i.val < 990
        ·
          by_cases h989 : i.val < 989
          ·
            have he : (⟨988, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 988 = i.val
              omega
            simpa only [he] using bucket0988
          ·
            have he : (⟨989, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 989 = i.val
              omega
            simpa only [he] using bucket0989
        ·
          by_cases h991 : i.val < 991
          ·
            have he : (⟨990, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 990 = i.val
              omega
            simpa only [he] using bucket0990
          ·
            have he : (⟨991, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 991 = i.val
              omega
            simpa only [he] using bucket0991

private theorem bucketGroup0031 (i : Fin 1069)
    (hlo : 992 ≤ i.val) (hhi : i.val < 1024) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket0992
          ·
            have he : (⟨993, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 993 = i.val
              omega
            simpa only [he] using bucket0993
        ·
          by_cases h995 : i.val < 995
          ·
            have he : (⟨994, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 994 = i.val
              omega
            simpa only [he] using bucket0994
          ·
            have he : (⟨995, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 995 = i.val
              omega
            simpa only [he] using bucket0995
      ·
        by_cases h998 : i.val < 998
        ·
          by_cases h997 : i.val < 997
          ·
            have he : (⟨996, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 996 = i.val
              omega
            simpa only [he] using bucket0996
          ·
            have he : (⟨997, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 997 = i.val
              omega
            simpa only [he] using bucket0997
        ·
          by_cases h999 : i.val < 999
          ·
            have he : (⟨998, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 998 = i.val
              omega
            simpa only [he] using bucket0998
          ·
            have he : (⟨999, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 999 = i.val
              omega
            simpa only [he] using bucket0999
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
            simpa only [he] using bucket1000
          ·
            have he : (⟨1001, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1001 = i.val
              omega
            simpa only [he] using bucket1001
        ·
          by_cases h1003 : i.val < 1003
          ·
            have he : (⟨1002, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1002 = i.val
              omega
            simpa only [he] using bucket1002
          ·
            have he : (⟨1003, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1003 = i.val
              omega
            simpa only [he] using bucket1003
      ·
        by_cases h1006 : i.val < 1006
        ·
          by_cases h1005 : i.val < 1005
          ·
            have he : (⟨1004, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1004 = i.val
              omega
            simpa only [he] using bucket1004
          ·
            have he : (⟨1005, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1005 = i.val
              omega
            simpa only [he] using bucket1005
        ·
          by_cases h1007 : i.val < 1007
          ·
            have he : (⟨1006, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1006 = i.val
              omega
            simpa only [he] using bucket1006
          ·
            have he : (⟨1007, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1007 = i.val
              omega
            simpa only [he] using bucket1007
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
            simpa only [he] using bucket1008
          ·
            have he : (⟨1009, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1009 = i.val
              omega
            simpa only [he] using bucket1009
        ·
          by_cases h1011 : i.val < 1011
          ·
            have he : (⟨1010, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1010 = i.val
              omega
            simpa only [he] using bucket1010
          ·
            have he : (⟨1011, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1011 = i.val
              omega
            simpa only [he] using bucket1011
      ·
        by_cases h1014 : i.val < 1014
        ·
          by_cases h1013 : i.val < 1013
          ·
            have he : (⟨1012, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1012 = i.val
              omega
            simpa only [he] using bucket1012
          ·
            have he : (⟨1013, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1013 = i.val
              omega
            simpa only [he] using bucket1013
        ·
          by_cases h1015 : i.val < 1015
          ·
            have he : (⟨1014, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1014 = i.val
              omega
            simpa only [he] using bucket1014
          ·
            have he : (⟨1015, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1015 = i.val
              omega
            simpa only [he] using bucket1015
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
            simpa only [he] using bucket1016
          ·
            have he : (⟨1017, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1017 = i.val
              omega
            simpa only [he] using bucket1017
        ·
          by_cases h1019 : i.val < 1019
          ·
            have he : (⟨1018, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1018 = i.val
              omega
            simpa only [he] using bucket1018
          ·
            have he : (⟨1019, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1019 = i.val
              omega
            simpa only [he] using bucket1019
      ·
        by_cases h1022 : i.val < 1022
        ·
          by_cases h1021 : i.val < 1021
          ·
            have he : (⟨1020, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1020 = i.val
              omega
            simpa only [he] using bucket1020
          ·
            have he : (⟨1021, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1021 = i.val
              omega
            simpa only [he] using bucket1021
        ·
          by_cases h1023 : i.val < 1023
          ·
            have he : (⟨1022, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1022 = i.val
              omega
            simpa only [he] using bucket1022
          ·
            have he : (⟨1023, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1023 = i.val
              omega
            simpa only [he] using bucket1023

private theorem bucketGroup0032 (i : Fin 1069)
    (hlo : 1024 ≤ i.val) (hhi : i.val < 1056) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            simpa only [he] using bucket1024
          ·
            have he : (⟨1025, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1025 = i.val
              omega
            simpa only [he] using bucket1025
        ·
          by_cases h1027 : i.val < 1027
          ·
            have he : (⟨1026, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1026 = i.val
              omega
            simpa only [he] using bucket1026
          ·
            have he : (⟨1027, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1027 = i.val
              omega
            simpa only [he] using bucket1027
      ·
        by_cases h1030 : i.val < 1030
        ·
          by_cases h1029 : i.val < 1029
          ·
            have he : (⟨1028, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1028 = i.val
              omega
            simpa only [he] using bucket1028
          ·
            have he : (⟨1029, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1029 = i.val
              omega
            simpa only [he] using bucket1029
        ·
          by_cases h1031 : i.val < 1031
          ·
            have he : (⟨1030, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1030 = i.val
              omega
            simpa only [he] using bucket1030
          ·
            have he : (⟨1031, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1031 = i.val
              omega
            simpa only [he] using bucket1031
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
            simpa only [he] using bucket1032
          ·
            have he : (⟨1033, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1033 = i.val
              omega
            simpa only [he] using bucket1033
        ·
          by_cases h1035 : i.val < 1035
          ·
            have he : (⟨1034, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1034 = i.val
              omega
            simpa only [he] using bucket1034
          ·
            have he : (⟨1035, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1035 = i.val
              omega
            simpa only [he] using bucket1035
      ·
        by_cases h1038 : i.val < 1038
        ·
          by_cases h1037 : i.val < 1037
          ·
            have he : (⟨1036, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1036 = i.val
              omega
            simpa only [he] using bucket1036
          ·
            have he : (⟨1037, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1037 = i.val
              omega
            simpa only [he] using bucket1037
        ·
          by_cases h1039 : i.val < 1039
          ·
            have he : (⟨1038, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1038 = i.val
              omega
            simpa only [he] using bucket1038
          ·
            have he : (⟨1039, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1039 = i.val
              omega
            simpa only [he] using bucket1039
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
            simpa only [he] using bucket1040
          ·
            have he : (⟨1041, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1041 = i.val
              omega
            simpa only [he] using bucket1041
        ·
          by_cases h1043 : i.val < 1043
          ·
            have he : (⟨1042, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1042 = i.val
              omega
            simpa only [he] using bucket1042
          ·
            have he : (⟨1043, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1043 = i.val
              omega
            simpa only [he] using bucket1043
      ·
        by_cases h1046 : i.val < 1046
        ·
          by_cases h1045 : i.val < 1045
          ·
            have he : (⟨1044, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1044 = i.val
              omega
            simpa only [he] using bucket1044
          ·
            have he : (⟨1045, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1045 = i.val
              omega
            simpa only [he] using bucket1045
        ·
          by_cases h1047 : i.val < 1047
          ·
            have he : (⟨1046, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1046 = i.val
              omega
            simpa only [he] using bucket1046
          ·
            have he : (⟨1047, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1047 = i.val
              omega
            simpa only [he] using bucket1047
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
            simpa only [he] using bucket1048
          ·
            have he : (⟨1049, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1049 = i.val
              omega
            simpa only [he] using bucket1049
        ·
          by_cases h1051 : i.val < 1051
          ·
            have he : (⟨1050, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1050 = i.val
              omega
            simpa only [he] using bucket1050
          ·
            have he : (⟨1051, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1051 = i.val
              omega
            simpa only [he] using bucket1051
      ·
        by_cases h1054 : i.val < 1054
        ·
          by_cases h1053 : i.val < 1053
          ·
            have he : (⟨1052, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1052 = i.val
              omega
            simpa only [he] using bucket1052
          ·
            have he : (⟨1053, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1053 = i.val
              omega
            simpa only [he] using bucket1053
        ·
          by_cases h1055 : i.val < 1055
          ·
            have he : (⟨1054, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1054 = i.val
              omega
            simpa only [he] using bucket1054
          ·
            have he : (⟨1055, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1055 = i.val
              omega
            simpa only [he] using bucket1055

private theorem bucketGroup0033 (i : Fin 1069)
    (hlo : 1056 ≤ i.val) (hhi : i.val < 1069) :
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
        simpa only [he] using bucket1056
      ·
        by_cases h1058 : i.val < 1058
        ·
          have he : (⟨1057, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1057 = i.val
            omega
          simpa only [he] using bucket1057
        ·
          have he : (⟨1058, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1058 = i.val
            omega
          simpa only [he] using bucket1058
    ·
      by_cases h1060 : i.val < 1060
      ·
        have he : (⟨1059, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1059 = i.val
          omega
        simpa only [he] using bucket1059
      ·
        by_cases h1061 : i.val < 1061
        ·
          have he : (⟨1060, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1060 = i.val
            omega
          simpa only [he] using bucket1060
        ·
          have he : (⟨1061, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1061 = i.val
            omega
          simpa only [he] using bucket1061
  ·
    by_cases h1065 : i.val < 1065
    ·
      by_cases h1063 : i.val < 1063
      ·
        have he : (⟨1062, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1062 = i.val
          omega
        simpa only [he] using bucket1062
      ·
        by_cases h1064 : i.val < 1064
        ·
          have he : (⟨1063, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1063 = i.val
            omega
          simpa only [he] using bucket1063
        ·
          have he : (⟨1064, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1064 = i.val
            omega
          simpa only [he] using bucket1064
    ·
      by_cases h1067 : i.val < 1067
      ·
        by_cases h1066 : i.val < 1066
        ·
          have he : (⟨1065, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1065 = i.val
            omega
          simpa only [he] using bucket1065
        ·
          have he : (⟨1066, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1066 = i.val
            omega
          simpa only [he] using bucket1066
      ·
        by_cases h1068 : i.val < 1068
        ·
          have he : (⟨1067, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1067 = i.val
            omega
          simpa only [he] using bucket1067
        ·
          have he : (⟨1068, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1068 = i.val
            omega
          simpa only [he] using bucket1068

private theorem anchoredFaces_self : ∀ i : Fin 1069,
    i ∈ anchoredFaces (faceRank i) (faceAnchor i) := by
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
            exact bucketGroup0000 i (by omega) (by omega)
          ·
            exact bucketGroup0001 i (by omega) (by omega)
        ·
          by_cases h96 : i.val < 96
          ·
            exact bucketGroup0002 i (by omega) (by omega)
          ·
            exact bucketGroup0003 i (by omega) (by omega)
      ·
        by_cases h192 : i.val < 192
        ·
          by_cases h160 : i.val < 160
          ·
            exact bucketGroup0004 i (by omega) (by omega)
          ·
            exact bucketGroup0005 i (by omega) (by omega)
        ·
          by_cases h224 : i.val < 224
          ·
            exact bucketGroup0006 i (by omega) (by omega)
          ·
            exact bucketGroup0007 i (by omega) (by omega)
    ·
      by_cases h384 : i.val < 384
      ·
        by_cases h320 : i.val < 320
        ·
          by_cases h288 : i.val < 288
          ·
            exact bucketGroup0008 i (by omega) (by omega)
          ·
            exact bucketGroup0009 i (by omega) (by omega)
        ·
          by_cases h352 : i.val < 352
          ·
            exact bucketGroup0010 i (by omega) (by omega)
          ·
            exact bucketGroup0011 i (by omega) (by omega)
      ·
        by_cases h448 : i.val < 448
        ·
          by_cases h416 : i.val < 416
          ·
            exact bucketGroup0012 i (by omega) (by omega)
          ·
            exact bucketGroup0013 i (by omega) (by omega)
        ·
          by_cases h480 : i.val < 480
          ·
            exact bucketGroup0014 i (by omega) (by omega)
          ·
            by_cases h512 : i.val < 512
            ·
              exact bucketGroup0015 i (by omega) (by omega)
            ·
              exact bucketGroup0016 i (by omega) (by omega)
  ·
    by_cases h800 : i.val < 800
    ·
      by_cases h672 : i.val < 672
      ·
        by_cases h608 : i.val < 608
        ·
          by_cases h576 : i.val < 576
          ·
            exact bucketGroup0017 i (by omega) (by omega)
          ·
            exact bucketGroup0018 i (by omega) (by omega)
        ·
          by_cases h640 : i.val < 640
          ·
            exact bucketGroup0019 i (by omega) (by omega)
          ·
            exact bucketGroup0020 i (by omega) (by omega)
      ·
        by_cases h736 : i.val < 736
        ·
          by_cases h704 : i.val < 704
          ·
            exact bucketGroup0021 i (by omega) (by omega)
          ·
            exact bucketGroup0022 i (by omega) (by omega)
        ·
          by_cases h768 : i.val < 768
          ·
            exact bucketGroup0023 i (by omega) (by omega)
          ·
            exact bucketGroup0024 i (by omega) (by omega)
    ·
      by_cases h928 : i.val < 928
      ·
        by_cases h864 : i.val < 864
        ·
          by_cases h832 : i.val < 832
          ·
            exact bucketGroup0025 i (by omega) (by omega)
          ·
            exact bucketGroup0026 i (by omega) (by omega)
        ·
          by_cases h896 : i.val < 896
          ·
            exact bucketGroup0027 i (by omega) (by omega)
          ·
            exact bucketGroup0028 i (by omega) (by omega)
      ·
        by_cases h992 : i.val < 992
        ·
          by_cases h960 : i.val < 960
          ·
            exact bucketGroup0029 i (by omega) (by omega)
          ·
            exact bucketGroup0030 i (by omega) (by omega)
        ·
          by_cases h1024 : i.val < 1024
          ·
            exact bucketGroup0031 i (by omega) (by omega)
          ·
            by_cases h1056 : i.val < 1056
            ·
              exact bucketGroup0032 i (by omega) (by omega)
            ·
              exact bucketGroup0033 i (by omega) (by omega)

private def previousRank (i : Fin 1069) : Fin 5 :=
  ⟨(faceRank i).val - 1, by have h := (faceRank i).isLt; omega⟩

private def lowerCandidates (i : Fin 1069) : Finset (Fin 1069) :=
  (faceMask i).biUnion (anchoredFaces (previousRank i))

private def lowerComputed (i : Fin 1069) : Finset (Fin 1069) :=
  (lowerCandidates i).filter
    (fun j => (faceRank j).val + 1 = (faceRank i).val ∧ faceMask j ⊆ faceMask i)

private theorem lower0000 : lowerComputed (⟨0, by decide⟩ : Fin 1069) = lowerFacets (⟨0, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0001 : lowerComputed (⟨1, by decide⟩ : Fin 1069) = lowerFacets (⟨1, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0002 : lowerComputed (⟨2, by decide⟩ : Fin 1069) = lowerFacets (⟨2, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0003 : lowerComputed (⟨3, by decide⟩ : Fin 1069) = lowerFacets (⟨3, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0004 : lowerComputed (⟨4, by decide⟩ : Fin 1069) = lowerFacets (⟨4, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0005 : lowerComputed (⟨5, by decide⟩ : Fin 1069) = lowerFacets (⟨5, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0006 : lowerComputed (⟨6, by decide⟩ : Fin 1069) = lowerFacets (⟨6, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0007 : lowerComputed (⟨7, by decide⟩ : Fin 1069) = lowerFacets (⟨7, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0008 : lowerComputed (⟨8, by decide⟩ : Fin 1069) = lowerFacets (⟨8, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0009 : lowerComputed (⟨9, by decide⟩ : Fin 1069) = lowerFacets (⟨9, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0010 : lowerComputed (⟨10, by decide⟩ : Fin 1069) = lowerFacets (⟨10, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0011 : lowerComputed (⟨11, by decide⟩ : Fin 1069) = lowerFacets (⟨11, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0012 : lowerComputed (⟨12, by decide⟩ : Fin 1069) = lowerFacets (⟨12, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0013 : lowerComputed (⟨13, by decide⟩ : Fin 1069) = lowerFacets (⟨13, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0014 : lowerComputed (⟨14, by decide⟩ : Fin 1069) = lowerFacets (⟨14, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0015 : lowerComputed (⟨15, by decide⟩ : Fin 1069) = lowerFacets (⟨15, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0016 : lowerComputed (⟨16, by decide⟩ : Fin 1069) = lowerFacets (⟨16, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0017 : lowerComputed (⟨17, by decide⟩ : Fin 1069) = lowerFacets (⟨17, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0018 : lowerComputed (⟨18, by decide⟩ : Fin 1069) = lowerFacets (⟨18, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0019 : lowerComputed (⟨19, by decide⟩ : Fin 1069) = lowerFacets (⟨19, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0020 : lowerComputed (⟨20, by decide⟩ : Fin 1069) = lowerFacets (⟨20, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0021 : lowerComputed (⟨21, by decide⟩ : Fin 1069) = lowerFacets (⟨21, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0022 : lowerComputed (⟨22, by decide⟩ : Fin 1069) = lowerFacets (⟨22, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0023 : lowerComputed (⟨23, by decide⟩ : Fin 1069) = lowerFacets (⟨23, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0024 : lowerComputed (⟨24, by decide⟩ : Fin 1069) = lowerFacets (⟨24, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0025 : lowerComputed (⟨25, by decide⟩ : Fin 1069) = lowerFacets (⟨25, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0026 : lowerComputed (⟨26, by decide⟩ : Fin 1069) = lowerFacets (⟨26, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0027 : lowerComputed (⟨27, by decide⟩ : Fin 1069) = lowerFacets (⟨27, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0028 : lowerComputed (⟨28, by decide⟩ : Fin 1069) = lowerFacets (⟨28, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0029 : lowerComputed (⟨29, by decide⟩ : Fin 1069) = lowerFacets (⟨29, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0030 : lowerComputed (⟨30, by decide⟩ : Fin 1069) = lowerFacets (⟨30, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0031 : lowerComputed (⟨31, by decide⟩ : Fin 1069) = lowerFacets (⟨31, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0032 : lowerComputed (⟨32, by decide⟩ : Fin 1069) = lowerFacets (⟨32, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0033 : lowerComputed (⟨33, by decide⟩ : Fin 1069) = lowerFacets (⟨33, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0034 : lowerComputed (⟨34, by decide⟩ : Fin 1069) = lowerFacets (⟨34, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0035 : lowerComputed (⟨35, by decide⟩ : Fin 1069) = lowerFacets (⟨35, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0036 : lowerComputed (⟨36, by decide⟩ : Fin 1069) = lowerFacets (⟨36, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0037 : lowerComputed (⟨37, by decide⟩ : Fin 1069) = lowerFacets (⟨37, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0038 : lowerComputed (⟨38, by decide⟩ : Fin 1069) = lowerFacets (⟨38, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0039 : lowerComputed (⟨39, by decide⟩ : Fin 1069) = lowerFacets (⟨39, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0040 : lowerComputed (⟨40, by decide⟩ : Fin 1069) = lowerFacets (⟨40, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0041 : lowerComputed (⟨41, by decide⟩ : Fin 1069) = lowerFacets (⟨41, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0042 : lowerComputed (⟨42, by decide⟩ : Fin 1069) = lowerFacets (⟨42, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0043 : lowerComputed (⟨43, by decide⟩ : Fin 1069) = lowerFacets (⟨43, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0044 : lowerComputed (⟨44, by decide⟩ : Fin 1069) = lowerFacets (⟨44, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0045 : lowerComputed (⟨45, by decide⟩ : Fin 1069) = lowerFacets (⟨45, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0046 : lowerComputed (⟨46, by decide⟩ : Fin 1069) = lowerFacets (⟨46, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0047 : lowerComputed (⟨47, by decide⟩ : Fin 1069) = lowerFacets (⟨47, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0048 : lowerComputed (⟨48, by decide⟩ : Fin 1069) = lowerFacets (⟨48, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0049 : lowerComputed (⟨49, by decide⟩ : Fin 1069) = lowerFacets (⟨49, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0050 : lowerComputed (⟨50, by decide⟩ : Fin 1069) = lowerFacets (⟨50, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0051 : lowerComputed (⟨51, by decide⟩ : Fin 1069) = lowerFacets (⟨51, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0052 : lowerComputed (⟨52, by decide⟩ : Fin 1069) = lowerFacets (⟨52, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0053 : lowerComputed (⟨53, by decide⟩ : Fin 1069) = lowerFacets (⟨53, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0054 : lowerComputed (⟨54, by decide⟩ : Fin 1069) = lowerFacets (⟨54, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0055 : lowerComputed (⟨55, by decide⟩ : Fin 1069) = lowerFacets (⟨55, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0056 : lowerComputed (⟨56, by decide⟩ : Fin 1069) = lowerFacets (⟨56, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0057 : lowerComputed (⟨57, by decide⟩ : Fin 1069) = lowerFacets (⟨57, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0058 : lowerComputed (⟨58, by decide⟩ : Fin 1069) = lowerFacets (⟨58, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0059 : lowerComputed (⟨59, by decide⟩ : Fin 1069) = lowerFacets (⟨59, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0060 : lowerComputed (⟨60, by decide⟩ : Fin 1069) = lowerFacets (⟨60, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0061 : lowerComputed (⟨61, by decide⟩ : Fin 1069) = lowerFacets (⟨61, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0062 : lowerComputed (⟨62, by decide⟩ : Fin 1069) = lowerFacets (⟨62, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0063 : lowerComputed (⟨63, by decide⟩ : Fin 1069) = lowerFacets (⟨63, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0064 : lowerComputed (⟨64, by decide⟩ : Fin 1069) = lowerFacets (⟨64, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0065 : lowerComputed (⟨65, by decide⟩ : Fin 1069) = lowerFacets (⟨65, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0066 : lowerComputed (⟨66, by decide⟩ : Fin 1069) = lowerFacets (⟨66, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0067 : lowerComputed (⟨67, by decide⟩ : Fin 1069) = lowerFacets (⟨67, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0068 : lowerComputed (⟨68, by decide⟩ : Fin 1069) = lowerFacets (⟨68, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0069 : lowerComputed (⟨69, by decide⟩ : Fin 1069) = lowerFacets (⟨69, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0070 : lowerComputed (⟨70, by decide⟩ : Fin 1069) = lowerFacets (⟨70, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0071 : lowerComputed (⟨71, by decide⟩ : Fin 1069) = lowerFacets (⟨71, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0072 : lowerComputed (⟨72, by decide⟩ : Fin 1069) = lowerFacets (⟨72, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0073 : lowerComputed (⟨73, by decide⟩ : Fin 1069) = lowerFacets (⟨73, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0074 : lowerComputed (⟨74, by decide⟩ : Fin 1069) = lowerFacets (⟨74, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0075 : lowerComputed (⟨75, by decide⟩ : Fin 1069) = lowerFacets (⟨75, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0076 : lowerComputed (⟨76, by decide⟩ : Fin 1069) = lowerFacets (⟨76, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0077 : lowerComputed (⟨77, by decide⟩ : Fin 1069) = lowerFacets (⟨77, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0078 : lowerComputed (⟨78, by decide⟩ : Fin 1069) = lowerFacets (⟨78, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0079 : lowerComputed (⟨79, by decide⟩ : Fin 1069) = lowerFacets (⟨79, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0080 : lowerComputed (⟨80, by decide⟩ : Fin 1069) = lowerFacets (⟨80, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0081 : lowerComputed (⟨81, by decide⟩ : Fin 1069) = lowerFacets (⟨81, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0082 : lowerComputed (⟨82, by decide⟩ : Fin 1069) = lowerFacets (⟨82, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0083 : lowerComputed (⟨83, by decide⟩ : Fin 1069) = lowerFacets (⟨83, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0084 : lowerComputed (⟨84, by decide⟩ : Fin 1069) = lowerFacets (⟨84, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0085 : lowerComputed (⟨85, by decide⟩ : Fin 1069) = lowerFacets (⟨85, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0086 : lowerComputed (⟨86, by decide⟩ : Fin 1069) = lowerFacets (⟨86, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0087 : lowerComputed (⟨87, by decide⟩ : Fin 1069) = lowerFacets (⟨87, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0088 : lowerComputed (⟨88, by decide⟩ : Fin 1069) = lowerFacets (⟨88, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0089 : lowerComputed (⟨89, by decide⟩ : Fin 1069) = lowerFacets (⟨89, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0090 : lowerComputed (⟨90, by decide⟩ : Fin 1069) = lowerFacets (⟨90, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0091 : lowerComputed (⟨91, by decide⟩ : Fin 1069) = lowerFacets (⟨91, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0092 : lowerComputed (⟨92, by decide⟩ : Fin 1069) = lowerFacets (⟨92, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0093 : lowerComputed (⟨93, by decide⟩ : Fin 1069) = lowerFacets (⟨93, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0094 : lowerComputed (⟨94, by decide⟩ : Fin 1069) = lowerFacets (⟨94, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0095 : lowerComputed (⟨95, by decide⟩ : Fin 1069) = lowerFacets (⟨95, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0096 : lowerComputed (⟨96, by decide⟩ : Fin 1069) = lowerFacets (⟨96, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0097 : lowerComputed (⟨97, by decide⟩ : Fin 1069) = lowerFacets (⟨97, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0098 : lowerComputed (⟨98, by decide⟩ : Fin 1069) = lowerFacets (⟨98, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0099 : lowerComputed (⟨99, by decide⟩ : Fin 1069) = lowerFacets (⟨99, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0100 : lowerComputed (⟨100, by decide⟩ : Fin 1069) = lowerFacets (⟨100, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0101 : lowerComputed (⟨101, by decide⟩ : Fin 1069) = lowerFacets (⟨101, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0102 : lowerComputed (⟨102, by decide⟩ : Fin 1069) = lowerFacets (⟨102, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0103 : lowerComputed (⟨103, by decide⟩ : Fin 1069) = lowerFacets (⟨103, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0104 : lowerComputed (⟨104, by decide⟩ : Fin 1069) = lowerFacets (⟨104, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0105 : lowerComputed (⟨105, by decide⟩ : Fin 1069) = lowerFacets (⟨105, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0106 : lowerComputed (⟨106, by decide⟩ : Fin 1069) = lowerFacets (⟨106, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0107 : lowerComputed (⟨107, by decide⟩ : Fin 1069) = lowerFacets (⟨107, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0108 : lowerComputed (⟨108, by decide⟩ : Fin 1069) = lowerFacets (⟨108, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0109 : lowerComputed (⟨109, by decide⟩ : Fin 1069) = lowerFacets (⟨109, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0110 : lowerComputed (⟨110, by decide⟩ : Fin 1069) = lowerFacets (⟨110, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0111 : lowerComputed (⟨111, by decide⟩ : Fin 1069) = lowerFacets (⟨111, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0112 : lowerComputed (⟨112, by decide⟩ : Fin 1069) = lowerFacets (⟨112, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0113 : lowerComputed (⟨113, by decide⟩ : Fin 1069) = lowerFacets (⟨113, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0114 : lowerComputed (⟨114, by decide⟩ : Fin 1069) = lowerFacets (⟨114, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0115 : lowerComputed (⟨115, by decide⟩ : Fin 1069) = lowerFacets (⟨115, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0116 : lowerComputed (⟨116, by decide⟩ : Fin 1069) = lowerFacets (⟨116, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0117 : lowerComputed (⟨117, by decide⟩ : Fin 1069) = lowerFacets (⟨117, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0118 : lowerComputed (⟨118, by decide⟩ : Fin 1069) = lowerFacets (⟨118, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0119 : lowerComputed (⟨119, by decide⟩ : Fin 1069) = lowerFacets (⟨119, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0120 : lowerComputed (⟨120, by decide⟩ : Fin 1069) = lowerFacets (⟨120, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0121 : lowerComputed (⟨121, by decide⟩ : Fin 1069) = lowerFacets (⟨121, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0122 : lowerComputed (⟨122, by decide⟩ : Fin 1069) = lowerFacets (⟨122, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0123 : lowerComputed (⟨123, by decide⟩ : Fin 1069) = lowerFacets (⟨123, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0124 : lowerComputed (⟨124, by decide⟩ : Fin 1069) = lowerFacets (⟨124, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0125 : lowerComputed (⟨125, by decide⟩ : Fin 1069) = lowerFacets (⟨125, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0126 : lowerComputed (⟨126, by decide⟩ : Fin 1069) = lowerFacets (⟨126, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0127 : lowerComputed (⟨127, by decide⟩ : Fin 1069) = lowerFacets (⟨127, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0128 : lowerComputed (⟨128, by decide⟩ : Fin 1069) = lowerFacets (⟨128, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0129 : lowerComputed (⟨129, by decide⟩ : Fin 1069) = lowerFacets (⟨129, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0130 : lowerComputed (⟨130, by decide⟩ : Fin 1069) = lowerFacets (⟨130, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0131 : lowerComputed (⟨131, by decide⟩ : Fin 1069) = lowerFacets (⟨131, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0132 : lowerComputed (⟨132, by decide⟩ : Fin 1069) = lowerFacets (⟨132, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0133 : lowerComputed (⟨133, by decide⟩ : Fin 1069) = lowerFacets (⟨133, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0134 : lowerComputed (⟨134, by decide⟩ : Fin 1069) = lowerFacets (⟨134, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0135 : lowerComputed (⟨135, by decide⟩ : Fin 1069) = lowerFacets (⟨135, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0136 : lowerComputed (⟨136, by decide⟩ : Fin 1069) = lowerFacets (⟨136, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0137 : lowerComputed (⟨137, by decide⟩ : Fin 1069) = lowerFacets (⟨137, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0138 : lowerComputed (⟨138, by decide⟩ : Fin 1069) = lowerFacets (⟨138, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0139 : lowerComputed (⟨139, by decide⟩ : Fin 1069) = lowerFacets (⟨139, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0140 : lowerComputed (⟨140, by decide⟩ : Fin 1069) = lowerFacets (⟨140, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0141 : lowerComputed (⟨141, by decide⟩ : Fin 1069) = lowerFacets (⟨141, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0142 : lowerComputed (⟨142, by decide⟩ : Fin 1069) = lowerFacets (⟨142, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0143 : lowerComputed (⟨143, by decide⟩ : Fin 1069) = lowerFacets (⟨143, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0144 : lowerComputed (⟨144, by decide⟩ : Fin 1069) = lowerFacets (⟨144, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0145 : lowerComputed (⟨145, by decide⟩ : Fin 1069) = lowerFacets (⟨145, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0146 : lowerComputed (⟨146, by decide⟩ : Fin 1069) = lowerFacets (⟨146, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0147 : lowerComputed (⟨147, by decide⟩ : Fin 1069) = lowerFacets (⟨147, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0148 : lowerComputed (⟨148, by decide⟩ : Fin 1069) = lowerFacets (⟨148, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0149 : lowerComputed (⟨149, by decide⟩ : Fin 1069) = lowerFacets (⟨149, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0150 : lowerComputed (⟨150, by decide⟩ : Fin 1069) = lowerFacets (⟨150, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0151 : lowerComputed (⟨151, by decide⟩ : Fin 1069) = lowerFacets (⟨151, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0152 : lowerComputed (⟨152, by decide⟩ : Fin 1069) = lowerFacets (⟨152, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0153 : lowerComputed (⟨153, by decide⟩ : Fin 1069) = lowerFacets (⟨153, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0154 : lowerComputed (⟨154, by decide⟩ : Fin 1069) = lowerFacets (⟨154, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0155 : lowerComputed (⟨155, by decide⟩ : Fin 1069) = lowerFacets (⟨155, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0156 : lowerComputed (⟨156, by decide⟩ : Fin 1069) = lowerFacets (⟨156, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0157 : lowerComputed (⟨157, by decide⟩ : Fin 1069) = lowerFacets (⟨157, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0158 : lowerComputed (⟨158, by decide⟩ : Fin 1069) = lowerFacets (⟨158, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0159 : lowerComputed (⟨159, by decide⟩ : Fin 1069) = lowerFacets (⟨159, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0160 : lowerComputed (⟨160, by decide⟩ : Fin 1069) = lowerFacets (⟨160, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0161 : lowerComputed (⟨161, by decide⟩ : Fin 1069) = lowerFacets (⟨161, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0162 : lowerComputed (⟨162, by decide⟩ : Fin 1069) = lowerFacets (⟨162, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0163 : lowerComputed (⟨163, by decide⟩ : Fin 1069) = lowerFacets (⟨163, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0164 : lowerComputed (⟨164, by decide⟩ : Fin 1069) = lowerFacets (⟨164, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0165 : lowerComputed (⟨165, by decide⟩ : Fin 1069) = lowerFacets (⟨165, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0166 : lowerComputed (⟨166, by decide⟩ : Fin 1069) = lowerFacets (⟨166, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0167 : lowerComputed (⟨167, by decide⟩ : Fin 1069) = lowerFacets (⟨167, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0168 : lowerComputed (⟨168, by decide⟩ : Fin 1069) = lowerFacets (⟨168, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0169 : lowerComputed (⟨169, by decide⟩ : Fin 1069) = lowerFacets (⟨169, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0170 : lowerComputed (⟨170, by decide⟩ : Fin 1069) = lowerFacets (⟨170, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0171 : lowerComputed (⟨171, by decide⟩ : Fin 1069) = lowerFacets (⟨171, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0172 : lowerComputed (⟨172, by decide⟩ : Fin 1069) = lowerFacets (⟨172, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0173 : lowerComputed (⟨173, by decide⟩ : Fin 1069) = lowerFacets (⟨173, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0174 : lowerComputed (⟨174, by decide⟩ : Fin 1069) = lowerFacets (⟨174, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0175 : lowerComputed (⟨175, by decide⟩ : Fin 1069) = lowerFacets (⟨175, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0176 : lowerComputed (⟨176, by decide⟩ : Fin 1069) = lowerFacets (⟨176, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0177 : lowerComputed (⟨177, by decide⟩ : Fin 1069) = lowerFacets (⟨177, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0178 : lowerComputed (⟨178, by decide⟩ : Fin 1069) = lowerFacets (⟨178, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0179 : lowerComputed (⟨179, by decide⟩ : Fin 1069) = lowerFacets (⟨179, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0180 : lowerComputed (⟨180, by decide⟩ : Fin 1069) = lowerFacets (⟨180, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0181 : lowerComputed (⟨181, by decide⟩ : Fin 1069) = lowerFacets (⟨181, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0182 : lowerComputed (⟨182, by decide⟩ : Fin 1069) = lowerFacets (⟨182, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0183 : lowerComputed (⟨183, by decide⟩ : Fin 1069) = lowerFacets (⟨183, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0184 : lowerComputed (⟨184, by decide⟩ : Fin 1069) = lowerFacets (⟨184, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0185 : lowerComputed (⟨185, by decide⟩ : Fin 1069) = lowerFacets (⟨185, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0186 : lowerComputed (⟨186, by decide⟩ : Fin 1069) = lowerFacets (⟨186, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0187 : lowerComputed (⟨187, by decide⟩ : Fin 1069) = lowerFacets (⟨187, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0188 : lowerComputed (⟨188, by decide⟩ : Fin 1069) = lowerFacets (⟨188, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0189 : lowerComputed (⟨189, by decide⟩ : Fin 1069) = lowerFacets (⟨189, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0190 : lowerComputed (⟨190, by decide⟩ : Fin 1069) = lowerFacets (⟨190, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0191 : lowerComputed (⟨191, by decide⟩ : Fin 1069) = lowerFacets (⟨191, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0192 : lowerComputed (⟨192, by decide⟩ : Fin 1069) = lowerFacets (⟨192, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0193 : lowerComputed (⟨193, by decide⟩ : Fin 1069) = lowerFacets (⟨193, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0194 : lowerComputed (⟨194, by decide⟩ : Fin 1069) = lowerFacets (⟨194, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0195 : lowerComputed (⟨195, by decide⟩ : Fin 1069) = lowerFacets (⟨195, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0196 : lowerComputed (⟨196, by decide⟩ : Fin 1069) = lowerFacets (⟨196, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0197 : lowerComputed (⟨197, by decide⟩ : Fin 1069) = lowerFacets (⟨197, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0198 : lowerComputed (⟨198, by decide⟩ : Fin 1069) = lowerFacets (⟨198, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0199 : lowerComputed (⟨199, by decide⟩ : Fin 1069) = lowerFacets (⟨199, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0200 : lowerComputed (⟨200, by decide⟩ : Fin 1069) = lowerFacets (⟨200, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0201 : lowerComputed (⟨201, by decide⟩ : Fin 1069) = lowerFacets (⟨201, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0202 : lowerComputed (⟨202, by decide⟩ : Fin 1069) = lowerFacets (⟨202, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0203 : lowerComputed (⟨203, by decide⟩ : Fin 1069) = lowerFacets (⟨203, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0204 : lowerComputed (⟨204, by decide⟩ : Fin 1069) = lowerFacets (⟨204, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0205 : lowerComputed (⟨205, by decide⟩ : Fin 1069) = lowerFacets (⟨205, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0206 : lowerComputed (⟨206, by decide⟩ : Fin 1069) = lowerFacets (⟨206, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0207 : lowerComputed (⟨207, by decide⟩ : Fin 1069) = lowerFacets (⟨207, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0208 : lowerComputed (⟨208, by decide⟩ : Fin 1069) = lowerFacets (⟨208, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0209 : lowerComputed (⟨209, by decide⟩ : Fin 1069) = lowerFacets (⟨209, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0210 : lowerComputed (⟨210, by decide⟩ : Fin 1069) = lowerFacets (⟨210, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0211 : lowerComputed (⟨211, by decide⟩ : Fin 1069) = lowerFacets (⟨211, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0212 : lowerComputed (⟨212, by decide⟩ : Fin 1069) = lowerFacets (⟨212, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0213 : lowerComputed (⟨213, by decide⟩ : Fin 1069) = lowerFacets (⟨213, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0214 : lowerComputed (⟨214, by decide⟩ : Fin 1069) = lowerFacets (⟨214, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0215 : lowerComputed (⟨215, by decide⟩ : Fin 1069) = lowerFacets (⟨215, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0216 : lowerComputed (⟨216, by decide⟩ : Fin 1069) = lowerFacets (⟨216, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0217 : lowerComputed (⟨217, by decide⟩ : Fin 1069) = lowerFacets (⟨217, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0218 : lowerComputed (⟨218, by decide⟩ : Fin 1069) = lowerFacets (⟨218, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0219 : lowerComputed (⟨219, by decide⟩ : Fin 1069) = lowerFacets (⟨219, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0220 : lowerComputed (⟨220, by decide⟩ : Fin 1069) = lowerFacets (⟨220, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0221 : lowerComputed (⟨221, by decide⟩ : Fin 1069) = lowerFacets (⟨221, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0222 : lowerComputed (⟨222, by decide⟩ : Fin 1069) = lowerFacets (⟨222, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0223 : lowerComputed (⟨223, by decide⟩ : Fin 1069) = lowerFacets (⟨223, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0224 : lowerComputed (⟨224, by decide⟩ : Fin 1069) = lowerFacets (⟨224, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0225 : lowerComputed (⟨225, by decide⟩ : Fin 1069) = lowerFacets (⟨225, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0226 : lowerComputed (⟨226, by decide⟩ : Fin 1069) = lowerFacets (⟨226, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0227 : lowerComputed (⟨227, by decide⟩ : Fin 1069) = lowerFacets (⟨227, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0228 : lowerComputed (⟨228, by decide⟩ : Fin 1069) = lowerFacets (⟨228, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0229 : lowerComputed (⟨229, by decide⟩ : Fin 1069) = lowerFacets (⟨229, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0230 : lowerComputed (⟨230, by decide⟩ : Fin 1069) = lowerFacets (⟨230, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0231 : lowerComputed (⟨231, by decide⟩ : Fin 1069) = lowerFacets (⟨231, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0232 : lowerComputed (⟨232, by decide⟩ : Fin 1069) = lowerFacets (⟨232, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0233 : lowerComputed (⟨233, by decide⟩ : Fin 1069) = lowerFacets (⟨233, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0234 : lowerComputed (⟨234, by decide⟩ : Fin 1069) = lowerFacets (⟨234, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0235 : lowerComputed (⟨235, by decide⟩ : Fin 1069) = lowerFacets (⟨235, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0236 : lowerComputed (⟨236, by decide⟩ : Fin 1069) = lowerFacets (⟨236, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0237 : lowerComputed (⟨237, by decide⟩ : Fin 1069) = lowerFacets (⟨237, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0238 : lowerComputed (⟨238, by decide⟩ : Fin 1069) = lowerFacets (⟨238, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0239 : lowerComputed (⟨239, by decide⟩ : Fin 1069) = lowerFacets (⟨239, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0240 : lowerComputed (⟨240, by decide⟩ : Fin 1069) = lowerFacets (⟨240, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0241 : lowerComputed (⟨241, by decide⟩ : Fin 1069) = lowerFacets (⟨241, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0242 : lowerComputed (⟨242, by decide⟩ : Fin 1069) = lowerFacets (⟨242, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0243 : lowerComputed (⟨243, by decide⟩ : Fin 1069) = lowerFacets (⟨243, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0244 : lowerComputed (⟨244, by decide⟩ : Fin 1069) = lowerFacets (⟨244, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0245 : lowerComputed (⟨245, by decide⟩ : Fin 1069) = lowerFacets (⟨245, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0246 : lowerComputed (⟨246, by decide⟩ : Fin 1069) = lowerFacets (⟨246, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0247 : lowerComputed (⟨247, by decide⟩ : Fin 1069) = lowerFacets (⟨247, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0248 : lowerComputed (⟨248, by decide⟩ : Fin 1069) = lowerFacets (⟨248, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0249 : lowerComputed (⟨249, by decide⟩ : Fin 1069) = lowerFacets (⟨249, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0250 : lowerComputed (⟨250, by decide⟩ : Fin 1069) = lowerFacets (⟨250, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0251 : lowerComputed (⟨251, by decide⟩ : Fin 1069) = lowerFacets (⟨251, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0252 : lowerComputed (⟨252, by decide⟩ : Fin 1069) = lowerFacets (⟨252, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0253 : lowerComputed (⟨253, by decide⟩ : Fin 1069) = lowerFacets (⟨253, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0254 : lowerComputed (⟨254, by decide⟩ : Fin 1069) = lowerFacets (⟨254, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0255 : lowerComputed (⟨255, by decide⟩ : Fin 1069) = lowerFacets (⟨255, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0256 : lowerComputed (⟨256, by decide⟩ : Fin 1069) = lowerFacets (⟨256, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0257 : lowerComputed (⟨257, by decide⟩ : Fin 1069) = lowerFacets (⟨257, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0258 : lowerComputed (⟨258, by decide⟩ : Fin 1069) = lowerFacets (⟨258, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0259 : lowerComputed (⟨259, by decide⟩ : Fin 1069) = lowerFacets (⟨259, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0260 : lowerComputed (⟨260, by decide⟩ : Fin 1069) = lowerFacets (⟨260, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0261 : lowerComputed (⟨261, by decide⟩ : Fin 1069) = lowerFacets (⟨261, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0262 : lowerComputed (⟨262, by decide⟩ : Fin 1069) = lowerFacets (⟨262, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0263 : lowerComputed (⟨263, by decide⟩ : Fin 1069) = lowerFacets (⟨263, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0264 : lowerComputed (⟨264, by decide⟩ : Fin 1069) = lowerFacets (⟨264, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0265 : lowerComputed (⟨265, by decide⟩ : Fin 1069) = lowerFacets (⟨265, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0266 : lowerComputed (⟨266, by decide⟩ : Fin 1069) = lowerFacets (⟨266, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0267 : lowerComputed (⟨267, by decide⟩ : Fin 1069) = lowerFacets (⟨267, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0268 : lowerComputed (⟨268, by decide⟩ : Fin 1069) = lowerFacets (⟨268, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0269 : lowerComputed (⟨269, by decide⟩ : Fin 1069) = lowerFacets (⟨269, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0270 : lowerComputed (⟨270, by decide⟩ : Fin 1069) = lowerFacets (⟨270, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0271 : lowerComputed (⟨271, by decide⟩ : Fin 1069) = lowerFacets (⟨271, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0272 : lowerComputed (⟨272, by decide⟩ : Fin 1069) = lowerFacets (⟨272, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0273 : lowerComputed (⟨273, by decide⟩ : Fin 1069) = lowerFacets (⟨273, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0274 : lowerComputed (⟨274, by decide⟩ : Fin 1069) = lowerFacets (⟨274, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0275 : lowerComputed (⟨275, by decide⟩ : Fin 1069) = lowerFacets (⟨275, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0276 : lowerComputed (⟨276, by decide⟩ : Fin 1069) = lowerFacets (⟨276, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0277 : lowerComputed (⟨277, by decide⟩ : Fin 1069) = lowerFacets (⟨277, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0278 : lowerComputed (⟨278, by decide⟩ : Fin 1069) = lowerFacets (⟨278, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0279 : lowerComputed (⟨279, by decide⟩ : Fin 1069) = lowerFacets (⟨279, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0280 : lowerComputed (⟨280, by decide⟩ : Fin 1069) = lowerFacets (⟨280, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0281 : lowerComputed (⟨281, by decide⟩ : Fin 1069) = lowerFacets (⟨281, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0282 : lowerComputed (⟨282, by decide⟩ : Fin 1069) = lowerFacets (⟨282, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0283 : lowerComputed (⟨283, by decide⟩ : Fin 1069) = lowerFacets (⟨283, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0284 : lowerComputed (⟨284, by decide⟩ : Fin 1069) = lowerFacets (⟨284, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0285 : lowerComputed (⟨285, by decide⟩ : Fin 1069) = lowerFacets (⟨285, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0286 : lowerComputed (⟨286, by decide⟩ : Fin 1069) = lowerFacets (⟨286, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0287 : lowerComputed (⟨287, by decide⟩ : Fin 1069) = lowerFacets (⟨287, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0288 : lowerComputed (⟨288, by decide⟩ : Fin 1069) = lowerFacets (⟨288, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0289 : lowerComputed (⟨289, by decide⟩ : Fin 1069) = lowerFacets (⟨289, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0290 : lowerComputed (⟨290, by decide⟩ : Fin 1069) = lowerFacets (⟨290, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0291 : lowerComputed (⟨291, by decide⟩ : Fin 1069) = lowerFacets (⟨291, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0292 : lowerComputed (⟨292, by decide⟩ : Fin 1069) = lowerFacets (⟨292, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0293 : lowerComputed (⟨293, by decide⟩ : Fin 1069) = lowerFacets (⟨293, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0294 : lowerComputed (⟨294, by decide⟩ : Fin 1069) = lowerFacets (⟨294, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0295 : lowerComputed (⟨295, by decide⟩ : Fin 1069) = lowerFacets (⟨295, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0296 : lowerComputed (⟨296, by decide⟩ : Fin 1069) = lowerFacets (⟨296, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0297 : lowerComputed (⟨297, by decide⟩ : Fin 1069) = lowerFacets (⟨297, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0298 : lowerComputed (⟨298, by decide⟩ : Fin 1069) = lowerFacets (⟨298, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0299 : lowerComputed (⟨299, by decide⟩ : Fin 1069) = lowerFacets (⟨299, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0300 : lowerComputed (⟨300, by decide⟩ : Fin 1069) = lowerFacets (⟨300, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0301 : lowerComputed (⟨301, by decide⟩ : Fin 1069) = lowerFacets (⟨301, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0302 : lowerComputed (⟨302, by decide⟩ : Fin 1069) = lowerFacets (⟨302, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0303 : lowerComputed (⟨303, by decide⟩ : Fin 1069) = lowerFacets (⟨303, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0304 : lowerComputed (⟨304, by decide⟩ : Fin 1069) = lowerFacets (⟨304, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0305 : lowerComputed (⟨305, by decide⟩ : Fin 1069) = lowerFacets (⟨305, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0306 : lowerComputed (⟨306, by decide⟩ : Fin 1069) = lowerFacets (⟨306, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0307 : lowerComputed (⟨307, by decide⟩ : Fin 1069) = lowerFacets (⟨307, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0308 : lowerComputed (⟨308, by decide⟩ : Fin 1069) = lowerFacets (⟨308, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0309 : lowerComputed (⟨309, by decide⟩ : Fin 1069) = lowerFacets (⟨309, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0310 : lowerComputed (⟨310, by decide⟩ : Fin 1069) = lowerFacets (⟨310, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0311 : lowerComputed (⟨311, by decide⟩ : Fin 1069) = lowerFacets (⟨311, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0312 : lowerComputed (⟨312, by decide⟩ : Fin 1069) = lowerFacets (⟨312, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0313 : lowerComputed (⟨313, by decide⟩ : Fin 1069) = lowerFacets (⟨313, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0314 : lowerComputed (⟨314, by decide⟩ : Fin 1069) = lowerFacets (⟨314, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0315 : lowerComputed (⟨315, by decide⟩ : Fin 1069) = lowerFacets (⟨315, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0316 : lowerComputed (⟨316, by decide⟩ : Fin 1069) = lowerFacets (⟨316, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0317 : lowerComputed (⟨317, by decide⟩ : Fin 1069) = lowerFacets (⟨317, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0318 : lowerComputed (⟨318, by decide⟩ : Fin 1069) = lowerFacets (⟨318, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0319 : lowerComputed (⟨319, by decide⟩ : Fin 1069) = lowerFacets (⟨319, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0320 : lowerComputed (⟨320, by decide⟩ : Fin 1069) = lowerFacets (⟨320, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0321 : lowerComputed (⟨321, by decide⟩ : Fin 1069) = lowerFacets (⟨321, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0322 : lowerComputed (⟨322, by decide⟩ : Fin 1069) = lowerFacets (⟨322, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0323 : lowerComputed (⟨323, by decide⟩ : Fin 1069) = lowerFacets (⟨323, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0324 : lowerComputed (⟨324, by decide⟩ : Fin 1069) = lowerFacets (⟨324, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0325 : lowerComputed (⟨325, by decide⟩ : Fin 1069) = lowerFacets (⟨325, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0326 : lowerComputed (⟨326, by decide⟩ : Fin 1069) = lowerFacets (⟨326, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0327 : lowerComputed (⟨327, by decide⟩ : Fin 1069) = lowerFacets (⟨327, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0328 : lowerComputed (⟨328, by decide⟩ : Fin 1069) = lowerFacets (⟨328, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0329 : lowerComputed (⟨329, by decide⟩ : Fin 1069) = lowerFacets (⟨329, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0330 : lowerComputed (⟨330, by decide⟩ : Fin 1069) = lowerFacets (⟨330, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0331 : lowerComputed (⟨331, by decide⟩ : Fin 1069) = lowerFacets (⟨331, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0332 : lowerComputed (⟨332, by decide⟩ : Fin 1069) = lowerFacets (⟨332, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0333 : lowerComputed (⟨333, by decide⟩ : Fin 1069) = lowerFacets (⟨333, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0334 : lowerComputed (⟨334, by decide⟩ : Fin 1069) = lowerFacets (⟨334, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0335 : lowerComputed (⟨335, by decide⟩ : Fin 1069) = lowerFacets (⟨335, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0336 : lowerComputed (⟨336, by decide⟩ : Fin 1069) = lowerFacets (⟨336, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0337 : lowerComputed (⟨337, by decide⟩ : Fin 1069) = lowerFacets (⟨337, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0338 : lowerComputed (⟨338, by decide⟩ : Fin 1069) = lowerFacets (⟨338, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0339 : lowerComputed (⟨339, by decide⟩ : Fin 1069) = lowerFacets (⟨339, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0340 : lowerComputed (⟨340, by decide⟩ : Fin 1069) = lowerFacets (⟨340, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0341 : lowerComputed (⟨341, by decide⟩ : Fin 1069) = lowerFacets (⟨341, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0342 : lowerComputed (⟨342, by decide⟩ : Fin 1069) = lowerFacets (⟨342, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0343 : lowerComputed (⟨343, by decide⟩ : Fin 1069) = lowerFacets (⟨343, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0344 : lowerComputed (⟨344, by decide⟩ : Fin 1069) = lowerFacets (⟨344, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0345 : lowerComputed (⟨345, by decide⟩ : Fin 1069) = lowerFacets (⟨345, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0346 : lowerComputed (⟨346, by decide⟩ : Fin 1069) = lowerFacets (⟨346, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0347 : lowerComputed (⟨347, by decide⟩ : Fin 1069) = lowerFacets (⟨347, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0348 : lowerComputed (⟨348, by decide⟩ : Fin 1069) = lowerFacets (⟨348, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0349 : lowerComputed (⟨349, by decide⟩ : Fin 1069) = lowerFacets (⟨349, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0350 : lowerComputed (⟨350, by decide⟩ : Fin 1069) = lowerFacets (⟨350, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0351 : lowerComputed (⟨351, by decide⟩ : Fin 1069) = lowerFacets (⟨351, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0352 : lowerComputed (⟨352, by decide⟩ : Fin 1069) = lowerFacets (⟨352, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0353 : lowerComputed (⟨353, by decide⟩ : Fin 1069) = lowerFacets (⟨353, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0354 : lowerComputed (⟨354, by decide⟩ : Fin 1069) = lowerFacets (⟨354, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0355 : lowerComputed (⟨355, by decide⟩ : Fin 1069) = lowerFacets (⟨355, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0356 : lowerComputed (⟨356, by decide⟩ : Fin 1069) = lowerFacets (⟨356, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0357 : lowerComputed (⟨357, by decide⟩ : Fin 1069) = lowerFacets (⟨357, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0358 : lowerComputed (⟨358, by decide⟩ : Fin 1069) = lowerFacets (⟨358, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0359 : lowerComputed (⟨359, by decide⟩ : Fin 1069) = lowerFacets (⟨359, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0360 : lowerComputed (⟨360, by decide⟩ : Fin 1069) = lowerFacets (⟨360, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0361 : lowerComputed (⟨361, by decide⟩ : Fin 1069) = lowerFacets (⟨361, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0362 : lowerComputed (⟨362, by decide⟩ : Fin 1069) = lowerFacets (⟨362, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0363 : lowerComputed (⟨363, by decide⟩ : Fin 1069) = lowerFacets (⟨363, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0364 : lowerComputed (⟨364, by decide⟩ : Fin 1069) = lowerFacets (⟨364, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0365 : lowerComputed (⟨365, by decide⟩ : Fin 1069) = lowerFacets (⟨365, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0366 : lowerComputed (⟨366, by decide⟩ : Fin 1069) = lowerFacets (⟨366, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0367 : lowerComputed (⟨367, by decide⟩ : Fin 1069) = lowerFacets (⟨367, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0368 : lowerComputed (⟨368, by decide⟩ : Fin 1069) = lowerFacets (⟨368, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0369 : lowerComputed (⟨369, by decide⟩ : Fin 1069) = lowerFacets (⟨369, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0370 : lowerComputed (⟨370, by decide⟩ : Fin 1069) = lowerFacets (⟨370, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0371 : lowerComputed (⟨371, by decide⟩ : Fin 1069) = lowerFacets (⟨371, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0372 : lowerComputed (⟨372, by decide⟩ : Fin 1069) = lowerFacets (⟨372, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0373 : lowerComputed (⟨373, by decide⟩ : Fin 1069) = lowerFacets (⟨373, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0374 : lowerComputed (⟨374, by decide⟩ : Fin 1069) = lowerFacets (⟨374, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0375 : lowerComputed (⟨375, by decide⟩ : Fin 1069) = lowerFacets (⟨375, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0376 : lowerComputed (⟨376, by decide⟩ : Fin 1069) = lowerFacets (⟨376, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0377 : lowerComputed (⟨377, by decide⟩ : Fin 1069) = lowerFacets (⟨377, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0378 : lowerComputed (⟨378, by decide⟩ : Fin 1069) = lowerFacets (⟨378, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0379 : lowerComputed (⟨379, by decide⟩ : Fin 1069) = lowerFacets (⟨379, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0380 : lowerComputed (⟨380, by decide⟩ : Fin 1069) = lowerFacets (⟨380, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0381 : lowerComputed (⟨381, by decide⟩ : Fin 1069) = lowerFacets (⟨381, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0382 : lowerComputed (⟨382, by decide⟩ : Fin 1069) = lowerFacets (⟨382, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0383 : lowerComputed (⟨383, by decide⟩ : Fin 1069) = lowerFacets (⟨383, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0384 : lowerComputed (⟨384, by decide⟩ : Fin 1069) = lowerFacets (⟨384, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0385 : lowerComputed (⟨385, by decide⟩ : Fin 1069) = lowerFacets (⟨385, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0386 : lowerComputed (⟨386, by decide⟩ : Fin 1069) = lowerFacets (⟨386, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0387 : lowerComputed (⟨387, by decide⟩ : Fin 1069) = lowerFacets (⟨387, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0388 : lowerComputed (⟨388, by decide⟩ : Fin 1069) = lowerFacets (⟨388, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0389 : lowerComputed (⟨389, by decide⟩ : Fin 1069) = lowerFacets (⟨389, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0390 : lowerComputed (⟨390, by decide⟩ : Fin 1069) = lowerFacets (⟨390, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0391 : lowerComputed (⟨391, by decide⟩ : Fin 1069) = lowerFacets (⟨391, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0392 : lowerComputed (⟨392, by decide⟩ : Fin 1069) = lowerFacets (⟨392, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0393 : lowerComputed (⟨393, by decide⟩ : Fin 1069) = lowerFacets (⟨393, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0394 : lowerComputed (⟨394, by decide⟩ : Fin 1069) = lowerFacets (⟨394, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0395 : lowerComputed (⟨395, by decide⟩ : Fin 1069) = lowerFacets (⟨395, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0396 : lowerComputed (⟨396, by decide⟩ : Fin 1069) = lowerFacets (⟨396, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0397 : lowerComputed (⟨397, by decide⟩ : Fin 1069) = lowerFacets (⟨397, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0398 : lowerComputed (⟨398, by decide⟩ : Fin 1069) = lowerFacets (⟨398, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0399 : lowerComputed (⟨399, by decide⟩ : Fin 1069) = lowerFacets (⟨399, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0400 : lowerComputed (⟨400, by decide⟩ : Fin 1069) = lowerFacets (⟨400, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0401 : lowerComputed (⟨401, by decide⟩ : Fin 1069) = lowerFacets (⟨401, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0402 : lowerComputed (⟨402, by decide⟩ : Fin 1069) = lowerFacets (⟨402, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0403 : lowerComputed (⟨403, by decide⟩ : Fin 1069) = lowerFacets (⟨403, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0404 : lowerComputed (⟨404, by decide⟩ : Fin 1069) = lowerFacets (⟨404, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0405 : lowerComputed (⟨405, by decide⟩ : Fin 1069) = lowerFacets (⟨405, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0406 : lowerComputed (⟨406, by decide⟩ : Fin 1069) = lowerFacets (⟨406, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0407 : lowerComputed (⟨407, by decide⟩ : Fin 1069) = lowerFacets (⟨407, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0408 : lowerComputed (⟨408, by decide⟩ : Fin 1069) = lowerFacets (⟨408, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0409 : lowerComputed (⟨409, by decide⟩ : Fin 1069) = lowerFacets (⟨409, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0410 : lowerComputed (⟨410, by decide⟩ : Fin 1069) = lowerFacets (⟨410, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0411 : lowerComputed (⟨411, by decide⟩ : Fin 1069) = lowerFacets (⟨411, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0412 : lowerComputed (⟨412, by decide⟩ : Fin 1069) = lowerFacets (⟨412, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0413 : lowerComputed (⟨413, by decide⟩ : Fin 1069) = lowerFacets (⟨413, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0414 : lowerComputed (⟨414, by decide⟩ : Fin 1069) = lowerFacets (⟨414, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0415 : lowerComputed (⟨415, by decide⟩ : Fin 1069) = lowerFacets (⟨415, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0416 : lowerComputed (⟨416, by decide⟩ : Fin 1069) = lowerFacets (⟨416, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0417 : lowerComputed (⟨417, by decide⟩ : Fin 1069) = lowerFacets (⟨417, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0418 : lowerComputed (⟨418, by decide⟩ : Fin 1069) = lowerFacets (⟨418, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0419 : lowerComputed (⟨419, by decide⟩ : Fin 1069) = lowerFacets (⟨419, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0420 : lowerComputed (⟨420, by decide⟩ : Fin 1069) = lowerFacets (⟨420, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0421 : lowerComputed (⟨421, by decide⟩ : Fin 1069) = lowerFacets (⟨421, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0422 : lowerComputed (⟨422, by decide⟩ : Fin 1069) = lowerFacets (⟨422, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0423 : lowerComputed (⟨423, by decide⟩ : Fin 1069) = lowerFacets (⟨423, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0424 : lowerComputed (⟨424, by decide⟩ : Fin 1069) = lowerFacets (⟨424, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0425 : lowerComputed (⟨425, by decide⟩ : Fin 1069) = lowerFacets (⟨425, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0426 : lowerComputed (⟨426, by decide⟩ : Fin 1069) = lowerFacets (⟨426, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0427 : lowerComputed (⟨427, by decide⟩ : Fin 1069) = lowerFacets (⟨427, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0428 : lowerComputed (⟨428, by decide⟩ : Fin 1069) = lowerFacets (⟨428, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0429 : lowerComputed (⟨429, by decide⟩ : Fin 1069) = lowerFacets (⟨429, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0430 : lowerComputed (⟨430, by decide⟩ : Fin 1069) = lowerFacets (⟨430, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0431 : lowerComputed (⟨431, by decide⟩ : Fin 1069) = lowerFacets (⟨431, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0432 : lowerComputed (⟨432, by decide⟩ : Fin 1069) = lowerFacets (⟨432, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0433 : lowerComputed (⟨433, by decide⟩ : Fin 1069) = lowerFacets (⟨433, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0434 : lowerComputed (⟨434, by decide⟩ : Fin 1069) = lowerFacets (⟨434, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0435 : lowerComputed (⟨435, by decide⟩ : Fin 1069) = lowerFacets (⟨435, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0436 : lowerComputed (⟨436, by decide⟩ : Fin 1069) = lowerFacets (⟨436, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0437 : lowerComputed (⟨437, by decide⟩ : Fin 1069) = lowerFacets (⟨437, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0438 : lowerComputed (⟨438, by decide⟩ : Fin 1069) = lowerFacets (⟨438, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0439 : lowerComputed (⟨439, by decide⟩ : Fin 1069) = lowerFacets (⟨439, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0440 : lowerComputed (⟨440, by decide⟩ : Fin 1069) = lowerFacets (⟨440, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0441 : lowerComputed (⟨441, by decide⟩ : Fin 1069) = lowerFacets (⟨441, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0442 : lowerComputed (⟨442, by decide⟩ : Fin 1069) = lowerFacets (⟨442, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0443 : lowerComputed (⟨443, by decide⟩ : Fin 1069) = lowerFacets (⟨443, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0444 : lowerComputed (⟨444, by decide⟩ : Fin 1069) = lowerFacets (⟨444, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0445 : lowerComputed (⟨445, by decide⟩ : Fin 1069) = lowerFacets (⟨445, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0446 : lowerComputed (⟨446, by decide⟩ : Fin 1069) = lowerFacets (⟨446, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0447 : lowerComputed (⟨447, by decide⟩ : Fin 1069) = lowerFacets (⟨447, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0448 : lowerComputed (⟨448, by decide⟩ : Fin 1069) = lowerFacets (⟨448, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0449 : lowerComputed (⟨449, by decide⟩ : Fin 1069) = lowerFacets (⟨449, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0450 : lowerComputed (⟨450, by decide⟩ : Fin 1069) = lowerFacets (⟨450, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0451 : lowerComputed (⟨451, by decide⟩ : Fin 1069) = lowerFacets (⟨451, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0452 : lowerComputed (⟨452, by decide⟩ : Fin 1069) = lowerFacets (⟨452, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0453 : lowerComputed (⟨453, by decide⟩ : Fin 1069) = lowerFacets (⟨453, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0454 : lowerComputed (⟨454, by decide⟩ : Fin 1069) = lowerFacets (⟨454, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0455 : lowerComputed (⟨455, by decide⟩ : Fin 1069) = lowerFacets (⟨455, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0456 : lowerComputed (⟨456, by decide⟩ : Fin 1069) = lowerFacets (⟨456, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0457 : lowerComputed (⟨457, by decide⟩ : Fin 1069) = lowerFacets (⟨457, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0458 : lowerComputed (⟨458, by decide⟩ : Fin 1069) = lowerFacets (⟨458, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0459 : lowerComputed (⟨459, by decide⟩ : Fin 1069) = lowerFacets (⟨459, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0460 : lowerComputed (⟨460, by decide⟩ : Fin 1069) = lowerFacets (⟨460, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0461 : lowerComputed (⟨461, by decide⟩ : Fin 1069) = lowerFacets (⟨461, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0462 : lowerComputed (⟨462, by decide⟩ : Fin 1069) = lowerFacets (⟨462, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0463 : lowerComputed (⟨463, by decide⟩ : Fin 1069) = lowerFacets (⟨463, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0464 : lowerComputed (⟨464, by decide⟩ : Fin 1069) = lowerFacets (⟨464, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0465 : lowerComputed (⟨465, by decide⟩ : Fin 1069) = lowerFacets (⟨465, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0466 : lowerComputed (⟨466, by decide⟩ : Fin 1069) = lowerFacets (⟨466, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0467 : lowerComputed (⟨467, by decide⟩ : Fin 1069) = lowerFacets (⟨467, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0468 : lowerComputed (⟨468, by decide⟩ : Fin 1069) = lowerFacets (⟨468, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0469 : lowerComputed (⟨469, by decide⟩ : Fin 1069) = lowerFacets (⟨469, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0470 : lowerComputed (⟨470, by decide⟩ : Fin 1069) = lowerFacets (⟨470, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0471 : lowerComputed (⟨471, by decide⟩ : Fin 1069) = lowerFacets (⟨471, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0472 : lowerComputed (⟨472, by decide⟩ : Fin 1069) = lowerFacets (⟨472, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0473 : lowerComputed (⟨473, by decide⟩ : Fin 1069) = lowerFacets (⟨473, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0474 : lowerComputed (⟨474, by decide⟩ : Fin 1069) = lowerFacets (⟨474, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0475 : lowerComputed (⟨475, by decide⟩ : Fin 1069) = lowerFacets (⟨475, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0476 : lowerComputed (⟨476, by decide⟩ : Fin 1069) = lowerFacets (⟨476, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0477 : lowerComputed (⟨477, by decide⟩ : Fin 1069) = lowerFacets (⟨477, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0478 : lowerComputed (⟨478, by decide⟩ : Fin 1069) = lowerFacets (⟨478, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0479 : lowerComputed (⟨479, by decide⟩ : Fin 1069) = lowerFacets (⟨479, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0480 : lowerComputed (⟨480, by decide⟩ : Fin 1069) = lowerFacets (⟨480, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0481 : lowerComputed (⟨481, by decide⟩ : Fin 1069) = lowerFacets (⟨481, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0482 : lowerComputed (⟨482, by decide⟩ : Fin 1069) = lowerFacets (⟨482, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0483 : lowerComputed (⟨483, by decide⟩ : Fin 1069) = lowerFacets (⟨483, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0484 : lowerComputed (⟨484, by decide⟩ : Fin 1069) = lowerFacets (⟨484, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0485 : lowerComputed (⟨485, by decide⟩ : Fin 1069) = lowerFacets (⟨485, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0486 : lowerComputed (⟨486, by decide⟩ : Fin 1069) = lowerFacets (⟨486, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0487 : lowerComputed (⟨487, by decide⟩ : Fin 1069) = lowerFacets (⟨487, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0488 : lowerComputed (⟨488, by decide⟩ : Fin 1069) = lowerFacets (⟨488, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0489 : lowerComputed (⟨489, by decide⟩ : Fin 1069) = lowerFacets (⟨489, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0490 : lowerComputed (⟨490, by decide⟩ : Fin 1069) = lowerFacets (⟨490, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0491 : lowerComputed (⟨491, by decide⟩ : Fin 1069) = lowerFacets (⟨491, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0492 : lowerComputed (⟨492, by decide⟩ : Fin 1069) = lowerFacets (⟨492, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0493 : lowerComputed (⟨493, by decide⟩ : Fin 1069) = lowerFacets (⟨493, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0494 : lowerComputed (⟨494, by decide⟩ : Fin 1069) = lowerFacets (⟨494, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0495 : lowerComputed (⟨495, by decide⟩ : Fin 1069) = lowerFacets (⟨495, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0496 : lowerComputed (⟨496, by decide⟩ : Fin 1069) = lowerFacets (⟨496, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0497 : lowerComputed (⟨497, by decide⟩ : Fin 1069) = lowerFacets (⟨497, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0498 : lowerComputed (⟨498, by decide⟩ : Fin 1069) = lowerFacets (⟨498, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0499 : lowerComputed (⟨499, by decide⟩ : Fin 1069) = lowerFacets (⟨499, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0500 : lowerComputed (⟨500, by decide⟩ : Fin 1069) = lowerFacets (⟨500, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0501 : lowerComputed (⟨501, by decide⟩ : Fin 1069) = lowerFacets (⟨501, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0502 : lowerComputed (⟨502, by decide⟩ : Fin 1069) = lowerFacets (⟨502, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0503 : lowerComputed (⟨503, by decide⟩ : Fin 1069) = lowerFacets (⟨503, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0504 : lowerComputed (⟨504, by decide⟩ : Fin 1069) = lowerFacets (⟨504, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0505 : lowerComputed (⟨505, by decide⟩ : Fin 1069) = lowerFacets (⟨505, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0506 : lowerComputed (⟨506, by decide⟩ : Fin 1069) = lowerFacets (⟨506, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0507 : lowerComputed (⟨507, by decide⟩ : Fin 1069) = lowerFacets (⟨507, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0508 : lowerComputed (⟨508, by decide⟩ : Fin 1069) = lowerFacets (⟨508, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0509 : lowerComputed (⟨509, by decide⟩ : Fin 1069) = lowerFacets (⟨509, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0510 : lowerComputed (⟨510, by decide⟩ : Fin 1069) = lowerFacets (⟨510, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0511 : lowerComputed (⟨511, by decide⟩ : Fin 1069) = lowerFacets (⟨511, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0512 : lowerComputed (⟨512, by decide⟩ : Fin 1069) = lowerFacets (⟨512, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0513 : lowerComputed (⟨513, by decide⟩ : Fin 1069) = lowerFacets (⟨513, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0514 : lowerComputed (⟨514, by decide⟩ : Fin 1069) = lowerFacets (⟨514, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0515 : lowerComputed (⟨515, by decide⟩ : Fin 1069) = lowerFacets (⟨515, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0516 : lowerComputed (⟨516, by decide⟩ : Fin 1069) = lowerFacets (⟨516, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0517 : lowerComputed (⟨517, by decide⟩ : Fin 1069) = lowerFacets (⟨517, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0518 : lowerComputed (⟨518, by decide⟩ : Fin 1069) = lowerFacets (⟨518, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0519 : lowerComputed (⟨519, by decide⟩ : Fin 1069) = lowerFacets (⟨519, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0520 : lowerComputed (⟨520, by decide⟩ : Fin 1069) = lowerFacets (⟨520, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0521 : lowerComputed (⟨521, by decide⟩ : Fin 1069) = lowerFacets (⟨521, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0522 : lowerComputed (⟨522, by decide⟩ : Fin 1069) = lowerFacets (⟨522, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0523 : lowerComputed (⟨523, by decide⟩ : Fin 1069) = lowerFacets (⟨523, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0524 : lowerComputed (⟨524, by decide⟩ : Fin 1069) = lowerFacets (⟨524, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0525 : lowerComputed (⟨525, by decide⟩ : Fin 1069) = lowerFacets (⟨525, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0526 : lowerComputed (⟨526, by decide⟩ : Fin 1069) = lowerFacets (⟨526, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0527 : lowerComputed (⟨527, by decide⟩ : Fin 1069) = lowerFacets (⟨527, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0528 : lowerComputed (⟨528, by decide⟩ : Fin 1069) = lowerFacets (⟨528, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0529 : lowerComputed (⟨529, by decide⟩ : Fin 1069) = lowerFacets (⟨529, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0530 : lowerComputed (⟨530, by decide⟩ : Fin 1069) = lowerFacets (⟨530, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0531 : lowerComputed (⟨531, by decide⟩ : Fin 1069) = lowerFacets (⟨531, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0532 : lowerComputed (⟨532, by decide⟩ : Fin 1069) = lowerFacets (⟨532, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0533 : lowerComputed (⟨533, by decide⟩ : Fin 1069) = lowerFacets (⟨533, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0534 : lowerComputed (⟨534, by decide⟩ : Fin 1069) = lowerFacets (⟨534, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0535 : lowerComputed (⟨535, by decide⟩ : Fin 1069) = lowerFacets (⟨535, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0536 : lowerComputed (⟨536, by decide⟩ : Fin 1069) = lowerFacets (⟨536, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0537 : lowerComputed (⟨537, by decide⟩ : Fin 1069) = lowerFacets (⟨537, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0538 : lowerComputed (⟨538, by decide⟩ : Fin 1069) = lowerFacets (⟨538, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0539 : lowerComputed (⟨539, by decide⟩ : Fin 1069) = lowerFacets (⟨539, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0540 : lowerComputed (⟨540, by decide⟩ : Fin 1069) = lowerFacets (⟨540, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0541 : lowerComputed (⟨541, by decide⟩ : Fin 1069) = lowerFacets (⟨541, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0542 : lowerComputed (⟨542, by decide⟩ : Fin 1069) = lowerFacets (⟨542, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0543 : lowerComputed (⟨543, by decide⟩ : Fin 1069) = lowerFacets (⟨543, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0544 : lowerComputed (⟨544, by decide⟩ : Fin 1069) = lowerFacets (⟨544, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0545 : lowerComputed (⟨545, by decide⟩ : Fin 1069) = lowerFacets (⟨545, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0546 : lowerComputed (⟨546, by decide⟩ : Fin 1069) = lowerFacets (⟨546, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0547 : lowerComputed (⟨547, by decide⟩ : Fin 1069) = lowerFacets (⟨547, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0548 : lowerComputed (⟨548, by decide⟩ : Fin 1069) = lowerFacets (⟨548, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0549 : lowerComputed (⟨549, by decide⟩ : Fin 1069) = lowerFacets (⟨549, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0550 : lowerComputed (⟨550, by decide⟩ : Fin 1069) = lowerFacets (⟨550, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0551 : lowerComputed (⟨551, by decide⟩ : Fin 1069) = lowerFacets (⟨551, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0552 : lowerComputed (⟨552, by decide⟩ : Fin 1069) = lowerFacets (⟨552, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0553 : lowerComputed (⟨553, by decide⟩ : Fin 1069) = lowerFacets (⟨553, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0554 : lowerComputed (⟨554, by decide⟩ : Fin 1069) = lowerFacets (⟨554, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0555 : lowerComputed (⟨555, by decide⟩ : Fin 1069) = lowerFacets (⟨555, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0556 : lowerComputed (⟨556, by decide⟩ : Fin 1069) = lowerFacets (⟨556, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0557 : lowerComputed (⟨557, by decide⟩ : Fin 1069) = lowerFacets (⟨557, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0558 : lowerComputed (⟨558, by decide⟩ : Fin 1069) = lowerFacets (⟨558, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0559 : lowerComputed (⟨559, by decide⟩ : Fin 1069) = lowerFacets (⟨559, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0560 : lowerComputed (⟨560, by decide⟩ : Fin 1069) = lowerFacets (⟨560, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0561 : lowerComputed (⟨561, by decide⟩ : Fin 1069) = lowerFacets (⟨561, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0562 : lowerComputed (⟨562, by decide⟩ : Fin 1069) = lowerFacets (⟨562, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0563 : lowerComputed (⟨563, by decide⟩ : Fin 1069) = lowerFacets (⟨563, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0564 : lowerComputed (⟨564, by decide⟩ : Fin 1069) = lowerFacets (⟨564, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0565 : lowerComputed (⟨565, by decide⟩ : Fin 1069) = lowerFacets (⟨565, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0566 : lowerComputed (⟨566, by decide⟩ : Fin 1069) = lowerFacets (⟨566, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0567 : lowerComputed (⟨567, by decide⟩ : Fin 1069) = lowerFacets (⟨567, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0568 : lowerComputed (⟨568, by decide⟩ : Fin 1069) = lowerFacets (⟨568, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0569 : lowerComputed (⟨569, by decide⟩ : Fin 1069) = lowerFacets (⟨569, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0570 : lowerComputed (⟨570, by decide⟩ : Fin 1069) = lowerFacets (⟨570, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0571 : lowerComputed (⟨571, by decide⟩ : Fin 1069) = lowerFacets (⟨571, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0572 : lowerComputed (⟨572, by decide⟩ : Fin 1069) = lowerFacets (⟨572, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0573 : lowerComputed (⟨573, by decide⟩ : Fin 1069) = lowerFacets (⟨573, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0574 : lowerComputed (⟨574, by decide⟩ : Fin 1069) = lowerFacets (⟨574, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0575 : lowerComputed (⟨575, by decide⟩ : Fin 1069) = lowerFacets (⟨575, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0576 : lowerComputed (⟨576, by decide⟩ : Fin 1069) = lowerFacets (⟨576, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0577 : lowerComputed (⟨577, by decide⟩ : Fin 1069) = lowerFacets (⟨577, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0578 : lowerComputed (⟨578, by decide⟩ : Fin 1069) = lowerFacets (⟨578, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0579 : lowerComputed (⟨579, by decide⟩ : Fin 1069) = lowerFacets (⟨579, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0580 : lowerComputed (⟨580, by decide⟩ : Fin 1069) = lowerFacets (⟨580, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0581 : lowerComputed (⟨581, by decide⟩ : Fin 1069) = lowerFacets (⟨581, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0582 : lowerComputed (⟨582, by decide⟩ : Fin 1069) = lowerFacets (⟨582, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0583 : lowerComputed (⟨583, by decide⟩ : Fin 1069) = lowerFacets (⟨583, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0584 : lowerComputed (⟨584, by decide⟩ : Fin 1069) = lowerFacets (⟨584, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0585 : lowerComputed (⟨585, by decide⟩ : Fin 1069) = lowerFacets (⟨585, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0586 : lowerComputed (⟨586, by decide⟩ : Fin 1069) = lowerFacets (⟨586, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0587 : lowerComputed (⟨587, by decide⟩ : Fin 1069) = lowerFacets (⟨587, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0588 : lowerComputed (⟨588, by decide⟩ : Fin 1069) = lowerFacets (⟨588, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0589 : lowerComputed (⟨589, by decide⟩ : Fin 1069) = lowerFacets (⟨589, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0590 : lowerComputed (⟨590, by decide⟩ : Fin 1069) = lowerFacets (⟨590, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0591 : lowerComputed (⟨591, by decide⟩ : Fin 1069) = lowerFacets (⟨591, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0592 : lowerComputed (⟨592, by decide⟩ : Fin 1069) = lowerFacets (⟨592, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0593 : lowerComputed (⟨593, by decide⟩ : Fin 1069) = lowerFacets (⟨593, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0594 : lowerComputed (⟨594, by decide⟩ : Fin 1069) = lowerFacets (⟨594, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0595 : lowerComputed (⟨595, by decide⟩ : Fin 1069) = lowerFacets (⟨595, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0596 : lowerComputed (⟨596, by decide⟩ : Fin 1069) = lowerFacets (⟨596, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0597 : lowerComputed (⟨597, by decide⟩ : Fin 1069) = lowerFacets (⟨597, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0598 : lowerComputed (⟨598, by decide⟩ : Fin 1069) = lowerFacets (⟨598, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0599 : lowerComputed (⟨599, by decide⟩ : Fin 1069) = lowerFacets (⟨599, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0600 : lowerComputed (⟨600, by decide⟩ : Fin 1069) = lowerFacets (⟨600, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0601 : lowerComputed (⟨601, by decide⟩ : Fin 1069) = lowerFacets (⟨601, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0602 : lowerComputed (⟨602, by decide⟩ : Fin 1069) = lowerFacets (⟨602, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0603 : lowerComputed (⟨603, by decide⟩ : Fin 1069) = lowerFacets (⟨603, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0604 : lowerComputed (⟨604, by decide⟩ : Fin 1069) = lowerFacets (⟨604, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0605 : lowerComputed (⟨605, by decide⟩ : Fin 1069) = lowerFacets (⟨605, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0606 : lowerComputed (⟨606, by decide⟩ : Fin 1069) = lowerFacets (⟨606, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0607 : lowerComputed (⟨607, by decide⟩ : Fin 1069) = lowerFacets (⟨607, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0608 : lowerComputed (⟨608, by decide⟩ : Fin 1069) = lowerFacets (⟨608, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0609 : lowerComputed (⟨609, by decide⟩ : Fin 1069) = lowerFacets (⟨609, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0610 : lowerComputed (⟨610, by decide⟩ : Fin 1069) = lowerFacets (⟨610, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0611 : lowerComputed (⟨611, by decide⟩ : Fin 1069) = lowerFacets (⟨611, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0612 : lowerComputed (⟨612, by decide⟩ : Fin 1069) = lowerFacets (⟨612, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0613 : lowerComputed (⟨613, by decide⟩ : Fin 1069) = lowerFacets (⟨613, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0614 : lowerComputed (⟨614, by decide⟩ : Fin 1069) = lowerFacets (⟨614, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0615 : lowerComputed (⟨615, by decide⟩ : Fin 1069) = lowerFacets (⟨615, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0616 : lowerComputed (⟨616, by decide⟩ : Fin 1069) = lowerFacets (⟨616, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0617 : lowerComputed (⟨617, by decide⟩ : Fin 1069) = lowerFacets (⟨617, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0618 : lowerComputed (⟨618, by decide⟩ : Fin 1069) = lowerFacets (⟨618, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0619 : lowerComputed (⟨619, by decide⟩ : Fin 1069) = lowerFacets (⟨619, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0620 : lowerComputed (⟨620, by decide⟩ : Fin 1069) = lowerFacets (⟨620, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0621 : lowerComputed (⟨621, by decide⟩ : Fin 1069) = lowerFacets (⟨621, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0622 : lowerComputed (⟨622, by decide⟩ : Fin 1069) = lowerFacets (⟨622, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0623 : lowerComputed (⟨623, by decide⟩ : Fin 1069) = lowerFacets (⟨623, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0624 : lowerComputed (⟨624, by decide⟩ : Fin 1069) = lowerFacets (⟨624, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0625 : lowerComputed (⟨625, by decide⟩ : Fin 1069) = lowerFacets (⟨625, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0626 : lowerComputed (⟨626, by decide⟩ : Fin 1069) = lowerFacets (⟨626, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0627 : lowerComputed (⟨627, by decide⟩ : Fin 1069) = lowerFacets (⟨627, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0628 : lowerComputed (⟨628, by decide⟩ : Fin 1069) = lowerFacets (⟨628, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0629 : lowerComputed (⟨629, by decide⟩ : Fin 1069) = lowerFacets (⟨629, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0630 : lowerComputed (⟨630, by decide⟩ : Fin 1069) = lowerFacets (⟨630, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0631 : lowerComputed (⟨631, by decide⟩ : Fin 1069) = lowerFacets (⟨631, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0632 : lowerComputed (⟨632, by decide⟩ : Fin 1069) = lowerFacets (⟨632, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0633 : lowerComputed (⟨633, by decide⟩ : Fin 1069) = lowerFacets (⟨633, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0634 : lowerComputed (⟨634, by decide⟩ : Fin 1069) = lowerFacets (⟨634, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0635 : lowerComputed (⟨635, by decide⟩ : Fin 1069) = lowerFacets (⟨635, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0636 : lowerComputed (⟨636, by decide⟩ : Fin 1069) = lowerFacets (⟨636, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0637 : lowerComputed (⟨637, by decide⟩ : Fin 1069) = lowerFacets (⟨637, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0638 : lowerComputed (⟨638, by decide⟩ : Fin 1069) = lowerFacets (⟨638, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0639 : lowerComputed (⟨639, by decide⟩ : Fin 1069) = lowerFacets (⟨639, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0640 : lowerComputed (⟨640, by decide⟩ : Fin 1069) = lowerFacets (⟨640, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0641 : lowerComputed (⟨641, by decide⟩ : Fin 1069) = lowerFacets (⟨641, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0642 : lowerComputed (⟨642, by decide⟩ : Fin 1069) = lowerFacets (⟨642, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0643 : lowerComputed (⟨643, by decide⟩ : Fin 1069) = lowerFacets (⟨643, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0644 : lowerComputed (⟨644, by decide⟩ : Fin 1069) = lowerFacets (⟨644, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0645 : lowerComputed (⟨645, by decide⟩ : Fin 1069) = lowerFacets (⟨645, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0646 : lowerComputed (⟨646, by decide⟩ : Fin 1069) = lowerFacets (⟨646, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0647 : lowerComputed (⟨647, by decide⟩ : Fin 1069) = lowerFacets (⟨647, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0648 : lowerComputed (⟨648, by decide⟩ : Fin 1069) = lowerFacets (⟨648, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0649 : lowerComputed (⟨649, by decide⟩ : Fin 1069) = lowerFacets (⟨649, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0650 : lowerComputed (⟨650, by decide⟩ : Fin 1069) = lowerFacets (⟨650, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0651 : lowerComputed (⟨651, by decide⟩ : Fin 1069) = lowerFacets (⟨651, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0652 : lowerComputed (⟨652, by decide⟩ : Fin 1069) = lowerFacets (⟨652, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0653 : lowerComputed (⟨653, by decide⟩ : Fin 1069) = lowerFacets (⟨653, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0654 : lowerComputed (⟨654, by decide⟩ : Fin 1069) = lowerFacets (⟨654, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0655 : lowerComputed (⟨655, by decide⟩ : Fin 1069) = lowerFacets (⟨655, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0656 : lowerComputed (⟨656, by decide⟩ : Fin 1069) = lowerFacets (⟨656, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0657 : lowerComputed (⟨657, by decide⟩ : Fin 1069) = lowerFacets (⟨657, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0658 : lowerComputed (⟨658, by decide⟩ : Fin 1069) = lowerFacets (⟨658, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0659 : lowerComputed (⟨659, by decide⟩ : Fin 1069) = lowerFacets (⟨659, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0660 : lowerComputed (⟨660, by decide⟩ : Fin 1069) = lowerFacets (⟨660, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0661 : lowerComputed (⟨661, by decide⟩ : Fin 1069) = lowerFacets (⟨661, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0662 : lowerComputed (⟨662, by decide⟩ : Fin 1069) = lowerFacets (⟨662, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0663 : lowerComputed (⟨663, by decide⟩ : Fin 1069) = lowerFacets (⟨663, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0664 : lowerComputed (⟨664, by decide⟩ : Fin 1069) = lowerFacets (⟨664, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0665 : lowerComputed (⟨665, by decide⟩ : Fin 1069) = lowerFacets (⟨665, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0666 : lowerComputed (⟨666, by decide⟩ : Fin 1069) = lowerFacets (⟨666, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0667 : lowerComputed (⟨667, by decide⟩ : Fin 1069) = lowerFacets (⟨667, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0668 : lowerComputed (⟨668, by decide⟩ : Fin 1069) = lowerFacets (⟨668, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0669 : lowerComputed (⟨669, by decide⟩ : Fin 1069) = lowerFacets (⟨669, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0670 : lowerComputed (⟨670, by decide⟩ : Fin 1069) = lowerFacets (⟨670, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0671 : lowerComputed (⟨671, by decide⟩ : Fin 1069) = lowerFacets (⟨671, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0672 : lowerComputed (⟨672, by decide⟩ : Fin 1069) = lowerFacets (⟨672, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0673 : lowerComputed (⟨673, by decide⟩ : Fin 1069) = lowerFacets (⟨673, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0674 : lowerComputed (⟨674, by decide⟩ : Fin 1069) = lowerFacets (⟨674, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0675 : lowerComputed (⟨675, by decide⟩ : Fin 1069) = lowerFacets (⟨675, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0676 : lowerComputed (⟨676, by decide⟩ : Fin 1069) = lowerFacets (⟨676, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0677 : lowerComputed (⟨677, by decide⟩ : Fin 1069) = lowerFacets (⟨677, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0678 : lowerComputed (⟨678, by decide⟩ : Fin 1069) = lowerFacets (⟨678, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0679 : lowerComputed (⟨679, by decide⟩ : Fin 1069) = lowerFacets (⟨679, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0680 : lowerComputed (⟨680, by decide⟩ : Fin 1069) = lowerFacets (⟨680, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0681 : lowerComputed (⟨681, by decide⟩ : Fin 1069) = lowerFacets (⟨681, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0682 : lowerComputed (⟨682, by decide⟩ : Fin 1069) = lowerFacets (⟨682, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0683 : lowerComputed (⟨683, by decide⟩ : Fin 1069) = lowerFacets (⟨683, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0684 : lowerComputed (⟨684, by decide⟩ : Fin 1069) = lowerFacets (⟨684, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0685 : lowerComputed (⟨685, by decide⟩ : Fin 1069) = lowerFacets (⟨685, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0686 : lowerComputed (⟨686, by decide⟩ : Fin 1069) = lowerFacets (⟨686, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0687 : lowerComputed (⟨687, by decide⟩ : Fin 1069) = lowerFacets (⟨687, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0688 : lowerComputed (⟨688, by decide⟩ : Fin 1069) = lowerFacets (⟨688, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0689 : lowerComputed (⟨689, by decide⟩ : Fin 1069) = lowerFacets (⟨689, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0690 : lowerComputed (⟨690, by decide⟩ : Fin 1069) = lowerFacets (⟨690, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0691 : lowerComputed (⟨691, by decide⟩ : Fin 1069) = lowerFacets (⟨691, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0692 : lowerComputed (⟨692, by decide⟩ : Fin 1069) = lowerFacets (⟨692, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0693 : lowerComputed (⟨693, by decide⟩ : Fin 1069) = lowerFacets (⟨693, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0694 : lowerComputed (⟨694, by decide⟩ : Fin 1069) = lowerFacets (⟨694, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0695 : lowerComputed (⟨695, by decide⟩ : Fin 1069) = lowerFacets (⟨695, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0696 : lowerComputed (⟨696, by decide⟩ : Fin 1069) = lowerFacets (⟨696, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0697 : lowerComputed (⟨697, by decide⟩ : Fin 1069) = lowerFacets (⟨697, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0698 : lowerComputed (⟨698, by decide⟩ : Fin 1069) = lowerFacets (⟨698, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0699 : lowerComputed (⟨699, by decide⟩ : Fin 1069) = lowerFacets (⟨699, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0700 : lowerComputed (⟨700, by decide⟩ : Fin 1069) = lowerFacets (⟨700, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0701 : lowerComputed (⟨701, by decide⟩ : Fin 1069) = lowerFacets (⟨701, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0702 : lowerComputed (⟨702, by decide⟩ : Fin 1069) = lowerFacets (⟨702, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0703 : lowerComputed (⟨703, by decide⟩ : Fin 1069) = lowerFacets (⟨703, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0704 : lowerComputed (⟨704, by decide⟩ : Fin 1069) = lowerFacets (⟨704, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0705 : lowerComputed (⟨705, by decide⟩ : Fin 1069) = lowerFacets (⟨705, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0706 : lowerComputed (⟨706, by decide⟩ : Fin 1069) = lowerFacets (⟨706, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0707 : lowerComputed (⟨707, by decide⟩ : Fin 1069) = lowerFacets (⟨707, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0708 : lowerComputed (⟨708, by decide⟩ : Fin 1069) = lowerFacets (⟨708, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0709 : lowerComputed (⟨709, by decide⟩ : Fin 1069) = lowerFacets (⟨709, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0710 : lowerComputed (⟨710, by decide⟩ : Fin 1069) = lowerFacets (⟨710, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0711 : lowerComputed (⟨711, by decide⟩ : Fin 1069) = lowerFacets (⟨711, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0712 : lowerComputed (⟨712, by decide⟩ : Fin 1069) = lowerFacets (⟨712, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0713 : lowerComputed (⟨713, by decide⟩ : Fin 1069) = lowerFacets (⟨713, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0714 : lowerComputed (⟨714, by decide⟩ : Fin 1069) = lowerFacets (⟨714, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0715 : lowerComputed (⟨715, by decide⟩ : Fin 1069) = lowerFacets (⟨715, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0716 : lowerComputed (⟨716, by decide⟩ : Fin 1069) = lowerFacets (⟨716, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0717 : lowerComputed (⟨717, by decide⟩ : Fin 1069) = lowerFacets (⟨717, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0718 : lowerComputed (⟨718, by decide⟩ : Fin 1069) = lowerFacets (⟨718, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0719 : lowerComputed (⟨719, by decide⟩ : Fin 1069) = lowerFacets (⟨719, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0720 : lowerComputed (⟨720, by decide⟩ : Fin 1069) = lowerFacets (⟨720, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0721 : lowerComputed (⟨721, by decide⟩ : Fin 1069) = lowerFacets (⟨721, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0722 : lowerComputed (⟨722, by decide⟩ : Fin 1069) = lowerFacets (⟨722, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0723 : lowerComputed (⟨723, by decide⟩ : Fin 1069) = lowerFacets (⟨723, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0724 : lowerComputed (⟨724, by decide⟩ : Fin 1069) = lowerFacets (⟨724, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0725 : lowerComputed (⟨725, by decide⟩ : Fin 1069) = lowerFacets (⟨725, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0726 : lowerComputed (⟨726, by decide⟩ : Fin 1069) = lowerFacets (⟨726, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0727 : lowerComputed (⟨727, by decide⟩ : Fin 1069) = lowerFacets (⟨727, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0728 : lowerComputed (⟨728, by decide⟩ : Fin 1069) = lowerFacets (⟨728, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0729 : lowerComputed (⟨729, by decide⟩ : Fin 1069) = lowerFacets (⟨729, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0730 : lowerComputed (⟨730, by decide⟩ : Fin 1069) = lowerFacets (⟨730, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0731 : lowerComputed (⟨731, by decide⟩ : Fin 1069) = lowerFacets (⟨731, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0732 : lowerComputed (⟨732, by decide⟩ : Fin 1069) = lowerFacets (⟨732, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0733 : lowerComputed (⟨733, by decide⟩ : Fin 1069) = lowerFacets (⟨733, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0734 : lowerComputed (⟨734, by decide⟩ : Fin 1069) = lowerFacets (⟨734, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0735 : lowerComputed (⟨735, by decide⟩ : Fin 1069) = lowerFacets (⟨735, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0736 : lowerComputed (⟨736, by decide⟩ : Fin 1069) = lowerFacets (⟨736, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0737 : lowerComputed (⟨737, by decide⟩ : Fin 1069) = lowerFacets (⟨737, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0738 : lowerComputed (⟨738, by decide⟩ : Fin 1069) = lowerFacets (⟨738, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0739 : lowerComputed (⟨739, by decide⟩ : Fin 1069) = lowerFacets (⟨739, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0740 : lowerComputed (⟨740, by decide⟩ : Fin 1069) = lowerFacets (⟨740, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0741 : lowerComputed (⟨741, by decide⟩ : Fin 1069) = lowerFacets (⟨741, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0742 : lowerComputed (⟨742, by decide⟩ : Fin 1069) = lowerFacets (⟨742, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0743 : lowerComputed (⟨743, by decide⟩ : Fin 1069) = lowerFacets (⟨743, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0744 : lowerComputed (⟨744, by decide⟩ : Fin 1069) = lowerFacets (⟨744, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0745 : lowerComputed (⟨745, by decide⟩ : Fin 1069) = lowerFacets (⟨745, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0746 : lowerComputed (⟨746, by decide⟩ : Fin 1069) = lowerFacets (⟨746, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0747 : lowerComputed (⟨747, by decide⟩ : Fin 1069) = lowerFacets (⟨747, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0748 : lowerComputed (⟨748, by decide⟩ : Fin 1069) = lowerFacets (⟨748, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0749 : lowerComputed (⟨749, by decide⟩ : Fin 1069) = lowerFacets (⟨749, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0750 : lowerComputed (⟨750, by decide⟩ : Fin 1069) = lowerFacets (⟨750, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0751 : lowerComputed (⟨751, by decide⟩ : Fin 1069) = lowerFacets (⟨751, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0752 : lowerComputed (⟨752, by decide⟩ : Fin 1069) = lowerFacets (⟨752, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0753 : lowerComputed (⟨753, by decide⟩ : Fin 1069) = lowerFacets (⟨753, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0754 : lowerComputed (⟨754, by decide⟩ : Fin 1069) = lowerFacets (⟨754, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0755 : lowerComputed (⟨755, by decide⟩ : Fin 1069) = lowerFacets (⟨755, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0756 : lowerComputed (⟨756, by decide⟩ : Fin 1069) = lowerFacets (⟨756, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0757 : lowerComputed (⟨757, by decide⟩ : Fin 1069) = lowerFacets (⟨757, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0758 : lowerComputed (⟨758, by decide⟩ : Fin 1069) = lowerFacets (⟨758, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0759 : lowerComputed (⟨759, by decide⟩ : Fin 1069) = lowerFacets (⟨759, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0760 : lowerComputed (⟨760, by decide⟩ : Fin 1069) = lowerFacets (⟨760, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0761 : lowerComputed (⟨761, by decide⟩ : Fin 1069) = lowerFacets (⟨761, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0762 : lowerComputed (⟨762, by decide⟩ : Fin 1069) = lowerFacets (⟨762, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0763 : lowerComputed (⟨763, by decide⟩ : Fin 1069) = lowerFacets (⟨763, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0764 : lowerComputed (⟨764, by decide⟩ : Fin 1069) = lowerFacets (⟨764, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0765 : lowerComputed (⟨765, by decide⟩ : Fin 1069) = lowerFacets (⟨765, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0766 : lowerComputed (⟨766, by decide⟩ : Fin 1069) = lowerFacets (⟨766, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0767 : lowerComputed (⟨767, by decide⟩ : Fin 1069) = lowerFacets (⟨767, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0768 : lowerComputed (⟨768, by decide⟩ : Fin 1069) = lowerFacets (⟨768, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0769 : lowerComputed (⟨769, by decide⟩ : Fin 1069) = lowerFacets (⟨769, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0770 : lowerComputed (⟨770, by decide⟩ : Fin 1069) = lowerFacets (⟨770, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0771 : lowerComputed (⟨771, by decide⟩ : Fin 1069) = lowerFacets (⟨771, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0772 : lowerComputed (⟨772, by decide⟩ : Fin 1069) = lowerFacets (⟨772, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0773 : lowerComputed (⟨773, by decide⟩ : Fin 1069) = lowerFacets (⟨773, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0774 : lowerComputed (⟨774, by decide⟩ : Fin 1069) = lowerFacets (⟨774, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0775 : lowerComputed (⟨775, by decide⟩ : Fin 1069) = lowerFacets (⟨775, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0776 : lowerComputed (⟨776, by decide⟩ : Fin 1069) = lowerFacets (⟨776, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0777 : lowerComputed (⟨777, by decide⟩ : Fin 1069) = lowerFacets (⟨777, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0778 : lowerComputed (⟨778, by decide⟩ : Fin 1069) = lowerFacets (⟨778, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0779 : lowerComputed (⟨779, by decide⟩ : Fin 1069) = lowerFacets (⟨779, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0780 : lowerComputed (⟨780, by decide⟩ : Fin 1069) = lowerFacets (⟨780, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0781 : lowerComputed (⟨781, by decide⟩ : Fin 1069) = lowerFacets (⟨781, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0782 : lowerComputed (⟨782, by decide⟩ : Fin 1069) = lowerFacets (⟨782, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0783 : lowerComputed (⟨783, by decide⟩ : Fin 1069) = lowerFacets (⟨783, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0784 : lowerComputed (⟨784, by decide⟩ : Fin 1069) = lowerFacets (⟨784, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0785 : lowerComputed (⟨785, by decide⟩ : Fin 1069) = lowerFacets (⟨785, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0786 : lowerComputed (⟨786, by decide⟩ : Fin 1069) = lowerFacets (⟨786, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0787 : lowerComputed (⟨787, by decide⟩ : Fin 1069) = lowerFacets (⟨787, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0788 : lowerComputed (⟨788, by decide⟩ : Fin 1069) = lowerFacets (⟨788, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0789 : lowerComputed (⟨789, by decide⟩ : Fin 1069) = lowerFacets (⟨789, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0790 : lowerComputed (⟨790, by decide⟩ : Fin 1069) = lowerFacets (⟨790, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0791 : lowerComputed (⟨791, by decide⟩ : Fin 1069) = lowerFacets (⟨791, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0792 : lowerComputed (⟨792, by decide⟩ : Fin 1069) = lowerFacets (⟨792, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0793 : lowerComputed (⟨793, by decide⟩ : Fin 1069) = lowerFacets (⟨793, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0794 : lowerComputed (⟨794, by decide⟩ : Fin 1069) = lowerFacets (⟨794, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0795 : lowerComputed (⟨795, by decide⟩ : Fin 1069) = lowerFacets (⟨795, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0796 : lowerComputed (⟨796, by decide⟩ : Fin 1069) = lowerFacets (⟨796, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0797 : lowerComputed (⟨797, by decide⟩ : Fin 1069) = lowerFacets (⟨797, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0798 : lowerComputed (⟨798, by decide⟩ : Fin 1069) = lowerFacets (⟨798, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0799 : lowerComputed (⟨799, by decide⟩ : Fin 1069) = lowerFacets (⟨799, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0800 : lowerComputed (⟨800, by decide⟩ : Fin 1069) = lowerFacets (⟨800, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0801 : lowerComputed (⟨801, by decide⟩ : Fin 1069) = lowerFacets (⟨801, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0802 : lowerComputed (⟨802, by decide⟩ : Fin 1069) = lowerFacets (⟨802, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0803 : lowerComputed (⟨803, by decide⟩ : Fin 1069) = lowerFacets (⟨803, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0804 : lowerComputed (⟨804, by decide⟩ : Fin 1069) = lowerFacets (⟨804, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0805 : lowerComputed (⟨805, by decide⟩ : Fin 1069) = lowerFacets (⟨805, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0806 : lowerComputed (⟨806, by decide⟩ : Fin 1069) = lowerFacets (⟨806, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0807 : lowerComputed (⟨807, by decide⟩ : Fin 1069) = lowerFacets (⟨807, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0808 : lowerComputed (⟨808, by decide⟩ : Fin 1069) = lowerFacets (⟨808, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0809 : lowerComputed (⟨809, by decide⟩ : Fin 1069) = lowerFacets (⟨809, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0810 : lowerComputed (⟨810, by decide⟩ : Fin 1069) = lowerFacets (⟨810, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0811 : lowerComputed (⟨811, by decide⟩ : Fin 1069) = lowerFacets (⟨811, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0812 : lowerComputed (⟨812, by decide⟩ : Fin 1069) = lowerFacets (⟨812, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0813 : lowerComputed (⟨813, by decide⟩ : Fin 1069) = lowerFacets (⟨813, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0814 : lowerComputed (⟨814, by decide⟩ : Fin 1069) = lowerFacets (⟨814, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0815 : lowerComputed (⟨815, by decide⟩ : Fin 1069) = lowerFacets (⟨815, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0816 : lowerComputed (⟨816, by decide⟩ : Fin 1069) = lowerFacets (⟨816, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0817 : lowerComputed (⟨817, by decide⟩ : Fin 1069) = lowerFacets (⟨817, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0818 : lowerComputed (⟨818, by decide⟩ : Fin 1069) = lowerFacets (⟨818, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0819 : lowerComputed (⟨819, by decide⟩ : Fin 1069) = lowerFacets (⟨819, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0820 : lowerComputed (⟨820, by decide⟩ : Fin 1069) = lowerFacets (⟨820, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0821 : lowerComputed (⟨821, by decide⟩ : Fin 1069) = lowerFacets (⟨821, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0822 : lowerComputed (⟨822, by decide⟩ : Fin 1069) = lowerFacets (⟨822, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0823 : lowerComputed (⟨823, by decide⟩ : Fin 1069) = lowerFacets (⟨823, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0824 : lowerComputed (⟨824, by decide⟩ : Fin 1069) = lowerFacets (⟨824, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0825 : lowerComputed (⟨825, by decide⟩ : Fin 1069) = lowerFacets (⟨825, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0826 : lowerComputed (⟨826, by decide⟩ : Fin 1069) = lowerFacets (⟨826, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0827 : lowerComputed (⟨827, by decide⟩ : Fin 1069) = lowerFacets (⟨827, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0828 : lowerComputed (⟨828, by decide⟩ : Fin 1069) = lowerFacets (⟨828, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0829 : lowerComputed (⟨829, by decide⟩ : Fin 1069) = lowerFacets (⟨829, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0830 : lowerComputed (⟨830, by decide⟩ : Fin 1069) = lowerFacets (⟨830, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0831 : lowerComputed (⟨831, by decide⟩ : Fin 1069) = lowerFacets (⟨831, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0832 : lowerComputed (⟨832, by decide⟩ : Fin 1069) = lowerFacets (⟨832, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0833 : lowerComputed (⟨833, by decide⟩ : Fin 1069) = lowerFacets (⟨833, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0834 : lowerComputed (⟨834, by decide⟩ : Fin 1069) = lowerFacets (⟨834, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0835 : lowerComputed (⟨835, by decide⟩ : Fin 1069) = lowerFacets (⟨835, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0836 : lowerComputed (⟨836, by decide⟩ : Fin 1069) = lowerFacets (⟨836, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0837 : lowerComputed (⟨837, by decide⟩ : Fin 1069) = lowerFacets (⟨837, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0838 : lowerComputed (⟨838, by decide⟩ : Fin 1069) = lowerFacets (⟨838, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0839 : lowerComputed (⟨839, by decide⟩ : Fin 1069) = lowerFacets (⟨839, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0840 : lowerComputed (⟨840, by decide⟩ : Fin 1069) = lowerFacets (⟨840, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0841 : lowerComputed (⟨841, by decide⟩ : Fin 1069) = lowerFacets (⟨841, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0842 : lowerComputed (⟨842, by decide⟩ : Fin 1069) = lowerFacets (⟨842, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0843 : lowerComputed (⟨843, by decide⟩ : Fin 1069) = lowerFacets (⟨843, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0844 : lowerComputed (⟨844, by decide⟩ : Fin 1069) = lowerFacets (⟨844, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0845 : lowerComputed (⟨845, by decide⟩ : Fin 1069) = lowerFacets (⟨845, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0846 : lowerComputed (⟨846, by decide⟩ : Fin 1069) = lowerFacets (⟨846, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0847 : lowerComputed (⟨847, by decide⟩ : Fin 1069) = lowerFacets (⟨847, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0848 : lowerComputed (⟨848, by decide⟩ : Fin 1069) = lowerFacets (⟨848, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0849 : lowerComputed (⟨849, by decide⟩ : Fin 1069) = lowerFacets (⟨849, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0850 : lowerComputed (⟨850, by decide⟩ : Fin 1069) = lowerFacets (⟨850, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0851 : lowerComputed (⟨851, by decide⟩ : Fin 1069) = lowerFacets (⟨851, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0852 : lowerComputed (⟨852, by decide⟩ : Fin 1069) = lowerFacets (⟨852, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0853 : lowerComputed (⟨853, by decide⟩ : Fin 1069) = lowerFacets (⟨853, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0854 : lowerComputed (⟨854, by decide⟩ : Fin 1069) = lowerFacets (⟨854, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0855 : lowerComputed (⟨855, by decide⟩ : Fin 1069) = lowerFacets (⟨855, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0856 : lowerComputed (⟨856, by decide⟩ : Fin 1069) = lowerFacets (⟨856, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0857 : lowerComputed (⟨857, by decide⟩ : Fin 1069) = lowerFacets (⟨857, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0858 : lowerComputed (⟨858, by decide⟩ : Fin 1069) = lowerFacets (⟨858, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0859 : lowerComputed (⟨859, by decide⟩ : Fin 1069) = lowerFacets (⟨859, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0860 : lowerComputed (⟨860, by decide⟩ : Fin 1069) = lowerFacets (⟨860, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0861 : lowerComputed (⟨861, by decide⟩ : Fin 1069) = lowerFacets (⟨861, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0862 : lowerComputed (⟨862, by decide⟩ : Fin 1069) = lowerFacets (⟨862, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0863 : lowerComputed (⟨863, by decide⟩ : Fin 1069) = lowerFacets (⟨863, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0864 : lowerComputed (⟨864, by decide⟩ : Fin 1069) = lowerFacets (⟨864, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0865 : lowerComputed (⟨865, by decide⟩ : Fin 1069) = lowerFacets (⟨865, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0866 : lowerComputed (⟨866, by decide⟩ : Fin 1069) = lowerFacets (⟨866, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0867 : lowerComputed (⟨867, by decide⟩ : Fin 1069) = lowerFacets (⟨867, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0868 : lowerComputed (⟨868, by decide⟩ : Fin 1069) = lowerFacets (⟨868, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0869 : lowerComputed (⟨869, by decide⟩ : Fin 1069) = lowerFacets (⟨869, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0870 : lowerComputed (⟨870, by decide⟩ : Fin 1069) = lowerFacets (⟨870, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0871 : lowerComputed (⟨871, by decide⟩ : Fin 1069) = lowerFacets (⟨871, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0872 : lowerComputed (⟨872, by decide⟩ : Fin 1069) = lowerFacets (⟨872, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0873 : lowerComputed (⟨873, by decide⟩ : Fin 1069) = lowerFacets (⟨873, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0874 : lowerComputed (⟨874, by decide⟩ : Fin 1069) = lowerFacets (⟨874, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0875 : lowerComputed (⟨875, by decide⟩ : Fin 1069) = lowerFacets (⟨875, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0876 : lowerComputed (⟨876, by decide⟩ : Fin 1069) = lowerFacets (⟨876, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0877 : lowerComputed (⟨877, by decide⟩ : Fin 1069) = lowerFacets (⟨877, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0878 : lowerComputed (⟨878, by decide⟩ : Fin 1069) = lowerFacets (⟨878, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0879 : lowerComputed (⟨879, by decide⟩ : Fin 1069) = lowerFacets (⟨879, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0880 : lowerComputed (⟨880, by decide⟩ : Fin 1069) = lowerFacets (⟨880, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0881 : lowerComputed (⟨881, by decide⟩ : Fin 1069) = lowerFacets (⟨881, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0882 : lowerComputed (⟨882, by decide⟩ : Fin 1069) = lowerFacets (⟨882, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0883 : lowerComputed (⟨883, by decide⟩ : Fin 1069) = lowerFacets (⟨883, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0884 : lowerComputed (⟨884, by decide⟩ : Fin 1069) = lowerFacets (⟨884, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0885 : lowerComputed (⟨885, by decide⟩ : Fin 1069) = lowerFacets (⟨885, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0886 : lowerComputed (⟨886, by decide⟩ : Fin 1069) = lowerFacets (⟨886, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0887 : lowerComputed (⟨887, by decide⟩ : Fin 1069) = lowerFacets (⟨887, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0888 : lowerComputed (⟨888, by decide⟩ : Fin 1069) = lowerFacets (⟨888, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0889 : lowerComputed (⟨889, by decide⟩ : Fin 1069) = lowerFacets (⟨889, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0890 : lowerComputed (⟨890, by decide⟩ : Fin 1069) = lowerFacets (⟨890, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0891 : lowerComputed (⟨891, by decide⟩ : Fin 1069) = lowerFacets (⟨891, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0892 : lowerComputed (⟨892, by decide⟩ : Fin 1069) = lowerFacets (⟨892, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0893 : lowerComputed (⟨893, by decide⟩ : Fin 1069) = lowerFacets (⟨893, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0894 : lowerComputed (⟨894, by decide⟩ : Fin 1069) = lowerFacets (⟨894, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0895 : lowerComputed (⟨895, by decide⟩ : Fin 1069) = lowerFacets (⟨895, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0896 : lowerComputed (⟨896, by decide⟩ : Fin 1069) = lowerFacets (⟨896, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0897 : lowerComputed (⟨897, by decide⟩ : Fin 1069) = lowerFacets (⟨897, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0898 : lowerComputed (⟨898, by decide⟩ : Fin 1069) = lowerFacets (⟨898, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0899 : lowerComputed (⟨899, by decide⟩ : Fin 1069) = lowerFacets (⟨899, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0900 : lowerComputed (⟨900, by decide⟩ : Fin 1069) = lowerFacets (⟨900, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0901 : lowerComputed (⟨901, by decide⟩ : Fin 1069) = lowerFacets (⟨901, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0902 : lowerComputed (⟨902, by decide⟩ : Fin 1069) = lowerFacets (⟨902, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0903 : lowerComputed (⟨903, by decide⟩ : Fin 1069) = lowerFacets (⟨903, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0904 : lowerComputed (⟨904, by decide⟩ : Fin 1069) = lowerFacets (⟨904, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0905 : lowerComputed (⟨905, by decide⟩ : Fin 1069) = lowerFacets (⟨905, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0906 : lowerComputed (⟨906, by decide⟩ : Fin 1069) = lowerFacets (⟨906, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0907 : lowerComputed (⟨907, by decide⟩ : Fin 1069) = lowerFacets (⟨907, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0908 : lowerComputed (⟨908, by decide⟩ : Fin 1069) = lowerFacets (⟨908, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0909 : lowerComputed (⟨909, by decide⟩ : Fin 1069) = lowerFacets (⟨909, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0910 : lowerComputed (⟨910, by decide⟩ : Fin 1069) = lowerFacets (⟨910, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0911 : lowerComputed (⟨911, by decide⟩ : Fin 1069) = lowerFacets (⟨911, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0912 : lowerComputed (⟨912, by decide⟩ : Fin 1069) = lowerFacets (⟨912, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0913 : lowerComputed (⟨913, by decide⟩ : Fin 1069) = lowerFacets (⟨913, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0914 : lowerComputed (⟨914, by decide⟩ : Fin 1069) = lowerFacets (⟨914, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0915 : lowerComputed (⟨915, by decide⟩ : Fin 1069) = lowerFacets (⟨915, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0916 : lowerComputed (⟨916, by decide⟩ : Fin 1069) = lowerFacets (⟨916, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0917 : lowerComputed (⟨917, by decide⟩ : Fin 1069) = lowerFacets (⟨917, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0918 : lowerComputed (⟨918, by decide⟩ : Fin 1069) = lowerFacets (⟨918, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0919 : lowerComputed (⟨919, by decide⟩ : Fin 1069) = lowerFacets (⟨919, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0920 : lowerComputed (⟨920, by decide⟩ : Fin 1069) = lowerFacets (⟨920, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0921 : lowerComputed (⟨921, by decide⟩ : Fin 1069) = lowerFacets (⟨921, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0922 : lowerComputed (⟨922, by decide⟩ : Fin 1069) = lowerFacets (⟨922, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0923 : lowerComputed (⟨923, by decide⟩ : Fin 1069) = lowerFacets (⟨923, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0924 : lowerComputed (⟨924, by decide⟩ : Fin 1069) = lowerFacets (⟨924, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0925 : lowerComputed (⟨925, by decide⟩ : Fin 1069) = lowerFacets (⟨925, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0926 : lowerComputed (⟨926, by decide⟩ : Fin 1069) = lowerFacets (⟨926, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0927 : lowerComputed (⟨927, by decide⟩ : Fin 1069) = lowerFacets (⟨927, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0928 : lowerComputed (⟨928, by decide⟩ : Fin 1069) = lowerFacets (⟨928, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0929 : lowerComputed (⟨929, by decide⟩ : Fin 1069) = lowerFacets (⟨929, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0930 : lowerComputed (⟨930, by decide⟩ : Fin 1069) = lowerFacets (⟨930, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0931 : lowerComputed (⟨931, by decide⟩ : Fin 1069) = lowerFacets (⟨931, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0932 : lowerComputed (⟨932, by decide⟩ : Fin 1069) = lowerFacets (⟨932, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0933 : lowerComputed (⟨933, by decide⟩ : Fin 1069) = lowerFacets (⟨933, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0934 : lowerComputed (⟨934, by decide⟩ : Fin 1069) = lowerFacets (⟨934, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0935 : lowerComputed (⟨935, by decide⟩ : Fin 1069) = lowerFacets (⟨935, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0936 : lowerComputed (⟨936, by decide⟩ : Fin 1069) = lowerFacets (⟨936, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0937 : lowerComputed (⟨937, by decide⟩ : Fin 1069) = lowerFacets (⟨937, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0938 : lowerComputed (⟨938, by decide⟩ : Fin 1069) = lowerFacets (⟨938, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0939 : lowerComputed (⟨939, by decide⟩ : Fin 1069) = lowerFacets (⟨939, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0940 : lowerComputed (⟨940, by decide⟩ : Fin 1069) = lowerFacets (⟨940, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0941 : lowerComputed (⟨941, by decide⟩ : Fin 1069) = lowerFacets (⟨941, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0942 : lowerComputed (⟨942, by decide⟩ : Fin 1069) = lowerFacets (⟨942, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0943 : lowerComputed (⟨943, by decide⟩ : Fin 1069) = lowerFacets (⟨943, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0944 : lowerComputed (⟨944, by decide⟩ : Fin 1069) = lowerFacets (⟨944, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0945 : lowerComputed (⟨945, by decide⟩ : Fin 1069) = lowerFacets (⟨945, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0946 : lowerComputed (⟨946, by decide⟩ : Fin 1069) = lowerFacets (⟨946, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0947 : lowerComputed (⟨947, by decide⟩ : Fin 1069) = lowerFacets (⟨947, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0948 : lowerComputed (⟨948, by decide⟩ : Fin 1069) = lowerFacets (⟨948, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0949 : lowerComputed (⟨949, by decide⟩ : Fin 1069) = lowerFacets (⟨949, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0950 : lowerComputed (⟨950, by decide⟩ : Fin 1069) = lowerFacets (⟨950, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0951 : lowerComputed (⟨951, by decide⟩ : Fin 1069) = lowerFacets (⟨951, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0952 : lowerComputed (⟨952, by decide⟩ : Fin 1069) = lowerFacets (⟨952, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0953 : lowerComputed (⟨953, by decide⟩ : Fin 1069) = lowerFacets (⟨953, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0954 : lowerComputed (⟨954, by decide⟩ : Fin 1069) = lowerFacets (⟨954, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0955 : lowerComputed (⟨955, by decide⟩ : Fin 1069) = lowerFacets (⟨955, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0956 : lowerComputed (⟨956, by decide⟩ : Fin 1069) = lowerFacets (⟨956, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0957 : lowerComputed (⟨957, by decide⟩ : Fin 1069) = lowerFacets (⟨957, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0958 : lowerComputed (⟨958, by decide⟩ : Fin 1069) = lowerFacets (⟨958, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0959 : lowerComputed (⟨959, by decide⟩ : Fin 1069) = lowerFacets (⟨959, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0960 : lowerComputed (⟨960, by decide⟩ : Fin 1069) = lowerFacets (⟨960, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0961 : lowerComputed (⟨961, by decide⟩ : Fin 1069) = lowerFacets (⟨961, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0962 : lowerComputed (⟨962, by decide⟩ : Fin 1069) = lowerFacets (⟨962, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0963 : lowerComputed (⟨963, by decide⟩ : Fin 1069) = lowerFacets (⟨963, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0964 : lowerComputed (⟨964, by decide⟩ : Fin 1069) = lowerFacets (⟨964, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0965 : lowerComputed (⟨965, by decide⟩ : Fin 1069) = lowerFacets (⟨965, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0966 : lowerComputed (⟨966, by decide⟩ : Fin 1069) = lowerFacets (⟨966, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0967 : lowerComputed (⟨967, by decide⟩ : Fin 1069) = lowerFacets (⟨967, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0968 : lowerComputed (⟨968, by decide⟩ : Fin 1069) = lowerFacets (⟨968, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0969 : lowerComputed (⟨969, by decide⟩ : Fin 1069) = lowerFacets (⟨969, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0970 : lowerComputed (⟨970, by decide⟩ : Fin 1069) = lowerFacets (⟨970, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0971 : lowerComputed (⟨971, by decide⟩ : Fin 1069) = lowerFacets (⟨971, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0972 : lowerComputed (⟨972, by decide⟩ : Fin 1069) = lowerFacets (⟨972, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0973 : lowerComputed (⟨973, by decide⟩ : Fin 1069) = lowerFacets (⟨973, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0974 : lowerComputed (⟨974, by decide⟩ : Fin 1069) = lowerFacets (⟨974, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0975 : lowerComputed (⟨975, by decide⟩ : Fin 1069) = lowerFacets (⟨975, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0976 : lowerComputed (⟨976, by decide⟩ : Fin 1069) = lowerFacets (⟨976, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0977 : lowerComputed (⟨977, by decide⟩ : Fin 1069) = lowerFacets (⟨977, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0978 : lowerComputed (⟨978, by decide⟩ : Fin 1069) = lowerFacets (⟨978, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0979 : lowerComputed (⟨979, by decide⟩ : Fin 1069) = lowerFacets (⟨979, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0980 : lowerComputed (⟨980, by decide⟩ : Fin 1069) = lowerFacets (⟨980, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0981 : lowerComputed (⟨981, by decide⟩ : Fin 1069) = lowerFacets (⟨981, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0982 : lowerComputed (⟨982, by decide⟩ : Fin 1069) = lowerFacets (⟨982, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0983 : lowerComputed (⟨983, by decide⟩ : Fin 1069) = lowerFacets (⟨983, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0984 : lowerComputed (⟨984, by decide⟩ : Fin 1069) = lowerFacets (⟨984, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0985 : lowerComputed (⟨985, by decide⟩ : Fin 1069) = lowerFacets (⟨985, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0986 : lowerComputed (⟨986, by decide⟩ : Fin 1069) = lowerFacets (⟨986, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0987 : lowerComputed (⟨987, by decide⟩ : Fin 1069) = lowerFacets (⟨987, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0988 : lowerComputed (⟨988, by decide⟩ : Fin 1069) = lowerFacets (⟨988, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0989 : lowerComputed (⟨989, by decide⟩ : Fin 1069) = lowerFacets (⟨989, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0990 : lowerComputed (⟨990, by decide⟩ : Fin 1069) = lowerFacets (⟨990, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0991 : lowerComputed (⟨991, by decide⟩ : Fin 1069) = lowerFacets (⟨991, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0992 : lowerComputed (⟨992, by decide⟩ : Fin 1069) = lowerFacets (⟨992, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0993 : lowerComputed (⟨993, by decide⟩ : Fin 1069) = lowerFacets (⟨993, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0994 : lowerComputed (⟨994, by decide⟩ : Fin 1069) = lowerFacets (⟨994, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0995 : lowerComputed (⟨995, by decide⟩ : Fin 1069) = lowerFacets (⟨995, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0996 : lowerComputed (⟨996, by decide⟩ : Fin 1069) = lowerFacets (⟨996, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0997 : lowerComputed (⟨997, by decide⟩ : Fin 1069) = lowerFacets (⟨997, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0998 : lowerComputed (⟨998, by decide⟩ : Fin 1069) = lowerFacets (⟨998, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower0999 : lowerComputed (⟨999, by decide⟩ : Fin 1069) = lowerFacets (⟨999, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1000 : lowerComputed (⟨1000, by decide⟩ : Fin 1069) = lowerFacets (⟨1000, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1001 : lowerComputed (⟨1001, by decide⟩ : Fin 1069) = lowerFacets (⟨1001, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1002 : lowerComputed (⟨1002, by decide⟩ : Fin 1069) = lowerFacets (⟨1002, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1003 : lowerComputed (⟨1003, by decide⟩ : Fin 1069) = lowerFacets (⟨1003, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1004 : lowerComputed (⟨1004, by decide⟩ : Fin 1069) = lowerFacets (⟨1004, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1005 : lowerComputed (⟨1005, by decide⟩ : Fin 1069) = lowerFacets (⟨1005, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1006 : lowerComputed (⟨1006, by decide⟩ : Fin 1069) = lowerFacets (⟨1006, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1007 : lowerComputed (⟨1007, by decide⟩ : Fin 1069) = lowerFacets (⟨1007, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1008 : lowerComputed (⟨1008, by decide⟩ : Fin 1069) = lowerFacets (⟨1008, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1009 : lowerComputed (⟨1009, by decide⟩ : Fin 1069) = lowerFacets (⟨1009, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1010 : lowerComputed (⟨1010, by decide⟩ : Fin 1069) = lowerFacets (⟨1010, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1011 : lowerComputed (⟨1011, by decide⟩ : Fin 1069) = lowerFacets (⟨1011, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1012 : lowerComputed (⟨1012, by decide⟩ : Fin 1069) = lowerFacets (⟨1012, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1013 : lowerComputed (⟨1013, by decide⟩ : Fin 1069) = lowerFacets (⟨1013, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1014 : lowerComputed (⟨1014, by decide⟩ : Fin 1069) = lowerFacets (⟨1014, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1015 : lowerComputed (⟨1015, by decide⟩ : Fin 1069) = lowerFacets (⟨1015, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1016 : lowerComputed (⟨1016, by decide⟩ : Fin 1069) = lowerFacets (⟨1016, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1017 : lowerComputed (⟨1017, by decide⟩ : Fin 1069) = lowerFacets (⟨1017, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1018 : lowerComputed (⟨1018, by decide⟩ : Fin 1069) = lowerFacets (⟨1018, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1019 : lowerComputed (⟨1019, by decide⟩ : Fin 1069) = lowerFacets (⟨1019, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1020 : lowerComputed (⟨1020, by decide⟩ : Fin 1069) = lowerFacets (⟨1020, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1021 : lowerComputed (⟨1021, by decide⟩ : Fin 1069) = lowerFacets (⟨1021, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1022 : lowerComputed (⟨1022, by decide⟩ : Fin 1069) = lowerFacets (⟨1022, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1023 : lowerComputed (⟨1023, by decide⟩ : Fin 1069) = lowerFacets (⟨1023, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1024 : lowerComputed (⟨1024, by decide⟩ : Fin 1069) = lowerFacets (⟨1024, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1025 : lowerComputed (⟨1025, by decide⟩ : Fin 1069) = lowerFacets (⟨1025, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1026 : lowerComputed (⟨1026, by decide⟩ : Fin 1069) = lowerFacets (⟨1026, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1027 : lowerComputed (⟨1027, by decide⟩ : Fin 1069) = lowerFacets (⟨1027, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1028 : lowerComputed (⟨1028, by decide⟩ : Fin 1069) = lowerFacets (⟨1028, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1029 : lowerComputed (⟨1029, by decide⟩ : Fin 1069) = lowerFacets (⟨1029, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1030 : lowerComputed (⟨1030, by decide⟩ : Fin 1069) = lowerFacets (⟨1030, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1031 : lowerComputed (⟨1031, by decide⟩ : Fin 1069) = lowerFacets (⟨1031, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1032 : lowerComputed (⟨1032, by decide⟩ : Fin 1069) = lowerFacets (⟨1032, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1033 : lowerComputed (⟨1033, by decide⟩ : Fin 1069) = lowerFacets (⟨1033, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1034 : lowerComputed (⟨1034, by decide⟩ : Fin 1069) = lowerFacets (⟨1034, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1035 : lowerComputed (⟨1035, by decide⟩ : Fin 1069) = lowerFacets (⟨1035, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1036 : lowerComputed (⟨1036, by decide⟩ : Fin 1069) = lowerFacets (⟨1036, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1037 : lowerComputed (⟨1037, by decide⟩ : Fin 1069) = lowerFacets (⟨1037, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1038 : lowerComputed (⟨1038, by decide⟩ : Fin 1069) = lowerFacets (⟨1038, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1039 : lowerComputed (⟨1039, by decide⟩ : Fin 1069) = lowerFacets (⟨1039, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1040 : lowerComputed (⟨1040, by decide⟩ : Fin 1069) = lowerFacets (⟨1040, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1041 : lowerComputed (⟨1041, by decide⟩ : Fin 1069) = lowerFacets (⟨1041, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1042 : lowerComputed (⟨1042, by decide⟩ : Fin 1069) = lowerFacets (⟨1042, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1043 : lowerComputed (⟨1043, by decide⟩ : Fin 1069) = lowerFacets (⟨1043, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1044 : lowerComputed (⟨1044, by decide⟩ : Fin 1069) = lowerFacets (⟨1044, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1045 : lowerComputed (⟨1045, by decide⟩ : Fin 1069) = lowerFacets (⟨1045, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1046 : lowerComputed (⟨1046, by decide⟩ : Fin 1069) = lowerFacets (⟨1046, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1047 : lowerComputed (⟨1047, by decide⟩ : Fin 1069) = lowerFacets (⟨1047, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1048 : lowerComputed (⟨1048, by decide⟩ : Fin 1069) = lowerFacets (⟨1048, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1049 : lowerComputed (⟨1049, by decide⟩ : Fin 1069) = lowerFacets (⟨1049, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1050 : lowerComputed (⟨1050, by decide⟩ : Fin 1069) = lowerFacets (⟨1050, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1051 : lowerComputed (⟨1051, by decide⟩ : Fin 1069) = lowerFacets (⟨1051, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1052 : lowerComputed (⟨1052, by decide⟩ : Fin 1069) = lowerFacets (⟨1052, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1053 : lowerComputed (⟨1053, by decide⟩ : Fin 1069) = lowerFacets (⟨1053, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1054 : lowerComputed (⟨1054, by decide⟩ : Fin 1069) = lowerFacets (⟨1054, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1055 : lowerComputed (⟨1055, by decide⟩ : Fin 1069) = lowerFacets (⟨1055, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1056 : lowerComputed (⟨1056, by decide⟩ : Fin 1069) = lowerFacets (⟨1056, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1057 : lowerComputed (⟨1057, by decide⟩ : Fin 1069) = lowerFacets (⟨1057, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1058 : lowerComputed (⟨1058, by decide⟩ : Fin 1069) = lowerFacets (⟨1058, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1059 : lowerComputed (⟨1059, by decide⟩ : Fin 1069) = lowerFacets (⟨1059, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1060 : lowerComputed (⟨1060, by decide⟩ : Fin 1069) = lowerFacets (⟨1060, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1061 : lowerComputed (⟨1061, by decide⟩ : Fin 1069) = lowerFacets (⟨1061, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1062 : lowerComputed (⟨1062, by decide⟩ : Fin 1069) = lowerFacets (⟨1062, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1063 : lowerComputed (⟨1063, by decide⟩ : Fin 1069) = lowerFacets (⟨1063, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1064 : lowerComputed (⟨1064, by decide⟩ : Fin 1069) = lowerFacets (⟨1064, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1065 : lowerComputed (⟨1065, by decide⟩ : Fin 1069) = lowerFacets (⟨1065, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1066 : lowerComputed (⟨1066, by decide⟩ : Fin 1069) = lowerFacets (⟨1066, by decide⟩ : Fin 1069) := by
  decide +kernel

private theorem lower1067 : lowerComputed (⟨1067, by decide⟩ : Fin 1069) = lowerFacets (⟨1067, by decide⟩ : Fin 1069) := by
  decide +kernel

/- The top face contains every vertex. A structural proof avoids
normalizing the union of all anchor buckets and repeatedly testing subset
membership in the full vertex set. Only the short interval table is checked. -/
private theorem lowerTop_interval :
    lowerFacets (1068 : Fin 1069) = Finset.Ico (938 : Fin 1069) 1068 := by
  decide +kernel

private theorem lowerTop_rank (j : Fin 1069) :
    j ∈ lowerFacets (1068 : Fin 1069) ↔ (faceRank j).val = 3 := by
  rw [lowerTop_interval, Finset.mem_Ico]
  change (938 ≤ j.val ∧ j.val < 1068) ↔ (faceRank j).val = 3
  unfold faceRank
  split_ifs <;> simp_all <;> omega

private theorem lower1068 :
    lowerComputed (1068 : Fin 1069) = lowerFacets (1068 : Fin 1069) := by
  ext j
  change j ∈ (lowerCandidates (1068 : Fin 1069)).filter _ ↔ _
  rw [Finset.mem_filter, lowerTop_rank]
  constructor
  · intro h
    have hr := h.2.1
    change (faceRank j).val + 1 = 4 at hr
    omega
  · intro h
    have hr : faceRank j = previousRank (1068 : Fin 1069) := by
      apply Fin.ext
      change (faceRank j).val = 3
      exact h
    have hb := anchoredFaces_self j
    rw [hr] at hb
    refine ⟨Finset.mem_biUnion.mpr ?_, ?_, ?_⟩
    · exact ⟨faceAnchor j, Finset.mem_univ _, hb⟩
    · change (faceRank j).val + 1 = 4
      omega
    · change faceMask j ⊆ Finset.univ
      exact Finset.subset_univ _

private theorem lowerGroup0000 (i : Fin 1069)
    (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0000
          ·
            have he : (⟨1, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using lower0001
        ·
          by_cases h3 : i.val < 3
          ·
            have he : (⟨2, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using lower0002
          ·
            have he : (⟨3, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 3 = i.val
              omega
            simpa only [he] using lower0003
      ·
        by_cases h6 : i.val < 6
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using lower0004
          ·
            have he : (⟨5, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using lower0005
        ·
          by_cases h7 : i.val < 7
          ·
            have he : (⟨6, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 6 = i.val
              omega
            simpa only [he] using lower0006
          ·
            have he : (⟨7, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using lower0007
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
            simpa only [he] using lower0008
          ·
            have he : (⟨9, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 9 = i.val
              omega
            simpa only [he] using lower0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using lower0010
          ·
            have he : (⟨11, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using lower0011
      ·
        by_cases h14 : i.val < 14
        ·
          by_cases h13 : i.val < 13
          ·
            have he : (⟨12, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 12 = i.val
              omega
            simpa only [he] using lower0012
          ·
            have he : (⟨13, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using lower0013
        ·
          by_cases h15 : i.val < 15
          ·
            have he : (⟨14, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using lower0014
          ·
            have he : (⟨15, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 15 = i.val
              omega
            simpa only [he] using lower0015
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
            simpa only [he] using lower0016
          ·
            have he : (⟨17, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using lower0017
        ·
          by_cases h19 : i.val < 19
          ·
            have he : (⟨18, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 18 = i.val
              omega
            simpa only [he] using lower0018
          ·
            have he : (⟨19, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using lower0019
      ·
        by_cases h22 : i.val < 22
        ·
          by_cases h21 : i.val < 21
          ·
            have he : (⟨20, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using lower0020
          ·
            have he : (⟨21, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 21 = i.val
              omega
            simpa only [he] using lower0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using lower0022
          ·
            have he : (⟨23, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using lower0023
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
            simpa only [he] using lower0024
          ·
            have he : (⟨25, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 25 = i.val
              omega
            simpa only [he] using lower0025
        ·
          by_cases h27 : i.val < 27
          ·
            have he : (⟨26, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 26 = i.val
              omega
            simpa only [he] using lower0026
          ·
            have he : (⟨27, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 27 = i.val
              omega
            simpa only [he] using lower0027
      ·
        by_cases h30 : i.val < 30
        ·
          by_cases h29 : i.val < 29
          ·
            have he : (⟨28, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 28 = i.val
              omega
            simpa only [he] using lower0028
          ·
            have he : (⟨29, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 29 = i.val
              omega
            simpa only [he] using lower0029
        ·
          by_cases h31 : i.val < 31
          ·
            have he : (⟨30, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 30 = i.val
              omega
            simpa only [he] using lower0030
          ·
            have he : (⟨31, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 31 = i.val
              omega
            simpa only [he] using lower0031

private theorem lowerGroup0001 (i : Fin 1069)
    (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0032
          ·
            have he : (⟨33, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 33 = i.val
              omega
            simpa only [he] using lower0033
        ·
          by_cases h35 : i.val < 35
          ·
            have he : (⟨34, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 34 = i.val
              omega
            simpa only [he] using lower0034
          ·
            have he : (⟨35, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 35 = i.val
              omega
            simpa only [he] using lower0035
      ·
        by_cases h38 : i.val < 38
        ·
          by_cases h37 : i.val < 37
          ·
            have he : (⟨36, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 36 = i.val
              omega
            simpa only [he] using lower0036
          ·
            have he : (⟨37, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 37 = i.val
              omega
            simpa only [he] using lower0037
        ·
          by_cases h39 : i.val < 39
          ·
            have he : (⟨38, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 38 = i.val
              omega
            simpa only [he] using lower0038
          ·
            have he : (⟨39, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 39 = i.val
              omega
            simpa only [he] using lower0039
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
            simpa only [he] using lower0040
          ·
            have he : (⟨41, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 41 = i.val
              omega
            simpa only [he] using lower0041
        ·
          by_cases h43 : i.val < 43
          ·
            have he : (⟨42, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 42 = i.val
              omega
            simpa only [he] using lower0042
          ·
            have he : (⟨43, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 43 = i.val
              omega
            simpa only [he] using lower0043
      ·
        by_cases h46 : i.val < 46
        ·
          by_cases h45 : i.val < 45
          ·
            have he : (⟨44, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 44 = i.val
              omega
            simpa only [he] using lower0044
          ·
            have he : (⟨45, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 45 = i.val
              omega
            simpa only [he] using lower0045
        ·
          by_cases h47 : i.val < 47
          ·
            have he : (⟨46, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 46 = i.val
              omega
            simpa only [he] using lower0046
          ·
            have he : (⟨47, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 47 = i.val
              omega
            simpa only [he] using lower0047
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
            simpa only [he] using lower0048
          ·
            have he : (⟨49, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 49 = i.val
              omega
            simpa only [he] using lower0049
        ·
          by_cases h51 : i.val < 51
          ·
            have he : (⟨50, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 50 = i.val
              omega
            simpa only [he] using lower0050
          ·
            have he : (⟨51, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 51 = i.val
              omega
            simpa only [he] using lower0051
      ·
        by_cases h54 : i.val < 54
        ·
          by_cases h53 : i.val < 53
          ·
            have he : (⟨52, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 52 = i.val
              omega
            simpa only [he] using lower0052
          ·
            have he : (⟨53, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 53 = i.val
              omega
            simpa only [he] using lower0053
        ·
          by_cases h55 : i.val < 55
          ·
            have he : (⟨54, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 54 = i.val
              omega
            simpa only [he] using lower0054
          ·
            have he : (⟨55, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 55 = i.val
              omega
            simpa only [he] using lower0055
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
            simpa only [he] using lower0056
          ·
            have he : (⟨57, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 57 = i.val
              omega
            simpa only [he] using lower0057
        ·
          by_cases h59 : i.val < 59
          ·
            have he : (⟨58, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 58 = i.val
              omega
            simpa only [he] using lower0058
          ·
            have he : (⟨59, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 59 = i.val
              omega
            simpa only [he] using lower0059
      ·
        by_cases h62 : i.val < 62
        ·
          by_cases h61 : i.val < 61
          ·
            have he : (⟨60, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 60 = i.val
              omega
            simpa only [he] using lower0060
          ·
            have he : (⟨61, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 61 = i.val
              omega
            simpa only [he] using lower0061
        ·
          by_cases h63 : i.val < 63
          ·
            have he : (⟨62, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 62 = i.val
              omega
            simpa only [he] using lower0062
          ·
            have he : (⟨63, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 63 = i.val
              omega
            simpa only [he] using lower0063

private theorem lowerGroup0002 (i : Fin 1069)
    (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0064
          ·
            have he : (⟨65, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 65 = i.val
              omega
            simpa only [he] using lower0065
        ·
          by_cases h67 : i.val < 67
          ·
            have he : (⟨66, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 66 = i.val
              omega
            simpa only [he] using lower0066
          ·
            have he : (⟨67, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 67 = i.val
              omega
            simpa only [he] using lower0067
      ·
        by_cases h70 : i.val < 70
        ·
          by_cases h69 : i.val < 69
          ·
            have he : (⟨68, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 68 = i.val
              omega
            simpa only [he] using lower0068
          ·
            have he : (⟨69, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 69 = i.val
              omega
            simpa only [he] using lower0069
        ·
          by_cases h71 : i.val < 71
          ·
            have he : (⟨70, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 70 = i.val
              omega
            simpa only [he] using lower0070
          ·
            have he : (⟨71, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 71 = i.val
              omega
            simpa only [he] using lower0071
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
            simpa only [he] using lower0072
          ·
            have he : (⟨73, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 73 = i.val
              omega
            simpa only [he] using lower0073
        ·
          by_cases h75 : i.val < 75
          ·
            have he : (⟨74, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 74 = i.val
              omega
            simpa only [he] using lower0074
          ·
            have he : (⟨75, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 75 = i.val
              omega
            simpa only [he] using lower0075
      ·
        by_cases h78 : i.val < 78
        ·
          by_cases h77 : i.val < 77
          ·
            have he : (⟨76, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 76 = i.val
              omega
            simpa only [he] using lower0076
          ·
            have he : (⟨77, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 77 = i.val
              omega
            simpa only [he] using lower0077
        ·
          by_cases h79 : i.val < 79
          ·
            have he : (⟨78, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 78 = i.val
              omega
            simpa only [he] using lower0078
          ·
            have he : (⟨79, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 79 = i.val
              omega
            simpa only [he] using lower0079
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
            simpa only [he] using lower0080
          ·
            have he : (⟨81, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 81 = i.val
              omega
            simpa only [he] using lower0081
        ·
          by_cases h83 : i.val < 83
          ·
            have he : (⟨82, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 82 = i.val
              omega
            simpa only [he] using lower0082
          ·
            have he : (⟨83, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 83 = i.val
              omega
            simpa only [he] using lower0083
      ·
        by_cases h86 : i.val < 86
        ·
          by_cases h85 : i.val < 85
          ·
            have he : (⟨84, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 84 = i.val
              omega
            simpa only [he] using lower0084
          ·
            have he : (⟨85, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 85 = i.val
              omega
            simpa only [he] using lower0085
        ·
          by_cases h87 : i.val < 87
          ·
            have he : (⟨86, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 86 = i.val
              omega
            simpa only [he] using lower0086
          ·
            have he : (⟨87, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 87 = i.val
              omega
            simpa only [he] using lower0087
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
            simpa only [he] using lower0088
          ·
            have he : (⟨89, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 89 = i.val
              omega
            simpa only [he] using lower0089
        ·
          by_cases h91 : i.val < 91
          ·
            have he : (⟨90, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 90 = i.val
              omega
            simpa only [he] using lower0090
          ·
            have he : (⟨91, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 91 = i.val
              omega
            simpa only [he] using lower0091
      ·
        by_cases h94 : i.val < 94
        ·
          by_cases h93 : i.val < 93
          ·
            have he : (⟨92, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 92 = i.val
              omega
            simpa only [he] using lower0092
          ·
            have he : (⟨93, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 93 = i.val
              omega
            simpa only [he] using lower0093
        ·
          by_cases h95 : i.val < 95
          ·
            have he : (⟨94, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 94 = i.val
              omega
            simpa only [he] using lower0094
          ·
            have he : (⟨95, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 95 = i.val
              omega
            simpa only [he] using lower0095

private theorem lowerGroup0003 (i : Fin 1069)
    (hlo : 96 ≤ i.val) (hhi : i.val < 128) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0096
          ·
            have he : (⟨97, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 97 = i.val
              omega
            simpa only [he] using lower0097
        ·
          by_cases h99 : i.val < 99
          ·
            have he : (⟨98, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 98 = i.val
              omega
            simpa only [he] using lower0098
          ·
            have he : (⟨99, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 99 = i.val
              omega
            simpa only [he] using lower0099
      ·
        by_cases h102 : i.val < 102
        ·
          by_cases h101 : i.val < 101
          ·
            have he : (⟨100, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 100 = i.val
              omega
            simpa only [he] using lower0100
          ·
            have he : (⟨101, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 101 = i.val
              omega
            simpa only [he] using lower0101
        ·
          by_cases h103 : i.val < 103
          ·
            have he : (⟨102, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 102 = i.val
              omega
            simpa only [he] using lower0102
          ·
            have he : (⟨103, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 103 = i.val
              omega
            simpa only [he] using lower0103
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
            simpa only [he] using lower0104
          ·
            have he : (⟨105, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 105 = i.val
              omega
            simpa only [he] using lower0105
        ·
          by_cases h107 : i.val < 107
          ·
            have he : (⟨106, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 106 = i.val
              omega
            simpa only [he] using lower0106
          ·
            have he : (⟨107, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 107 = i.val
              omega
            simpa only [he] using lower0107
      ·
        by_cases h110 : i.val < 110
        ·
          by_cases h109 : i.val < 109
          ·
            have he : (⟨108, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 108 = i.val
              omega
            simpa only [he] using lower0108
          ·
            have he : (⟨109, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 109 = i.val
              omega
            simpa only [he] using lower0109
        ·
          by_cases h111 : i.val < 111
          ·
            have he : (⟨110, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 110 = i.val
              omega
            simpa only [he] using lower0110
          ·
            have he : (⟨111, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 111 = i.val
              omega
            simpa only [he] using lower0111
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
            simpa only [he] using lower0112
          ·
            have he : (⟨113, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 113 = i.val
              omega
            simpa only [he] using lower0113
        ·
          by_cases h115 : i.val < 115
          ·
            have he : (⟨114, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 114 = i.val
              omega
            simpa only [he] using lower0114
          ·
            have he : (⟨115, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 115 = i.val
              omega
            simpa only [he] using lower0115
      ·
        by_cases h118 : i.val < 118
        ·
          by_cases h117 : i.val < 117
          ·
            have he : (⟨116, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 116 = i.val
              omega
            simpa only [he] using lower0116
          ·
            have he : (⟨117, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 117 = i.val
              omega
            simpa only [he] using lower0117
        ·
          by_cases h119 : i.val < 119
          ·
            have he : (⟨118, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 118 = i.val
              omega
            simpa only [he] using lower0118
          ·
            have he : (⟨119, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 119 = i.val
              omega
            simpa only [he] using lower0119
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
            simpa only [he] using lower0120
          ·
            have he : (⟨121, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 121 = i.val
              omega
            simpa only [he] using lower0121
        ·
          by_cases h123 : i.val < 123
          ·
            have he : (⟨122, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 122 = i.val
              omega
            simpa only [he] using lower0122
          ·
            have he : (⟨123, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 123 = i.val
              omega
            simpa only [he] using lower0123
      ·
        by_cases h126 : i.val < 126
        ·
          by_cases h125 : i.val < 125
          ·
            have he : (⟨124, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 124 = i.val
              omega
            simpa only [he] using lower0124
          ·
            have he : (⟨125, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 125 = i.val
              omega
            simpa only [he] using lower0125
        ·
          by_cases h127 : i.val < 127
          ·
            have he : (⟨126, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 126 = i.val
              omega
            simpa only [he] using lower0126
          ·
            have he : (⟨127, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 127 = i.val
              omega
            simpa only [he] using lower0127

private theorem lowerGroup0004 (i : Fin 1069)
    (hlo : 128 ≤ i.val) (hhi : i.val < 160) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0128
          ·
            have he : (⟨129, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 129 = i.val
              omega
            simpa only [he] using lower0129
        ·
          by_cases h131 : i.val < 131
          ·
            have he : (⟨130, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 130 = i.val
              omega
            simpa only [he] using lower0130
          ·
            have he : (⟨131, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 131 = i.val
              omega
            simpa only [he] using lower0131
      ·
        by_cases h134 : i.val < 134
        ·
          by_cases h133 : i.val < 133
          ·
            have he : (⟨132, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 132 = i.val
              omega
            simpa only [he] using lower0132
          ·
            have he : (⟨133, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 133 = i.val
              omega
            simpa only [he] using lower0133
        ·
          by_cases h135 : i.val < 135
          ·
            have he : (⟨134, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 134 = i.val
              omega
            simpa only [he] using lower0134
          ·
            have he : (⟨135, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 135 = i.val
              omega
            simpa only [he] using lower0135
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
            simpa only [he] using lower0136
          ·
            have he : (⟨137, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 137 = i.val
              omega
            simpa only [he] using lower0137
        ·
          by_cases h139 : i.val < 139
          ·
            have he : (⟨138, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 138 = i.val
              omega
            simpa only [he] using lower0138
          ·
            have he : (⟨139, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 139 = i.val
              omega
            simpa only [he] using lower0139
      ·
        by_cases h142 : i.val < 142
        ·
          by_cases h141 : i.val < 141
          ·
            have he : (⟨140, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 140 = i.val
              omega
            simpa only [he] using lower0140
          ·
            have he : (⟨141, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 141 = i.val
              omega
            simpa only [he] using lower0141
        ·
          by_cases h143 : i.val < 143
          ·
            have he : (⟨142, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 142 = i.val
              omega
            simpa only [he] using lower0142
          ·
            have he : (⟨143, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 143 = i.val
              omega
            simpa only [he] using lower0143
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
            simpa only [he] using lower0144
          ·
            have he : (⟨145, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 145 = i.val
              omega
            simpa only [he] using lower0145
        ·
          by_cases h147 : i.val < 147
          ·
            have he : (⟨146, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 146 = i.val
              omega
            simpa only [he] using lower0146
          ·
            have he : (⟨147, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 147 = i.val
              omega
            simpa only [he] using lower0147
      ·
        by_cases h150 : i.val < 150
        ·
          by_cases h149 : i.val < 149
          ·
            have he : (⟨148, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 148 = i.val
              omega
            simpa only [he] using lower0148
          ·
            have he : (⟨149, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 149 = i.val
              omega
            simpa only [he] using lower0149
        ·
          by_cases h151 : i.val < 151
          ·
            have he : (⟨150, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 150 = i.val
              omega
            simpa only [he] using lower0150
          ·
            have he : (⟨151, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 151 = i.val
              omega
            simpa only [he] using lower0151
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
            simpa only [he] using lower0152
          ·
            have he : (⟨153, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 153 = i.val
              omega
            simpa only [he] using lower0153
        ·
          by_cases h155 : i.val < 155
          ·
            have he : (⟨154, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 154 = i.val
              omega
            simpa only [he] using lower0154
          ·
            have he : (⟨155, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 155 = i.val
              omega
            simpa only [he] using lower0155
      ·
        by_cases h158 : i.val < 158
        ·
          by_cases h157 : i.val < 157
          ·
            have he : (⟨156, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 156 = i.val
              omega
            simpa only [he] using lower0156
          ·
            have he : (⟨157, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 157 = i.val
              omega
            simpa only [he] using lower0157
        ·
          by_cases h159 : i.val < 159
          ·
            have he : (⟨158, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 158 = i.val
              omega
            simpa only [he] using lower0158
          ·
            have he : (⟨159, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 159 = i.val
              omega
            simpa only [he] using lower0159

private theorem lowerGroup0005 (i : Fin 1069)
    (hlo : 160 ≤ i.val) (hhi : i.val < 192) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0160
          ·
            have he : (⟨161, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 161 = i.val
              omega
            simpa only [he] using lower0161
        ·
          by_cases h163 : i.val < 163
          ·
            have he : (⟨162, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 162 = i.val
              omega
            simpa only [he] using lower0162
          ·
            have he : (⟨163, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 163 = i.val
              omega
            simpa only [he] using lower0163
      ·
        by_cases h166 : i.val < 166
        ·
          by_cases h165 : i.val < 165
          ·
            have he : (⟨164, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 164 = i.val
              omega
            simpa only [he] using lower0164
          ·
            have he : (⟨165, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 165 = i.val
              omega
            simpa only [he] using lower0165
        ·
          by_cases h167 : i.val < 167
          ·
            have he : (⟨166, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 166 = i.val
              omega
            simpa only [he] using lower0166
          ·
            have he : (⟨167, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 167 = i.val
              omega
            simpa only [he] using lower0167
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
            simpa only [he] using lower0168
          ·
            have he : (⟨169, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 169 = i.val
              omega
            simpa only [he] using lower0169
        ·
          by_cases h171 : i.val < 171
          ·
            have he : (⟨170, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 170 = i.val
              omega
            simpa only [he] using lower0170
          ·
            have he : (⟨171, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 171 = i.val
              omega
            simpa only [he] using lower0171
      ·
        by_cases h174 : i.val < 174
        ·
          by_cases h173 : i.val < 173
          ·
            have he : (⟨172, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 172 = i.val
              omega
            simpa only [he] using lower0172
          ·
            have he : (⟨173, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 173 = i.val
              omega
            simpa only [he] using lower0173
        ·
          by_cases h175 : i.val < 175
          ·
            have he : (⟨174, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 174 = i.val
              omega
            simpa only [he] using lower0174
          ·
            have he : (⟨175, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 175 = i.val
              omega
            simpa only [he] using lower0175
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
            simpa only [he] using lower0176
          ·
            have he : (⟨177, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 177 = i.val
              omega
            simpa only [he] using lower0177
        ·
          by_cases h179 : i.val < 179
          ·
            have he : (⟨178, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 178 = i.val
              omega
            simpa only [he] using lower0178
          ·
            have he : (⟨179, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 179 = i.val
              omega
            simpa only [he] using lower0179
      ·
        by_cases h182 : i.val < 182
        ·
          by_cases h181 : i.val < 181
          ·
            have he : (⟨180, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 180 = i.val
              omega
            simpa only [he] using lower0180
          ·
            have he : (⟨181, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 181 = i.val
              omega
            simpa only [he] using lower0181
        ·
          by_cases h183 : i.val < 183
          ·
            have he : (⟨182, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 182 = i.val
              omega
            simpa only [he] using lower0182
          ·
            have he : (⟨183, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 183 = i.val
              omega
            simpa only [he] using lower0183
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
            simpa only [he] using lower0184
          ·
            have he : (⟨185, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 185 = i.val
              omega
            simpa only [he] using lower0185
        ·
          by_cases h187 : i.val < 187
          ·
            have he : (⟨186, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 186 = i.val
              omega
            simpa only [he] using lower0186
          ·
            have he : (⟨187, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 187 = i.val
              omega
            simpa only [he] using lower0187
      ·
        by_cases h190 : i.val < 190
        ·
          by_cases h189 : i.val < 189
          ·
            have he : (⟨188, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 188 = i.val
              omega
            simpa only [he] using lower0188
          ·
            have he : (⟨189, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 189 = i.val
              omega
            simpa only [he] using lower0189
        ·
          by_cases h191 : i.val < 191
          ·
            have he : (⟨190, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 190 = i.val
              omega
            simpa only [he] using lower0190
          ·
            have he : (⟨191, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 191 = i.val
              omega
            simpa only [he] using lower0191

private theorem lowerGroup0006 (i : Fin 1069)
    (hlo : 192 ≤ i.val) (hhi : i.val < 224) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0192
          ·
            have he : (⟨193, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 193 = i.val
              omega
            simpa only [he] using lower0193
        ·
          by_cases h195 : i.val < 195
          ·
            have he : (⟨194, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 194 = i.val
              omega
            simpa only [he] using lower0194
          ·
            have he : (⟨195, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 195 = i.val
              omega
            simpa only [he] using lower0195
      ·
        by_cases h198 : i.val < 198
        ·
          by_cases h197 : i.val < 197
          ·
            have he : (⟨196, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 196 = i.val
              omega
            simpa only [he] using lower0196
          ·
            have he : (⟨197, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 197 = i.val
              omega
            simpa only [he] using lower0197
        ·
          by_cases h199 : i.val < 199
          ·
            have he : (⟨198, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 198 = i.val
              omega
            simpa only [he] using lower0198
          ·
            have he : (⟨199, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 199 = i.val
              omega
            simpa only [he] using lower0199
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
            simpa only [he] using lower0200
          ·
            have he : (⟨201, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 201 = i.val
              omega
            simpa only [he] using lower0201
        ·
          by_cases h203 : i.val < 203
          ·
            have he : (⟨202, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 202 = i.val
              omega
            simpa only [he] using lower0202
          ·
            have he : (⟨203, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 203 = i.val
              omega
            simpa only [he] using lower0203
      ·
        by_cases h206 : i.val < 206
        ·
          by_cases h205 : i.val < 205
          ·
            have he : (⟨204, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 204 = i.val
              omega
            simpa only [he] using lower0204
          ·
            have he : (⟨205, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 205 = i.val
              omega
            simpa only [he] using lower0205
        ·
          by_cases h207 : i.val < 207
          ·
            have he : (⟨206, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 206 = i.val
              omega
            simpa only [he] using lower0206
          ·
            have he : (⟨207, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 207 = i.val
              omega
            simpa only [he] using lower0207
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
            simpa only [he] using lower0208
          ·
            have he : (⟨209, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 209 = i.val
              omega
            simpa only [he] using lower0209
        ·
          by_cases h211 : i.val < 211
          ·
            have he : (⟨210, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 210 = i.val
              omega
            simpa only [he] using lower0210
          ·
            have he : (⟨211, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 211 = i.val
              omega
            simpa only [he] using lower0211
      ·
        by_cases h214 : i.val < 214
        ·
          by_cases h213 : i.val < 213
          ·
            have he : (⟨212, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 212 = i.val
              omega
            simpa only [he] using lower0212
          ·
            have he : (⟨213, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 213 = i.val
              omega
            simpa only [he] using lower0213
        ·
          by_cases h215 : i.val < 215
          ·
            have he : (⟨214, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 214 = i.val
              omega
            simpa only [he] using lower0214
          ·
            have he : (⟨215, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 215 = i.val
              omega
            simpa only [he] using lower0215
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
            simpa only [he] using lower0216
          ·
            have he : (⟨217, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 217 = i.val
              omega
            simpa only [he] using lower0217
        ·
          by_cases h219 : i.val < 219
          ·
            have he : (⟨218, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 218 = i.val
              omega
            simpa only [he] using lower0218
          ·
            have he : (⟨219, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 219 = i.val
              omega
            simpa only [he] using lower0219
      ·
        by_cases h222 : i.val < 222
        ·
          by_cases h221 : i.val < 221
          ·
            have he : (⟨220, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 220 = i.val
              omega
            simpa only [he] using lower0220
          ·
            have he : (⟨221, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 221 = i.val
              omega
            simpa only [he] using lower0221
        ·
          by_cases h223 : i.val < 223
          ·
            have he : (⟨222, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 222 = i.val
              omega
            simpa only [he] using lower0222
          ·
            have he : (⟨223, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 223 = i.val
              omega
            simpa only [he] using lower0223

private theorem lowerGroup0007 (i : Fin 1069)
    (hlo : 224 ≤ i.val) (hhi : i.val < 256) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0224
          ·
            have he : (⟨225, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 225 = i.val
              omega
            simpa only [he] using lower0225
        ·
          by_cases h227 : i.val < 227
          ·
            have he : (⟨226, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 226 = i.val
              omega
            simpa only [he] using lower0226
          ·
            have he : (⟨227, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 227 = i.val
              omega
            simpa only [he] using lower0227
      ·
        by_cases h230 : i.val < 230
        ·
          by_cases h229 : i.val < 229
          ·
            have he : (⟨228, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 228 = i.val
              omega
            simpa only [he] using lower0228
          ·
            have he : (⟨229, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 229 = i.val
              omega
            simpa only [he] using lower0229
        ·
          by_cases h231 : i.val < 231
          ·
            have he : (⟨230, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 230 = i.val
              omega
            simpa only [he] using lower0230
          ·
            have he : (⟨231, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 231 = i.val
              omega
            simpa only [he] using lower0231
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
            simpa only [he] using lower0232
          ·
            have he : (⟨233, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 233 = i.val
              omega
            simpa only [he] using lower0233
        ·
          by_cases h235 : i.val < 235
          ·
            have he : (⟨234, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 234 = i.val
              omega
            simpa only [he] using lower0234
          ·
            have he : (⟨235, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 235 = i.val
              omega
            simpa only [he] using lower0235
      ·
        by_cases h238 : i.val < 238
        ·
          by_cases h237 : i.val < 237
          ·
            have he : (⟨236, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 236 = i.val
              omega
            simpa only [he] using lower0236
          ·
            have he : (⟨237, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 237 = i.val
              omega
            simpa only [he] using lower0237
        ·
          by_cases h239 : i.val < 239
          ·
            have he : (⟨238, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 238 = i.val
              omega
            simpa only [he] using lower0238
          ·
            have he : (⟨239, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 239 = i.val
              omega
            simpa only [he] using lower0239
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
            simpa only [he] using lower0240
          ·
            have he : (⟨241, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 241 = i.val
              omega
            simpa only [he] using lower0241
        ·
          by_cases h243 : i.val < 243
          ·
            have he : (⟨242, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 242 = i.val
              omega
            simpa only [he] using lower0242
          ·
            have he : (⟨243, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 243 = i.val
              omega
            simpa only [he] using lower0243
      ·
        by_cases h246 : i.val < 246
        ·
          by_cases h245 : i.val < 245
          ·
            have he : (⟨244, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 244 = i.val
              omega
            simpa only [he] using lower0244
          ·
            have he : (⟨245, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 245 = i.val
              omega
            simpa only [he] using lower0245
        ·
          by_cases h247 : i.val < 247
          ·
            have he : (⟨246, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 246 = i.val
              omega
            simpa only [he] using lower0246
          ·
            have he : (⟨247, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 247 = i.val
              omega
            simpa only [he] using lower0247
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
            simpa only [he] using lower0248
          ·
            have he : (⟨249, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 249 = i.val
              omega
            simpa only [he] using lower0249
        ·
          by_cases h251 : i.val < 251
          ·
            have he : (⟨250, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 250 = i.val
              omega
            simpa only [he] using lower0250
          ·
            have he : (⟨251, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 251 = i.val
              omega
            simpa only [he] using lower0251
      ·
        by_cases h254 : i.val < 254
        ·
          by_cases h253 : i.val < 253
          ·
            have he : (⟨252, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 252 = i.val
              omega
            simpa only [he] using lower0252
          ·
            have he : (⟨253, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 253 = i.val
              omega
            simpa only [he] using lower0253
        ·
          by_cases h255 : i.val < 255
          ·
            have he : (⟨254, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 254 = i.val
              omega
            simpa only [he] using lower0254
          ·
            have he : (⟨255, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 255 = i.val
              omega
            simpa only [he] using lower0255

private theorem lowerGroup0008 (i : Fin 1069)
    (hlo : 256 ≤ i.val) (hhi : i.val < 288) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0256
          ·
            have he : (⟨257, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 257 = i.val
              omega
            simpa only [he] using lower0257
        ·
          by_cases h259 : i.val < 259
          ·
            have he : (⟨258, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 258 = i.val
              omega
            simpa only [he] using lower0258
          ·
            have he : (⟨259, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 259 = i.val
              omega
            simpa only [he] using lower0259
      ·
        by_cases h262 : i.val < 262
        ·
          by_cases h261 : i.val < 261
          ·
            have he : (⟨260, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 260 = i.val
              omega
            simpa only [he] using lower0260
          ·
            have he : (⟨261, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 261 = i.val
              omega
            simpa only [he] using lower0261
        ·
          by_cases h263 : i.val < 263
          ·
            have he : (⟨262, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 262 = i.val
              omega
            simpa only [he] using lower0262
          ·
            have he : (⟨263, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 263 = i.val
              omega
            simpa only [he] using lower0263
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
            simpa only [he] using lower0264
          ·
            have he : (⟨265, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 265 = i.val
              omega
            simpa only [he] using lower0265
        ·
          by_cases h267 : i.val < 267
          ·
            have he : (⟨266, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 266 = i.val
              omega
            simpa only [he] using lower0266
          ·
            have he : (⟨267, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 267 = i.val
              omega
            simpa only [he] using lower0267
      ·
        by_cases h270 : i.val < 270
        ·
          by_cases h269 : i.val < 269
          ·
            have he : (⟨268, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 268 = i.val
              omega
            simpa only [he] using lower0268
          ·
            have he : (⟨269, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 269 = i.val
              omega
            simpa only [he] using lower0269
        ·
          by_cases h271 : i.val < 271
          ·
            have he : (⟨270, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 270 = i.val
              omega
            simpa only [he] using lower0270
          ·
            have he : (⟨271, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 271 = i.val
              omega
            simpa only [he] using lower0271
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
            simpa only [he] using lower0272
          ·
            have he : (⟨273, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 273 = i.val
              omega
            simpa only [he] using lower0273
        ·
          by_cases h275 : i.val < 275
          ·
            have he : (⟨274, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 274 = i.val
              omega
            simpa only [he] using lower0274
          ·
            have he : (⟨275, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 275 = i.val
              omega
            simpa only [he] using lower0275
      ·
        by_cases h278 : i.val < 278
        ·
          by_cases h277 : i.val < 277
          ·
            have he : (⟨276, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 276 = i.val
              omega
            simpa only [he] using lower0276
          ·
            have he : (⟨277, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 277 = i.val
              omega
            simpa only [he] using lower0277
        ·
          by_cases h279 : i.val < 279
          ·
            have he : (⟨278, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 278 = i.val
              omega
            simpa only [he] using lower0278
          ·
            have he : (⟨279, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 279 = i.val
              omega
            simpa only [he] using lower0279
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
            simpa only [he] using lower0280
          ·
            have he : (⟨281, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 281 = i.val
              omega
            simpa only [he] using lower0281
        ·
          by_cases h283 : i.val < 283
          ·
            have he : (⟨282, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 282 = i.val
              omega
            simpa only [he] using lower0282
          ·
            have he : (⟨283, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 283 = i.val
              omega
            simpa only [he] using lower0283
      ·
        by_cases h286 : i.val < 286
        ·
          by_cases h285 : i.val < 285
          ·
            have he : (⟨284, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 284 = i.val
              omega
            simpa only [he] using lower0284
          ·
            have he : (⟨285, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 285 = i.val
              omega
            simpa only [he] using lower0285
        ·
          by_cases h287 : i.val < 287
          ·
            have he : (⟨286, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 286 = i.val
              omega
            simpa only [he] using lower0286
          ·
            have he : (⟨287, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 287 = i.val
              omega
            simpa only [he] using lower0287

private theorem lowerGroup0009 (i : Fin 1069)
    (hlo : 288 ≤ i.val) (hhi : i.val < 320) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0288
          ·
            have he : (⟨289, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 289 = i.val
              omega
            simpa only [he] using lower0289
        ·
          by_cases h291 : i.val < 291
          ·
            have he : (⟨290, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 290 = i.val
              omega
            simpa only [he] using lower0290
          ·
            have he : (⟨291, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 291 = i.val
              omega
            simpa only [he] using lower0291
      ·
        by_cases h294 : i.val < 294
        ·
          by_cases h293 : i.val < 293
          ·
            have he : (⟨292, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 292 = i.val
              omega
            simpa only [he] using lower0292
          ·
            have he : (⟨293, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 293 = i.val
              omega
            simpa only [he] using lower0293
        ·
          by_cases h295 : i.val < 295
          ·
            have he : (⟨294, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 294 = i.val
              omega
            simpa only [he] using lower0294
          ·
            have he : (⟨295, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 295 = i.val
              omega
            simpa only [he] using lower0295
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
            simpa only [he] using lower0296
          ·
            have he : (⟨297, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 297 = i.val
              omega
            simpa only [he] using lower0297
        ·
          by_cases h299 : i.val < 299
          ·
            have he : (⟨298, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 298 = i.val
              omega
            simpa only [he] using lower0298
          ·
            have he : (⟨299, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 299 = i.val
              omega
            simpa only [he] using lower0299
      ·
        by_cases h302 : i.val < 302
        ·
          by_cases h301 : i.val < 301
          ·
            have he : (⟨300, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 300 = i.val
              omega
            simpa only [he] using lower0300
          ·
            have he : (⟨301, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 301 = i.val
              omega
            simpa only [he] using lower0301
        ·
          by_cases h303 : i.val < 303
          ·
            have he : (⟨302, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 302 = i.val
              omega
            simpa only [he] using lower0302
          ·
            have he : (⟨303, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 303 = i.val
              omega
            simpa only [he] using lower0303
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
            simpa only [he] using lower0304
          ·
            have he : (⟨305, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 305 = i.val
              omega
            simpa only [he] using lower0305
        ·
          by_cases h307 : i.val < 307
          ·
            have he : (⟨306, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 306 = i.val
              omega
            simpa only [he] using lower0306
          ·
            have he : (⟨307, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 307 = i.val
              omega
            simpa only [he] using lower0307
      ·
        by_cases h310 : i.val < 310
        ·
          by_cases h309 : i.val < 309
          ·
            have he : (⟨308, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 308 = i.val
              omega
            simpa only [he] using lower0308
          ·
            have he : (⟨309, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 309 = i.val
              omega
            simpa only [he] using lower0309
        ·
          by_cases h311 : i.val < 311
          ·
            have he : (⟨310, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 310 = i.val
              omega
            simpa only [he] using lower0310
          ·
            have he : (⟨311, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 311 = i.val
              omega
            simpa only [he] using lower0311
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
            simpa only [he] using lower0312
          ·
            have he : (⟨313, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 313 = i.val
              omega
            simpa only [he] using lower0313
        ·
          by_cases h315 : i.val < 315
          ·
            have he : (⟨314, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 314 = i.val
              omega
            simpa only [he] using lower0314
          ·
            have he : (⟨315, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 315 = i.val
              omega
            simpa only [he] using lower0315
      ·
        by_cases h318 : i.val < 318
        ·
          by_cases h317 : i.val < 317
          ·
            have he : (⟨316, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 316 = i.val
              omega
            simpa only [he] using lower0316
          ·
            have he : (⟨317, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 317 = i.val
              omega
            simpa only [he] using lower0317
        ·
          by_cases h319 : i.val < 319
          ·
            have he : (⟨318, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 318 = i.val
              omega
            simpa only [he] using lower0318
          ·
            have he : (⟨319, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 319 = i.val
              omega
            simpa only [he] using lower0319

private theorem lowerGroup0010 (i : Fin 1069)
    (hlo : 320 ≤ i.val) (hhi : i.val < 352) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0320
          ·
            have he : (⟨321, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 321 = i.val
              omega
            simpa only [he] using lower0321
        ·
          by_cases h323 : i.val < 323
          ·
            have he : (⟨322, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 322 = i.val
              omega
            simpa only [he] using lower0322
          ·
            have he : (⟨323, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 323 = i.val
              omega
            simpa only [he] using lower0323
      ·
        by_cases h326 : i.val < 326
        ·
          by_cases h325 : i.val < 325
          ·
            have he : (⟨324, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 324 = i.val
              omega
            simpa only [he] using lower0324
          ·
            have he : (⟨325, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 325 = i.val
              omega
            simpa only [he] using lower0325
        ·
          by_cases h327 : i.val < 327
          ·
            have he : (⟨326, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 326 = i.val
              omega
            simpa only [he] using lower0326
          ·
            have he : (⟨327, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 327 = i.val
              omega
            simpa only [he] using lower0327
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
            simpa only [he] using lower0328
          ·
            have he : (⟨329, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 329 = i.val
              omega
            simpa only [he] using lower0329
        ·
          by_cases h331 : i.val < 331
          ·
            have he : (⟨330, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 330 = i.val
              omega
            simpa only [he] using lower0330
          ·
            have he : (⟨331, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 331 = i.val
              omega
            simpa only [he] using lower0331
      ·
        by_cases h334 : i.val < 334
        ·
          by_cases h333 : i.val < 333
          ·
            have he : (⟨332, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 332 = i.val
              omega
            simpa only [he] using lower0332
          ·
            have he : (⟨333, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 333 = i.val
              omega
            simpa only [he] using lower0333
        ·
          by_cases h335 : i.val < 335
          ·
            have he : (⟨334, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 334 = i.val
              omega
            simpa only [he] using lower0334
          ·
            have he : (⟨335, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 335 = i.val
              omega
            simpa only [he] using lower0335
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
            simpa only [he] using lower0336
          ·
            have he : (⟨337, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 337 = i.val
              omega
            simpa only [he] using lower0337
        ·
          by_cases h339 : i.val < 339
          ·
            have he : (⟨338, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 338 = i.val
              omega
            simpa only [he] using lower0338
          ·
            have he : (⟨339, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 339 = i.val
              omega
            simpa only [he] using lower0339
      ·
        by_cases h342 : i.val < 342
        ·
          by_cases h341 : i.val < 341
          ·
            have he : (⟨340, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 340 = i.val
              omega
            simpa only [he] using lower0340
          ·
            have he : (⟨341, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 341 = i.val
              omega
            simpa only [he] using lower0341
        ·
          by_cases h343 : i.val < 343
          ·
            have he : (⟨342, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 342 = i.val
              omega
            simpa only [he] using lower0342
          ·
            have he : (⟨343, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 343 = i.val
              omega
            simpa only [he] using lower0343
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
            simpa only [he] using lower0344
          ·
            have he : (⟨345, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 345 = i.val
              omega
            simpa only [he] using lower0345
        ·
          by_cases h347 : i.val < 347
          ·
            have he : (⟨346, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 346 = i.val
              omega
            simpa only [he] using lower0346
          ·
            have he : (⟨347, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 347 = i.val
              omega
            simpa only [he] using lower0347
      ·
        by_cases h350 : i.val < 350
        ·
          by_cases h349 : i.val < 349
          ·
            have he : (⟨348, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 348 = i.val
              omega
            simpa only [he] using lower0348
          ·
            have he : (⟨349, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 349 = i.val
              omega
            simpa only [he] using lower0349
        ·
          by_cases h351 : i.val < 351
          ·
            have he : (⟨350, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 350 = i.val
              omega
            simpa only [he] using lower0350
          ·
            have he : (⟨351, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 351 = i.val
              omega
            simpa only [he] using lower0351

private theorem lowerGroup0011 (i : Fin 1069)
    (hlo : 352 ≤ i.val) (hhi : i.val < 384) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0352
          ·
            have he : (⟨353, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 353 = i.val
              omega
            simpa only [he] using lower0353
        ·
          by_cases h355 : i.val < 355
          ·
            have he : (⟨354, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 354 = i.val
              omega
            simpa only [he] using lower0354
          ·
            have he : (⟨355, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 355 = i.val
              omega
            simpa only [he] using lower0355
      ·
        by_cases h358 : i.val < 358
        ·
          by_cases h357 : i.val < 357
          ·
            have he : (⟨356, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 356 = i.val
              omega
            simpa only [he] using lower0356
          ·
            have he : (⟨357, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 357 = i.val
              omega
            simpa only [he] using lower0357
        ·
          by_cases h359 : i.val < 359
          ·
            have he : (⟨358, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 358 = i.val
              omega
            simpa only [he] using lower0358
          ·
            have he : (⟨359, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 359 = i.val
              omega
            simpa only [he] using lower0359
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
            simpa only [he] using lower0360
          ·
            have he : (⟨361, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 361 = i.val
              omega
            simpa only [he] using lower0361
        ·
          by_cases h363 : i.val < 363
          ·
            have he : (⟨362, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 362 = i.val
              omega
            simpa only [he] using lower0362
          ·
            have he : (⟨363, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 363 = i.val
              omega
            simpa only [he] using lower0363
      ·
        by_cases h366 : i.val < 366
        ·
          by_cases h365 : i.val < 365
          ·
            have he : (⟨364, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 364 = i.val
              omega
            simpa only [he] using lower0364
          ·
            have he : (⟨365, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 365 = i.val
              omega
            simpa only [he] using lower0365
        ·
          by_cases h367 : i.val < 367
          ·
            have he : (⟨366, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 366 = i.val
              omega
            simpa only [he] using lower0366
          ·
            have he : (⟨367, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 367 = i.val
              omega
            simpa only [he] using lower0367
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
            simpa only [he] using lower0368
          ·
            have he : (⟨369, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 369 = i.val
              omega
            simpa only [he] using lower0369
        ·
          by_cases h371 : i.val < 371
          ·
            have he : (⟨370, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 370 = i.val
              omega
            simpa only [he] using lower0370
          ·
            have he : (⟨371, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 371 = i.val
              omega
            simpa only [he] using lower0371
      ·
        by_cases h374 : i.val < 374
        ·
          by_cases h373 : i.val < 373
          ·
            have he : (⟨372, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 372 = i.val
              omega
            simpa only [he] using lower0372
          ·
            have he : (⟨373, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 373 = i.val
              omega
            simpa only [he] using lower0373
        ·
          by_cases h375 : i.val < 375
          ·
            have he : (⟨374, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 374 = i.val
              omega
            simpa only [he] using lower0374
          ·
            have he : (⟨375, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 375 = i.val
              omega
            simpa only [he] using lower0375
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
            simpa only [he] using lower0376
          ·
            have he : (⟨377, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 377 = i.val
              omega
            simpa only [he] using lower0377
        ·
          by_cases h379 : i.val < 379
          ·
            have he : (⟨378, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 378 = i.val
              omega
            simpa only [he] using lower0378
          ·
            have he : (⟨379, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 379 = i.val
              omega
            simpa only [he] using lower0379
      ·
        by_cases h382 : i.val < 382
        ·
          by_cases h381 : i.val < 381
          ·
            have he : (⟨380, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 380 = i.val
              omega
            simpa only [he] using lower0380
          ·
            have he : (⟨381, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 381 = i.val
              omega
            simpa only [he] using lower0381
        ·
          by_cases h383 : i.val < 383
          ·
            have he : (⟨382, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 382 = i.val
              omega
            simpa only [he] using lower0382
          ·
            have he : (⟨383, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 383 = i.val
              omega
            simpa only [he] using lower0383

private theorem lowerGroup0012 (i : Fin 1069)
    (hlo : 384 ≤ i.val) (hhi : i.val < 416) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0384
          ·
            have he : (⟨385, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 385 = i.val
              omega
            simpa only [he] using lower0385
        ·
          by_cases h387 : i.val < 387
          ·
            have he : (⟨386, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 386 = i.val
              omega
            simpa only [he] using lower0386
          ·
            have he : (⟨387, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 387 = i.val
              omega
            simpa only [he] using lower0387
      ·
        by_cases h390 : i.val < 390
        ·
          by_cases h389 : i.val < 389
          ·
            have he : (⟨388, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 388 = i.val
              omega
            simpa only [he] using lower0388
          ·
            have he : (⟨389, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 389 = i.val
              omega
            simpa only [he] using lower0389
        ·
          by_cases h391 : i.val < 391
          ·
            have he : (⟨390, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 390 = i.val
              omega
            simpa only [he] using lower0390
          ·
            have he : (⟨391, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 391 = i.val
              omega
            simpa only [he] using lower0391
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
            simpa only [he] using lower0392
          ·
            have he : (⟨393, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 393 = i.val
              omega
            simpa only [he] using lower0393
        ·
          by_cases h395 : i.val < 395
          ·
            have he : (⟨394, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 394 = i.val
              omega
            simpa only [he] using lower0394
          ·
            have he : (⟨395, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 395 = i.val
              omega
            simpa only [he] using lower0395
      ·
        by_cases h398 : i.val < 398
        ·
          by_cases h397 : i.val < 397
          ·
            have he : (⟨396, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 396 = i.val
              omega
            simpa only [he] using lower0396
          ·
            have he : (⟨397, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 397 = i.val
              omega
            simpa only [he] using lower0397
        ·
          by_cases h399 : i.val < 399
          ·
            have he : (⟨398, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 398 = i.val
              omega
            simpa only [he] using lower0398
          ·
            have he : (⟨399, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 399 = i.val
              omega
            simpa only [he] using lower0399
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
            simpa only [he] using lower0400
          ·
            have he : (⟨401, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 401 = i.val
              omega
            simpa only [he] using lower0401
        ·
          by_cases h403 : i.val < 403
          ·
            have he : (⟨402, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 402 = i.val
              omega
            simpa only [he] using lower0402
          ·
            have he : (⟨403, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 403 = i.val
              omega
            simpa only [he] using lower0403
      ·
        by_cases h406 : i.val < 406
        ·
          by_cases h405 : i.val < 405
          ·
            have he : (⟨404, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 404 = i.val
              omega
            simpa only [he] using lower0404
          ·
            have he : (⟨405, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 405 = i.val
              omega
            simpa only [he] using lower0405
        ·
          by_cases h407 : i.val < 407
          ·
            have he : (⟨406, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 406 = i.val
              omega
            simpa only [he] using lower0406
          ·
            have he : (⟨407, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 407 = i.val
              omega
            simpa only [he] using lower0407
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
            simpa only [he] using lower0408
          ·
            have he : (⟨409, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 409 = i.val
              omega
            simpa only [he] using lower0409
        ·
          by_cases h411 : i.val < 411
          ·
            have he : (⟨410, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 410 = i.val
              omega
            simpa only [he] using lower0410
          ·
            have he : (⟨411, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 411 = i.val
              omega
            simpa only [he] using lower0411
      ·
        by_cases h414 : i.val < 414
        ·
          by_cases h413 : i.val < 413
          ·
            have he : (⟨412, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 412 = i.val
              omega
            simpa only [he] using lower0412
          ·
            have he : (⟨413, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 413 = i.val
              omega
            simpa only [he] using lower0413
        ·
          by_cases h415 : i.val < 415
          ·
            have he : (⟨414, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 414 = i.val
              omega
            simpa only [he] using lower0414
          ·
            have he : (⟨415, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 415 = i.val
              omega
            simpa only [he] using lower0415

private theorem lowerGroup0013 (i : Fin 1069)
    (hlo : 416 ≤ i.val) (hhi : i.val < 448) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0416
          ·
            have he : (⟨417, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 417 = i.val
              omega
            simpa only [he] using lower0417
        ·
          by_cases h419 : i.val < 419
          ·
            have he : (⟨418, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 418 = i.val
              omega
            simpa only [he] using lower0418
          ·
            have he : (⟨419, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 419 = i.val
              omega
            simpa only [he] using lower0419
      ·
        by_cases h422 : i.val < 422
        ·
          by_cases h421 : i.val < 421
          ·
            have he : (⟨420, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 420 = i.val
              omega
            simpa only [he] using lower0420
          ·
            have he : (⟨421, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 421 = i.val
              omega
            simpa only [he] using lower0421
        ·
          by_cases h423 : i.val < 423
          ·
            have he : (⟨422, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 422 = i.val
              omega
            simpa only [he] using lower0422
          ·
            have he : (⟨423, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 423 = i.val
              omega
            simpa only [he] using lower0423
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
            simpa only [he] using lower0424
          ·
            have he : (⟨425, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 425 = i.val
              omega
            simpa only [he] using lower0425
        ·
          by_cases h427 : i.val < 427
          ·
            have he : (⟨426, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 426 = i.val
              omega
            simpa only [he] using lower0426
          ·
            have he : (⟨427, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 427 = i.val
              omega
            simpa only [he] using lower0427
      ·
        by_cases h430 : i.val < 430
        ·
          by_cases h429 : i.val < 429
          ·
            have he : (⟨428, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 428 = i.val
              omega
            simpa only [he] using lower0428
          ·
            have he : (⟨429, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 429 = i.val
              omega
            simpa only [he] using lower0429
        ·
          by_cases h431 : i.val < 431
          ·
            have he : (⟨430, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 430 = i.val
              omega
            simpa only [he] using lower0430
          ·
            have he : (⟨431, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 431 = i.val
              omega
            simpa only [he] using lower0431
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
            simpa only [he] using lower0432
          ·
            have he : (⟨433, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 433 = i.val
              omega
            simpa only [he] using lower0433
        ·
          by_cases h435 : i.val < 435
          ·
            have he : (⟨434, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 434 = i.val
              omega
            simpa only [he] using lower0434
          ·
            have he : (⟨435, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 435 = i.val
              omega
            simpa only [he] using lower0435
      ·
        by_cases h438 : i.val < 438
        ·
          by_cases h437 : i.val < 437
          ·
            have he : (⟨436, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 436 = i.val
              omega
            simpa only [he] using lower0436
          ·
            have he : (⟨437, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 437 = i.val
              omega
            simpa only [he] using lower0437
        ·
          by_cases h439 : i.val < 439
          ·
            have he : (⟨438, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 438 = i.val
              omega
            simpa only [he] using lower0438
          ·
            have he : (⟨439, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 439 = i.val
              omega
            simpa only [he] using lower0439
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
            simpa only [he] using lower0440
          ·
            have he : (⟨441, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 441 = i.val
              omega
            simpa only [he] using lower0441
        ·
          by_cases h443 : i.val < 443
          ·
            have he : (⟨442, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 442 = i.val
              omega
            simpa only [he] using lower0442
          ·
            have he : (⟨443, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 443 = i.val
              omega
            simpa only [he] using lower0443
      ·
        by_cases h446 : i.val < 446
        ·
          by_cases h445 : i.val < 445
          ·
            have he : (⟨444, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 444 = i.val
              omega
            simpa only [he] using lower0444
          ·
            have he : (⟨445, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 445 = i.val
              omega
            simpa only [he] using lower0445
        ·
          by_cases h447 : i.val < 447
          ·
            have he : (⟨446, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 446 = i.val
              omega
            simpa only [he] using lower0446
          ·
            have he : (⟨447, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 447 = i.val
              omega
            simpa only [he] using lower0447

private theorem lowerGroup0014 (i : Fin 1069)
    (hlo : 448 ≤ i.val) (hhi : i.val < 480) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0448
          ·
            have he : (⟨449, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 449 = i.val
              omega
            simpa only [he] using lower0449
        ·
          by_cases h451 : i.val < 451
          ·
            have he : (⟨450, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 450 = i.val
              omega
            simpa only [he] using lower0450
          ·
            have he : (⟨451, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 451 = i.val
              omega
            simpa only [he] using lower0451
      ·
        by_cases h454 : i.val < 454
        ·
          by_cases h453 : i.val < 453
          ·
            have he : (⟨452, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 452 = i.val
              omega
            simpa only [he] using lower0452
          ·
            have he : (⟨453, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 453 = i.val
              omega
            simpa only [he] using lower0453
        ·
          by_cases h455 : i.val < 455
          ·
            have he : (⟨454, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 454 = i.val
              omega
            simpa only [he] using lower0454
          ·
            have he : (⟨455, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 455 = i.val
              omega
            simpa only [he] using lower0455
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
            simpa only [he] using lower0456
          ·
            have he : (⟨457, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 457 = i.val
              omega
            simpa only [he] using lower0457
        ·
          by_cases h459 : i.val < 459
          ·
            have he : (⟨458, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 458 = i.val
              omega
            simpa only [he] using lower0458
          ·
            have he : (⟨459, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 459 = i.val
              omega
            simpa only [he] using lower0459
      ·
        by_cases h462 : i.val < 462
        ·
          by_cases h461 : i.val < 461
          ·
            have he : (⟨460, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 460 = i.val
              omega
            simpa only [he] using lower0460
          ·
            have he : (⟨461, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 461 = i.val
              omega
            simpa only [he] using lower0461
        ·
          by_cases h463 : i.val < 463
          ·
            have he : (⟨462, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 462 = i.val
              omega
            simpa only [he] using lower0462
          ·
            have he : (⟨463, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 463 = i.val
              omega
            simpa only [he] using lower0463
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
            simpa only [he] using lower0464
          ·
            have he : (⟨465, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 465 = i.val
              omega
            simpa only [he] using lower0465
        ·
          by_cases h467 : i.val < 467
          ·
            have he : (⟨466, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 466 = i.val
              omega
            simpa only [he] using lower0466
          ·
            have he : (⟨467, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 467 = i.val
              omega
            simpa only [he] using lower0467
      ·
        by_cases h470 : i.val < 470
        ·
          by_cases h469 : i.val < 469
          ·
            have he : (⟨468, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 468 = i.val
              omega
            simpa only [he] using lower0468
          ·
            have he : (⟨469, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 469 = i.val
              omega
            simpa only [he] using lower0469
        ·
          by_cases h471 : i.val < 471
          ·
            have he : (⟨470, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 470 = i.val
              omega
            simpa only [he] using lower0470
          ·
            have he : (⟨471, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 471 = i.val
              omega
            simpa only [he] using lower0471
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
            simpa only [he] using lower0472
          ·
            have he : (⟨473, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 473 = i.val
              omega
            simpa only [he] using lower0473
        ·
          by_cases h475 : i.val < 475
          ·
            have he : (⟨474, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 474 = i.val
              omega
            simpa only [he] using lower0474
          ·
            have he : (⟨475, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 475 = i.val
              omega
            simpa only [he] using lower0475
      ·
        by_cases h478 : i.val < 478
        ·
          by_cases h477 : i.val < 477
          ·
            have he : (⟨476, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 476 = i.val
              omega
            simpa only [he] using lower0476
          ·
            have he : (⟨477, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 477 = i.val
              omega
            simpa only [he] using lower0477
        ·
          by_cases h479 : i.val < 479
          ·
            have he : (⟨478, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 478 = i.val
              omega
            simpa only [he] using lower0478
          ·
            have he : (⟨479, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 479 = i.val
              omega
            simpa only [he] using lower0479

private theorem lowerGroup0015 (i : Fin 1069)
    (hlo : 480 ≤ i.val) (hhi : i.val < 512) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0480
          ·
            have he : (⟨481, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 481 = i.val
              omega
            simpa only [he] using lower0481
        ·
          by_cases h483 : i.val < 483
          ·
            have he : (⟨482, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 482 = i.val
              omega
            simpa only [he] using lower0482
          ·
            have he : (⟨483, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 483 = i.val
              omega
            simpa only [he] using lower0483
      ·
        by_cases h486 : i.val < 486
        ·
          by_cases h485 : i.val < 485
          ·
            have he : (⟨484, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 484 = i.val
              omega
            simpa only [he] using lower0484
          ·
            have he : (⟨485, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 485 = i.val
              omega
            simpa only [he] using lower0485
        ·
          by_cases h487 : i.val < 487
          ·
            have he : (⟨486, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 486 = i.val
              omega
            simpa only [he] using lower0486
          ·
            have he : (⟨487, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 487 = i.val
              omega
            simpa only [he] using lower0487
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
            simpa only [he] using lower0488
          ·
            have he : (⟨489, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 489 = i.val
              omega
            simpa only [he] using lower0489
        ·
          by_cases h491 : i.val < 491
          ·
            have he : (⟨490, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 490 = i.val
              omega
            simpa only [he] using lower0490
          ·
            have he : (⟨491, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 491 = i.val
              omega
            simpa only [he] using lower0491
      ·
        by_cases h494 : i.val < 494
        ·
          by_cases h493 : i.val < 493
          ·
            have he : (⟨492, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 492 = i.val
              omega
            simpa only [he] using lower0492
          ·
            have he : (⟨493, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 493 = i.val
              omega
            simpa only [he] using lower0493
        ·
          by_cases h495 : i.val < 495
          ·
            have he : (⟨494, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 494 = i.val
              omega
            simpa only [he] using lower0494
          ·
            have he : (⟨495, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 495 = i.val
              omega
            simpa only [he] using lower0495
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
            simpa only [he] using lower0496
          ·
            have he : (⟨497, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 497 = i.val
              omega
            simpa only [he] using lower0497
        ·
          by_cases h499 : i.val < 499
          ·
            have he : (⟨498, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 498 = i.val
              omega
            simpa only [he] using lower0498
          ·
            have he : (⟨499, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 499 = i.val
              omega
            simpa only [he] using lower0499
      ·
        by_cases h502 : i.val < 502
        ·
          by_cases h501 : i.val < 501
          ·
            have he : (⟨500, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 500 = i.val
              omega
            simpa only [he] using lower0500
          ·
            have he : (⟨501, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 501 = i.val
              omega
            simpa only [he] using lower0501
        ·
          by_cases h503 : i.val < 503
          ·
            have he : (⟨502, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 502 = i.val
              omega
            simpa only [he] using lower0502
          ·
            have he : (⟨503, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 503 = i.val
              omega
            simpa only [he] using lower0503
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
            simpa only [he] using lower0504
          ·
            have he : (⟨505, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 505 = i.val
              omega
            simpa only [he] using lower0505
        ·
          by_cases h507 : i.val < 507
          ·
            have he : (⟨506, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 506 = i.val
              omega
            simpa only [he] using lower0506
          ·
            have he : (⟨507, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 507 = i.val
              omega
            simpa only [he] using lower0507
      ·
        by_cases h510 : i.val < 510
        ·
          by_cases h509 : i.val < 509
          ·
            have he : (⟨508, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 508 = i.val
              omega
            simpa only [he] using lower0508
          ·
            have he : (⟨509, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 509 = i.val
              omega
            simpa only [he] using lower0509
        ·
          by_cases h511 : i.val < 511
          ·
            have he : (⟨510, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 510 = i.val
              omega
            simpa only [he] using lower0510
          ·
            have he : (⟨511, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 511 = i.val
              omega
            simpa only [he] using lower0511

private theorem lowerGroup0016 (i : Fin 1069)
    (hlo : 512 ≤ i.val) (hhi : i.val < 544) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0512
          ·
            have he : (⟨513, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 513 = i.val
              omega
            simpa only [he] using lower0513
        ·
          by_cases h515 : i.val < 515
          ·
            have he : (⟨514, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 514 = i.val
              omega
            simpa only [he] using lower0514
          ·
            have he : (⟨515, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 515 = i.val
              omega
            simpa only [he] using lower0515
      ·
        by_cases h518 : i.val < 518
        ·
          by_cases h517 : i.val < 517
          ·
            have he : (⟨516, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 516 = i.val
              omega
            simpa only [he] using lower0516
          ·
            have he : (⟨517, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 517 = i.val
              omega
            simpa only [he] using lower0517
        ·
          by_cases h519 : i.val < 519
          ·
            have he : (⟨518, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 518 = i.val
              omega
            simpa only [he] using lower0518
          ·
            have he : (⟨519, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 519 = i.val
              omega
            simpa only [he] using lower0519
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
            simpa only [he] using lower0520
          ·
            have he : (⟨521, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 521 = i.val
              omega
            simpa only [he] using lower0521
        ·
          by_cases h523 : i.val < 523
          ·
            have he : (⟨522, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 522 = i.val
              omega
            simpa only [he] using lower0522
          ·
            have he : (⟨523, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 523 = i.val
              omega
            simpa only [he] using lower0523
      ·
        by_cases h526 : i.val < 526
        ·
          by_cases h525 : i.val < 525
          ·
            have he : (⟨524, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 524 = i.val
              omega
            simpa only [he] using lower0524
          ·
            have he : (⟨525, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 525 = i.val
              omega
            simpa only [he] using lower0525
        ·
          by_cases h527 : i.val < 527
          ·
            have he : (⟨526, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 526 = i.val
              omega
            simpa only [he] using lower0526
          ·
            have he : (⟨527, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 527 = i.val
              omega
            simpa only [he] using lower0527
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
            simpa only [he] using lower0528
          ·
            have he : (⟨529, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 529 = i.val
              omega
            simpa only [he] using lower0529
        ·
          by_cases h531 : i.val < 531
          ·
            have he : (⟨530, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 530 = i.val
              omega
            simpa only [he] using lower0530
          ·
            have he : (⟨531, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 531 = i.val
              omega
            simpa only [he] using lower0531
      ·
        by_cases h534 : i.val < 534
        ·
          by_cases h533 : i.val < 533
          ·
            have he : (⟨532, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 532 = i.val
              omega
            simpa only [he] using lower0532
          ·
            have he : (⟨533, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 533 = i.val
              omega
            simpa only [he] using lower0533
        ·
          by_cases h535 : i.val < 535
          ·
            have he : (⟨534, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 534 = i.val
              omega
            simpa only [he] using lower0534
          ·
            have he : (⟨535, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 535 = i.val
              omega
            simpa only [he] using lower0535
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
            simpa only [he] using lower0536
          ·
            have he : (⟨537, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 537 = i.val
              omega
            simpa only [he] using lower0537
        ·
          by_cases h539 : i.val < 539
          ·
            have he : (⟨538, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 538 = i.val
              omega
            simpa only [he] using lower0538
          ·
            have he : (⟨539, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 539 = i.val
              omega
            simpa only [he] using lower0539
      ·
        by_cases h542 : i.val < 542
        ·
          by_cases h541 : i.val < 541
          ·
            have he : (⟨540, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 540 = i.val
              omega
            simpa only [he] using lower0540
          ·
            have he : (⟨541, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 541 = i.val
              omega
            simpa only [he] using lower0541
        ·
          by_cases h543 : i.val < 543
          ·
            have he : (⟨542, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 542 = i.val
              omega
            simpa only [he] using lower0542
          ·
            have he : (⟨543, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 543 = i.val
              omega
            simpa only [he] using lower0543

private theorem lowerGroup0017 (i : Fin 1069)
    (hlo : 544 ≤ i.val) (hhi : i.val < 576) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0544
          ·
            have he : (⟨545, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 545 = i.val
              omega
            simpa only [he] using lower0545
        ·
          by_cases h547 : i.val < 547
          ·
            have he : (⟨546, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 546 = i.val
              omega
            simpa only [he] using lower0546
          ·
            have he : (⟨547, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 547 = i.val
              omega
            simpa only [he] using lower0547
      ·
        by_cases h550 : i.val < 550
        ·
          by_cases h549 : i.val < 549
          ·
            have he : (⟨548, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 548 = i.val
              omega
            simpa only [he] using lower0548
          ·
            have he : (⟨549, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 549 = i.val
              omega
            simpa only [he] using lower0549
        ·
          by_cases h551 : i.val < 551
          ·
            have he : (⟨550, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 550 = i.val
              omega
            simpa only [he] using lower0550
          ·
            have he : (⟨551, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 551 = i.val
              omega
            simpa only [he] using lower0551
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
            simpa only [he] using lower0552
          ·
            have he : (⟨553, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 553 = i.val
              omega
            simpa only [he] using lower0553
        ·
          by_cases h555 : i.val < 555
          ·
            have he : (⟨554, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 554 = i.val
              omega
            simpa only [he] using lower0554
          ·
            have he : (⟨555, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 555 = i.val
              omega
            simpa only [he] using lower0555
      ·
        by_cases h558 : i.val < 558
        ·
          by_cases h557 : i.val < 557
          ·
            have he : (⟨556, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 556 = i.val
              omega
            simpa only [he] using lower0556
          ·
            have he : (⟨557, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 557 = i.val
              omega
            simpa only [he] using lower0557
        ·
          by_cases h559 : i.val < 559
          ·
            have he : (⟨558, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 558 = i.val
              omega
            simpa only [he] using lower0558
          ·
            have he : (⟨559, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 559 = i.val
              omega
            simpa only [he] using lower0559
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
            simpa only [he] using lower0560
          ·
            have he : (⟨561, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 561 = i.val
              omega
            simpa only [he] using lower0561
        ·
          by_cases h563 : i.val < 563
          ·
            have he : (⟨562, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 562 = i.val
              omega
            simpa only [he] using lower0562
          ·
            have he : (⟨563, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 563 = i.val
              omega
            simpa only [he] using lower0563
      ·
        by_cases h566 : i.val < 566
        ·
          by_cases h565 : i.val < 565
          ·
            have he : (⟨564, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 564 = i.val
              omega
            simpa only [he] using lower0564
          ·
            have he : (⟨565, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 565 = i.val
              omega
            simpa only [he] using lower0565
        ·
          by_cases h567 : i.val < 567
          ·
            have he : (⟨566, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 566 = i.val
              omega
            simpa only [he] using lower0566
          ·
            have he : (⟨567, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 567 = i.val
              omega
            simpa only [he] using lower0567
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
            simpa only [he] using lower0568
          ·
            have he : (⟨569, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 569 = i.val
              omega
            simpa only [he] using lower0569
        ·
          by_cases h571 : i.val < 571
          ·
            have he : (⟨570, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 570 = i.val
              omega
            simpa only [he] using lower0570
          ·
            have he : (⟨571, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 571 = i.val
              omega
            simpa only [he] using lower0571
      ·
        by_cases h574 : i.val < 574
        ·
          by_cases h573 : i.val < 573
          ·
            have he : (⟨572, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 572 = i.val
              omega
            simpa only [he] using lower0572
          ·
            have he : (⟨573, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 573 = i.val
              omega
            simpa only [he] using lower0573
        ·
          by_cases h575 : i.val < 575
          ·
            have he : (⟨574, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 574 = i.val
              omega
            simpa only [he] using lower0574
          ·
            have he : (⟨575, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 575 = i.val
              omega
            simpa only [he] using lower0575

private theorem lowerGroup0018 (i : Fin 1069)
    (hlo : 576 ≤ i.val) (hhi : i.val < 608) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0576
          ·
            have he : (⟨577, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 577 = i.val
              omega
            simpa only [he] using lower0577
        ·
          by_cases h579 : i.val < 579
          ·
            have he : (⟨578, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 578 = i.val
              omega
            simpa only [he] using lower0578
          ·
            have he : (⟨579, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 579 = i.val
              omega
            simpa only [he] using lower0579
      ·
        by_cases h582 : i.val < 582
        ·
          by_cases h581 : i.val < 581
          ·
            have he : (⟨580, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 580 = i.val
              omega
            simpa only [he] using lower0580
          ·
            have he : (⟨581, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 581 = i.val
              omega
            simpa only [he] using lower0581
        ·
          by_cases h583 : i.val < 583
          ·
            have he : (⟨582, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 582 = i.val
              omega
            simpa only [he] using lower0582
          ·
            have he : (⟨583, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 583 = i.val
              omega
            simpa only [he] using lower0583
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
            simpa only [he] using lower0584
          ·
            have he : (⟨585, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 585 = i.val
              omega
            simpa only [he] using lower0585
        ·
          by_cases h587 : i.val < 587
          ·
            have he : (⟨586, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 586 = i.val
              omega
            simpa only [he] using lower0586
          ·
            have he : (⟨587, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 587 = i.val
              omega
            simpa only [he] using lower0587
      ·
        by_cases h590 : i.val < 590
        ·
          by_cases h589 : i.val < 589
          ·
            have he : (⟨588, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 588 = i.val
              omega
            simpa only [he] using lower0588
          ·
            have he : (⟨589, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 589 = i.val
              omega
            simpa only [he] using lower0589
        ·
          by_cases h591 : i.val < 591
          ·
            have he : (⟨590, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 590 = i.val
              omega
            simpa only [he] using lower0590
          ·
            have he : (⟨591, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 591 = i.val
              omega
            simpa only [he] using lower0591
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
            simpa only [he] using lower0592
          ·
            have he : (⟨593, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 593 = i.val
              omega
            simpa only [he] using lower0593
        ·
          by_cases h595 : i.val < 595
          ·
            have he : (⟨594, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 594 = i.val
              omega
            simpa only [he] using lower0594
          ·
            have he : (⟨595, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 595 = i.val
              omega
            simpa only [he] using lower0595
      ·
        by_cases h598 : i.val < 598
        ·
          by_cases h597 : i.val < 597
          ·
            have he : (⟨596, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 596 = i.val
              omega
            simpa only [he] using lower0596
          ·
            have he : (⟨597, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 597 = i.val
              omega
            simpa only [he] using lower0597
        ·
          by_cases h599 : i.val < 599
          ·
            have he : (⟨598, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 598 = i.val
              omega
            simpa only [he] using lower0598
          ·
            have he : (⟨599, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 599 = i.val
              omega
            simpa only [he] using lower0599
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
            simpa only [he] using lower0600
          ·
            have he : (⟨601, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 601 = i.val
              omega
            simpa only [he] using lower0601
        ·
          by_cases h603 : i.val < 603
          ·
            have he : (⟨602, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 602 = i.val
              omega
            simpa only [he] using lower0602
          ·
            have he : (⟨603, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 603 = i.val
              omega
            simpa only [he] using lower0603
      ·
        by_cases h606 : i.val < 606
        ·
          by_cases h605 : i.val < 605
          ·
            have he : (⟨604, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 604 = i.val
              omega
            simpa only [he] using lower0604
          ·
            have he : (⟨605, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 605 = i.val
              omega
            simpa only [he] using lower0605
        ·
          by_cases h607 : i.val < 607
          ·
            have he : (⟨606, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 606 = i.val
              omega
            simpa only [he] using lower0606
          ·
            have he : (⟨607, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 607 = i.val
              omega
            simpa only [he] using lower0607

private theorem lowerGroup0019 (i : Fin 1069)
    (hlo : 608 ≤ i.val) (hhi : i.val < 640) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0608
          ·
            have he : (⟨609, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 609 = i.val
              omega
            simpa only [he] using lower0609
        ·
          by_cases h611 : i.val < 611
          ·
            have he : (⟨610, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 610 = i.val
              omega
            simpa only [he] using lower0610
          ·
            have he : (⟨611, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 611 = i.val
              omega
            simpa only [he] using lower0611
      ·
        by_cases h614 : i.val < 614
        ·
          by_cases h613 : i.val < 613
          ·
            have he : (⟨612, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 612 = i.val
              omega
            simpa only [he] using lower0612
          ·
            have he : (⟨613, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 613 = i.val
              omega
            simpa only [he] using lower0613
        ·
          by_cases h615 : i.val < 615
          ·
            have he : (⟨614, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 614 = i.val
              omega
            simpa only [he] using lower0614
          ·
            have he : (⟨615, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 615 = i.val
              omega
            simpa only [he] using lower0615
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
            simpa only [he] using lower0616
          ·
            have he : (⟨617, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 617 = i.val
              omega
            simpa only [he] using lower0617
        ·
          by_cases h619 : i.val < 619
          ·
            have he : (⟨618, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 618 = i.val
              omega
            simpa only [he] using lower0618
          ·
            have he : (⟨619, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 619 = i.val
              omega
            simpa only [he] using lower0619
      ·
        by_cases h622 : i.val < 622
        ·
          by_cases h621 : i.val < 621
          ·
            have he : (⟨620, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 620 = i.val
              omega
            simpa only [he] using lower0620
          ·
            have he : (⟨621, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 621 = i.val
              omega
            simpa only [he] using lower0621
        ·
          by_cases h623 : i.val < 623
          ·
            have he : (⟨622, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 622 = i.val
              omega
            simpa only [he] using lower0622
          ·
            have he : (⟨623, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 623 = i.val
              omega
            simpa only [he] using lower0623
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
            simpa only [he] using lower0624
          ·
            have he : (⟨625, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 625 = i.val
              omega
            simpa only [he] using lower0625
        ·
          by_cases h627 : i.val < 627
          ·
            have he : (⟨626, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 626 = i.val
              omega
            simpa only [he] using lower0626
          ·
            have he : (⟨627, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 627 = i.val
              omega
            simpa only [he] using lower0627
      ·
        by_cases h630 : i.val < 630
        ·
          by_cases h629 : i.val < 629
          ·
            have he : (⟨628, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 628 = i.val
              omega
            simpa only [he] using lower0628
          ·
            have he : (⟨629, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 629 = i.val
              omega
            simpa only [he] using lower0629
        ·
          by_cases h631 : i.val < 631
          ·
            have he : (⟨630, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 630 = i.val
              omega
            simpa only [he] using lower0630
          ·
            have he : (⟨631, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 631 = i.val
              omega
            simpa only [he] using lower0631
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
            simpa only [he] using lower0632
          ·
            have he : (⟨633, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 633 = i.val
              omega
            simpa only [he] using lower0633
        ·
          by_cases h635 : i.val < 635
          ·
            have he : (⟨634, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 634 = i.val
              omega
            simpa only [he] using lower0634
          ·
            have he : (⟨635, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 635 = i.val
              omega
            simpa only [he] using lower0635
      ·
        by_cases h638 : i.val < 638
        ·
          by_cases h637 : i.val < 637
          ·
            have he : (⟨636, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 636 = i.val
              omega
            simpa only [he] using lower0636
          ·
            have he : (⟨637, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 637 = i.val
              omega
            simpa only [he] using lower0637
        ·
          by_cases h639 : i.val < 639
          ·
            have he : (⟨638, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 638 = i.val
              omega
            simpa only [he] using lower0638
          ·
            have he : (⟨639, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 639 = i.val
              omega
            simpa only [he] using lower0639

private theorem lowerGroup0020 (i : Fin 1069)
    (hlo : 640 ≤ i.val) (hhi : i.val < 672) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0640
          ·
            have he : (⟨641, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 641 = i.val
              omega
            simpa only [he] using lower0641
        ·
          by_cases h643 : i.val < 643
          ·
            have he : (⟨642, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 642 = i.val
              omega
            simpa only [he] using lower0642
          ·
            have he : (⟨643, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 643 = i.val
              omega
            simpa only [he] using lower0643
      ·
        by_cases h646 : i.val < 646
        ·
          by_cases h645 : i.val < 645
          ·
            have he : (⟨644, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 644 = i.val
              omega
            simpa only [he] using lower0644
          ·
            have he : (⟨645, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 645 = i.val
              omega
            simpa only [he] using lower0645
        ·
          by_cases h647 : i.val < 647
          ·
            have he : (⟨646, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 646 = i.val
              omega
            simpa only [he] using lower0646
          ·
            have he : (⟨647, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 647 = i.val
              omega
            simpa only [he] using lower0647
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
            simpa only [he] using lower0648
          ·
            have he : (⟨649, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 649 = i.val
              omega
            simpa only [he] using lower0649
        ·
          by_cases h651 : i.val < 651
          ·
            have he : (⟨650, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 650 = i.val
              omega
            simpa only [he] using lower0650
          ·
            have he : (⟨651, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 651 = i.val
              omega
            simpa only [he] using lower0651
      ·
        by_cases h654 : i.val < 654
        ·
          by_cases h653 : i.val < 653
          ·
            have he : (⟨652, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 652 = i.val
              omega
            simpa only [he] using lower0652
          ·
            have he : (⟨653, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 653 = i.val
              omega
            simpa only [he] using lower0653
        ·
          by_cases h655 : i.val < 655
          ·
            have he : (⟨654, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 654 = i.val
              omega
            simpa only [he] using lower0654
          ·
            have he : (⟨655, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 655 = i.val
              omega
            simpa only [he] using lower0655
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
            simpa only [he] using lower0656
          ·
            have he : (⟨657, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 657 = i.val
              omega
            simpa only [he] using lower0657
        ·
          by_cases h659 : i.val < 659
          ·
            have he : (⟨658, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 658 = i.val
              omega
            simpa only [he] using lower0658
          ·
            have he : (⟨659, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 659 = i.val
              omega
            simpa only [he] using lower0659
      ·
        by_cases h662 : i.val < 662
        ·
          by_cases h661 : i.val < 661
          ·
            have he : (⟨660, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 660 = i.val
              omega
            simpa only [he] using lower0660
          ·
            have he : (⟨661, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 661 = i.val
              omega
            simpa only [he] using lower0661
        ·
          by_cases h663 : i.val < 663
          ·
            have he : (⟨662, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 662 = i.val
              omega
            simpa only [he] using lower0662
          ·
            have he : (⟨663, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 663 = i.val
              omega
            simpa only [he] using lower0663
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
            simpa only [he] using lower0664
          ·
            have he : (⟨665, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 665 = i.val
              omega
            simpa only [he] using lower0665
        ·
          by_cases h667 : i.val < 667
          ·
            have he : (⟨666, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 666 = i.val
              omega
            simpa only [he] using lower0666
          ·
            have he : (⟨667, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 667 = i.val
              omega
            simpa only [he] using lower0667
      ·
        by_cases h670 : i.val < 670
        ·
          by_cases h669 : i.val < 669
          ·
            have he : (⟨668, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 668 = i.val
              omega
            simpa only [he] using lower0668
          ·
            have he : (⟨669, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 669 = i.val
              omega
            simpa only [he] using lower0669
        ·
          by_cases h671 : i.val < 671
          ·
            have he : (⟨670, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 670 = i.val
              omega
            simpa only [he] using lower0670
          ·
            have he : (⟨671, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 671 = i.val
              omega
            simpa only [he] using lower0671

private theorem lowerGroup0021 (i : Fin 1069)
    (hlo : 672 ≤ i.val) (hhi : i.val < 704) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0672
          ·
            have he : (⟨673, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 673 = i.val
              omega
            simpa only [he] using lower0673
        ·
          by_cases h675 : i.val < 675
          ·
            have he : (⟨674, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 674 = i.val
              omega
            simpa only [he] using lower0674
          ·
            have he : (⟨675, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 675 = i.val
              omega
            simpa only [he] using lower0675
      ·
        by_cases h678 : i.val < 678
        ·
          by_cases h677 : i.val < 677
          ·
            have he : (⟨676, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 676 = i.val
              omega
            simpa only [he] using lower0676
          ·
            have he : (⟨677, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 677 = i.val
              omega
            simpa only [he] using lower0677
        ·
          by_cases h679 : i.val < 679
          ·
            have he : (⟨678, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 678 = i.val
              omega
            simpa only [he] using lower0678
          ·
            have he : (⟨679, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 679 = i.val
              omega
            simpa only [he] using lower0679
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
            simpa only [he] using lower0680
          ·
            have he : (⟨681, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 681 = i.val
              omega
            simpa only [he] using lower0681
        ·
          by_cases h683 : i.val < 683
          ·
            have he : (⟨682, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 682 = i.val
              omega
            simpa only [he] using lower0682
          ·
            have he : (⟨683, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 683 = i.val
              omega
            simpa only [he] using lower0683
      ·
        by_cases h686 : i.val < 686
        ·
          by_cases h685 : i.val < 685
          ·
            have he : (⟨684, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 684 = i.val
              omega
            simpa only [he] using lower0684
          ·
            have he : (⟨685, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 685 = i.val
              omega
            simpa only [he] using lower0685
        ·
          by_cases h687 : i.val < 687
          ·
            have he : (⟨686, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 686 = i.val
              omega
            simpa only [he] using lower0686
          ·
            have he : (⟨687, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 687 = i.val
              omega
            simpa only [he] using lower0687
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
            simpa only [he] using lower0688
          ·
            have he : (⟨689, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 689 = i.val
              omega
            simpa only [he] using lower0689
        ·
          by_cases h691 : i.val < 691
          ·
            have he : (⟨690, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 690 = i.val
              omega
            simpa only [he] using lower0690
          ·
            have he : (⟨691, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 691 = i.val
              omega
            simpa only [he] using lower0691
      ·
        by_cases h694 : i.val < 694
        ·
          by_cases h693 : i.val < 693
          ·
            have he : (⟨692, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 692 = i.val
              omega
            simpa only [he] using lower0692
          ·
            have he : (⟨693, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 693 = i.val
              omega
            simpa only [he] using lower0693
        ·
          by_cases h695 : i.val < 695
          ·
            have he : (⟨694, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 694 = i.val
              omega
            simpa only [he] using lower0694
          ·
            have he : (⟨695, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 695 = i.val
              omega
            simpa only [he] using lower0695
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
            simpa only [he] using lower0696
          ·
            have he : (⟨697, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 697 = i.val
              omega
            simpa only [he] using lower0697
        ·
          by_cases h699 : i.val < 699
          ·
            have he : (⟨698, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 698 = i.val
              omega
            simpa only [he] using lower0698
          ·
            have he : (⟨699, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 699 = i.val
              omega
            simpa only [he] using lower0699
      ·
        by_cases h702 : i.val < 702
        ·
          by_cases h701 : i.val < 701
          ·
            have he : (⟨700, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 700 = i.val
              omega
            simpa only [he] using lower0700
          ·
            have he : (⟨701, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 701 = i.val
              omega
            simpa only [he] using lower0701
        ·
          by_cases h703 : i.val < 703
          ·
            have he : (⟨702, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 702 = i.val
              omega
            simpa only [he] using lower0702
          ·
            have he : (⟨703, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 703 = i.val
              omega
            simpa only [he] using lower0703

private theorem lowerGroup0022 (i : Fin 1069)
    (hlo : 704 ≤ i.val) (hhi : i.val < 736) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0704
          ·
            have he : (⟨705, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 705 = i.val
              omega
            simpa only [he] using lower0705
        ·
          by_cases h707 : i.val < 707
          ·
            have he : (⟨706, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 706 = i.val
              omega
            simpa only [he] using lower0706
          ·
            have he : (⟨707, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 707 = i.val
              omega
            simpa only [he] using lower0707
      ·
        by_cases h710 : i.val < 710
        ·
          by_cases h709 : i.val < 709
          ·
            have he : (⟨708, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 708 = i.val
              omega
            simpa only [he] using lower0708
          ·
            have he : (⟨709, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 709 = i.val
              omega
            simpa only [he] using lower0709
        ·
          by_cases h711 : i.val < 711
          ·
            have he : (⟨710, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 710 = i.val
              omega
            simpa only [he] using lower0710
          ·
            have he : (⟨711, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 711 = i.val
              omega
            simpa only [he] using lower0711
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
            simpa only [he] using lower0712
          ·
            have he : (⟨713, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 713 = i.val
              omega
            simpa only [he] using lower0713
        ·
          by_cases h715 : i.val < 715
          ·
            have he : (⟨714, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 714 = i.val
              omega
            simpa only [he] using lower0714
          ·
            have he : (⟨715, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 715 = i.val
              omega
            simpa only [he] using lower0715
      ·
        by_cases h718 : i.val < 718
        ·
          by_cases h717 : i.val < 717
          ·
            have he : (⟨716, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 716 = i.val
              omega
            simpa only [he] using lower0716
          ·
            have he : (⟨717, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 717 = i.val
              omega
            simpa only [he] using lower0717
        ·
          by_cases h719 : i.val < 719
          ·
            have he : (⟨718, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 718 = i.val
              omega
            simpa only [he] using lower0718
          ·
            have he : (⟨719, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 719 = i.val
              omega
            simpa only [he] using lower0719
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
            simpa only [he] using lower0720
          ·
            have he : (⟨721, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 721 = i.val
              omega
            simpa only [he] using lower0721
        ·
          by_cases h723 : i.val < 723
          ·
            have he : (⟨722, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 722 = i.val
              omega
            simpa only [he] using lower0722
          ·
            have he : (⟨723, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 723 = i.val
              omega
            simpa only [he] using lower0723
      ·
        by_cases h726 : i.val < 726
        ·
          by_cases h725 : i.val < 725
          ·
            have he : (⟨724, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 724 = i.val
              omega
            simpa only [he] using lower0724
          ·
            have he : (⟨725, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 725 = i.val
              omega
            simpa only [he] using lower0725
        ·
          by_cases h727 : i.val < 727
          ·
            have he : (⟨726, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 726 = i.val
              omega
            simpa only [he] using lower0726
          ·
            have he : (⟨727, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 727 = i.val
              omega
            simpa only [he] using lower0727
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
            simpa only [he] using lower0728
          ·
            have he : (⟨729, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 729 = i.val
              omega
            simpa only [he] using lower0729
        ·
          by_cases h731 : i.val < 731
          ·
            have he : (⟨730, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 730 = i.val
              omega
            simpa only [he] using lower0730
          ·
            have he : (⟨731, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 731 = i.val
              omega
            simpa only [he] using lower0731
      ·
        by_cases h734 : i.val < 734
        ·
          by_cases h733 : i.val < 733
          ·
            have he : (⟨732, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 732 = i.val
              omega
            simpa only [he] using lower0732
          ·
            have he : (⟨733, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 733 = i.val
              omega
            simpa only [he] using lower0733
        ·
          by_cases h735 : i.val < 735
          ·
            have he : (⟨734, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 734 = i.val
              omega
            simpa only [he] using lower0734
          ·
            have he : (⟨735, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 735 = i.val
              omega
            simpa only [he] using lower0735

private theorem lowerGroup0023 (i : Fin 1069)
    (hlo : 736 ≤ i.val) (hhi : i.val < 768) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0736
          ·
            have he : (⟨737, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 737 = i.val
              omega
            simpa only [he] using lower0737
        ·
          by_cases h739 : i.val < 739
          ·
            have he : (⟨738, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 738 = i.val
              omega
            simpa only [he] using lower0738
          ·
            have he : (⟨739, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 739 = i.val
              omega
            simpa only [he] using lower0739
      ·
        by_cases h742 : i.val < 742
        ·
          by_cases h741 : i.val < 741
          ·
            have he : (⟨740, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 740 = i.val
              omega
            simpa only [he] using lower0740
          ·
            have he : (⟨741, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 741 = i.val
              omega
            simpa only [he] using lower0741
        ·
          by_cases h743 : i.val < 743
          ·
            have he : (⟨742, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 742 = i.val
              omega
            simpa only [he] using lower0742
          ·
            have he : (⟨743, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 743 = i.val
              omega
            simpa only [he] using lower0743
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
            simpa only [he] using lower0744
          ·
            have he : (⟨745, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 745 = i.val
              omega
            simpa only [he] using lower0745
        ·
          by_cases h747 : i.val < 747
          ·
            have he : (⟨746, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 746 = i.val
              omega
            simpa only [he] using lower0746
          ·
            have he : (⟨747, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 747 = i.val
              omega
            simpa only [he] using lower0747
      ·
        by_cases h750 : i.val < 750
        ·
          by_cases h749 : i.val < 749
          ·
            have he : (⟨748, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 748 = i.val
              omega
            simpa only [he] using lower0748
          ·
            have he : (⟨749, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 749 = i.val
              omega
            simpa only [he] using lower0749
        ·
          by_cases h751 : i.val < 751
          ·
            have he : (⟨750, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 750 = i.val
              omega
            simpa only [he] using lower0750
          ·
            have he : (⟨751, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 751 = i.val
              omega
            simpa only [he] using lower0751
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
            simpa only [he] using lower0752
          ·
            have he : (⟨753, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 753 = i.val
              omega
            simpa only [he] using lower0753
        ·
          by_cases h755 : i.val < 755
          ·
            have he : (⟨754, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 754 = i.val
              omega
            simpa only [he] using lower0754
          ·
            have he : (⟨755, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 755 = i.val
              omega
            simpa only [he] using lower0755
      ·
        by_cases h758 : i.val < 758
        ·
          by_cases h757 : i.val < 757
          ·
            have he : (⟨756, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 756 = i.val
              omega
            simpa only [he] using lower0756
          ·
            have he : (⟨757, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 757 = i.val
              omega
            simpa only [he] using lower0757
        ·
          by_cases h759 : i.val < 759
          ·
            have he : (⟨758, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 758 = i.val
              omega
            simpa only [he] using lower0758
          ·
            have he : (⟨759, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 759 = i.val
              omega
            simpa only [he] using lower0759
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
            simpa only [he] using lower0760
          ·
            have he : (⟨761, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 761 = i.val
              omega
            simpa only [he] using lower0761
        ·
          by_cases h763 : i.val < 763
          ·
            have he : (⟨762, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 762 = i.val
              omega
            simpa only [he] using lower0762
          ·
            have he : (⟨763, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 763 = i.val
              omega
            simpa only [he] using lower0763
      ·
        by_cases h766 : i.val < 766
        ·
          by_cases h765 : i.val < 765
          ·
            have he : (⟨764, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 764 = i.val
              omega
            simpa only [he] using lower0764
          ·
            have he : (⟨765, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 765 = i.val
              omega
            simpa only [he] using lower0765
        ·
          by_cases h767 : i.val < 767
          ·
            have he : (⟨766, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 766 = i.val
              omega
            simpa only [he] using lower0766
          ·
            have he : (⟨767, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 767 = i.val
              omega
            simpa only [he] using lower0767

private theorem lowerGroup0024 (i : Fin 1069)
    (hlo : 768 ≤ i.val) (hhi : i.val < 800) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0768
          ·
            have he : (⟨769, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 769 = i.val
              omega
            simpa only [he] using lower0769
        ·
          by_cases h771 : i.val < 771
          ·
            have he : (⟨770, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 770 = i.val
              omega
            simpa only [he] using lower0770
          ·
            have he : (⟨771, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 771 = i.val
              omega
            simpa only [he] using lower0771
      ·
        by_cases h774 : i.val < 774
        ·
          by_cases h773 : i.val < 773
          ·
            have he : (⟨772, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 772 = i.val
              omega
            simpa only [he] using lower0772
          ·
            have he : (⟨773, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 773 = i.val
              omega
            simpa only [he] using lower0773
        ·
          by_cases h775 : i.val < 775
          ·
            have he : (⟨774, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 774 = i.val
              omega
            simpa only [he] using lower0774
          ·
            have he : (⟨775, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 775 = i.val
              omega
            simpa only [he] using lower0775
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
            simpa only [he] using lower0776
          ·
            have he : (⟨777, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 777 = i.val
              omega
            simpa only [he] using lower0777
        ·
          by_cases h779 : i.val < 779
          ·
            have he : (⟨778, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 778 = i.val
              omega
            simpa only [he] using lower0778
          ·
            have he : (⟨779, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 779 = i.val
              omega
            simpa only [he] using lower0779
      ·
        by_cases h782 : i.val < 782
        ·
          by_cases h781 : i.val < 781
          ·
            have he : (⟨780, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 780 = i.val
              omega
            simpa only [he] using lower0780
          ·
            have he : (⟨781, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 781 = i.val
              omega
            simpa only [he] using lower0781
        ·
          by_cases h783 : i.val < 783
          ·
            have he : (⟨782, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 782 = i.val
              omega
            simpa only [he] using lower0782
          ·
            have he : (⟨783, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 783 = i.val
              omega
            simpa only [he] using lower0783
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
            simpa only [he] using lower0784
          ·
            have he : (⟨785, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 785 = i.val
              omega
            simpa only [he] using lower0785
        ·
          by_cases h787 : i.val < 787
          ·
            have he : (⟨786, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 786 = i.val
              omega
            simpa only [he] using lower0786
          ·
            have he : (⟨787, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 787 = i.val
              omega
            simpa only [he] using lower0787
      ·
        by_cases h790 : i.val < 790
        ·
          by_cases h789 : i.val < 789
          ·
            have he : (⟨788, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 788 = i.val
              omega
            simpa only [he] using lower0788
          ·
            have he : (⟨789, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 789 = i.val
              omega
            simpa only [he] using lower0789
        ·
          by_cases h791 : i.val < 791
          ·
            have he : (⟨790, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 790 = i.val
              omega
            simpa only [he] using lower0790
          ·
            have he : (⟨791, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 791 = i.val
              omega
            simpa only [he] using lower0791
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
            simpa only [he] using lower0792
          ·
            have he : (⟨793, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 793 = i.val
              omega
            simpa only [he] using lower0793
        ·
          by_cases h795 : i.val < 795
          ·
            have he : (⟨794, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 794 = i.val
              omega
            simpa only [he] using lower0794
          ·
            have he : (⟨795, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 795 = i.val
              omega
            simpa only [he] using lower0795
      ·
        by_cases h798 : i.val < 798
        ·
          by_cases h797 : i.val < 797
          ·
            have he : (⟨796, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 796 = i.val
              omega
            simpa only [he] using lower0796
          ·
            have he : (⟨797, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 797 = i.val
              omega
            simpa only [he] using lower0797
        ·
          by_cases h799 : i.val < 799
          ·
            have he : (⟨798, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 798 = i.val
              omega
            simpa only [he] using lower0798
          ·
            have he : (⟨799, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 799 = i.val
              omega
            simpa only [he] using lower0799

private theorem lowerGroup0025 (i : Fin 1069)
    (hlo : 800 ≤ i.val) (hhi : i.val < 832) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0800
          ·
            have he : (⟨801, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 801 = i.val
              omega
            simpa only [he] using lower0801
        ·
          by_cases h803 : i.val < 803
          ·
            have he : (⟨802, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 802 = i.val
              omega
            simpa only [he] using lower0802
          ·
            have he : (⟨803, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 803 = i.val
              omega
            simpa only [he] using lower0803
      ·
        by_cases h806 : i.val < 806
        ·
          by_cases h805 : i.val < 805
          ·
            have he : (⟨804, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 804 = i.val
              omega
            simpa only [he] using lower0804
          ·
            have he : (⟨805, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 805 = i.val
              omega
            simpa only [he] using lower0805
        ·
          by_cases h807 : i.val < 807
          ·
            have he : (⟨806, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 806 = i.val
              omega
            simpa only [he] using lower0806
          ·
            have he : (⟨807, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 807 = i.val
              omega
            simpa only [he] using lower0807
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
            simpa only [he] using lower0808
          ·
            have he : (⟨809, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 809 = i.val
              omega
            simpa only [he] using lower0809
        ·
          by_cases h811 : i.val < 811
          ·
            have he : (⟨810, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 810 = i.val
              omega
            simpa only [he] using lower0810
          ·
            have he : (⟨811, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 811 = i.val
              omega
            simpa only [he] using lower0811
      ·
        by_cases h814 : i.val < 814
        ·
          by_cases h813 : i.val < 813
          ·
            have he : (⟨812, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 812 = i.val
              omega
            simpa only [he] using lower0812
          ·
            have he : (⟨813, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 813 = i.val
              omega
            simpa only [he] using lower0813
        ·
          by_cases h815 : i.val < 815
          ·
            have he : (⟨814, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 814 = i.val
              omega
            simpa only [he] using lower0814
          ·
            have he : (⟨815, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 815 = i.val
              omega
            simpa only [he] using lower0815
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
            simpa only [he] using lower0816
          ·
            have he : (⟨817, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 817 = i.val
              omega
            simpa only [he] using lower0817
        ·
          by_cases h819 : i.val < 819
          ·
            have he : (⟨818, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 818 = i.val
              omega
            simpa only [he] using lower0818
          ·
            have he : (⟨819, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 819 = i.val
              omega
            simpa only [he] using lower0819
      ·
        by_cases h822 : i.val < 822
        ·
          by_cases h821 : i.val < 821
          ·
            have he : (⟨820, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 820 = i.val
              omega
            simpa only [he] using lower0820
          ·
            have he : (⟨821, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 821 = i.val
              omega
            simpa only [he] using lower0821
        ·
          by_cases h823 : i.val < 823
          ·
            have he : (⟨822, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 822 = i.val
              omega
            simpa only [he] using lower0822
          ·
            have he : (⟨823, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 823 = i.val
              omega
            simpa only [he] using lower0823
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
            simpa only [he] using lower0824
          ·
            have he : (⟨825, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 825 = i.val
              omega
            simpa only [he] using lower0825
        ·
          by_cases h827 : i.val < 827
          ·
            have he : (⟨826, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 826 = i.val
              omega
            simpa only [he] using lower0826
          ·
            have he : (⟨827, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 827 = i.val
              omega
            simpa only [he] using lower0827
      ·
        by_cases h830 : i.val < 830
        ·
          by_cases h829 : i.val < 829
          ·
            have he : (⟨828, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 828 = i.val
              omega
            simpa only [he] using lower0828
          ·
            have he : (⟨829, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 829 = i.val
              omega
            simpa only [he] using lower0829
        ·
          by_cases h831 : i.val < 831
          ·
            have he : (⟨830, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 830 = i.val
              omega
            simpa only [he] using lower0830
          ·
            have he : (⟨831, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 831 = i.val
              omega
            simpa only [he] using lower0831

private theorem lowerGroup0026 (i : Fin 1069)
    (hlo : 832 ≤ i.val) (hhi : i.val < 864) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0832
          ·
            have he : (⟨833, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 833 = i.val
              omega
            simpa only [he] using lower0833
        ·
          by_cases h835 : i.val < 835
          ·
            have he : (⟨834, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 834 = i.val
              omega
            simpa only [he] using lower0834
          ·
            have he : (⟨835, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 835 = i.val
              omega
            simpa only [he] using lower0835
      ·
        by_cases h838 : i.val < 838
        ·
          by_cases h837 : i.val < 837
          ·
            have he : (⟨836, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 836 = i.val
              omega
            simpa only [he] using lower0836
          ·
            have he : (⟨837, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 837 = i.val
              omega
            simpa only [he] using lower0837
        ·
          by_cases h839 : i.val < 839
          ·
            have he : (⟨838, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 838 = i.val
              omega
            simpa only [he] using lower0838
          ·
            have he : (⟨839, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 839 = i.val
              omega
            simpa only [he] using lower0839
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
            simpa only [he] using lower0840
          ·
            have he : (⟨841, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 841 = i.val
              omega
            simpa only [he] using lower0841
        ·
          by_cases h843 : i.val < 843
          ·
            have he : (⟨842, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 842 = i.val
              omega
            simpa only [he] using lower0842
          ·
            have he : (⟨843, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 843 = i.val
              omega
            simpa only [he] using lower0843
      ·
        by_cases h846 : i.val < 846
        ·
          by_cases h845 : i.val < 845
          ·
            have he : (⟨844, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 844 = i.val
              omega
            simpa only [he] using lower0844
          ·
            have he : (⟨845, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 845 = i.val
              omega
            simpa only [he] using lower0845
        ·
          by_cases h847 : i.val < 847
          ·
            have he : (⟨846, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 846 = i.val
              omega
            simpa only [he] using lower0846
          ·
            have he : (⟨847, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 847 = i.val
              omega
            simpa only [he] using lower0847
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
            simpa only [he] using lower0848
          ·
            have he : (⟨849, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 849 = i.val
              omega
            simpa only [he] using lower0849
        ·
          by_cases h851 : i.val < 851
          ·
            have he : (⟨850, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 850 = i.val
              omega
            simpa only [he] using lower0850
          ·
            have he : (⟨851, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 851 = i.val
              omega
            simpa only [he] using lower0851
      ·
        by_cases h854 : i.val < 854
        ·
          by_cases h853 : i.val < 853
          ·
            have he : (⟨852, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 852 = i.val
              omega
            simpa only [he] using lower0852
          ·
            have he : (⟨853, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 853 = i.val
              omega
            simpa only [he] using lower0853
        ·
          by_cases h855 : i.val < 855
          ·
            have he : (⟨854, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 854 = i.val
              omega
            simpa only [he] using lower0854
          ·
            have he : (⟨855, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 855 = i.val
              omega
            simpa only [he] using lower0855
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
            simpa only [he] using lower0856
          ·
            have he : (⟨857, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 857 = i.val
              omega
            simpa only [he] using lower0857
        ·
          by_cases h859 : i.val < 859
          ·
            have he : (⟨858, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 858 = i.val
              omega
            simpa only [he] using lower0858
          ·
            have he : (⟨859, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 859 = i.val
              omega
            simpa only [he] using lower0859
      ·
        by_cases h862 : i.val < 862
        ·
          by_cases h861 : i.val < 861
          ·
            have he : (⟨860, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 860 = i.val
              omega
            simpa only [he] using lower0860
          ·
            have he : (⟨861, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 861 = i.val
              omega
            simpa only [he] using lower0861
        ·
          by_cases h863 : i.val < 863
          ·
            have he : (⟨862, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 862 = i.val
              omega
            simpa only [he] using lower0862
          ·
            have he : (⟨863, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 863 = i.val
              omega
            simpa only [he] using lower0863

private theorem lowerGroup0027 (i : Fin 1069)
    (hlo : 864 ≤ i.val) (hhi : i.val < 896) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0864
          ·
            have he : (⟨865, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 865 = i.val
              omega
            simpa only [he] using lower0865
        ·
          by_cases h867 : i.val < 867
          ·
            have he : (⟨866, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 866 = i.val
              omega
            simpa only [he] using lower0866
          ·
            have he : (⟨867, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 867 = i.val
              omega
            simpa only [he] using lower0867
      ·
        by_cases h870 : i.val < 870
        ·
          by_cases h869 : i.val < 869
          ·
            have he : (⟨868, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 868 = i.val
              omega
            simpa only [he] using lower0868
          ·
            have he : (⟨869, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 869 = i.val
              omega
            simpa only [he] using lower0869
        ·
          by_cases h871 : i.val < 871
          ·
            have he : (⟨870, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 870 = i.val
              omega
            simpa only [he] using lower0870
          ·
            have he : (⟨871, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 871 = i.val
              omega
            simpa only [he] using lower0871
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
            simpa only [he] using lower0872
          ·
            have he : (⟨873, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 873 = i.val
              omega
            simpa only [he] using lower0873
        ·
          by_cases h875 : i.val < 875
          ·
            have he : (⟨874, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 874 = i.val
              omega
            simpa only [he] using lower0874
          ·
            have he : (⟨875, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 875 = i.val
              omega
            simpa only [he] using lower0875
      ·
        by_cases h878 : i.val < 878
        ·
          by_cases h877 : i.val < 877
          ·
            have he : (⟨876, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 876 = i.val
              omega
            simpa only [he] using lower0876
          ·
            have he : (⟨877, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 877 = i.val
              omega
            simpa only [he] using lower0877
        ·
          by_cases h879 : i.val < 879
          ·
            have he : (⟨878, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 878 = i.val
              omega
            simpa only [he] using lower0878
          ·
            have he : (⟨879, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 879 = i.val
              omega
            simpa only [he] using lower0879
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
            simpa only [he] using lower0880
          ·
            have he : (⟨881, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 881 = i.val
              omega
            simpa only [he] using lower0881
        ·
          by_cases h883 : i.val < 883
          ·
            have he : (⟨882, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 882 = i.val
              omega
            simpa only [he] using lower0882
          ·
            have he : (⟨883, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 883 = i.val
              omega
            simpa only [he] using lower0883
      ·
        by_cases h886 : i.val < 886
        ·
          by_cases h885 : i.val < 885
          ·
            have he : (⟨884, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 884 = i.val
              omega
            simpa only [he] using lower0884
          ·
            have he : (⟨885, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 885 = i.val
              omega
            simpa only [he] using lower0885
        ·
          by_cases h887 : i.val < 887
          ·
            have he : (⟨886, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 886 = i.val
              omega
            simpa only [he] using lower0886
          ·
            have he : (⟨887, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 887 = i.val
              omega
            simpa only [he] using lower0887
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
            simpa only [he] using lower0888
          ·
            have he : (⟨889, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 889 = i.val
              omega
            simpa only [he] using lower0889
        ·
          by_cases h891 : i.val < 891
          ·
            have he : (⟨890, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 890 = i.val
              omega
            simpa only [he] using lower0890
          ·
            have he : (⟨891, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 891 = i.val
              omega
            simpa only [he] using lower0891
      ·
        by_cases h894 : i.val < 894
        ·
          by_cases h893 : i.val < 893
          ·
            have he : (⟨892, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 892 = i.val
              omega
            simpa only [he] using lower0892
          ·
            have he : (⟨893, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 893 = i.val
              omega
            simpa only [he] using lower0893
        ·
          by_cases h895 : i.val < 895
          ·
            have he : (⟨894, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 894 = i.val
              omega
            simpa only [he] using lower0894
          ·
            have he : (⟨895, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 895 = i.val
              omega
            simpa only [he] using lower0895

private theorem lowerGroup0028 (i : Fin 1069)
    (hlo : 896 ≤ i.val) (hhi : i.val < 928) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0896
          ·
            have he : (⟨897, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 897 = i.val
              omega
            simpa only [he] using lower0897
        ·
          by_cases h899 : i.val < 899
          ·
            have he : (⟨898, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 898 = i.val
              omega
            simpa only [he] using lower0898
          ·
            have he : (⟨899, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 899 = i.val
              omega
            simpa only [he] using lower0899
      ·
        by_cases h902 : i.val < 902
        ·
          by_cases h901 : i.val < 901
          ·
            have he : (⟨900, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 900 = i.val
              omega
            simpa only [he] using lower0900
          ·
            have he : (⟨901, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 901 = i.val
              omega
            simpa only [he] using lower0901
        ·
          by_cases h903 : i.val < 903
          ·
            have he : (⟨902, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 902 = i.val
              omega
            simpa only [he] using lower0902
          ·
            have he : (⟨903, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 903 = i.val
              omega
            simpa only [he] using lower0903
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
            simpa only [he] using lower0904
          ·
            have he : (⟨905, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 905 = i.val
              omega
            simpa only [he] using lower0905
        ·
          by_cases h907 : i.val < 907
          ·
            have he : (⟨906, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 906 = i.val
              omega
            simpa only [he] using lower0906
          ·
            have he : (⟨907, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 907 = i.val
              omega
            simpa only [he] using lower0907
      ·
        by_cases h910 : i.val < 910
        ·
          by_cases h909 : i.val < 909
          ·
            have he : (⟨908, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 908 = i.val
              omega
            simpa only [he] using lower0908
          ·
            have he : (⟨909, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 909 = i.val
              omega
            simpa only [he] using lower0909
        ·
          by_cases h911 : i.val < 911
          ·
            have he : (⟨910, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 910 = i.val
              omega
            simpa only [he] using lower0910
          ·
            have he : (⟨911, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 911 = i.val
              omega
            simpa only [he] using lower0911
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
            simpa only [he] using lower0912
          ·
            have he : (⟨913, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 913 = i.val
              omega
            simpa only [he] using lower0913
        ·
          by_cases h915 : i.val < 915
          ·
            have he : (⟨914, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 914 = i.val
              omega
            simpa only [he] using lower0914
          ·
            have he : (⟨915, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 915 = i.val
              omega
            simpa only [he] using lower0915
      ·
        by_cases h918 : i.val < 918
        ·
          by_cases h917 : i.val < 917
          ·
            have he : (⟨916, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 916 = i.val
              omega
            simpa only [he] using lower0916
          ·
            have he : (⟨917, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 917 = i.val
              omega
            simpa only [he] using lower0917
        ·
          by_cases h919 : i.val < 919
          ·
            have he : (⟨918, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 918 = i.val
              omega
            simpa only [he] using lower0918
          ·
            have he : (⟨919, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 919 = i.val
              omega
            simpa only [he] using lower0919
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
            simpa only [he] using lower0920
          ·
            have he : (⟨921, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 921 = i.val
              omega
            simpa only [he] using lower0921
        ·
          by_cases h923 : i.val < 923
          ·
            have he : (⟨922, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 922 = i.val
              omega
            simpa only [he] using lower0922
          ·
            have he : (⟨923, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 923 = i.val
              omega
            simpa only [he] using lower0923
      ·
        by_cases h926 : i.val < 926
        ·
          by_cases h925 : i.val < 925
          ·
            have he : (⟨924, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 924 = i.val
              omega
            simpa only [he] using lower0924
          ·
            have he : (⟨925, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 925 = i.val
              omega
            simpa only [he] using lower0925
        ·
          by_cases h927 : i.val < 927
          ·
            have he : (⟨926, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 926 = i.val
              omega
            simpa only [he] using lower0926
          ·
            have he : (⟨927, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 927 = i.val
              omega
            simpa only [he] using lower0927

private theorem lowerGroup0029 (i : Fin 1069)
    (hlo : 928 ≤ i.val) (hhi : i.val < 960) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0928
          ·
            have he : (⟨929, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 929 = i.val
              omega
            simpa only [he] using lower0929
        ·
          by_cases h931 : i.val < 931
          ·
            have he : (⟨930, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 930 = i.val
              omega
            simpa only [he] using lower0930
          ·
            have he : (⟨931, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 931 = i.val
              omega
            simpa only [he] using lower0931
      ·
        by_cases h934 : i.val < 934
        ·
          by_cases h933 : i.val < 933
          ·
            have he : (⟨932, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 932 = i.val
              omega
            simpa only [he] using lower0932
          ·
            have he : (⟨933, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 933 = i.val
              omega
            simpa only [he] using lower0933
        ·
          by_cases h935 : i.val < 935
          ·
            have he : (⟨934, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 934 = i.val
              omega
            simpa only [he] using lower0934
          ·
            have he : (⟨935, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 935 = i.val
              omega
            simpa only [he] using lower0935
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
            simpa only [he] using lower0936
          ·
            have he : (⟨937, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 937 = i.val
              omega
            simpa only [he] using lower0937
        ·
          by_cases h939 : i.val < 939
          ·
            have he : (⟨938, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 938 = i.val
              omega
            simpa only [he] using lower0938
          ·
            have he : (⟨939, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 939 = i.val
              omega
            simpa only [he] using lower0939
      ·
        by_cases h942 : i.val < 942
        ·
          by_cases h941 : i.val < 941
          ·
            have he : (⟨940, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 940 = i.val
              omega
            simpa only [he] using lower0940
          ·
            have he : (⟨941, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 941 = i.val
              omega
            simpa only [he] using lower0941
        ·
          by_cases h943 : i.val < 943
          ·
            have he : (⟨942, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 942 = i.val
              omega
            simpa only [he] using lower0942
          ·
            have he : (⟨943, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 943 = i.val
              omega
            simpa only [he] using lower0943
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
            simpa only [he] using lower0944
          ·
            have he : (⟨945, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 945 = i.val
              omega
            simpa only [he] using lower0945
        ·
          by_cases h947 : i.val < 947
          ·
            have he : (⟨946, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 946 = i.val
              omega
            simpa only [he] using lower0946
          ·
            have he : (⟨947, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 947 = i.val
              omega
            simpa only [he] using lower0947
      ·
        by_cases h950 : i.val < 950
        ·
          by_cases h949 : i.val < 949
          ·
            have he : (⟨948, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 948 = i.val
              omega
            simpa only [he] using lower0948
          ·
            have he : (⟨949, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 949 = i.val
              omega
            simpa only [he] using lower0949
        ·
          by_cases h951 : i.val < 951
          ·
            have he : (⟨950, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 950 = i.val
              omega
            simpa only [he] using lower0950
          ·
            have he : (⟨951, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 951 = i.val
              omega
            simpa only [he] using lower0951
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
            simpa only [he] using lower0952
          ·
            have he : (⟨953, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 953 = i.val
              omega
            simpa only [he] using lower0953
        ·
          by_cases h955 : i.val < 955
          ·
            have he : (⟨954, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 954 = i.val
              omega
            simpa only [he] using lower0954
          ·
            have he : (⟨955, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 955 = i.val
              omega
            simpa only [he] using lower0955
      ·
        by_cases h958 : i.val < 958
        ·
          by_cases h957 : i.val < 957
          ·
            have he : (⟨956, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 956 = i.val
              omega
            simpa only [he] using lower0956
          ·
            have he : (⟨957, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 957 = i.val
              omega
            simpa only [he] using lower0957
        ·
          by_cases h959 : i.val < 959
          ·
            have he : (⟨958, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 958 = i.val
              omega
            simpa only [he] using lower0958
          ·
            have he : (⟨959, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 959 = i.val
              omega
            simpa only [he] using lower0959

private theorem lowerGroup0030 (i : Fin 1069)
    (hlo : 960 ≤ i.val) (hhi : i.val < 992) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0960
          ·
            have he : (⟨961, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 961 = i.val
              omega
            simpa only [he] using lower0961
        ·
          by_cases h963 : i.val < 963
          ·
            have he : (⟨962, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 962 = i.val
              omega
            simpa only [he] using lower0962
          ·
            have he : (⟨963, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 963 = i.val
              omega
            simpa only [he] using lower0963
      ·
        by_cases h966 : i.val < 966
        ·
          by_cases h965 : i.val < 965
          ·
            have he : (⟨964, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 964 = i.val
              omega
            simpa only [he] using lower0964
          ·
            have he : (⟨965, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 965 = i.val
              omega
            simpa only [he] using lower0965
        ·
          by_cases h967 : i.val < 967
          ·
            have he : (⟨966, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 966 = i.val
              omega
            simpa only [he] using lower0966
          ·
            have he : (⟨967, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 967 = i.val
              omega
            simpa only [he] using lower0967
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
            simpa only [he] using lower0968
          ·
            have he : (⟨969, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 969 = i.val
              omega
            simpa only [he] using lower0969
        ·
          by_cases h971 : i.val < 971
          ·
            have he : (⟨970, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 970 = i.val
              omega
            simpa only [he] using lower0970
          ·
            have he : (⟨971, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 971 = i.val
              omega
            simpa only [he] using lower0971
      ·
        by_cases h974 : i.val < 974
        ·
          by_cases h973 : i.val < 973
          ·
            have he : (⟨972, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 972 = i.val
              omega
            simpa only [he] using lower0972
          ·
            have he : (⟨973, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 973 = i.val
              omega
            simpa only [he] using lower0973
        ·
          by_cases h975 : i.val < 975
          ·
            have he : (⟨974, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 974 = i.val
              omega
            simpa only [he] using lower0974
          ·
            have he : (⟨975, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 975 = i.val
              omega
            simpa only [he] using lower0975
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
            simpa only [he] using lower0976
          ·
            have he : (⟨977, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 977 = i.val
              omega
            simpa only [he] using lower0977
        ·
          by_cases h979 : i.val < 979
          ·
            have he : (⟨978, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 978 = i.val
              omega
            simpa only [he] using lower0978
          ·
            have he : (⟨979, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 979 = i.val
              omega
            simpa only [he] using lower0979
      ·
        by_cases h982 : i.val < 982
        ·
          by_cases h981 : i.val < 981
          ·
            have he : (⟨980, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 980 = i.val
              omega
            simpa only [he] using lower0980
          ·
            have he : (⟨981, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 981 = i.val
              omega
            simpa only [he] using lower0981
        ·
          by_cases h983 : i.val < 983
          ·
            have he : (⟨982, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 982 = i.val
              omega
            simpa only [he] using lower0982
          ·
            have he : (⟨983, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 983 = i.val
              omega
            simpa only [he] using lower0983
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
            simpa only [he] using lower0984
          ·
            have he : (⟨985, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 985 = i.val
              omega
            simpa only [he] using lower0985
        ·
          by_cases h987 : i.val < 987
          ·
            have he : (⟨986, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 986 = i.val
              omega
            simpa only [he] using lower0986
          ·
            have he : (⟨987, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 987 = i.val
              omega
            simpa only [he] using lower0987
      ·
        by_cases h990 : i.val < 990
        ·
          by_cases h989 : i.val < 989
          ·
            have he : (⟨988, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 988 = i.val
              omega
            simpa only [he] using lower0988
          ·
            have he : (⟨989, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 989 = i.val
              omega
            simpa only [he] using lower0989
        ·
          by_cases h991 : i.val < 991
          ·
            have he : (⟨990, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 990 = i.val
              omega
            simpa only [he] using lower0990
          ·
            have he : (⟨991, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 991 = i.val
              omega
            simpa only [he] using lower0991

private theorem lowerGroup0031 (i : Fin 1069)
    (hlo : 992 ≤ i.val) (hhi : i.val < 1024) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower0992
          ·
            have he : (⟨993, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 993 = i.val
              omega
            simpa only [he] using lower0993
        ·
          by_cases h995 : i.val < 995
          ·
            have he : (⟨994, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 994 = i.val
              omega
            simpa only [he] using lower0994
          ·
            have he : (⟨995, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 995 = i.val
              omega
            simpa only [he] using lower0995
      ·
        by_cases h998 : i.val < 998
        ·
          by_cases h997 : i.val < 997
          ·
            have he : (⟨996, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 996 = i.val
              omega
            simpa only [he] using lower0996
          ·
            have he : (⟨997, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 997 = i.val
              omega
            simpa only [he] using lower0997
        ·
          by_cases h999 : i.val < 999
          ·
            have he : (⟨998, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 998 = i.val
              omega
            simpa only [he] using lower0998
          ·
            have he : (⟨999, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 999 = i.val
              omega
            simpa only [he] using lower0999
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
            simpa only [he] using lower1000
          ·
            have he : (⟨1001, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1001 = i.val
              omega
            simpa only [he] using lower1001
        ·
          by_cases h1003 : i.val < 1003
          ·
            have he : (⟨1002, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1002 = i.val
              omega
            simpa only [he] using lower1002
          ·
            have he : (⟨1003, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1003 = i.val
              omega
            simpa only [he] using lower1003
      ·
        by_cases h1006 : i.val < 1006
        ·
          by_cases h1005 : i.val < 1005
          ·
            have he : (⟨1004, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1004 = i.val
              omega
            simpa only [he] using lower1004
          ·
            have he : (⟨1005, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1005 = i.val
              omega
            simpa only [he] using lower1005
        ·
          by_cases h1007 : i.val < 1007
          ·
            have he : (⟨1006, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1006 = i.val
              omega
            simpa only [he] using lower1006
          ·
            have he : (⟨1007, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1007 = i.val
              omega
            simpa only [he] using lower1007
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
            simpa only [he] using lower1008
          ·
            have he : (⟨1009, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1009 = i.val
              omega
            simpa only [he] using lower1009
        ·
          by_cases h1011 : i.val < 1011
          ·
            have he : (⟨1010, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1010 = i.val
              omega
            simpa only [he] using lower1010
          ·
            have he : (⟨1011, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1011 = i.val
              omega
            simpa only [he] using lower1011
      ·
        by_cases h1014 : i.val < 1014
        ·
          by_cases h1013 : i.val < 1013
          ·
            have he : (⟨1012, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1012 = i.val
              omega
            simpa only [he] using lower1012
          ·
            have he : (⟨1013, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1013 = i.val
              omega
            simpa only [he] using lower1013
        ·
          by_cases h1015 : i.val < 1015
          ·
            have he : (⟨1014, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1014 = i.val
              omega
            simpa only [he] using lower1014
          ·
            have he : (⟨1015, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1015 = i.val
              omega
            simpa only [he] using lower1015
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
            simpa only [he] using lower1016
          ·
            have he : (⟨1017, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1017 = i.val
              omega
            simpa only [he] using lower1017
        ·
          by_cases h1019 : i.val < 1019
          ·
            have he : (⟨1018, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1018 = i.val
              omega
            simpa only [he] using lower1018
          ·
            have he : (⟨1019, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1019 = i.val
              omega
            simpa only [he] using lower1019
      ·
        by_cases h1022 : i.val < 1022
        ·
          by_cases h1021 : i.val < 1021
          ·
            have he : (⟨1020, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1020 = i.val
              omega
            simpa only [he] using lower1020
          ·
            have he : (⟨1021, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1021 = i.val
              omega
            simpa only [he] using lower1021
        ·
          by_cases h1023 : i.val < 1023
          ·
            have he : (⟨1022, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1022 = i.val
              omega
            simpa only [he] using lower1022
          ·
            have he : (⟨1023, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1023 = i.val
              omega
            simpa only [he] using lower1023

private theorem lowerGroup0032 (i : Fin 1069)
    (hlo : 1024 ≤ i.val) (hhi : i.val < 1056) :
    lowerComputed i = lowerFacets i := by
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
            simpa only [he] using lower1024
          ·
            have he : (⟨1025, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1025 = i.val
              omega
            simpa only [he] using lower1025
        ·
          by_cases h1027 : i.val < 1027
          ·
            have he : (⟨1026, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1026 = i.val
              omega
            simpa only [he] using lower1026
          ·
            have he : (⟨1027, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1027 = i.val
              omega
            simpa only [he] using lower1027
      ·
        by_cases h1030 : i.val < 1030
        ·
          by_cases h1029 : i.val < 1029
          ·
            have he : (⟨1028, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1028 = i.val
              omega
            simpa only [he] using lower1028
          ·
            have he : (⟨1029, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1029 = i.val
              omega
            simpa only [he] using lower1029
        ·
          by_cases h1031 : i.val < 1031
          ·
            have he : (⟨1030, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1030 = i.val
              omega
            simpa only [he] using lower1030
          ·
            have he : (⟨1031, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1031 = i.val
              omega
            simpa only [he] using lower1031
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
            simpa only [he] using lower1032
          ·
            have he : (⟨1033, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1033 = i.val
              omega
            simpa only [he] using lower1033
        ·
          by_cases h1035 : i.val < 1035
          ·
            have he : (⟨1034, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1034 = i.val
              omega
            simpa only [he] using lower1034
          ·
            have he : (⟨1035, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1035 = i.val
              omega
            simpa only [he] using lower1035
      ·
        by_cases h1038 : i.val < 1038
        ·
          by_cases h1037 : i.val < 1037
          ·
            have he : (⟨1036, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1036 = i.val
              omega
            simpa only [he] using lower1036
          ·
            have he : (⟨1037, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1037 = i.val
              omega
            simpa only [he] using lower1037
        ·
          by_cases h1039 : i.val < 1039
          ·
            have he : (⟨1038, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1038 = i.val
              omega
            simpa only [he] using lower1038
          ·
            have he : (⟨1039, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1039 = i.val
              omega
            simpa only [he] using lower1039
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
            simpa only [he] using lower1040
          ·
            have he : (⟨1041, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1041 = i.val
              omega
            simpa only [he] using lower1041
        ·
          by_cases h1043 : i.val < 1043
          ·
            have he : (⟨1042, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1042 = i.val
              omega
            simpa only [he] using lower1042
          ·
            have he : (⟨1043, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1043 = i.val
              omega
            simpa only [he] using lower1043
      ·
        by_cases h1046 : i.val < 1046
        ·
          by_cases h1045 : i.val < 1045
          ·
            have he : (⟨1044, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1044 = i.val
              omega
            simpa only [he] using lower1044
          ·
            have he : (⟨1045, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1045 = i.val
              omega
            simpa only [he] using lower1045
        ·
          by_cases h1047 : i.val < 1047
          ·
            have he : (⟨1046, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1046 = i.val
              omega
            simpa only [he] using lower1046
          ·
            have he : (⟨1047, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1047 = i.val
              omega
            simpa only [he] using lower1047
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
            simpa only [he] using lower1048
          ·
            have he : (⟨1049, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1049 = i.val
              omega
            simpa only [he] using lower1049
        ·
          by_cases h1051 : i.val < 1051
          ·
            have he : (⟨1050, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1050 = i.val
              omega
            simpa only [he] using lower1050
          ·
            have he : (⟨1051, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1051 = i.val
              omega
            simpa only [he] using lower1051
      ·
        by_cases h1054 : i.val < 1054
        ·
          by_cases h1053 : i.val < 1053
          ·
            have he : (⟨1052, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1052 = i.val
              omega
            simpa only [he] using lower1052
          ·
            have he : (⟨1053, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1053 = i.val
              omega
            simpa only [he] using lower1053
        ·
          by_cases h1055 : i.val < 1055
          ·
            have he : (⟨1054, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1054 = i.val
              omega
            simpa only [he] using lower1054
          ·
            have he : (⟨1055, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1055 = i.val
              omega
            simpa only [he] using lower1055

private theorem lowerGroup0033 (i : Fin 1069)
    (hlo : 1056 ≤ i.val) (hhi : i.val < 1069) :
    lowerComputed i = lowerFacets i := by
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
        simpa only [he] using lower1056
      ·
        by_cases h1058 : i.val < 1058
        ·
          have he : (⟨1057, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1057 = i.val
            omega
          simpa only [he] using lower1057
        ·
          have he : (⟨1058, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1058 = i.val
            omega
          simpa only [he] using lower1058
    ·
      by_cases h1060 : i.val < 1060
      ·
        have he : (⟨1059, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1059 = i.val
          omega
        simpa only [he] using lower1059
      ·
        by_cases h1061 : i.val < 1061
        ·
          have he : (⟨1060, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1060 = i.val
            omega
          simpa only [he] using lower1060
        ·
          have he : (⟨1061, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1061 = i.val
            omega
          simpa only [he] using lower1061
  ·
    by_cases h1065 : i.val < 1065
    ·
      by_cases h1063 : i.val < 1063
      ·
        have he : (⟨1062, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1062 = i.val
          omega
        simpa only [he] using lower1062
      ·
        by_cases h1064 : i.val < 1064
        ·
          have he : (⟨1063, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1063 = i.val
            omega
          simpa only [he] using lower1063
        ·
          have he : (⟨1064, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1064 = i.val
            omega
          simpa only [he] using lower1064
    ·
      by_cases h1067 : i.val < 1067
      ·
        by_cases h1066 : i.val < 1066
        ·
          have he : (⟨1065, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1065 = i.val
            omega
          simpa only [he] using lower1065
        ·
          have he : (⟨1066, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1066 = i.val
            omega
          simpa only [he] using lower1066
      ·
        by_cases h1068 : i.val < 1068
        ·
          have he : (⟨1067, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1067 = i.val
            omega
          simpa only [he] using lower1067
        ·
          have he : (1068 : Fin 1069) = i := by
            apply Fin.ext
            change 1068 = i.val
            omega
          simpa only [he] using lower1068

private theorem lowerComputed_eq : ∀ i : Fin 1069,
    lowerComputed i = lowerFacets i := by
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
            exact lowerGroup0000 i (by omega) (by omega)
          ·
            exact lowerGroup0001 i (by omega) (by omega)
        ·
          by_cases h96 : i.val < 96
          ·
            exact lowerGroup0002 i (by omega) (by omega)
          ·
            exact lowerGroup0003 i (by omega) (by omega)
      ·
        by_cases h192 : i.val < 192
        ·
          by_cases h160 : i.val < 160
          ·
            exact lowerGroup0004 i (by omega) (by omega)
          ·
            exact lowerGroup0005 i (by omega) (by omega)
        ·
          by_cases h224 : i.val < 224
          ·
            exact lowerGroup0006 i (by omega) (by omega)
          ·
            exact lowerGroup0007 i (by omega) (by omega)
    ·
      by_cases h384 : i.val < 384
      ·
        by_cases h320 : i.val < 320
        ·
          by_cases h288 : i.val < 288
          ·
            exact lowerGroup0008 i (by omega) (by omega)
          ·
            exact lowerGroup0009 i (by omega) (by omega)
        ·
          by_cases h352 : i.val < 352
          ·
            exact lowerGroup0010 i (by omega) (by omega)
          ·
            exact lowerGroup0011 i (by omega) (by omega)
      ·
        by_cases h448 : i.val < 448
        ·
          by_cases h416 : i.val < 416
          ·
            exact lowerGroup0012 i (by omega) (by omega)
          ·
            exact lowerGroup0013 i (by omega) (by omega)
        ·
          by_cases h480 : i.val < 480
          ·
            exact lowerGroup0014 i (by omega) (by omega)
          ·
            by_cases h512 : i.val < 512
            ·
              exact lowerGroup0015 i (by omega) (by omega)
            ·
              exact lowerGroup0016 i (by omega) (by omega)
  ·
    by_cases h800 : i.val < 800
    ·
      by_cases h672 : i.val < 672
      ·
        by_cases h608 : i.val < 608
        ·
          by_cases h576 : i.val < 576
          ·
            exact lowerGroup0017 i (by omega) (by omega)
          ·
            exact lowerGroup0018 i (by omega) (by omega)
        ·
          by_cases h640 : i.val < 640
          ·
            exact lowerGroup0019 i (by omega) (by omega)
          ·
            exact lowerGroup0020 i (by omega) (by omega)
      ·
        by_cases h736 : i.val < 736
        ·
          by_cases h704 : i.val < 704
          ·
            exact lowerGroup0021 i (by omega) (by omega)
          ·
            exact lowerGroup0022 i (by omega) (by omega)
        ·
          by_cases h768 : i.val < 768
          ·
            exact lowerGroup0023 i (by omega) (by omega)
          ·
            exact lowerGroup0024 i (by omega) (by omega)
    ·
      by_cases h928 : i.val < 928
      ·
        by_cases h864 : i.val < 864
        ·
          by_cases h832 : i.val < 832
          ·
            exact lowerGroup0025 i (by omega) (by omega)
          ·
            exact lowerGroup0026 i (by omega) (by omega)
        ·
          by_cases h896 : i.val < 896
          ·
            exact lowerGroup0027 i (by omega) (by omega)
          ·
            exact lowerGroup0028 i (by omega) (by omega)
      ·
        by_cases h992 : i.val < 992
        ·
          by_cases h960 : i.val < 960
          ·
            exact lowerGroup0029 i (by omega) (by omega)
          ·
            exact lowerGroup0030 i (by omega) (by omega)
        ·
          by_cases h1024 : i.val < 1024
          ·
            exact lowerGroup0031 i (by omega) (by omega)
          ·
            by_cases h1056 : i.val < 1056
            ·
              exact lowerGroup0032 i (by omega) (by omega)
            ·
              exact lowerGroup0033 i (by omega) (by omega)

/-- The table lists precisely the contained faces of the preceding rank. -/
theorem lowerFacets_iff : ∀ (i j : Fin 1069),
    j ∈ lowerFacets i ↔
      (faceRank j).val + 1 = (faceRank i).val ∧ faceMask j ⊆ faceMask i := by
  intro i j
  rw [← lowerComputed_eq i]
  change j ∈ (lowerCandidates i).filter _ ↔ _
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have hr : faceRank j = previousRank i := by
      apply Fin.ext
      change (faceRank j).val = (faceRank i).val - 1
      omega
    have ha : faceAnchor j ∈ faceMask i := h.2 (faceAnchor_mem j)
    have hb := anchoredFaces_self j
    rw [hr] at hb
    exact Finset.mem_biUnion.mpr ⟨faceAnchor j, ha, hb⟩

end CubicalIndecomposability
