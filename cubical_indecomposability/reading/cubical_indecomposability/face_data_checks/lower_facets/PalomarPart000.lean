module

public import cubical_indecomposability.face_data_checks.anchors
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Fin
public import Lean.Elab.Tactic.Omega

@[expose] public section

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

end CubicalIndecomposability
