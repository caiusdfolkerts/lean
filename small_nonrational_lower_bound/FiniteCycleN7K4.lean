module

public import FiniteCycleData7
public import FiniteInjectionWitnessChecks

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FiniteCycleCandidates.N7
open MatroidChecked

noncomputable def coverageTable4 : LiteralLookup ℕ := (.node 480 (.node 276 (.node 164 (.node 106 (.node 68 (.node 34 (.node 27 (.node 25 (.node 24 (.leaf 0) (.leaf 35)) (.node 26 (.leaf 36) (.leaf 38))) (.node 31 (.node 28 (.leaf 40) (.leaf 0)) (.node 32 (.leaf 37) (.node 33 (.leaf 41) (.leaf 42))))) (.node 40 (.node 38 (.node 35 (.leaf 44) (.leaf 0)) (.node 39 (.leaf 39) (.leaf 43))) (.node 42 (.node 41 (.leaf 45) (.leaf 46)) (.node 66 (.leaf 0) (.node 67 (.leaf 36) (.leaf 35)))))) (.node 81 (.node 74 (.node 70 (.node 69 (.leaf 37) (.leaf 39)) (.node 73 (.leaf 0) (.leaf 38))) (.node 76 (.node 75 (.leaf 42) (.leaf 41)) (.node 77 (.leaf 43) (.node 80 (.leaf 0) (.leaf 40))))) (.node 98 (.node 83 (.node 82 (.leaf 44) (.leaf 46)) (.node 84 (.leaf 45) (.leaf 0))) (.node 100 (.node 99 (.leaf 36) (.leaf 35)) (.node 101 (.leaf 47) (.node 105 (.leaf 0) (.leaf 35))))))) (.node 140 (.node 117 (.node 111 (.node 109 (.node 107 (.leaf 36) (.leaf 48)) (.node 110 (.leaf 47) (.leaf 49))) (.node 113 (.node 112 (.leaf 51) (.leaf 37)) (.node 114 (.leaf 38) (.node 116 (.leaf 50) (.leaf 54))))) (.node 121 (.node 119 (.node 118 (.leaf 53) (.leaf 55)) (.node 120 (.leaf 39) (.leaf 40))) (.node 124 (.node 123 (.leaf 52) (.leaf 56)) (.node 125 (.leaf 58) (.node 126 (.leaf 57) (.leaf 0)))))) (.node 153 (.node 147 (.node 142 (.node 141 (.leaf 38) (.leaf 37)) (.node 143 (.leaf 49) (.leaf 0))) (.node 149 (.node 148 (.leaf 42) (.leaf 41)) (.node 150 (.leaf 53) (.node 151 (.leaf 59) (.leaf 61))))) (.node 159 (.node 155 (.node 154 (.leaf 64) (.leaf 41)) (.node 156 (.leaf 42) (.node 157 (.leaf 54) (.leaf 60)))) (.node 161 (.node 160 (.leaf 59) (.leaf 62)) (.node 162 (.leaf 43) (.node 163 (.leaf 44) (.leaf 56)))))))) (.node 227 (.node 200 (.node 190 (.node 182 (.node 167 (.node 166 (.leaf 63) (.leaf 66)) (.node 168 (.leaf 65) (.leaf 0))) (.node 184 (.node 183 (.leaf 40) (.leaf 39)) (.node 185 (.leaf 51) (.node 189 (.leaf 0) (.leaf 44))))) (.node 194 (.node 192 (.node 191 (.leaf 43) (.leaf 55)) (.node 193 (.leaf 62) (.leaf 64))) (.node 197 (.node 196 (.leaf 67) (.leaf 46)) (.node 198 (.leaf 45) (.node 199 (.leaf 57) (.leaf 65)))))) (.node 213 (.node 205 (.node 203 (.node 201 (.leaf 68) (.leaf 70)) (.node 204 (.leaf 45) (.leaf 46))) (.node 207 (.node 206 (.leaf 58) (.leaf 66)) (.node 209 (.leaf 69) (.node 210 (.leaf 68) (.leaf 0))))) (.node 220 (.node 215 (.node 214 (.leaf 36) (.leaf 35)) (.node 216 (.leaf 37) (.node 217 (.leaf 39) (.leaf 0)))) (.node 222 (.node 221 (.leaf 35) (.leaf 36)) (.node 223 (.leaf 38) (.node 224 (.leaf 40) (.leaf 0))))))) (.node 251 (.node 238 (.node 231 (.node 229 (.node 228 (.leaf 47) (.leaf 48)) (.node 230 (.leaf 50) (.leaf 52))) (.node 235 (.node 234 (.leaf 0) (.leaf 47)) (.node 236 (.leaf 48) (.node 237 (.leaf 50) (.leaf 52))))) (.node 244 (.node 242 (.node 241 (.leaf 0) (.leaf 49)) (.node 243 (.leaf 53) (.leaf 54))) (.node 248 (.node 245 (.leaf 56) (.leaf 0)) (.node 249 (.leaf 51) (.node 250 (.leaf 55) (.leaf 57)))))) (.node 261 (.node 256 (.node 253 (.node 252 (.leaf 58) (.leaf 35)) (.node 254 (.leaf 36) (.leaf 48))) (.node 258 (.node 257 (.leaf 47) (.leaf 49)) (.node 259 (.leaf 51) (.node 260 (.leaf 47) (.leaf 71))))) (.node 269 (.node 264 (.node 263 (.leaf 72) (.leaf 71)) (.node 265 (.leaf 73) (.node 266 (.leaf 75) (.leaf 0)))) (.node 271 (.node 270 (.leaf 71) (.leaf 72)) (.node 272 (.leaf 74) (.node 273 (.leaf 76) (.leaf 0))))))))) (.node 378 (.node 328 (.node 301 (.node 287 (.node 280 (.node 278 (.node 277 (.leaf 71) (.leaf 72)) (.node 279 (.leaf 74) (.leaf 76))) (.node 284 (.node 283 (.leaf 0) (.leaf 73)) (.node 285 (.leaf 77) (.node 286 (.leaf 78) (.leaf 80))))) (.node 293 (.node 291 (.node 290 (.leaf 0) (.leaf 75)) (.node 292 (.leaf 79) (.leaf 81))) (.node 295 (.node 294 (.leaf 82) (.leaf 36)) (.node 296 (.leaf 35) (.node 297 (.leaf 47) (.leaf 0)))))) (.node 316 (.node 308 (.node 303 (.node 302 (.leaf 48) (.leaf 72)) (.node 304 (.leaf 71) (.leaf 0))) (.node 310 (.node 309 (.leaf 48) (.leaf 72)) (.node 311 (.leaf 71) (.node 315 (.leaf 0) (.leaf 47))))) (.node 322 (.node 319 (.node 317 (.leaf 71) (.leaf 72)) (.node 320 (.leaf 71) (.node 321 (.leaf 73) (.leaf 75)))) (.node 324 (.node 323 (.leaf 49) (.leaf 73)) (.node 326 (.leaf 74) (.node 327 (.leaf 78) (.leaf 77))))))) (.node 353 (.node 338 (.node 333 (.node 330 (.node 329 (.leaf 79) (.leaf 51)) (.node 331 (.leaf 75) (.leaf 76))) (.node 335 (.node 334 (.leaf 80) (.leaf 82)) (.node 336 (.leaf 81) (.node 337 (.leaf 38) (.leaf 37))))) (.node 345 (.node 343 (.node 339 (.leaf 49) (.leaf 0)) (.node 344 (.leaf 50) (.leaf 74))) (.node 350 (.node 346 (.leaf 73) (.leaf 0)) (.node 351 (.leaf 50) (.node 352 (.leaf 74) (.leaf 73)))))) (.node 366 (.node 360 (.node 358 (.node 357 (.leaf 0) (.leaf 54)) (.node 359 (.leaf 78) (.leaf 77))) (.node 363 (.node 361 (.leaf 83) (.leaf 85)) (.node 364 (.leaf 88) (.node 365 (.leaf 53) (.leaf 77))))) (.node 372 (.node 369 (.node 367 (.leaf 78) (.leaf 84)) (.node 370 (.leaf 83) (.node 371 (.leaf 86) (.leaf 55)))) (.node 374 (.node 373 (.leaf 79) (.leaf 80)) (.node 376 (.leaf 87) (.node 377 (.leaf 90) (.leaf 89)))))))) (.node 431 (.node 406 (.node 393 (.node 385 (.node 380 (.node 379 (.leaf 40) (.leaf 39)) (.node 381 (.leaf 51) (.leaf 0))) (.node 387 (.node 386 (.leaf 52) (.leaf 76)) (.node 388 (.leaf 75) (.node 392 (.leaf 0) (.leaf 52))))) (.node 400 (.node 395 (.node 394 (.leaf 76) (.leaf 75)) (.node 399 (.leaf 0) (.leaf 56))) (.node 402 (.node 401 (.leaf 80) (.leaf 79)) (.node 403 (.leaf 86) (.node 404 (.leaf 88) (.leaf 91)))))) (.node 416 (.node 410 (.node 408 (.node 407 (.leaf 58) (.leaf 82)) (.node 409 (.leaf 81) (.leaf 89))) (.node 413 (.node 411 (.leaf 92) (.leaf 94)) (.node 414 (.leaf 57) (.node 415 (.leaf 81) (.leaf 82))))) (.node 424 (.node 419 (.node 417 (.leaf 90) (.leaf 93)) (.node 420 (.leaf 92) (.node 423 (.leaf 0) (.leaf 38)))) (.node 426 (.node 425 (.leaf 42) (.leaf 41)) (.node 427 (.leaf 43) (.node 430 (.leaf 0) (.leaf 37))))))) (.node 455 (.node 444 (.node 437 (.node 433 (.node 432 (.leaf 41) (.leaf 42)) (.node 434 (.leaf 44) (.leaf 0))) (.node 439 (.node 438 (.leaf 49) (.leaf 53)) (.node 440 (.leaf 54) (.node 441 (.leaf 56) (.leaf 0))))) (.node 448 (.node 446 (.node 445 (.leaf 61) (.leaf 59)) (.node 447 (.leaf 60) (.leaf 63))) (.node 452 (.node 451 (.leaf 0) (.leaf 61)) (.node 453 (.leaf 59) (.node 454 (.leaf 60) (.leaf 63)))))) (.node 467 (.node 461 (.node 459 (.node 458 (.leaf 0) (.leaf 64)) (.node 460 (.leaf 62) (.leaf 65))) (.node 463 (.node 462 (.leaf 66) (.leaf 37)) (.node 464 (.leaf 38) (.node 466 (.leaf 50) (.leaf 54))))) (.node 473 (.node 469 (.node 468 (.leaf 53) (.leaf 55)) (.node 470 (.leaf 49) (.node 471 (.leaf 73) (.leaf 74)))) (.node 475 (.node 474 (.leaf 78) (.leaf 77)) (.node 476 (.leaf 79) (.node 479 (.leaf 0) (.leaf 73)))))))))) (.node 662 (.node 569 (.node 526 (.node 504 (.node 493 (.node 486 (.node 482 (.node 481 (.leaf 77) (.leaf 78)) (.node 483 (.leaf 80) (.leaf 0))) (.node 488 (.node 487 (.leaf 85) (.leaf 83)) (.node 489 (.leaf 84) (.node 490 (.leaf 87) (.leaf 0))))) (.node 497 (.node 495 (.node 494 (.leaf 85) (.leaf 83)) (.node 496 (.leaf 84) (.leaf 87))) (.node 501 (.node 500 (.leaf 0) (.leaf 88)) (.node 502 (.leaf 86) (.node 503 (.leaf 89) (.leaf 90)))))) (.node 514 (.node 509 (.node 506 (.node 505 (.leaf 41) (.leaf 42)) (.node 507 (.leaf 54) (.leaf 60))) (.node 511 (.node 510 (.leaf 59) (.leaf 62)) (.node 512 (.leaf 53) (.node 513 (.leaf 77) (.leaf 78))))) (.node 520 (.node 517 (.node 516 (.leaf 84) (.leaf 83)) (.node 518 (.leaf 86) (.node 519 (.leaf 59) (.leaf 83)))) (.node 523 (.node 521 (.leaf 95) (.leaf 96)) (.node 524 (.leaf 95) (.node 525 (.leaf 98) (.leaf 61))))))) (.node 547 (.node 537 (.node 531 (.node 529 (.node 527 (.leaf 85) (.leaf 97)) (.node 530 (.leaf 95) (.leaf 96))) (.node 533 (.node 532 (.leaf 99) (.leaf 61)) (.node 534 (.leaf 85) (.node 536 (.leaf 97) (.leaf 95))))) (.node 541 (.node 539 (.node 538 (.leaf 96) (.leaf 99)) (.node 540 (.leaf 64) (.leaf 88))) (.node 544 (.node 543 (.leaf 100) (.leaf 98)) (.node 545 (.leaf 101) (.node 546 (.leaf 102) (.leaf 42)))))) (.node 557 (.node 552 (.node 549 (.node 548 (.leaf 41) (.leaf 53)) (.node 550 (.leaf 59) (.leaf 61))) (.node 554 (.node 553 (.leaf 64) (.leaf 54)) (.node 555 (.leaf 78) (.node 556 (.leaf 77) (.leaf 83))))) (.node 563 (.node 560 (.node 559 (.leaf 85) (.leaf 88)) (.node 561 (.leaf 60) (.node 562 (.leaf 84) (.leaf 96)))) (.node 566 (.node 564 (.leaf 95) (.leaf 97)) (.node 567 (.leaf 100) (.node 568 (.leaf 60) (.leaf 84)))))))) (.node 612 (.node 590 (.node 580 (.node 574 (.node 571 (.node 570 (.leaf 96) (.leaf 95)) (.node 573 (.leaf 97) (.leaf 100))) (.node 576 (.node 575 (.leaf 59) (.leaf 83)) (.node 577 (.leaf 95) (.node 579 (.leaf 96) (.leaf 95))))) (.node 584 (.node 582 (.node 581 (.leaf 98) (.leaf 62)) (.node 583 (.leaf 86) (.leaf 98))) (.node 587 (.node 586 (.leaf 99) (.leaf 102)) (.node 588 (.leaf 101) (.node 589 (.leaf 44) (.leaf 43)))))) (.node 600 (.node 595 (.node 592 (.node 591 (.leaf 55) (.leaf 62)) (.node 593 (.leaf 64) (.leaf 67))) (.node 597 (.node 596 (.leaf 56) (.leaf 80)) (.node 598 (.leaf 79) (.node 599 (.leaf 86) (.leaf 88))))) (.node 606 (.node 603 (.node 602 (.leaf 91) (.leaf 63)) (.node 604 (.leaf 87) (.node 605 (.leaf 99) (.leaf 98)))) (.node 609 (.node 607 (.leaf 100) (.leaf 103)) (.node 610 (.leaf 63) (.node 611 (.leaf 87) (.leaf 99))))))) (.node 635 (.node 623 (.node 617 (.node 614 (.node 613 (.leaf 98) (.leaf 100)) (.node 616 (.leaf 103) (.leaf 66))) (.node 619 (.node 618 (.leaf 90) (.leaf 102)) (.node 620 (.leaf 101) (.node 621 (.leaf 104) (.leaf 106))))) (.node 627 (.node 625 (.node 624 (.leaf 65) (.leaf 89)) (.node 626 (.leaf 101) (.leaf 102))) (.node 630 (.node 629 (.leaf 105) (.leaf 104)) (.node 633 (.leaf 0) (.node 634 (.leaf 40) (.leaf 44)))))) (.node 648 (.node 641 (.node 637 (.node 636 (.leaf 46) (.leaf 45)) (.node 640 (.leaf 0) (.leaf 39))) (.node 643 (.node 642 (.leaf 43) (.leaf 45)) (.node 644 (.leaf 46) (.node 647 (.leaf 0) (.leaf 51))))) (.node 655 (.node 650 (.node 649 (.leaf 55) (.leaf 57)) (.node 651 (.leaf 58) (.node 654 (.leaf 0) (.leaf 64)))) (.node 657 (.node 656 (.leaf 62) (.leaf 65)) (.node 658 (.leaf 66) (.node 661 (.leaf 0) (.leaf 67))))))))) (.node 754 (.node 711 (.node 684 (.node 673 (.node 668 (.node 664 (.node 663 (.leaf 70) (.leaf 68)) (.node 665 (.leaf 69) (.leaf 0))) (.node 670 (.node 669 (.leaf 67) (.leaf 70)) (.node 671 (.leaf 68) (.node 672 (.leaf 69) (.leaf 39))))) (.node 678 (.node 676 (.node 674 (.leaf 40) (.leaf 52)) (.node 677 (.leaf 56) (.leaf 58))) (.node 680 (.node 679 (.leaf 57) (.leaf 51)) (.node 681 (.leaf 75) (.node 683 (.leaf 76) (.leaf 80)))))) (.node 697 (.node 690 (.node 686 (.node 685 (.leaf 82) (.leaf 81)) (.node 689 (.leaf 0) (.leaf 75))) (.node 692 (.node 691 (.leaf 79) (.leaf 81)) (.node 693 (.leaf 82) (.node 696 (.leaf 0) (.leaf 88))))) (.node 704 (.node 699 (.node 698 (.leaf 86) (.leaf 89)) (.node 700 (.leaf 90) (.node 703 (.leaf 0) (.leaf 91)))) (.node 706 (.node 705 (.leaf 94) (.leaf 92)) (.node 707 (.leaf 93) (.node 710 (.leaf 0) (.leaf 91))))))) (.node 731 (.node 721 (.node 715 (.node 713 (.node 712 (.leaf 94) (.leaf 92)) (.node 714 (.leaf 93) (.leaf 43))) (.node 717 (.node 716 (.leaf 44) (.leaf 56)) (.node 719 (.leaf 63) (.node 720 (.leaf 66) (.leaf 65))))) (.node 726 (.node 723 (.node 722 (.leaf 55) (.leaf 79)) (.node 724 (.leaf 80) (.leaf 87))) (.node 728 (.node 727 (.leaf 90) (.leaf 89)) (.node 729 (.leaf 62) (.node 730 (.leaf 86) (.leaf 98)))))) (.node 742 (.node 736 (.node 734 (.node 733 (.leaf 99) (.leaf 102)) (.node 735 (.leaf 101) (.leaf 64))) (.node 739 (.node 737 (.leaf 88) (.leaf 100)) (.node 740 (.leaf 98) (.node 741 (.leaf 101) (.leaf 102))))) (.node 748 (.node 744 (.node 743 (.leaf 67) (.leaf 91)) (.node 746 (.leaf 103) (.node 747 (.leaf 106) (.leaf 104)))) (.node 750 (.node 749 (.leaf 105) (.leaf 67)) (.node 751 (.leaf 91) (.node 753 (.leaf 103) (.leaf 106)))))))) (.node 797 (.node 774 (.node 764 (.node 758 (.node 756 (.node 755 (.leaf 104) (.leaf 105)) (.node 757 (.leaf 45) (.leaf 46))) (.node 760 (.node 759 (.leaf 58) (.leaf 66)) (.node 762 (.leaf 69) (.node 763 (.leaf 68) (.leaf 57))))) (.node 769 (.node 766 (.node 765 (.leaf 81) (.leaf 82)) (.node 767 (.leaf 90) (.leaf 93))) (.node 771 (.node 770 (.leaf 92) (.leaf 65)) (.node 772 (.leaf 89) (.node 773 (.leaf 101) (.leaf 102)))))) (.node 785 (.node 779 (.node 777 (.node 776 (.leaf 105) (.leaf 104)) (.node 778 (.leaf 68) (.leaf 92))) (.node 781 (.node 780 (.leaf 104) (.leaf 107)) (.node 783 (.leaf 108) (.node 784 (.leaf 107) (.leaf 70))))) (.node 791 (.node 787 (.node 786 (.leaf 94) (.leaf 106)) (.node 789 (.leaf 109) (.node 790 (.leaf 107) (.leaf 108)))) (.node 793 (.node 792 (.leaf 70) (.leaf 94)) (.node 794 (.leaf 106) (.node 796 (.leaf 109) (.leaf 107))))))) (.node 817 (.node 807 (.node 801 (.node 799 (.node 798 (.leaf 108) (.leaf 46)) (.node 800 (.leaf 45) (.leaf 57))) (.node 803 (.node 802 (.leaf 65) (.leaf 68)) (.node 805 (.leaf 70) (.node 806 (.leaf 58) (.leaf 82))))) (.node 812 (.node 809 (.node 808 (.leaf 81) (.leaf 89)) (.node 810 (.leaf 92) (.leaf 94))) (.node 814 (.node 813 (.leaf 66) (.leaf 90)) (.node 815 (.leaf 102) (.node 816 (.leaf 101) (.leaf 104)))))) (.node 828 (.node 822 (.node 820 (.node 819 (.leaf 106) (.leaf 69)) (.node 821 (.leaf 93) (.leaf 105))) (.node 824 (.node 823 (.leaf 108) (.leaf 107)) (.node 826 (.leaf 109) (.node 827 (.leaf 69) (.leaf 93))))) (.node 834 (.node 830 (.node 829 (.leaf 105) (.leaf 108)) (.node 831 (.leaf 107) (.node 833 (.leaf 109) (.leaf 68)))) (.node 836 (.node 835 (.leaf 92) (.leaf 104)) (.node 837 (.leaf 107) (.node 839 (.leaf 108) (.leaf 107)))))))))))
noncomputable def permutationTable4 : LiteralLookup ℕ := (.node 205 (.node 99 (.node 66 (.node 33 (.node 27 (.node 25 (.leaf 0) (.node 26 (.leaf 6) (.leaf 8))) (.node 31 (.node 28 (.leaf 9) (.leaf 0)) (.node 32 (.leaf 2) (.leaf 12)))) (.node 39 (.node 35 (.node 34 (.leaf 14) (.leaf 15)) (.node 38 (.leaf 0) (.leaf 3))) (.node 41 (.node 40 (.leaf 13) (.leaf 16)) (.node 42 (.leaf 17) (.leaf 0))))) (.node 76 (.node 70 (.node 68 (.node 67 (.leaf 6) (.leaf 0)) (.node 69 (.leaf 2) (.leaf 3))) (.node 74 (.node 73 (.leaf 0) (.leaf 8)) (.node 75 (.leaf 14) (.leaf 12)))) (.node 82 (.node 80 (.node 77 (.leaf 13) (.leaf 0)) (.node 81 (.leaf 9) (.leaf 15))) (.node 84 (.node 83 (.leaf 17) (.leaf 16)) (.node 98 (.leaf 0) (.leaf 6)))))) (.node 155 (.node 121 (.node 113 (.node 107 (.node 106 (.leaf 0) (.leaf 6)) (.node 112 (.leaf 0) (.leaf 2))) (.node 119 (.node 114 (.leaf 8) (.leaf 0)) (.node 120 (.leaf 3) (.leaf 9)))) (.node 147 (.node 141 (.node 140 (.leaf 0) (.leaf 8)) (.node 142 (.leaf 2) (.leaf 0))) (.node 149 (.node 148 (.leaf 14) (.leaf 12)) (.node 154 (.leaf 0) (.leaf 12))))) (.node 189 (.node 163 (.node 161 (.node 156 (.leaf 14) (.leaf 0)) (.node 162 (.leaf 13) (.leaf 15))) (.node 183 (.node 182 (.leaf 0) (.leaf 9)) (.node 184 (.leaf 3) (.leaf 0)))) (.node 197 (.node 191 (.node 190 (.leaf 15) (.leaf 13)) (.node 196 (.leaf 0) (.leaf 17))) (.node 203 (.node 198 (.leaf 16) (.leaf 0)) (.node 204 (.leaf 16) (.leaf 17))))))) (.node 464 (.node 338 (.node 223 (.node 216 (.node 214 (.node 213 (.leaf 0) (.leaf 6)) (.node 215 (.leaf 0) (.leaf 2))) (.node 221 (.node 217 (.leaf 3) (.leaf 0)) (.node 222 (.leaf 6) (.leaf 8)))) (.node 294 (.node 253 (.node 224 (.leaf 9) (.leaf 0)) (.node 254 (.leaf 6) (.leaf 0))) (.node 336 (.node 295 (.leaf 6) (.leaf 0)) (.node 337 (.leaf 8) (.leaf 2))))) (.node 427 (.node 423 (.node 379 (.node 378 (.leaf 0) (.leaf 9)) (.node 380 (.leaf 3) (.leaf 0))) (.node 425 (.node 424 (.leaf 8) (.leaf 14)) (.node 426 (.leaf 12) (.leaf 13)))) (.node 433 (.node 431 (.node 430 (.leaf 0) (.leaf 2)) (.node 432 (.leaf 12) (.leaf 14))) (.node 462 (.node 434 (.leaf 15) (.leaf 0)) (.node 463 (.leaf 2) (.leaf 8)))))) (.node 641 (.node 589 (.node 546 (.node 505 (.node 504 (.leaf 0) (.leaf 12)) (.node 506 (.leaf 14) (.leaf 0))) (.node 548 (.node 547 (.leaf 14) (.leaf 12)) (.node 588 (.leaf 0) (.leaf 15)))) (.node 635 (.node 633 (.node 590 (.leaf 13) (.leaf 0)) (.node 634 (.leaf 9) (.leaf 15))) (.node 637 (.node 636 (.leaf 17) (.leaf 16)) (.node 640 (.leaf 0) (.leaf 3))))) (.node 715 (.node 672 (.node 643 (.node 642 (.leaf 13) (.leaf 16)) (.node 644 (.leaf 17) (.leaf 0))) (.node 674 (.node 673 (.leaf 3) (.leaf 9)) (.node 714 (.leaf 0) (.leaf 13)))) (.node 758 (.node 756 (.node 716 (.leaf 15) (.leaf 0)) (.node 757 (.leaf 16) (.leaf 17))) (.node 799 (.node 798 (.leaf 0) (.leaf 17)) (.node 800 (.leaf 16) (.leaf 0))))))))
noncomputable def neighborTable4 : LiteralLookup ℕ := (.node 205 (.node 114 (.node 73 (.node 35 (.node 28 (.node 24 (.leaf 0) (.leaf 35)) (.node 31 (.leaf 0) (.leaf 35))) (.node 42 (.node 38 (.leaf 0) (.leaf 35)) (.node 66 (.leaf 0) (.node 70 (.leaf 35) (.leaf 0))))) (.node 98 (.node 80 (.node 77 (.leaf 35) (.leaf 0)) (.node 84 (.leaf 35) (.leaf 0))) (.node 105 (.node 100 (.leaf 35) (.leaf 0)) (.node 107 (.leaf 35) (.node 112 (.leaf 0) (.leaf 35)))))) (.node 161 (.node 142 (.node 121 (.node 119 (.leaf 0) (.leaf 35)) (.node 140 (.leaf 0) (.leaf 35))) (.node 149 (.node 147 (.leaf 0) (.leaf 35)) (.node 154 (.leaf 0) (.node 156 (.leaf 35) (.leaf 0))))) (.node 189 (.node 182 (.node 163 (.leaf 35) (.leaf 0)) (.node 184 (.leaf 35) (.leaf 0))) (.node 196 (.node 191 (.leaf 35) (.leaf 0)) (.node 198 (.leaf 35) (.node 203 (.leaf 0) (.leaf 35))))))) (.node 464 (.node 336 (.node 224 (.node 217 (.node 213 (.leaf 0) (.leaf 35)) (.node 220 (.leaf 0) (.leaf 35))) (.node 254 (.node 252 (.leaf 0) (.leaf 35)) (.node 294 (.leaf 0) (.node 296 (.leaf 35) (.leaf 0))))) (.node 423 (.node 378 (.node 338 (.leaf 35) (.leaf 0)) (.node 380 (.leaf 35) (.leaf 0))) (.node 430 (.node 427 (.leaf 35) (.leaf 0)) (.node 434 (.leaf 35) (.node 462 (.leaf 0) (.leaf 35)))))) (.node 640 (.node 548 (.node 506 (.node 504 (.leaf 0) (.leaf 35)) (.node 546 (.leaf 0) (.leaf 35))) (.node 590 (.node 588 (.leaf 0) (.leaf 35)) (.node 633 (.leaf 0) (.node 637 (.leaf 35) (.leaf 0))))) (.node 716 (.node 672 (.node 644 (.leaf 35) (.leaf 0)) (.node 674 (.leaf 35) (.node 714 (.leaf 0) (.leaf 35)))) (.node 758 (.node 756 (.leaf 0) (.leaf 35)) (.node 798 (.leaf 0) (.node 800 (.leaf 35) (.leaf 0))))))))

noncomputable def coverageWitness4 (code : ℕ) : Fin 290 :=
  Fin.ofNat 290 (coverageTable4.get code)
noncomputable def permutationWitness4 (code : ℕ) : Fin 24 :=
  Fin.ofNat 24 (permutationTable4.get code)
noncomputable def neighborWitness4 (code : ℕ) : Fin 290 :=
  Fin.ofNat 290 (neighborTable4.get code)

noncomputable def coveredTest4 (code : ℕ) : Bool :=
  coverageAt cells (triangle 7 (by decide)) (decodeInjection 7 4 (by decide) code)
    (coverageWitness4 code)
noncomputable def neighborTest4 (code : ℕ) : Bool :=
  neighborAt cells neighbors (by decide) permMaps (decodeInjection 7 4 (by decide) code)
    (permutationWitness4 code) (neighborWitness4 code)

theorem covered_4_codes_000000 : CodeInterval coveredTest4 0 64 :=
  codeInterval_of_check coveredTest4 0 64 (by decide +kernel)

theorem covered_4_codes_000064 : CodeInterval coveredTest4 64 128 :=
  codeInterval_of_check coveredTest4 64 64 (by decide +kernel)

theorem covered_4_codes_000128 : CodeInterval coveredTest4 128 192 :=
  codeInterval_of_check coveredTest4 128 64 (by decide +kernel)

theorem covered_4_codes_000192 : CodeInterval coveredTest4 192 256 :=
  codeInterval_of_check coveredTest4 192 64 (by decide +kernel)

theorem covered_4_codes_000256 : CodeInterval coveredTest4 256 320 :=
  codeInterval_of_check coveredTest4 256 64 (by decide +kernel)

theorem covered_4_codes_000320 : CodeInterval coveredTest4 320 384 :=
  codeInterval_of_check coveredTest4 320 64 (by decide +kernel)

theorem covered_4_codes_000384 : CodeInterval coveredTest4 384 448 :=
  codeInterval_of_check coveredTest4 384 64 (by decide +kernel)

theorem covered_4_codes_000448 : CodeInterval coveredTest4 448 512 :=
  codeInterval_of_check coveredTest4 448 64 (by decide +kernel)

theorem covered_4_codes_000512 : CodeInterval coveredTest4 512 576 :=
  codeInterval_of_check coveredTest4 512 64 (by decide +kernel)

theorem covered_4_codes_000576 : CodeInterval coveredTest4 576 640 :=
  codeInterval_of_check coveredTest4 576 64 (by decide +kernel)

theorem covered_4_codes_000640 : CodeInterval coveredTest4 640 704 :=
  codeInterval_of_check coveredTest4 640 64 (by decide +kernel)

theorem covered_4_codes_000704 : CodeInterval coveredTest4 704 768 :=
  codeInterval_of_check coveredTest4 704 64 (by decide +kernel)

theorem covered_4_codes_000768 : CodeInterval coveredTest4 768 832 :=
  codeInterval_of_check coveredTest4 768 64 (by decide +kernel)

theorem covered_4_codes_000832 : CodeInterval coveredTest4 832 840 :=
  codeInterval_of_check coveredTest4 832 8 (by decide +kernel)

theorem covered_4_join_000064_000192 : CodeInterval coveredTest4 64 192 :=
  codeInterval_append coveredTest4 64 128 192 covered_4_codes_000064 covered_4_codes_000128

theorem covered_4_join_000000_000192 : CodeInterval coveredTest4 0 192 :=
  codeInterval_append coveredTest4 0 64 192 covered_4_codes_000000 covered_4_join_000064_000192

theorem covered_4_join_000192_000320 : CodeInterval coveredTest4 192 320 :=
  codeInterval_append coveredTest4 192 256 320 covered_4_codes_000192 covered_4_codes_000256

theorem covered_4_join_000320_000448 : CodeInterval coveredTest4 320 448 :=
  codeInterval_append coveredTest4 320 384 448 covered_4_codes_000320 covered_4_codes_000384

theorem covered_4_join_000192_000448 : CodeInterval coveredTest4 192 448 :=
  codeInterval_append coveredTest4 192 320 448 covered_4_join_000192_000320 covered_4_join_000320_000448

theorem covered_4_join_000000_000448 : CodeInterval coveredTest4 0 448 :=
  codeInterval_append coveredTest4 0 192 448 covered_4_join_000000_000192 covered_4_join_000192_000448

theorem covered_4_join_000512_000640 : CodeInterval coveredTest4 512 640 :=
  codeInterval_append coveredTest4 512 576 640 covered_4_codes_000512 covered_4_codes_000576

theorem covered_4_join_000448_000640 : CodeInterval coveredTest4 448 640 :=
  codeInterval_append coveredTest4 448 512 640 covered_4_codes_000448 covered_4_join_000512_000640

theorem covered_4_join_000640_000768 : CodeInterval coveredTest4 640 768 :=
  codeInterval_append coveredTest4 640 704 768 covered_4_codes_000640 covered_4_codes_000704

theorem covered_4_join_000768_000840 : CodeInterval coveredTest4 768 840 :=
  codeInterval_append coveredTest4 768 832 840 covered_4_codes_000768 covered_4_codes_000832

theorem covered_4_join_000640_000840 : CodeInterval coveredTest4 640 840 :=
  codeInterval_append coveredTest4 640 768 840 covered_4_join_000640_000768 covered_4_join_000768_000840

theorem covered_4_join_000448_000840 : CodeInterval coveredTest4 448 840 :=
  codeInterval_append coveredTest4 448 640 840 covered_4_join_000448_000640 covered_4_join_000640_000840

theorem covered_4_join_000000_000840 : CodeInterval coveredTest4 0 840 :=
  codeInterval_append coveredTest4 0 448 840 covered_4_join_000000_000448 covered_4_join_000448_000840

theorem covered_4 : ∀ f : Fin 4 → Fin 7, Covered cells (triangle 7 (by decide)) f :=
  covered_of_injection_checks (by decide) cells (triangle 7 (by decide)) coverageWitness4 covered_4_join_000000_000840

theorem neighbor_4_codes_000000 : CodeInterval neighborTest4 0 64 :=
  codeInterval_of_check neighborTest4 0 64 (by decide +kernel)

theorem neighbor_4_codes_000064 : CodeInterval neighborTest4 64 128 :=
  codeInterval_of_check neighborTest4 64 64 (by decide +kernel)

theorem neighbor_4_codes_000128 : CodeInterval neighborTest4 128 192 :=
  codeInterval_of_check neighborTest4 128 64 (by decide +kernel)

theorem neighbor_4_codes_000192 : CodeInterval neighborTest4 192 256 :=
  codeInterval_of_check neighborTest4 192 64 (by decide +kernel)

theorem neighbor_4_codes_000256 : CodeInterval neighborTest4 256 320 :=
  codeInterval_of_check neighborTest4 256 64 (by decide +kernel)

theorem neighbor_4_codes_000320 : CodeInterval neighborTest4 320 384 :=
  codeInterval_of_check neighborTest4 320 64 (by decide +kernel)

theorem neighbor_4_codes_000384 : CodeInterval neighborTest4 384 448 :=
  codeInterval_of_check neighborTest4 384 64 (by decide +kernel)

theorem neighbor_4_codes_000448 : CodeInterval neighborTest4 448 512 :=
  codeInterval_of_check neighborTest4 448 64 (by decide +kernel)

theorem neighbor_4_codes_000512 : CodeInterval neighborTest4 512 576 :=
  codeInterval_of_check neighborTest4 512 64 (by decide +kernel)

theorem neighbor_4_codes_000576 : CodeInterval neighborTest4 576 640 :=
  codeInterval_of_check neighborTest4 576 64 (by decide +kernel)

theorem neighbor_4_codes_000640 : CodeInterval neighborTest4 640 704 :=
  codeInterval_of_check neighborTest4 640 64 (by decide +kernel)

theorem neighbor_4_codes_000704 : CodeInterval neighborTest4 704 768 :=
  codeInterval_of_check neighborTest4 704 64 (by decide +kernel)

theorem neighbor_4_codes_000768 : CodeInterval neighborTest4 768 832 :=
  codeInterval_of_check neighborTest4 768 64 (by decide +kernel)

theorem neighbor_4_codes_000832 : CodeInterval neighborTest4 832 840 :=
  codeInterval_of_check neighborTest4 832 8 (by decide +kernel)

theorem neighbor_4_join_000064_000192 : CodeInterval neighborTest4 64 192 :=
  codeInterval_append neighborTest4 64 128 192 neighbor_4_codes_000064 neighbor_4_codes_000128

theorem neighbor_4_join_000000_000192 : CodeInterval neighborTest4 0 192 :=
  codeInterval_append neighborTest4 0 64 192 neighbor_4_codes_000000 neighbor_4_join_000064_000192

theorem neighbor_4_join_000192_000320 : CodeInterval neighborTest4 192 320 :=
  codeInterval_append neighborTest4 192 256 320 neighbor_4_codes_000192 neighbor_4_codes_000256

theorem neighbor_4_join_000320_000448 : CodeInterval neighborTest4 320 448 :=
  codeInterval_append neighborTest4 320 384 448 neighbor_4_codes_000320 neighbor_4_codes_000384

theorem neighbor_4_join_000192_000448 : CodeInterval neighborTest4 192 448 :=
  codeInterval_append neighborTest4 192 320 448 neighbor_4_join_000192_000320 neighbor_4_join_000320_000448

theorem neighbor_4_join_000000_000448 : CodeInterval neighborTest4 0 448 :=
  codeInterval_append neighborTest4 0 192 448 neighbor_4_join_000000_000192 neighbor_4_join_000192_000448

theorem neighbor_4_join_000512_000640 : CodeInterval neighborTest4 512 640 :=
  codeInterval_append neighborTest4 512 576 640 neighbor_4_codes_000512 neighbor_4_codes_000576

theorem neighbor_4_join_000448_000640 : CodeInterval neighborTest4 448 640 :=
  codeInterval_append neighborTest4 448 512 640 neighbor_4_codes_000448 neighbor_4_join_000512_000640

theorem neighbor_4_join_000640_000768 : CodeInterval neighborTest4 640 768 :=
  codeInterval_append neighborTest4 640 704 768 neighbor_4_codes_000640 neighbor_4_codes_000704

theorem neighbor_4_join_000768_000840 : CodeInterval neighborTest4 768 840 :=
  codeInterval_append neighborTest4 768 832 840 neighbor_4_codes_000768 neighbor_4_codes_000832

theorem neighbor_4_join_000640_000840 : CodeInterval neighborTest4 640 840 :=
  codeInterval_append neighborTest4 640 768 840 neighbor_4_join_000640_000768 neighbor_4_join_000768_000840

theorem neighbor_4_join_000448_000840 : CodeInterval neighborTest4 448 840 :=
  codeInterval_append neighborTest4 448 640 840 neighbor_4_join_000448_000640 neighbor_4_join_000640_000840

theorem neighbor_4_join_000000_000840 : CodeInterval neighborTest4 0 840 :=
  codeInterval_append neighborTest4 0 448 840 neighbor_4_join_000000_000448 neighbor_4_join_000448_000840

theorem neighbor_4 : ∀ f : Fin 4 → Fin 7, NeighborWitness cells neighbors (by decide) permMaps f :=
  neighbor_of_injection_checks (by decide) (by decide) cells neighbors permMaps
    permutationWitness4 neighborWitness4 neighbor_4_join_000000_000840

end Papers.RationalityTen.FiniteCycleCandidates.N7
