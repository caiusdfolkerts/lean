module

public import FiniteCycleData6
public import FiniteInjectionWitnessChecks

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FiniteCycleCandidates.N6
open MatroidChecked

noncomputable def coverageTable5 : LiteralLookup ℕ := (.node 528 (.node 413 (.node 327 (.node 238 (.node 119 (.node 113 (.node 111 (.leaf 0) (.node 112 (.leaf 47) (.leaf 49))) (.node 117 (.node 114 (.leaf 51) (.leaf 0)) (.node 118 (.leaf 48) (.leaf 50)))) (.node 232 (.node 120 (.leaf 52) (.node 231 (.leaf 0) (.leaf 52))) (.node 234 (.node 233 (.leaf 51) (.leaf 49)) (.node 237 (.leaf 0) (.leaf 50))))) (.node 318 (.node 312 (.node 239 (.leaf 48) (.node 240 (.leaf 47) (.leaf 0))) (.node 314 (.node 313 (.leaf 52) (.leaf 47)) (.node 315 (.leaf 53) (.leaf 0)))) (.node 321 (.node 319 (.leaf 51) (.node 320 (.leaf 49) (.leaf 55))) (.node 325 (.node 324 (.leaf 0) (.leaf 49)) (.node 326 (.leaf 51) (.leaf 57)))))) (.node 357 (.node 350 (.node 344 (.node 342 (.leaf 0) (.node 343 (.leaf 50) (.leaf 48))) (.node 348 (.node 345 (.leaf 54) (.leaf 0)) (.node 349 (.leaf 48) (.leaf 50)))) (.node 353 (.node 351 (.leaf 56) (.node 352 (.leaf 58) (.leaf 57))) (.node 355 (.node 354 (.leaf 55) (.leaf 47)) (.node 356 (.leaf 52) (.leaf 58))))) (.node 384 (.node 360 (.node 358 (.leaf 56) (.node 359 (.leaf 54) (.leaf 53))) (.node 382 (.node 381 (.leaf 0) (.leaf 51)) (.node 383 (.leaf 52) (.leaf 50)))) (.node 389 (.node 387 (.leaf 0) (.node 388 (.leaf 49) (.leaf 47))) (.node 411 (.node 390 (.leaf 48) (.leaf 0)) (.node 412 (.leaf 49) (.leaf 47))))))) (.node 491 (.node 471 (.node 442 (.node 418 (.node 414 (.leaf 48) (.node 417 (.leaf 0) (.leaf 51))) (.node 420 (.node 419 (.leaf 52) (.leaf 50)) (.node 441 (.leaf 0) (.leaf 55)))) (.node 447 (.node 443 (.leaf 53) (.node 444 (.leaf 54) (.leaf 0))) (.node 449 (.node 448 (.leaf 57) (.leaf 58)) (.node 450 (.leaf 56) (.leaf 0))))) (.node 480 (.node 474 (.node 472 (.leaf 53) (.node 473 (.leaf 55) (.leaf 57))) (.node 478 (.node 477 (.leaf 0) (.leaf 54)) (.node 479 (.leaf 56) (.leaf 58)))) (.node 485 (.node 483 (.leaf 0) (.node 484 (.leaf 50) (.leaf 48))) (.node 489 (.node 486 (.leaf 47) (.leaf 0)) (.node 490 (.leaf 48) (.leaf 50)))))) (.node 511 (.node 502 (.node 496 (.node 492 (.leaf 52) (.node 495 (.leaf 0) (.leaf 54))) (.node 498 (.node 497 (.leaf 56) (.leaf 58)) (.node 501 (.leaf 0) (.leaf 57)))) (.node 507 (.node 503 (.leaf 58) (.node 504 (.leaf 56) (.leaf 0))) (.node 509 (.node 508 (.leaf 55) (.leaf 53)) (.node 510 (.leaf 54) (.leaf 47))))) (.node 519 (.node 514 (.node 512 (.leaf 52) (.node 513 (.leaf 58) (.leaf 56))) (.node 517 (.node 515 (.leaf 54) (.leaf 53)) (.node 518 (.leaf 59) (.leaf 64)))) (.node 522 (.node 520 (.leaf 62) (.node 521 (.leaf 60) (.leaf 59))) (.node 526 (.node 525 (.leaf 0) (.leaf 60)) (.node 527 (.leaf 62) (.leaf 64)))))))) (.node 635 (.node 577 (.node 548 (.node 539 (.node 533 (.node 531 (.leaf 0) (.node 532 (.leaf 63) (.leaf 64))) (.node 537 (.node 534 (.leaf 62) (.leaf 0)) (.node 538 (.leaf 61) (.leaf 59)))) (.node 542 (.node 540 (.leaf 60) (.node 541 (.leaf 49) (.leaf 51))) (.node 546 (.node 543 (.leaf 57) (.leaf 0)) (.node 547 (.leaf 55) (.leaf 61))))) (.node 568 (.node 562 (.node 549 (.leaf 63) (.node 561 (.leaf 0) (.leaf 61))) (.node 564 (.node 563 (.leaf 59) (.leaf 60)) (.node 567 (.leaf 0) (.leaf 63)))) (.node 571 (.node 569 (.leaf 64) (.node 570 (.leaf 62) (.leaf 51))) (.node 573 (.node 572 (.leaf 49) (.leaf 55)) (.node 576 (.leaf 0) (.leaf 57)))))) (.node 606 (.node 597 (.node 591 (.node 578 (.leaf 63) (.node 579 (.leaf 61) (.leaf 0))) (.node 593 (.node 592 (.leaf 59) (.leaf 61)) (.node 594 (.leaf 63) (.leaf 0)))) (.node 600 (.node 598 (.leaf 60) (.node 599 (.leaf 62) (.leaf 64))) (.node 604 (.node 603 (.leaf 0) (.leaf 52)) (.node 605 (.leaf 51) (.leaf 49))))) (.node 617 (.node 611 (.node 609 (.leaf 0) (.node 610 (.leaf 47) (.leaf 49))) (.node 615 (.node 612 (.leaf 51) (.leaf 0)) (.node 616 (.leaf 53) (.leaf 55)))) (.node 631 (.node 618 (.leaf 57) (.node 630 (.leaf 0) (.leaf 48))) (.node 633 (.node 632 (.leaf 50) (.leaf 56)) (.node 634 (.leaf 58) (.leaf 57))))))) (.node 684 (.node 662 (.node 642 (.node 638 (.node 636 (.leaf 55) (.node 637 (.leaf 54) (.leaf 60))) (.node 640 (.node 639 (.leaf 62) (.leaf 64)) (.node 641 (.leaf 63) (.leaf 61)))) (.node 647 (.node 645 (.leaf 0) (.node 646 (.leaf 59) (.leaf 61))) (.node 660 (.node 648 (.leaf 63) (.leaf 0)) (.node 661 (.leaf 50) (.leaf 48))))) (.node 673 (.node 667 (.node 663 (.leaf 54) (.node 666 (.leaf 0) (.leaf 56))) (.node 669 (.node 668 (.leaf 62) (.leaf 60)) (.node 672 (.leaf 0) (.leaf 58)))) (.node 678 (.node 674 (.leaf 64) (.node 675 (.leaf 59) (.leaf 0))) (.node 680 (.node 679 (.leaf 57) (.leaf 63)) (.node 681 (.leaf 61) (.leaf 0)))))) (.node 704 (.node 693 (.node 687 (.node 685 (.leaf 55) (.node 686 (.leaf 61) (.leaf 63))) (.node 691 (.node 690 (.leaf 0) (.leaf 52)) (.node 692 (.leaf 47) (.leaf 53)))) (.node 698 (.node 696 (.leaf 0) (.node 697 (.leaf 58) (.leaf 64))) (.node 702 (.node 699 (.leaf 59) (.leaf 0)) (.node 703 (.leaf 56) (.leaf 62))))) (.node 713 (.node 709 (.node 705 (.leaf 60) (.node 708 (.leaf 0) (.leaf 54))) (.node 711 (.node 710 (.leaf 60) (.leaf 62)) (.node 712 (.leaf 64) (.leaf 63)))) (.node 716 (.node 714 (.leaf 61) (.node 715 (.leaf 53) (.leaf 59))) (.node 718 (.node 717 (.leaf 64) (.leaf 62)) (.node 719 (.leaf 60) (.leaf 59)))))))))
noncomputable def permutationTable5 : LiteralLookup ℕ := (.node 390 (.node 320 (.node 232 (.node 117 (.node 113 (.node 112 (.leaf 0) (.leaf 2)) (.node 114 (.leaf 3) (.leaf 0))) (.node 119 (.node 118 (.leaf 1) (.leaf 4)) (.node 120 (.leaf 5) (.node 231 (.leaf 0) (.leaf 5))))) (.node 239 (.node 234 (.node 233 (.leaf 3) (.leaf 2)) (.node 237 (.leaf 0) (.node 238 (.leaf 4) (.leaf 1)))) (.node 313 (.node 312 (.leaf 0) (.leaf 5)) (.node 318 (.leaf 0) (.node 319 (.leaf 3) (.leaf 2)))))) (.node 350 (.node 342 (.node 325 (.node 324 (.leaf 0) (.leaf 2)) (.node 326 (.leaf 3) (.leaf 0))) (.node 344 (.node 343 (.leaf 4) (.leaf 1)) (.node 348 (.leaf 0) (.node 349 (.leaf 1) (.leaf 4))))) (.node 383 (.node 356 (.node 355 (.leaf 0) (.leaf 5)) (.node 381 (.leaf 0) (.node 382 (.leaf 3) (.leaf 5)))) (.node 387 (.node 384 (.leaf 4) (.leaf 0)) (.node 388 (.leaf 2) (.node 389 (.leaf 0) (.leaf 1))))))) (.node 541 (.node 483 (.node 414 (.node 412 (.node 411 (.leaf 0) (.leaf 2)) (.node 413 (.leaf 0) (.leaf 1))) (.node 418 (.node 417 (.leaf 0) (.leaf 3)) (.node 419 (.leaf 5) (.node 420 (.leaf 4) (.leaf 0))))) (.node 491 (.node 485 (.node 484 (.leaf 4) (.leaf 1)) (.node 489 (.leaf 0) (.node 490 (.leaf 1) (.leaf 4)))) (.node 511 (.node 492 (.leaf 5) (.leaf 0)) (.node 512 (.leaf 5) (.node 540 (.leaf 0) (.leaf 2)))))) (.node 611 (.node 603 (.node 570 (.node 542 (.leaf 3) (.leaf 0)) (.node 571 (.leaf 3) (.node 572 (.leaf 2) (.leaf 0)))) (.node 605 (.node 604 (.leaf 5) (.leaf 3)) (.node 606 (.leaf 2) (.node 610 (.leaf 0) (.leaf 2))))) (.node 660 (.node 630 (.node 612 (.leaf 3) (.leaf 0)) (.node 631 (.leaf 1) (.node 632 (.leaf 4) (.leaf 0)))) (.node 662 (.node 661 (.leaf 4) (.leaf 1)) (.node 690 (.leaf 0) (.node 691 (.leaf 5) (.leaf 0))))))))
noncomputable def neighborTable5 : LiteralLookup ℕ := (.node 390 (.node 320 (.node 234 (.node 117 (.node 111 (.leaf 0) (.node 114 (.leaf 47) (.leaf 0))) (.node 120 (.leaf 47) (.node 231 (.leaf 0) (.leaf 47)))) (.node 312 (.node 237 (.leaf 0) (.node 240 (.leaf 47) (.leaf 0))) (.node 314 (.leaf 47) (.node 318 (.leaf 0) (.leaf 47))))) (.node 350 (.node 342 (.node 324 (.leaf 0) (.node 326 (.leaf 47) (.leaf 0))) (.node 344 (.leaf 47) (.node 348 (.leaf 0) (.leaf 47)))) (.node 381 (.node 354 (.leaf 0) (.node 356 (.leaf 47) (.leaf 0))) (.node 384 (.leaf 47) (.node 387 (.leaf 0) (.leaf 47)))))) (.node 542 (.node 486 (.node 417 (.node 411 (.leaf 0) (.node 414 (.leaf 47) (.leaf 0))) (.node 420 (.leaf 47) (.node 483 (.leaf 0) (.leaf 47)))) (.node 510 (.node 489 (.leaf 0) (.node 492 (.leaf 47) (.leaf 0))) (.node 512 (.leaf 47) (.node 540 (.leaf 0) (.leaf 47))))) (.node 612 (.node 603 (.node 570 (.leaf 0) (.node 572 (.leaf 47) (.leaf 0))) (.node 606 (.leaf 47) (.node 609 (.leaf 0) (.leaf 47)))) (.node 660 (.node 630 (.leaf 0) (.node 632 (.leaf 47) (.leaf 0))) (.node 690 (.node 662 (.leaf 47) (.leaf 0)) (.node 692 (.leaf 47) (.leaf 0)))))))

noncomputable def coverageWitness5 (code : ℕ) : Fin 65 :=
  Fin.ofNat 65 (coverageTable5.get code)
noncomputable def permutationWitness5 (code : ℕ) : Fin 6 :=
  Fin.ofNat 6 (permutationTable5.get code)
noncomputable def neighborWitness5 (code : ℕ) : Fin 65 :=
  Fin.ofNat 65 (neighborTable5.get code)

noncomputable def coveredTest5 (code : ℕ) : Bool :=
  coverageAt cells (triangle 6 (by decide)) (decodeInjection 6 5 (by decide) code)
    (coverageWitness5 code)
noncomputable def neighborTest5 (code : ℕ) : Bool :=
  neighborAt cells neighbors (by decide) permMaps (decodeInjection 6 5 (by decide) code)
    (permutationWitness5 code) (neighborWitness5 code)

theorem covered_5_codes_000000 : CodeInterval coveredTest5 0 64 :=
  codeInterval_of_check coveredTest5 0 64 (by decide +kernel)

theorem covered_5_codes_000064 : CodeInterval coveredTest5 64 128 :=
  codeInterval_of_check coveredTest5 64 64 (by decide +kernel)

theorem covered_5_codes_000128 : CodeInterval coveredTest5 128 192 :=
  codeInterval_of_check coveredTest5 128 64 (by decide +kernel)

theorem covered_5_codes_000192 : CodeInterval coveredTest5 192 256 :=
  codeInterval_of_check coveredTest5 192 64 (by decide +kernel)

theorem covered_5_codes_000256 : CodeInterval coveredTest5 256 320 :=
  codeInterval_of_check coveredTest5 256 64 (by decide +kernel)

theorem covered_5_codes_000320 : CodeInterval coveredTest5 320 384 :=
  codeInterval_of_check coveredTest5 320 64 (by decide +kernel)

theorem covered_5_codes_000384 : CodeInterval coveredTest5 384 448 :=
  codeInterval_of_check coveredTest5 384 64 (by decide +kernel)

theorem covered_5_codes_000448 : CodeInterval coveredTest5 448 512 :=
  codeInterval_of_check coveredTest5 448 64 (by decide +kernel)

theorem covered_5_codes_000512 : CodeInterval coveredTest5 512 576 :=
  codeInterval_of_check coveredTest5 512 64 (by decide +kernel)

theorem covered_5_codes_000576 : CodeInterval coveredTest5 576 640 :=
  codeInterval_of_check coveredTest5 576 64 (by decide +kernel)

theorem covered_5_codes_000640 : CodeInterval coveredTest5 640 704 :=
  codeInterval_of_check coveredTest5 640 64 (by decide +kernel)

theorem covered_5_codes_000704 : CodeInterval coveredTest5 704 720 :=
  codeInterval_of_check coveredTest5 704 16 (by decide +kernel)

theorem covered_5_join_000064_000192 : CodeInterval coveredTest5 64 192 :=
  codeInterval_append coveredTest5 64 128 192 covered_5_codes_000064 covered_5_codes_000128

theorem covered_5_join_000000_000192 : CodeInterval coveredTest5 0 192 :=
  codeInterval_append coveredTest5 0 64 192 covered_5_codes_000000 covered_5_join_000064_000192

theorem covered_5_join_000256_000384 : CodeInterval coveredTest5 256 384 :=
  codeInterval_append coveredTest5 256 320 384 covered_5_codes_000256 covered_5_codes_000320

theorem covered_5_join_000192_000384 : CodeInterval coveredTest5 192 384 :=
  codeInterval_append coveredTest5 192 256 384 covered_5_codes_000192 covered_5_join_000256_000384

theorem covered_5_join_000000_000384 : CodeInterval coveredTest5 0 384 :=
  codeInterval_append coveredTest5 0 192 384 covered_5_join_000000_000192 covered_5_join_000192_000384

theorem covered_5_join_000448_000576 : CodeInterval coveredTest5 448 576 :=
  codeInterval_append coveredTest5 448 512 576 covered_5_codes_000448 covered_5_codes_000512

theorem covered_5_join_000384_000576 : CodeInterval coveredTest5 384 576 :=
  codeInterval_append coveredTest5 384 448 576 covered_5_codes_000384 covered_5_join_000448_000576

theorem covered_5_join_000640_000720 : CodeInterval coveredTest5 640 720 :=
  codeInterval_append coveredTest5 640 704 720 covered_5_codes_000640 covered_5_codes_000704

theorem covered_5_join_000576_000720 : CodeInterval coveredTest5 576 720 :=
  codeInterval_append coveredTest5 576 640 720 covered_5_codes_000576 covered_5_join_000640_000720

theorem covered_5_join_000384_000720 : CodeInterval coveredTest5 384 720 :=
  codeInterval_append coveredTest5 384 576 720 covered_5_join_000384_000576 covered_5_join_000576_000720

theorem covered_5_join_000000_000720 : CodeInterval coveredTest5 0 720 :=
  codeInterval_append coveredTest5 0 384 720 covered_5_join_000000_000384 covered_5_join_000384_000720

theorem covered_5 : ∀ f : Fin 5 → Fin 6, Covered cells (triangle 6 (by decide)) f :=
  covered_of_injection_checks (by decide) cells (triangle 6 (by decide)) coverageWitness5 covered_5_join_000000_000720

theorem neighbor_5_codes_000000 : CodeInterval neighborTest5 0 64 :=
  codeInterval_of_check neighborTest5 0 64 (by decide +kernel)

theorem neighbor_5_codes_000064 : CodeInterval neighborTest5 64 128 :=
  codeInterval_of_check neighborTest5 64 64 (by decide +kernel)

theorem neighbor_5_codes_000128 : CodeInterval neighborTest5 128 192 :=
  codeInterval_of_check neighborTest5 128 64 (by decide +kernel)

theorem neighbor_5_codes_000192 : CodeInterval neighborTest5 192 256 :=
  codeInterval_of_check neighborTest5 192 64 (by decide +kernel)

theorem neighbor_5_codes_000256 : CodeInterval neighborTest5 256 320 :=
  codeInterval_of_check neighborTest5 256 64 (by decide +kernel)

theorem neighbor_5_codes_000320 : CodeInterval neighborTest5 320 384 :=
  codeInterval_of_check neighborTest5 320 64 (by decide +kernel)

theorem neighbor_5_codes_000384 : CodeInterval neighborTest5 384 448 :=
  codeInterval_of_check neighborTest5 384 64 (by decide +kernel)

theorem neighbor_5_codes_000448 : CodeInterval neighborTest5 448 512 :=
  codeInterval_of_check neighborTest5 448 64 (by decide +kernel)

theorem neighbor_5_codes_000512 : CodeInterval neighborTest5 512 576 :=
  codeInterval_of_check neighborTest5 512 64 (by decide +kernel)

theorem neighbor_5_codes_000576 : CodeInterval neighborTest5 576 640 :=
  codeInterval_of_check neighborTest5 576 64 (by decide +kernel)

theorem neighbor_5_codes_000640 : CodeInterval neighborTest5 640 704 :=
  codeInterval_of_check neighborTest5 640 64 (by decide +kernel)

theorem neighbor_5_codes_000704 : CodeInterval neighborTest5 704 720 :=
  codeInterval_of_check neighborTest5 704 16 (by decide +kernel)

theorem neighbor_5_join_000064_000192 : CodeInterval neighborTest5 64 192 :=
  codeInterval_append neighborTest5 64 128 192 neighbor_5_codes_000064 neighbor_5_codes_000128

theorem neighbor_5_join_000000_000192 : CodeInterval neighborTest5 0 192 :=
  codeInterval_append neighborTest5 0 64 192 neighbor_5_codes_000000 neighbor_5_join_000064_000192

theorem neighbor_5_join_000256_000384 : CodeInterval neighborTest5 256 384 :=
  codeInterval_append neighborTest5 256 320 384 neighbor_5_codes_000256 neighbor_5_codes_000320

theorem neighbor_5_join_000192_000384 : CodeInterval neighborTest5 192 384 :=
  codeInterval_append neighborTest5 192 256 384 neighbor_5_codes_000192 neighbor_5_join_000256_000384

theorem neighbor_5_join_000000_000384 : CodeInterval neighborTest5 0 384 :=
  codeInterval_append neighborTest5 0 192 384 neighbor_5_join_000000_000192 neighbor_5_join_000192_000384

theorem neighbor_5_join_000448_000576 : CodeInterval neighborTest5 448 576 :=
  codeInterval_append neighborTest5 448 512 576 neighbor_5_codes_000448 neighbor_5_codes_000512

theorem neighbor_5_join_000384_000576 : CodeInterval neighborTest5 384 576 :=
  codeInterval_append neighborTest5 384 448 576 neighbor_5_codes_000384 neighbor_5_join_000448_000576

theorem neighbor_5_join_000640_000720 : CodeInterval neighborTest5 640 720 :=
  codeInterval_append neighborTest5 640 704 720 neighbor_5_codes_000640 neighbor_5_codes_000704

theorem neighbor_5_join_000576_000720 : CodeInterval neighborTest5 576 720 :=
  codeInterval_append neighborTest5 576 640 720 neighbor_5_codes_000576 neighbor_5_join_000640_000720

theorem neighbor_5_join_000384_000720 : CodeInterval neighborTest5 384 720 :=
  codeInterval_append neighborTest5 384 576 720 neighbor_5_join_000384_000576 neighbor_5_join_000576_000720

theorem neighbor_5_join_000000_000720 : CodeInterval neighborTest5 0 720 :=
  codeInterval_append neighborTest5 0 384 720 neighbor_5_join_000000_000384 neighbor_5_join_000384_000720

theorem neighbor_5 : ∀ f : Fin 5 → Fin 6, NeighborWitness cells neighbors (by decide) permMaps f :=
  neighbor_of_injection_checks (by decide) (by decide) cells neighbors permMaps
    permutationWitness5 neighborWitness5 neighbor_5_join_000000_000720

end Papers.RationalityTen.FiniteCycleCandidates.N6
