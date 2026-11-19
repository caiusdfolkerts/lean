module
public import FullSmallFacetEmbedding0Part000
public import FullSmallFacetEmbedding0Part001
public import FullSmallFacetEmbedding0Part002
public import FullSmallFacetEmbedding0Part003
public import FullSmallFacetEmbedding0Part004
public import RawFacetEmbeddingSemantics
public import FinitePolygonTemplates
public import FullSmallFacetEmbedding1Part000
public import FullSmallFacetEmbedding1Part001
public import FullSmallFacetEmbedding1Part002
public import FullSmallFacetEmbedding1Part003
public import FullSmallFacetEmbedding1Part004
public import FullSmallFacetEmbedding1Part005
public import FullSmallFacetEmbedding1Part006
public import FullSmallFacetEmbedding1Part007
public import FullSmallFacetEmbedding1Part008
public import FullSmallFacetEmbedding1Part009
public import FullSmallFacetEmbedding1Part010
public import FullSmallFacetEmbedding1Part011
public import FullSmallFacetEmbedding1Part012
public import FullSmallFacetEmbedding1Part013
public import FullSmallFacetEmbedding1Part014
public import FullSmallFacetEmbedding1Part015
public import FullSmallFacetEmbedding1Part016
public import FullSmallFacetEmbedding1Part017
public import FullSmallFacetEmbedding1Part018
public import FullSmallFacetEmbedding1Part019
public import FullSmallFacetEmbedding1Part020
public import FullSmallFacetEmbedding1Part021
public import FullSmallFacetEmbedding1Part022
public import FullSmallFacetEmbedding1Part023
public import FullSmallFacetEmbedding1Part024
public import FullSmallFacetEmbedding1Part025
public import FullSmallFacetEmbedding1Part026
public import FullSmallFacetEmbedding1Part027
public import FullSmallFacetEmbedding1Part028
public import FullSmallFacetEmbedding1Part029
public import FullSmallFacetEmbedding2Part000
public import FullSmallFacetEmbedding2Part001
public import FullSmallFacetEmbedding2Part002
public import FullSmallFacetEmbedding2Part003
public import FullSmallFacetEmbedding2Part004
public import FullSmallFacetEmbedding2Part005
public import FullSmallFacetEmbedding2Part006
public import FullSmallFacetEmbedding2Part007
public import FullSmallFacetEmbedding2Part008
public import FullSmallFacetEmbedding2Part009
public import FullSmallFacetEmbedding2Part010
public import FullSmallFacetEmbedding2Part011
public import FullSmallFacetEmbedding2Part012
public import FullSmallFacetEmbedding2Part013
public import FullSmallFacetEmbedding2Part014
public import FullSmallFacetEmbedding2Part015
public import FullSmallFacetEmbedding2Part016
public import FullSmallFacetEmbedding2Part017
public import FullSmallFacetEmbedding2Part018
public import FullSmallFacetEmbedding2Part019
public import FullSmallFacetEmbedding2Part020
public import FullSmallFacetEmbedding2Part021
public import FullSmallFacetEmbedding2Part022
public import FullSmallFacetEmbedding2Part023
public import FullSmallFacetEmbedding2Part024
public import FullSmallFacetEmbedding2Part025
public import FullSmallFacetEmbedding2Part026
public import FullSmallFacetEmbedding2Part027
public import FullSmallFacetEmbedding2Part028
public import FullSmallFacetEmbedding2Part029
public import FullSmallFacetRecordPart000
public import FullSmallFacetRecordPart001
public import FullSmallFacetRecordPart002
public import FullSmallFacetRecordPart003
public import FullSmallFacetRecordPart004
public import FullSmallFacetRecordPart005
public import FullSmallFacetRecordPart006
public import FullSmallFacetRecordPart007
public import FullSmallFacetRecordPart008
public import FullSmallFacetRecordPart009
public import FullSmallFacetRecordPart010
public import FullSmallFacetRecordPart011
public import FullSmallFacetRecordPart012
public import RawSmallCellMetadataSemantics
public import MatroidChecked.FacetBoundaryCompatibility
public import GrowthRenaming
public import ActualFacetCatalogueTransport
public import Papers.TenVertexSmallFacetBudgets
public import LiteralMaskGeometry
public import CellFacetInvariantsBase
public import MatroidChecked.IncidentFacetSimplicity
public import ActualNonedgeFacetCoverage
public import Mathlib.Data.Finset.Powerset
public import ActualSmallFacetClassification

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: FullSmallFacetEmbedding0.lean -/










@[expose] public section
namespace Papers.RationalityTen.FullSmallFacetEmbeddings.T0
open FiniteCycleCandidates LiteralCellEncoding RawFacetEmbeddingSemantics
open ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N4.templates 0)
theorem template_decodes : decodeTemplate 4 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem all_joined_0_2048 : FiniteChecks.Interval embeddingTest 0 2048 :=
  FiniteChecks.interval_append embeddingTest 0 1024 2048 part_000 part_001
theorem all_joined_3072_5040 : FiniteChecks.Interval embeddingTest 3072 5040 :=
  FiniteChecks.interval_append embeddingTest 3072 4096 5040 part_003 part_004
theorem all_joined_2048_5040 : FiniteChecks.Interval embeddingTest 2048 5040 :=
  FiniteChecks.interval_append embeddingTest 2048 3072 5040 part_002 all_joined_3072_5040
theorem all_joined_0_5040 : FiniteChecks.Interval embeddingTest 0 5040 :=
  FiniteChecks.interval_append embeddingTest 0 2048 5040 all_joined_0_2048 all_joined_2048_5040
theorem covers : ∀ f : Fin 4 ↪ Fin 10,
    ∃ i, LiteralMaskGeometry.decodeCell (FacetUniverses.FullSmall.cells i) =
      ActualFacetCatalogueTransport.mapCell f localCell :=
  full_coverage_of_checks (by decide) template localCell template_decodes
    FacetUniverses.FullSmall.cells witness all_joined_0_5040
end Papers.RationalityTen.FullSmallFacetEmbeddings.T0

end
end BundlePart0

section BundlePart1
/- Source: FullSmallFacetEmbedding1.lean -/



































@[expose] public section
namespace Papers.RationalityTen.FullSmallFacetEmbeddings.T1
open FiniteCycleCandidates LiteralCellEncoding RawFacetEmbeddingSemantics
open ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 0)
theorem template_decodes : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem all_joined_1024_3072 : FiniteChecks.Interval embeddingTest 1024 3072 :=
  FiniteChecks.interval_append embeddingTest 1024 2048 3072 part_001 part_002
theorem all_joined_0_3072 : FiniteChecks.Interval embeddingTest 0 3072 :=
  FiniteChecks.interval_append embeddingTest 0 1024 3072 part_000 all_joined_1024_3072
theorem all_joined_3072_5120 : FiniteChecks.Interval embeddingTest 3072 5120 :=
  FiniteChecks.interval_append embeddingTest 3072 4096 5120 part_003 part_004
theorem all_joined_5120_7168 : FiniteChecks.Interval embeddingTest 5120 7168 :=
  FiniteChecks.interval_append embeddingTest 5120 6144 7168 part_005 part_006
theorem all_joined_3072_7168 : FiniteChecks.Interval embeddingTest 3072 7168 :=
  FiniteChecks.interval_append embeddingTest 3072 5120 7168 all_joined_3072_5120 all_joined_5120_7168
theorem all_joined_0_7168 : FiniteChecks.Interval embeddingTest 0 7168 :=
  FiniteChecks.interval_append embeddingTest 0 3072 7168 all_joined_0_3072 all_joined_3072_7168
theorem all_joined_7168_9216 : FiniteChecks.Interval embeddingTest 7168 9216 :=
  FiniteChecks.interval_append embeddingTest 7168 8192 9216 part_007 part_008
theorem all_joined_9216_11264 : FiniteChecks.Interval embeddingTest 9216 11264 :=
  FiniteChecks.interval_append embeddingTest 9216 10240 11264 part_009 part_010
theorem all_joined_7168_11264 : FiniteChecks.Interval embeddingTest 7168 11264 :=
  FiniteChecks.interval_append embeddingTest 7168 9216 11264 all_joined_7168_9216 all_joined_9216_11264
theorem all_joined_11264_13312 : FiniteChecks.Interval embeddingTest 11264 13312 :=
  FiniteChecks.interval_append embeddingTest 11264 12288 13312 part_011 part_012
theorem all_joined_13312_15360 : FiniteChecks.Interval embeddingTest 13312 15360 :=
  FiniteChecks.interval_append embeddingTest 13312 14336 15360 part_013 part_014
theorem all_joined_11264_15360 : FiniteChecks.Interval embeddingTest 11264 15360 :=
  FiniteChecks.interval_append embeddingTest 11264 13312 15360 all_joined_11264_13312 all_joined_13312_15360
theorem all_joined_7168_15360 : FiniteChecks.Interval embeddingTest 7168 15360 :=
  FiniteChecks.interval_append embeddingTest 7168 11264 15360 all_joined_7168_11264 all_joined_11264_15360
theorem all_joined_0_15360 : FiniteChecks.Interval embeddingTest 0 15360 :=
  FiniteChecks.interval_append embeddingTest 0 7168 15360 all_joined_0_7168 all_joined_7168_15360
theorem all_joined_16384_18432 : FiniteChecks.Interval embeddingTest 16384 18432 :=
  FiniteChecks.interval_append embeddingTest 16384 17408 18432 part_016 part_017
theorem all_joined_15360_18432 : FiniteChecks.Interval embeddingTest 15360 18432 :=
  FiniteChecks.interval_append embeddingTest 15360 16384 18432 part_015 all_joined_16384_18432
theorem all_joined_18432_20480 : FiniteChecks.Interval embeddingTest 18432 20480 :=
  FiniteChecks.interval_append embeddingTest 18432 19456 20480 part_018 part_019
theorem all_joined_20480_22528 : FiniteChecks.Interval embeddingTest 20480 22528 :=
  FiniteChecks.interval_append embeddingTest 20480 21504 22528 part_020 part_021
theorem all_joined_18432_22528 : FiniteChecks.Interval embeddingTest 18432 22528 :=
  FiniteChecks.interval_append embeddingTest 18432 20480 22528 all_joined_18432_20480 all_joined_20480_22528
theorem all_joined_15360_22528 : FiniteChecks.Interval embeddingTest 15360 22528 :=
  FiniteChecks.interval_append embeddingTest 15360 18432 22528 all_joined_15360_18432 all_joined_18432_22528
theorem all_joined_22528_24576 : FiniteChecks.Interval embeddingTest 22528 24576 :=
  FiniteChecks.interval_append embeddingTest 22528 23552 24576 part_022 part_023
theorem all_joined_24576_26624 : FiniteChecks.Interval embeddingTest 24576 26624 :=
  FiniteChecks.interval_append embeddingTest 24576 25600 26624 part_024 part_025
theorem all_joined_22528_26624 : FiniteChecks.Interval embeddingTest 22528 26624 :=
  FiniteChecks.interval_append embeddingTest 22528 24576 26624 all_joined_22528_24576 all_joined_24576_26624
theorem all_joined_26624_28672 : FiniteChecks.Interval embeddingTest 26624 28672 :=
  FiniteChecks.interval_append embeddingTest 26624 27648 28672 part_026 part_027
theorem all_joined_28672_30240 : FiniteChecks.Interval embeddingTest 28672 30240 :=
  FiniteChecks.interval_append embeddingTest 28672 29696 30240 part_028 part_029
theorem all_joined_26624_30240 : FiniteChecks.Interval embeddingTest 26624 30240 :=
  FiniteChecks.interval_append embeddingTest 26624 28672 30240 all_joined_26624_28672 all_joined_28672_30240
theorem all_joined_22528_30240 : FiniteChecks.Interval embeddingTest 22528 30240 :=
  FiniteChecks.interval_append embeddingTest 22528 26624 30240 all_joined_22528_26624 all_joined_26624_30240
theorem all_joined_15360_30240 : FiniteChecks.Interval embeddingTest 15360 30240 :=
  FiniteChecks.interval_append embeddingTest 15360 22528 30240 all_joined_15360_22528 all_joined_22528_30240
theorem all_joined_0_30240 : FiniteChecks.Interval embeddingTest 0 30240 :=
  FiniteChecks.interval_append embeddingTest 0 15360 30240 all_joined_0_15360 all_joined_15360_30240
theorem covers : ∀ f : Fin 5 ↪ Fin 10,
    ∃ i, LiteralMaskGeometry.decodeCell (FacetUniverses.FullSmall.cells i) =
      ActualFacetCatalogueTransport.mapCell f localCell :=
  full_coverage_of_checks (by decide) template localCell template_decodes
    FacetUniverses.FullSmall.cells witness all_joined_0_30240
end Papers.RationalityTen.FullSmallFacetEmbeddings.T1

end
end BundlePart1

section BundlePart2
/- Source: FullSmallFacetEmbedding2.lean -/



































@[expose] public section
namespace Papers.RationalityTen.FullSmallFacetEmbeddings.T2
open FiniteCycleCandidates LiteralCellEncoding RawFacetEmbeddingSemantics
open ActualFacetCatalogueTransport
noncomputable def localCell := cellOfBoundary (FiniteCycleCandidates.N5.templates 1)
theorem template_decodes : decodeTemplate 5 template = localCell := by
  apply cell_ext <;> decide +kernel
theorem all_joined_1024_3072 : FiniteChecks.Interval embeddingTest 1024 3072 :=
  FiniteChecks.interval_append embeddingTest 1024 2048 3072 part_001 part_002
theorem all_joined_0_3072 : FiniteChecks.Interval embeddingTest 0 3072 :=
  FiniteChecks.interval_append embeddingTest 0 1024 3072 part_000 all_joined_1024_3072
theorem all_joined_3072_5120 : FiniteChecks.Interval embeddingTest 3072 5120 :=
  FiniteChecks.interval_append embeddingTest 3072 4096 5120 part_003 part_004
theorem all_joined_5120_7168 : FiniteChecks.Interval embeddingTest 5120 7168 :=
  FiniteChecks.interval_append embeddingTest 5120 6144 7168 part_005 part_006
theorem all_joined_3072_7168 : FiniteChecks.Interval embeddingTest 3072 7168 :=
  FiniteChecks.interval_append embeddingTest 3072 5120 7168 all_joined_3072_5120 all_joined_5120_7168
theorem all_joined_0_7168 : FiniteChecks.Interval embeddingTest 0 7168 :=
  FiniteChecks.interval_append embeddingTest 0 3072 7168 all_joined_0_3072 all_joined_3072_7168
theorem all_joined_7168_9216 : FiniteChecks.Interval embeddingTest 7168 9216 :=
  FiniteChecks.interval_append embeddingTest 7168 8192 9216 part_007 part_008
theorem all_joined_9216_11264 : FiniteChecks.Interval embeddingTest 9216 11264 :=
  FiniteChecks.interval_append embeddingTest 9216 10240 11264 part_009 part_010
theorem all_joined_7168_11264 : FiniteChecks.Interval embeddingTest 7168 11264 :=
  FiniteChecks.interval_append embeddingTest 7168 9216 11264 all_joined_7168_9216 all_joined_9216_11264
theorem all_joined_11264_13312 : FiniteChecks.Interval embeddingTest 11264 13312 :=
  FiniteChecks.interval_append embeddingTest 11264 12288 13312 part_011 part_012
theorem all_joined_13312_15360 : FiniteChecks.Interval embeddingTest 13312 15360 :=
  FiniteChecks.interval_append embeddingTest 13312 14336 15360 part_013 part_014
theorem all_joined_11264_15360 : FiniteChecks.Interval embeddingTest 11264 15360 :=
  FiniteChecks.interval_append embeddingTest 11264 13312 15360 all_joined_11264_13312 all_joined_13312_15360
theorem all_joined_7168_15360 : FiniteChecks.Interval embeddingTest 7168 15360 :=
  FiniteChecks.interval_append embeddingTest 7168 11264 15360 all_joined_7168_11264 all_joined_11264_15360
theorem all_joined_0_15360 : FiniteChecks.Interval embeddingTest 0 15360 :=
  FiniteChecks.interval_append embeddingTest 0 7168 15360 all_joined_0_7168 all_joined_7168_15360
theorem all_joined_16384_18432 : FiniteChecks.Interval embeddingTest 16384 18432 :=
  FiniteChecks.interval_append embeddingTest 16384 17408 18432 part_016 part_017
theorem all_joined_15360_18432 : FiniteChecks.Interval embeddingTest 15360 18432 :=
  FiniteChecks.interval_append embeddingTest 15360 16384 18432 part_015 all_joined_16384_18432
theorem all_joined_18432_20480 : FiniteChecks.Interval embeddingTest 18432 20480 :=
  FiniteChecks.interval_append embeddingTest 18432 19456 20480 part_018 part_019
theorem all_joined_20480_22528 : FiniteChecks.Interval embeddingTest 20480 22528 :=
  FiniteChecks.interval_append embeddingTest 20480 21504 22528 part_020 part_021
theorem all_joined_18432_22528 : FiniteChecks.Interval embeddingTest 18432 22528 :=
  FiniteChecks.interval_append embeddingTest 18432 20480 22528 all_joined_18432_20480 all_joined_20480_22528
theorem all_joined_15360_22528 : FiniteChecks.Interval embeddingTest 15360 22528 :=
  FiniteChecks.interval_append embeddingTest 15360 18432 22528 all_joined_15360_18432 all_joined_18432_22528
theorem all_joined_22528_24576 : FiniteChecks.Interval embeddingTest 22528 24576 :=
  FiniteChecks.interval_append embeddingTest 22528 23552 24576 part_022 part_023
theorem all_joined_24576_26624 : FiniteChecks.Interval embeddingTest 24576 26624 :=
  FiniteChecks.interval_append embeddingTest 24576 25600 26624 part_024 part_025
theorem all_joined_22528_26624 : FiniteChecks.Interval embeddingTest 22528 26624 :=
  FiniteChecks.interval_append embeddingTest 22528 24576 26624 all_joined_22528_24576 all_joined_24576_26624
theorem all_joined_26624_28672 : FiniteChecks.Interval embeddingTest 26624 28672 :=
  FiniteChecks.interval_append embeddingTest 26624 27648 28672 part_026 part_027
theorem all_joined_28672_30240 : FiniteChecks.Interval embeddingTest 28672 30240 :=
  FiniteChecks.interval_append embeddingTest 28672 29696 30240 part_028 part_029
theorem all_joined_26624_30240 : FiniteChecks.Interval embeddingTest 26624 30240 :=
  FiniteChecks.interval_append embeddingTest 26624 28672 30240 all_joined_26624_28672 all_joined_28672_30240
theorem all_joined_22528_30240 : FiniteChecks.Interval embeddingTest 22528 30240 :=
  FiniteChecks.interval_append embeddingTest 22528 26624 30240 all_joined_22528_26624 all_joined_26624_30240
theorem all_joined_15360_30240 : FiniteChecks.Interval embeddingTest 15360 30240 :=
  FiniteChecks.interval_append embeddingTest 15360 22528 30240 all_joined_15360_22528 all_joined_22528_30240
theorem all_joined_0_30240 : FiniteChecks.Interval embeddingTest 0 30240 :=
  FiniteChecks.interval_append embeddingTest 0 15360 30240 all_joined_0_15360 all_joined_15360_30240
theorem covers : ∀ f : Fin 5 ↪ Fin 10,
    ∃ i, LiteralMaskGeometry.decodeCell (FacetUniverses.FullSmall.cells i) =
      ActualFacetCatalogueTransport.mapCell f localCell :=
  full_coverage_of_checks (by decide) template localCell template_decodes
    FacetUniverses.FullSmall.cells witness all_joined_0_30240
end Papers.RationalityTen.FullSmallFacetEmbeddings.T2

end
end BundlePart2

section BundlePart3
/- Source: FullSmallFacetRecordChecks.lean -/

















@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

open LiteralMaskGeometry CellFacetInvariants

theorem records_join_0512_1536 : FiniteChecks.Interval recordTest 512 1536 :=
  FiniteChecks.interval_append recordTest 512 1024 1536 records_part_001 records_part_002

theorem records_join_0000_1536 : FiniteChecks.Interval recordTest 0 1536 :=
  FiniteChecks.interval_append recordTest 0 512 1536 records_part_000 records_join_0512_1536

theorem records_join_2048_3072 : FiniteChecks.Interval recordTest 2048 3072 :=
  FiniteChecks.interval_append recordTest 2048 2560 3072 records_part_004 records_part_005

theorem records_join_1536_3072 : FiniteChecks.Interval recordTest 1536 3072 :=
  FiniteChecks.interval_append recordTest 1536 2048 3072 records_part_003 records_join_2048_3072

theorem records_join_0000_3072 : FiniteChecks.Interval recordTest 0 3072 :=
  FiniteChecks.interval_append recordTest 0 1536 3072 records_join_0000_1536 records_join_1536_3072

theorem records_join_3584_4608 : FiniteChecks.Interval recordTest 3584 4608 :=
  FiniteChecks.interval_append recordTest 3584 4096 4608 records_part_007 records_part_008

theorem records_join_3072_4608 : FiniteChecks.Interval recordTest 3072 4608 :=
  FiniteChecks.interval_append recordTest 3072 3584 4608 records_part_006 records_join_3584_4608

theorem records_join_4608_5632 : FiniteChecks.Interval recordTest 4608 5632 :=
  FiniteChecks.interval_append recordTest 4608 5120 5632 records_part_009 records_part_010

theorem records_join_5632_6510 : FiniteChecks.Interval recordTest 5632 6510 :=
  FiniteChecks.interval_append recordTest 5632 6144 6510 records_part_011 records_part_012

theorem records_join_4608_6510 : FiniteChecks.Interval recordTest 4608 6510 :=
  FiniteChecks.interval_append recordTest 4608 5632 6510 records_join_4608_5632 records_join_5632_6510

theorem records_join_3072_6510 : FiniteChecks.Interval recordTest 3072 6510 :=
  FiniteChecks.interval_append recordTest 3072 4608 6510 records_join_3072_4608 records_join_4608_6510

theorem records_join_0000_6510 : FiniteChecks.Interval recordTest 0 6510 :=
  FiniteChecks.interval_append recordTest 0 3072 6510 records_join_0000_3072 records_join_3072_6510

theorem records_checked_full (i : Fin cellCount) :
        WellFormed (cells i) ∧ UnrootedKindCheck cells i ∧
          (decodeCell (cells i)).vertices.card ≤ 5 :=
      RawSmallCellMetadata.check_sound cells i
        (FiniteChecks.fin_of_interval
          (fun a : Fin cellCount => RawSmallCellMetadata.check (cells a)) records_join_0000_6510 i)

    theorem records_checked (i : Fin cellCount) :
        WellFormed (cells i) ∧ UnrootedKindCheck cells i :=
      ⟨(records_checked_full i).1, (records_checked_full i).2.1⟩

    theorem cells_wellFormed (i : Fin cellCount) : WellFormed (cells i) := (records_checked i).1

    theorem cells_kind_correct (i : Fin cellCount) : UnrootedKindCheck cells i :=
      (records_checked i).2

    theorem cells_vertex_card_le_five_from_records (i : Fin cellCount) :
        (decodeCell (cells i)).vertices.card ≤ 5 := (records_checked_full i).2.2
    end Papers.RationalityTen.FacetUniverses.FullSmall
    
end
end BundlePart3

section BundlePart4
/- Source: ActualGrowthTarget.lean -/






@[expose] public section

/-!
# Actual convex boundaries satisfy every finite growth target condition

A ridge codec and literal compatibility semantics are the only interfaces
between the mathematical cells and the executable checker. Pairing,
connectedness, and the minimum nonsimple-vertex incidence come from actual
convex geometry. Quotas are stated as ordinary filtered facet counts.
-/

noncomputable section
namespace Papers.RationalityTen.ActualGrowthTarget

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open MatroidChecked.FacetBoundaryEncoding
open BoundarySearch GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open ActualFaceTransport ActualFacetCatalogueTransport

variable {d n c r : ℕ}

theorem family_toList (S : Finset (Fin c)) (a : Fin c) :
    SparseGrowthDAG.family S.toList a = true ↔ a ∈ S := by
  rw [SparseGrowthDAG.family, has_true, Finset.mem_toList]

/-- The list checker and the mathematical finset count the same cells. -/
theorem kindCount_toList (kind : Fin c → ℕ) (S : Finset (Fin c)) (k : ℕ) :
    kindCount kind S.toList k = (S.filter fun a => kind a = k).card := by
  rw [kindCount, ← List.toFinset_card_of_nodup (S.nodup_toList.filter _)]
  congr 1
  ext a
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_toList,
    decide_eq_true_eq, Finset.mem_filter]

/-- Pairing of genuine ridge incidences gives a distinct mate in the
Boolean target used by the checker. -/
theorem hasMate_of_pairing {R : Type*} [DecidableEq R]
    (facets : Fin c → Finset R) (S : Finset (Fin c))
    (inc : Fin c → Fin r → Bool) (code : R ≃ Fin r)
    (hcode : ∀ a q, inc a (code q) = true ↔ q ∈ facets a)
    (hpair : ∀ q, (incidence facets S q).card = 0 ∨
      (incidence facets S q).card = 2) :
    HasMate inc (SparseGrowthDAG.family S.toList) := by
  intro q a ha
  let I := incidence facets S (code.symm q)
  have haI : a ∈ I := Finset.mem_filter.mpr
    ⟨(family_toList S a).mp ha.1, (hcode a _).mp (by simpa using ha.2)⟩
  have hcard : I.card = 2 := by
    have hp := Finset.card_pos.mpr ⟨a, haI⟩
    have hcounts : I.card = 0 ∨ I.card = 2 := hpair (code.symm q)
    rcases hcounts with h | h <;> omega
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < I.card) a
  obtain ⟨hbS, hbq⟩ := Finset.mem_filter.mp hb
  refine ⟨b, ⟨(family_toList S b).mpr hbS, ?_⟩, hba⟩
  simpa using (hcode b (code.symm q)).mpr hbq

theorem noThree_of_pairing {R : Type*} [DecidableEq R]
    (facets : Fin c → Finset R) (S : Finset (Fin c))
    (inc : Fin c → Fin r → Bool) (code : R ≃ Fin r)
    (hcode : ∀ a q, inc a (code q) = true ↔ q ∈ facets a)
    (hpair : ∀ q, (incidence facets S q).card = 0 ∨
      (incidence facets S q).card = 2) :
    NoThree inc (SparseGrowthDAG.family S.toList) := by
  intro q a b z ha hb hz
  by_cases hab : a = b
  · exact Or.inl hab
  by_cases haz : a = z
  · exact Or.inr (Or.inl haz)
  by_cases hbz : b = z
  · exact Or.inr (Or.inr hbz)
  exfalso
  let I := incidence facets S (code.symm q)
  have memI (x : Fin c) (hx : Incident inc (SparseGrowthDAG.family S.toList) q x) : x ∈ I :=
    Finset.mem_filter.mpr ⟨(family_toList S x).mp hx.1,
      (hcode x _).mp (by simpa using hx.2)⟩
  have hsub : ({a, b, z} : Finset (Fin c)) ⊆ I := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · exact hx.symm ▸ memI a ha
    · exact hx.symm ▸ memI b hb
    · exact hx.symm ▸ memI z hz
  have hc := Finset.card_le_card hsub
  have hthree : ({a, b, z} : Finset (Fin c)).card = 3 := by simp [hab, haz, hbz]
  rw [hthree] at hc
  have hcounts : I.card = 0 ∨ I.card = 2 := hpair (code.symm q)
  rcases hcounts with h | h <;> omega

theorem connected_of_boundary {R : Type*} [DecidableEq R]
    (facets : Fin c → Finset R) (S : Finset (Fin c))
    (inc : Fin c → Fin r → Bool) (code : R ≃ Fin r)
    (hcode : ∀ a q, inc a (code q) = true ↔ q ∈ facets a)
    (hc : RidgeConnected facets S) :
    Connected inc (SparseGrowthDAG.family S.toList) := by
  intro U hUS hUne hUneS
  let T : Finset (Fin c) := Finset.univ.filter fun a => U a = true
  have hTsub : T ⊆ S := by
    intro a ha
    exact (family_toList S a).mp (hUS a (Finset.mem_filter.mp ha).2)
  have hTne : T.Nonempty := by
    obtain ⟨a, ha⟩ := hUne
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  have hTneq : T ≠ S := by
    intro hTS
    apply hUneS
    intro a
    apply Bool.eq_iff_iff.mpr
    rw [family_toList, ← hTS]
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨a, haT, b, hbS, hbT, q, hqa, hqb⟩ := hc T hTsub hTne hTneq
  refine ⟨code q, a, b, ⟨(Finset.mem_filter.mp haT).2, (hcode a q).mpr hqa⟩,
    ⟨(family_toList S b).mpr hbS, (hcode b q).mpr hqb⟩, ?_⟩
  cases hUb : U b with
  | false => rfl
  | true => exact (hbT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUb⟩)).elim

/-- All five target conditions follow for the actual encoded facet family.
The remaining inputs express exact finite codec semantics and ordinary
facet-count bounds; they are not geometric regularity assumptions. -/
theorem actual_growth_target {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n}
    (E : Encoding P lab cells) (hP : P.dim = 4)
    (inc : Fin c → Fin r → Bool) (code : Finset (Fin n) ≃ Fin r)
    (hcode : ∀ a q, inc a (code q) = true ↔ q ∈ (cells a).ridges)
    (compatible : Fin c → Fin c → Bool)
    (hcompatible : ∀ a b, (cells a).Compatible (cells b) → compatible a b = true)
    (kind : Fin c → ℕ) (quota : ℕ → ℕ)
    (hbudget : ∀ k, (E.family.filter fun a => kind a = k).card ≤ quota k) :
    Target inc compatible kind quota E.family.toList := by
  refine ⟨?_, ?_, hasMate_of_pairing _ _ inc code hcode (E.ridge_pairing hP),
    noThree_of_pairing _ _ inc code hcode (E.ridge_pairing hP),
    connected_of_boundary _ _ inc code hcode (E.ridge_connected hP)⟩
  · intro k
    rw [kindCount_toList]
    exact hbudget k
  · intro a b ha hb hab
    exact hcompatible a b (E.pairwise_compatible
      (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb) hab)

/-- The quota count can be read directly on the actual facets. -/
theorem encoded_kind_card {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n}
    (E : Encoding P lab cells) (kind : Fin c → ℕ) (k : ℕ) :
    (E.family.filter fun a => kind a = k).card =
      ((Finset.univ : Finset (Face P 3)).filter fun F => kind (E.index F) = k).card := by
  have heq : E.family.filter (fun a => kind a = k) =
      ((Finset.univ : Finset (Face P 3)).filter fun F => kind (E.index F) = k).image E.index := by
    ext a
    simp only [Finset.mem_filter, Encoding.mem_family, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨F, rfl⟩, hk⟩
      exact ⟨F, hk, rfl⟩
    · rintro ⟨F, hk, rfl⟩
      exact ⟨⟨F, rfl⟩, hk⟩
  rw [heq, Finset.card_image_of_injective _ E.index_injective]

/-- Coverage may be chosen to send a distinguished actual facet to a
specified root index even if the candidate table contains redundancy. -/
theorem encoding_of_coverage_with_root (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (cells : Fin c → Cell n)
    (F : Face P 3) (root : Fin c) (hroot : cells root = actualCell P lab F)
    (hcoverage : ∀ G : Face P 3, ∃ i, cells i = actualCell P lab G) :
    ∃ E : Encoding P lab cells, E.index F = root := by
  choose index hindex using hcoverage
  let E : Encoding P lab cells :=
    { index := fun G => if G = F then root else index G
      index_spec := by
        intro G
        split_ifs with h
        · simpa only [h] using hroot
        · exact hindex G }
  refine ⟨E, ?_⟩
  change (if F = F then root else index F) = root
  exact if_pos rfl

theorem actual_root_included {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n}
    (E : Encoding P lab cells) (F : Face P 3) (root : Fin c)
    (hroot : E.index F = root) :
    Included (SparseGrowthDAG.family [root]) (SparseGrowthDAG.family E.family.toList) := by
  intro i hi
  have hi' : i = root := by
    simpa only [SparseGrowthDAG.family, has_true, List.mem_singleton] using hi
  subst i
  exact (family_toList E.family root).mpr ((E.mem_family root).mpr ⟨F, hroot⟩)

/-- Normalize a complete actual facet template to the first local labels
by extending its injection to a permutation of all global labels. -/
theorem normalize_facet_template {m : ℕ} (P : ConvexPolytope d)
    (lab₀ : P.vertices ≃ Fin n) (F : Face P 3)
    (loc : (facePolytope P F.val.isFace).vertices ≃ Fin m)
    (B : Finset (PolygonBoundaryCatalogue.Polygon m))
    (hB : polygonBoundary (facePolytope P F.val.isFace) loc = B) (hm : m ≤ n) :
    ∃ lab : P.vertices ≃ Fin n,
      actualCell P lab F = mapCell
        ⟨Fin.castLE hm, fun a b h => Fin.ext (congrArg (fun i : Fin n => i.val) h)⟩ (cellOfBoundary B) := by
  let f := labelEmbedding P lab₀ F loc
  let g : Fin m ↪ Fin n := ⟨Fin.castLE hm, fun a b h => Fin.ext (congrArg (fun i : Fin n => i.val) h)⟩
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g f.injective g.injective
  refine ⟨lab₀.trans σ, ?_⟩
  rw [actualCell_of_template P (lab₀.trans σ) F loc B hB]
  have hemb : labelEmbedding P (lab₀.trans σ) F loc = g := by
    apply Function.Embedding.ext
    intro i
    change σ (f i) = g i
    exact hσ i
  rw [hemb]

/-- The same normalization may use any prescribed injective placement of
the local template, including the catalogue's canonical root labeling. -/
theorem normalize_facet_template_to_embedding {m : ℕ} (P : ConvexPolytope d)
    (lab₀ : P.vertices ≃ Fin n) (F : Face P 3)
    (loc : (facePolytope P F.val.isFace).vertices ≃ Fin m)
    (B : Finset (PolygonBoundaryCatalogue.Polygon m))
    (hB : polygonBoundary (facePolytope P F.val.isFace) loc = B)
    (g : Fin m ↪ Fin n) :
    ∃ lab : P.vertices ≃ Fin n, actualCell P lab F = mapCell g (cellOfBoundary B) := by
  let f := labelEmbedding P lab₀ F loc
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g f.injective g.injective
  refine ⟨lab₀.trans σ, ?_⟩
  rw [actualCell_of_template P (lab₀.trans σ) F loc B hB]
  have hemb : labelEmbedding P (lab₀.trans σ) F loc = g := by
    apply Function.Embedding.ext
    intro i
    change σ (f i) = g i
    exact hσ i
  rw [hemb]

/-- A singleton distinguished root is nonempty in the checker semantics. -/
theorem singleton_root_nonempty (root : Fin c) :
    GrowthDAG.Nonempty (SparseGrowthDAG.family [root]) := by
  refine ⟨root, ?_⟩
  simp only [SparseGrowthDAG.family, has_true, List.mem_singleton]

/-- Original nonsimplicity supplies the minimum facet-incidence bound
used by the local and global capacity cuts. -/
theorem actual_nonsimple_incidence {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n}
    (E : Encoding P lab cells) (hP : P.dim = 4)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v) (v : Fin n) :
    5 ≤ (E.family.filter fun i => v ∈ (cells i).vertices).card := by
  apply E.vertex_incidence_ge_five hP
  intro w hfour
  apply hnonsimple w
  change (polytopeGraph P).degree w = P.dim
  rw [← NineBipyramidIncidence.vertexGraph_eq_polytopeGraph,
    MatroidChecked.IncidentFacetSimplicity.degree_eq_actual_neighbors, hfour, hP]

end Papers.RationalityTen.ActualGrowthTarget

end
end
end BundlePart4

section BundlePart5
/- Source: SmallFacetTargetBudgets.lean -/





@[expose] public section

/-!
# Exact rooted quotas for the small-facet residual

The root is a genuine triangular bipyramid. The remaining three kinds
are tetrahedra, triangular bipyramids, and square pyramids. The numerical
quotas count actual facets and are derived from the paper's geometric
incidence and excess identities before the finite search is invoked.
-/

noncomputable section
namespace Papers.RationalityTen.SmallFacetTargetBudgets

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus
open ChirotopeDensity MatroidChecked.FacetBoundaryEncoding

/-- Separate a distinguished root from the other three facet classes. -/
def partitionKind {α : Type*} [DecidableEq α] (N Q : Finset α) (root : α) (a : α) : ℕ :=
  if a = root then 0 else if a ∈ N then if a ∈ Q then 3 else 2 else 1

def quota (m E q : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => m - E
  | 2 => E - 2 * q - 1
  | 3 => 2 * q
  | _ => 0

/-- Pure finite bookkeeping for a nested partition, with the root removed
exactly once from the bipyramid class. -/
theorem partition_kind_counts {α : Type*} [Fintype α] [DecidableEq α]
    (N Q : Finset α) (root : α) (hQN : Q ⊆ N) (hroot : root ∈ N \ Q)
    (q : ℕ) (hQcard : Q.card = 2 * q) :
    ∀ k, ((Finset.univ : Finset α).filter fun a => partitionKind N Q root a = k).card =
      quota (Fintype.card α) N.card q k := by
  obtain ⟨hrootN, hrootQ⟩ := Finset.mem_sdiff.mp hroot
  have h0 : Finset.univ.filter (fun a => partitionKind N Q root a = 0) = {root} := by
    ext a
    by_cases hr : a = root <;> by_cases hn : a ∈ N <;> by_cases hq : a ∈ Q <;>
      simp [partitionKind, hr, hn, hq]
  have h1 : Finset.univ.filter (fun a => partitionKind N Q root a = 1) = Finset.univ \ N := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    by_cases hr : a = root
    · subst a; simp [partitionKind, hrootN, hrootQ]
    · by_cases hn : a ∈ N
      · by_cases hq : a ∈ Q <;> simp [partitionKind, hr, hn, hq]
      · have hq : a ∉ Q := fun h => hn (hQN h)
        simp [partitionKind, hr, hn, hq]
  have h2 : Finset.univ.filter (fun a => partitionKind N Q root a = 2) = (N \ Q).erase root := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      Finset.mem_sdiff]
    by_cases hr : a = root
    · subst a; simp [partitionKind, hrootN, hrootQ]
    · by_cases hn : a ∈ N
      · by_cases hq : a ∈ Q <;> simp [partitionKind, hr, hn, hq]
      · have hq : a ∉ Q := fun h => hn (hQN h)
        simp [partitionKind, hr, hn, hq]
  have h3 : Finset.univ.filter (fun a => partitionKind N Q root a = 3) = Q := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hr : a = root
    · subst a; simp [partitionKind, hrootN, hrootQ]
    · by_cases hn : a ∈ N
      · by_cases hq : a ∈ Q <;> simp [partitionKind, hr, hn, hq]
      · have hq : a ∉ Q := fun h => hn (hQN h)
        simp [partitionKind, hr, hn, hq]
  intro k
  rcases k with _ | k
  · rw [h0, Finset.card_singleton]; rfl
  rcases k with _ | k
  · rw [h1, Finset.card_sdiff_of_subset (Finset.subset_univ N), Finset.card_univ]; rfl
  rcases k with _ | k
  · rw [h2, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hrootN, hrootQ⟩),
      Finset.card_sdiff_of_subset hQN, hQcard]
    rfl
  rcases k with _ | k
  · rw [h3, hQcard]; rfl
  have hempty : Finset.univ.filter (fun a => partitionKind N Q root a = k + 4) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a _ hkind
    unfold partitionKind at hkind
    split_ifs at hkind <;> omega
  simpa only [quota, Finset.card_empty, Nat.add_assoc] using congrArg Finset.card hempty

/-- A small facet with polygon excess one is a square pyramid; its count
is twice the number of global quadrilateral ridges. -/
def squareFacets {d : ℕ} (P : ConvexPolytope d) : Finset (Face P 3) :=
  Finset.univ.filter fun F => facetPolygonExcess P F = 1

theorem squareFacets_subset_nonsimplicial {d : ℕ} (P : ConvexPolytope d) :
    squareFacets P ⊆ nonsimplicialFacets P := by
  intro F hF
  have hg := (Finset.mem_filter.mp hF).2
  have hbound := twice_facet_polygon_excess_le_three_vertices_sub_twelve P F
  apply (mem_nonsimplicialFacets P F).mpr
  omega

theorem squareFacets_card {d : ℕ} (P : ConvexPolytope d) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    (squareFacets P).card = 2 * (quadrilateralFaces P).card := by
  have h := small_facets_one_polygon_excess_count P hP hfacets
  exact_mod_cast h

/-- The complement of the square-pyramid class among nonsimplicial small
facets consists exactly of triangular bipyramids. -/
theorem mem_bipyramid_class_iff {d : ℕ} (P : ConvexPolytope d)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) (F : Face P 3) :
    F ∈ nonsimplicialFacets P \ squareFacets P ↔
      facetVertexCount P F = 5 ∧ facetPolygonExcess P F = 0 := by
  have hmin : 4 ≤ facetVertexCount P F :=
    Nat.succ_le_iff.mpr (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 F)
  have hmax := hfacets F
  have hgmin : 0 ≤ facetPolygonExcess P F :=
    polygonExcess_nonnegative (facePolytope P F.val.isFace)
  have hgmax := facetPolygonExcess_le_one_of_card_le_five P F hmax
  simp only [Finset.mem_sdiff, mem_nonsimplicialFacets, squareFacets,
    Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- Every one of the 32 residual budgets contains a bipyramid root. This
is an actual facet-existence statement, not a choice assumed by search. -/
theorem actual_bipyramid_root {n : ℕ} (P : ConvexPolytope 4)
    (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    ∃ F : Face P 3, facetVertexCount P F = 5 ∧ facetPolygonExcess P F = 0 := by
  have hbudget := actual_small_facet_budget_mem P hP e hn hN hc hfacets
  have hbound : 2 * (quadrilateralFaces P).card < (nonsimplicialFacets P).card := by
    have hfinite : ∀ B ∈ smallFacetBudgets, 2 * B.q < B.E := by decide +kernel
    exact hfinite _ hbudget
  have hcard := squareFacets_card P hP hfacets
  have hdiff : (nonsimplicialFacets P \ squareFacets P).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset (squareFacets_subset_nonsimplicial P), hcard]
    omega
  obtain ⟨F, hF⟩ := hdiff
  exact ⟨F, (mem_bipyramid_class_iff P hfacets F).mp hF⟩

/-- All rooted small-facet quotas are exact counts of genuine facets. -/
theorem actual_rooted_quota_counts {d : ℕ} (P : ConvexPolytope d) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (root : Face P 3) (hroot : facetVertexCount P root = 5 ∧ facetPolygonExcess P root = 0) :
    ∀ k, ((Finset.univ : Finset (Face P 3)).filter fun F =>
      partitionKind (nonsimplicialFacets P) (squareFacets P) root F = k).card =
      quota (Nat.card (Face P 3)) (nonsimplicialFacets P).card
        (quadrilateralFaces P).card k := by
  have h := partition_kind_counts (nonsimplicialFacets P) (squareFacets P) root
    (squareFacets_subset_nonsimplicial P)
    ((mem_bipyramid_class_iff P hfacets root).mpr hroot)
    (quadrilateralFaces P).card (squareFacets_card P hP hfacets)
  simpa only [Nat.card_eq_fintype_card] using h

/-- An exact finite kind-label check transports those actual counts to
the candidate indices expected by the growth kernel. -/
theorem encoded_rooted_quota {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} {cells : Fin c → Cell 10}
    (E : Encoding P lab cells) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (root : Face P 3) (hroot : facetVertexCount P root = 5 ∧ facetPolygonExcess P root = 0)
    (kind : Fin c → ℕ)
    (hkind : ∀ F, kind (E.index F) =
      partitionKind (nonsimplicialFacets P) (squareFacets P) root F) :
    ∀ k, (E.family.filter fun a => kind a = k).card ≤
      quota (Nat.card (Face P 3)) (nonsimplicialFacets P).card
        (quadrilateralFaces P).card k := by
  intro k
  rw [ActualGrowthTarget.encoded_kind_card]
  simp only [hkind]
  exact (actual_rooted_quota_counts P hP hfacets root hroot k).le

end Papers.RationalityTen.SmallFacetTargetBudgets

end
end
end BundlePart5

section BundlePart6
/- Source: ActualLiteralGrowthTarget.lean -/





@[expose] public section
noncomputable section
namespace Papers.RationalityTen.LiteralMaskGeometry
open Finset Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open MatroidChecked.FacetBoundaryEncoding
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming

/-- Every actual encoded boundary is a target for the literal growth
problem, once its checked mask records and genuine count bounds are supplied. -/
theorem actual_literal_target {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hcell : ∀ a, WellFormed (cells a))
    (E : Encoding P lab (fun a => decodeCell (cells a))) (hP : P.dim = 4)
    (quota : ℕ → ℕ)
    (hbudget : ∀ k, (E.family.filter fun a => (cells a).kind = k).card ≤ quota k) :
    Target (fun a => has (ConcreteGrowth.ridgeList cells a))
      (fun a b => ConcreteGrowth.compatible (cells a) (cells b))
      (fun a => (cells a).kind) quota E.family.toList := by
  apply ActualGrowthTarget.actual_growth_target E hP _ maskEquiv.symm
  · intro a q
    rw [ridge_list_semantics cells hcell a]
    change maskEquiv (maskEquiv.symm q) ∈ (decodeCell (cells a)).ridges ↔ _
    rw [maskEquiv.apply_symm_apply]
  · exact fun a b h => literal_compatible_of_compatible (cells a) (cells b)
      (hcell a) (hcell b) h
  · exact hbudget

end Papers.RationalityTen.LiteralMaskGeometry

end
end
end BundlePart6

section BundlePart7
/- Source: CellFacetInvariants.lean -/






@[expose] public section

/-!
# Intrinsic facet counts recovered from complete finite cells

For a three-dimensional facet, its polygon excess is three times its
vertex count minus its edge count minus six. Both counts are preserved by
the exact cell encoding. This identifies the finite search's kind labels
with the actual nonsimplicial and square-pyramid partition.
-/

noncomputable section
namespace Papers.RationalityTen.CellFacetInvariants

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus ChirotopeDensity
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport

variable {d n c : ℕ}

theorem actualCell_vertex_card (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P 3) : (actualCell P lab F).vertices.card = facetVertexCount P F :=
  ActualFaceTransport.labels_card P lab F

theorem actualCell_edge_card (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P 3) :
    (actualCell P lab F).edges.card = Nat.card (FaceBelow P F.val.carrier 1) := by
  change (((Finset.univ : Finset (Face P 1)).filter
    (fun e => e.val.carrier ⊆ F.val.carrier)).image (faceLabels P lab)).card = _
  rw [Finset.card_image_of_injective _ (faceLabels_injective P lab)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem actualCell_excess (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (F : Face P 3) : cellExcess (actualCell P lab F) = facetPolygonExcess P F := by
  rw [cellExcess, actualCell_vertex_card, actualCell_edge_card,
    facet_polygon_excess_formula]

/-- Literal kind metadata, checked once per cell, agree with the actual
facet partition at every member of the encoded family. -/
theorem actual_kind_of_checks {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (cells : Fin c → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => LiteralMaskGeometry.decodeCell (cells i)))
    (root : Fin c) (F : Face P 3) (hroot : E.index F = root)
    (hcheck : ∀ i, KindCheck cells root i) (G : Face P 3) :
    (cells (E.index G)).kind =
      SmallFacetTargetBudgets.partitionKind (nonsimplicialFacets P)
        (SmallFacetTargetBudgets.squareFacets P) F G := by
  have hi := hcheck (E.index G)
  unfold KindCheck at hi
  rw [E.index_spec, actualCell_vertex_card, actualCell_excess] at hi
  have hroot_iff : E.index G = root ↔ G = F := by
    rw [← hroot]
    exact E.index_injective.eq_iff
  simpa only [SmallFacetTargetBudgets.partitionKind, hroot_iff,
    mem_nonsimplicialFacets, SmallFacetTargetBudgets.squareFacets,
    Finset.mem_filter, Finset.mem_univ, true_and] using hi

/-- A normalized actual small-facet residual supplies the complete literal
growth target with the exact paper budget, after finite record checks. -/
theorem actual_small_literal_target {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (cells : Fin c → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => LiteralMaskGeometry.decodeCell (cells i)))
    (hP : P.dim = 4) (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (root : Fin c) (F : Face P 3) (hroot : E.index F = root)
    (hF : facetVertexCount P F = 5 ∧ facetPolygonExcess P F = 0)
    (hwell : ∀ i, LiteralMaskGeometry.WellFormed (cells i))
    (hkind : ∀ i, KindCheck cells root i) :
    GrowthRenaming.Target (fun a => SparseGrowthDAG.has (ConcreteGrowth.ridgeList cells a))
      (fun a b => ConcreteGrowth.compatible (cells a) (cells b))
      (fun a => (cells a).kind)
      (SmallFacetTargetBudgets.quota (Nat.card (Face P 3))
        (nonsimplicialFacets P).card (quadrilateralFaces P).card) E.family.toList := by
  apply LiteralMaskGeometry.actual_literal_target cells hwell E hP
  exact SmallFacetTargetBudgets.encoded_rooted_quota E hP hfacets F hF
    (fun i => (cells i).kind) (actual_kind_of_checks cells E root F hroot hkind)

end Papers.RationalityTen.CellFacetInvariants

end
end
end BundlePart7

section BundlePart8
/- Source: FullSmallFacetTargetBudgets.lean -/




@[expose] public section

/-!
# Exact quotas without a distinguished facet

The graph-first search uses every tetrahedron, bipyramid and square pyramid
on the ten labels. The quotas count the complete facet classes, so no
distinguished root is removed from the bipyramid count.
-/

noncomputable section
namespace Papers.RationalityTen.FullSmallFacetTargetBudgets

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus ChirotopeDensity
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry CellFacetInvariants
open SmallFacetTargetBudgets

def partitionKind {α : Type*} [DecidableEq α] (N Q : Finset α) (a : α) : ℕ :=
  if a ∈ N then if a ∈ Q then 3 else 2 else 1

def quota (m E q : ℕ) : ℕ → ℕ
  | 1 => m - E
  | 2 => E - 2 * q
  | 3 => 2 * q
  | _ => 0

theorem partition_kind_counts {α : Type*} [Fintype α] [DecidableEq α]
    (N Q : Finset α) (hQN : Q ⊆ N) (q : ℕ) (hQ : Q.card = 2 * q) :
    ∀ k, ((Finset.univ : Finset α).filter fun a => partitionKind N Q a = k).card =
      quota (Fintype.card α) N.card q k := by
  have h1 : Finset.univ.filter (fun a => partitionKind N Q a = 1) = Finset.univ \ N := by
    ext a
    by_cases hn : a ∈ N <;> by_cases hq : a ∈ Q <;> simp [partitionKind, hn, hq]
  have h2 : Finset.univ.filter (fun a => partitionKind N Q a = 2) = N \ Q := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    by_cases hn : a ∈ N <;> by_cases hq : a ∈ Q <;> simp [partitionKind, hn, hq]
  have h3 : Finset.univ.filter (fun a => partitionKind N Q a = 3) = Q := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hn : a ∈ N
    · by_cases hq : a ∈ Q <;> simp [partitionKind, hn, hq]
    · have hq : a ∉ Q := fun h => hn (hQN h)
      simp [partitionKind, hn, hq]
  intro k
  by_cases hk1 : k = 1
  · subst k
    rw [h1, Finset.card_sdiff_of_subset (Finset.subset_univ N), Finset.card_univ]
    rfl
  by_cases hk2 : k = 2
  · subst k
    rw [h2, Finset.card_sdiff_of_subset hQN, hQ]
    rfl
  by_cases hk3 : k = 3
  · subst k
    rw [h3, hQ]
    rfl
  have hempty : Finset.univ.filter (fun a => partitionKind N Q a = k) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a _
    simp only [partitionKind]
    split_ifs <;> omega
  rw [hempty, Finset.card_empty]
  unfold quota
  split <;> omega

theorem actual_quota_counts {d : ℕ} (P : ConvexPolytope d) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    ∀ k, ((Finset.univ : Finset (Face P 3)).filter fun F =>
      partitionKind (nonsimplicialFacets P) (squareFacets P) F = k).card =
        quota (Nat.card (Face P 3)) (nonsimplicialFacets P).card
          (quadrilateralFaces P).card k := by
  have h := partition_kind_counts (nonsimplicialFacets P) (squareFacets P)
    (squareFacets_subset_nonsimplicial P) (quadrilateralFaces P).card
    (squareFacets_card P hP hfacets)
  simpa only [Nat.card_eq_fintype_card] using h

theorem actual_kind_of_checks {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (hcheck : ∀ i, UnrootedKindCheck cells i) (F : Face P 3) :
    (cells (E.index F)).kind =
      partitionKind (nonsimplicialFacets P) (squareFacets P) F := by
  have hi := hcheck (E.index F)
  unfold UnrootedKindCheck at hi
  rw [E.index_spec, actualCell_vertex_card, actualCell_excess] at hi
  simpa only [partitionKind, mem_nonsimplicialFacets, squareFacets,
    Finset.mem_filter, Finset.mem_univ, true_and] using hi

theorem actual_literal_target {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (hP : P.dim = 4) (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5)
    (hwell : ∀ i, WellFormed (cells i)) (hkind : ∀ i, UnrootedKindCheck cells i) :
    GrowthRenaming.Target (fun a => SparseGrowthDAG.has (ConcreteGrowth.ridgeList cells a))
      (fun a b => ConcreteGrowth.compatible (cells a) (cells b)) (fun a => (cells a).kind)
      (quota (Nat.card (Face P 3)) (nonsimplicialFacets P).card
        (quadrilateralFaces P).card) E.family.toList := by
  apply LiteralMaskGeometry.actual_literal_target cells hwell E hP
  intro k
  rw [ActualGrowthTarget.encoded_kind_card]
  simp only [actual_kind_of_checks cells E hkind]
  exact (actual_quota_counts P hP hfacets k).le

end Papers.RationalityTen.FullSmallFacetTargetBudgets

end
end
end BundlePart8

section BundlePart9
/- Source: ActualFacetInducedGraph.lean -/





@[expose] public section

/-!
# Facets carry the induced actual edge graph

An exposed face is the convex hull of its vertices. Therefore an actual
edge whose endpoints lie in a facet lies wholly in that facet. The literal
adapter records this as equality with the restriction of the global graph,
including its exact edge count.
-/

noncomputable section
namespace Papers.RationalityTen.ActualFacetInducedGraph

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry

def actualGraphEdges {d n : ℕ} (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n) :
    Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Face P 1)).image (faceLabels P lab)

/-- Equality of the full edge sets, not merely preservation of selected
edges or an inequality between their numbers. -/
theorem actual_facet_edges_induced {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3) :
    (actualCell P lab F).edges =
      (actualGraphEdges P lab).filter fun e => e ⊆ (actualCell P lab F).vertices := by
  ext e
  rw [actualCell_edge_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩,
        (faceLabels_subset_iff P lab a F).mpr ha⟩
  · intro he
    obtain ⟨hglobal, hsub⟩ := Finset.mem_filter.mp he
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hglobal
    exact ⟨a, (faceLabels_subset_iff P lab a F).mp hsub, rfl⟩

/-- Every selected candidate is an induced subgraph of the same actual
global edge set represented by the union of all selected facets. -/
theorem encoded_facet_edges_induced {d n c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n}
    (E : Encoding P lab cells) (hP : P.dim = 4) (i : Fin c) (hi : i ∈ E.family) :
    (cells i).edges =
      (E.family.biUnion fun j => (cells j).edges).filter fun e => e ⊆ (cells i).vertices := by
  obtain ⟨F, rfl⟩ := (E.mem_family i).mp hi
  rw [E.edges_eq_actual hP, E.index_spec]
  exact actual_facet_edges_induced P lab F

def literalGraphEdges {c : ℕ} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : Finset (Fin c)) : Finset ℕ :=
  selected.biUnion fun a => (cells a).edges.toFinset

theorem literalGraphEdges_bound {c : ℕ} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : Finset (Fin c)) (hwell : ∀ i, WellFormed (cells i))
    {e : ℕ} (he : e ∈ literalGraphEdges cells selected) : e < 1024 := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
  exact (hwell i).edges_bound e (List.mem_toFinset.mp hi)

theorem literalGraphEdges_image {c : ℕ} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : Finset (Fin c)) :
    (literalGraphEdges cells selected).image maskSet =
      selected.biUnion fun a => (decodeCell (cells a)).edges := by
  exact Finset.biUnion_image

/-- The global mask graph has exactly the actual number of edges. Bounded
mask injectivity prevents collisions in this cardinality statement. -/
theorem literalGraphEdges_card {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4) :
    (literalGraphEdges cells E.family).card = Nat.card (Face P 1) := by
  have hinj : Set.InjOn maskSet (literalGraphEdges cells E.family) := by
    intro a ha b hb hab
    exact maskSet_injective (literalGraphEdges_bound cells E.family hwell ha)
      (literalGraphEdges_bound cells E.family hwell hb) hab
  rw [← Finset.card_image_of_injOn hinj, literalGraphEdges_image]
  exact E.edge_card hP

/-- Every mask in the global literal graph represents exactly two vertices. -/
theorem literalGraphEdges_two_vertices {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    {e : ℕ} (he : e ∈ literalGraphEdges cells E.family) : (maskSet e).card = 2 := by
  have h : maskSet e ∈ (literalGraphEdges cells E.family).image maskSet :=
    Finset.mem_image.mpr ⟨e, he, rfl⟩
  rw [literalGraphEdges_image, E.edges_eq_actual hP] at h
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
  rw [← ha]
  exact (ActualFaceTransport.labels_card P lab a).trans (one_face_vertex_card P a)

/-- Literal vertex incidence counts equal actual edge incidence counts. -/
theorem literalGraphEdges_incidence_card {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (v : Fin 10) :
    ((literalGraphEdges cells E.family).filter fun e => e.testBit v.val = true).card =
      Nat.card (IncidentFace P (lab.symm v).val 1) := by
  let G := literalGraphEdges cells E.family
  have hfiltered : ((G.image maskSet).filter fun S => v ∈ S).card =
      (G.filter fun e => e.testBit v.val = true).card := by
    rw [Finset.filter_image]
    have hinj : Set.InjOn maskSet (G.filter fun e => v ∈ maskSet e) := by
      intro a ha b hb hab
      exact maskSet_injective
        (literalGraphEdges_bound cells E.family hwell (Finset.mem_filter.mp ha).1)
        (literalGraphEdges_bound cells E.family hwell (Finset.mem_filter.mp hb).1) hab
    rw [Finset.card_image_of_injOn hinj]
    simp only [mem_maskSet]
  calc
    _ = ((G.image maskSet).filter fun S => v ∈ S).card := hfiltered.symm
    _ = Nat.card (IncidentFace P (lab.symm v).val 1) := by
      dsimp only [G]
      rw [literalGraphEdges_image, E.edges_eq_actual hP, Finset.filter_image,
        Finset.card_image_of_injective _ (faceLabels_injective P lab)]
      simp only [mem_faceLabels_iff, IncidentFace, Nat.card_eq_fintype_card,
        Fintype.card_subtype]

/-- Nonsimplicity of the original vertices gives the minimum degree five
used in the complete complement-graph enumeration. -/
theorem literal_nonsimple_degree_ge_five {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v) (v : Fin 10) :
    5 ≤ ((literalGraphEdges cells E.family).filter fun e => e.testBit v.val = true).card := by
  rw [literalGraphEdges_incidence_card cells hwell E hP v]
  apply MatroidChecked.IncidentFacetSimplicity.nonsimple_incident_edges_ge_five
    P hP (lab.symm v)
  intro hfour
  apply hnonsimple (lab.symm v)
  change (polytopeGraph P).degree (lab.symm v) = P.dim
  rw [← NineBipyramidIncidence.vertexGraph_eq_polytopeGraph,
    MatroidChecked.IncidentFacetSimplicity.degree_eq_actual_neighbors, hfour, hP]

/-- A literal facet's edge masks are precisely the global graph's masks
whose two endpoints lie in its vertex mask. -/
theorem literal_facet_edges_induced {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (i : Fin c) (hi : i ∈ E.family) :
    (cells i).edges.toFinset = (literalGraphEdges cells E.family).filter
      fun e => Nat.land e (cells i).vertices = e := by
  have hdecoded := encoded_facet_edges_induced E hP i hi
  ext e
  constructor
  · intro he
    have heList := List.mem_toFinset.mp he
    have hbound := (hwell i).edges_bound e heList
    have hgeometry : maskSet e ∈ (decodeCell (cells i)).edges :=
      (mask_mem_image_iff (cells i).edges (hwell i).edges_bound hbound).mpr heList
    rw [hdecoded] at hgeometry
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨i, hi, he⟩,
        (maskSet_subset_iff hbound).mp (Finset.mem_filter.mp hgeometry).2⟩
  · intro he
    obtain ⟨hglobal, hsub⟩ := Finset.mem_filter.mp he
    have hbound := literalGraphEdges_bound cells E.family hwell hglobal
    have hgeometry : maskSet e ∈ (decodeCell (cells i)).edges := by
      rw [hdecoded]
      apply Finset.mem_filter.mpr
      refine ⟨?_, (maskSet_subset_iff hbound).mpr hsub⟩
      rw [← literalGraphEdges_image]
      exact Finset.mem_image.mpr ⟨e, hglobal, rfl⟩
    exact List.mem_toFinset.mpr
      ((mask_mem_image_iff (cells i).edges (hwell i).edges_bound hbound).mp hgeometry)

end Papers.RationalityTen.ActualFacetInducedGraph

end
end
end BundlePart9

section BundlePart10
/- Source: EncodedNonedgeFacetCoverage.lean -/






@[expose] public section

/-!
# The exact internal-nonedge budget in literal vertex masks

Every unordered pair is encoded injectively as a two-bit mask. The union
of internal missing pairs in the selected candidate facets therefore has
the cardinal proved for the genuine convex polytope. These statements
justify both missing-pair capacity cuts and forced-pair branching.
-/

noncomputable section
namespace Papers.RationalityTen.EncodedNonedgeFacetCoverage

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeBalinski Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeNonedgeAllocation
open Papers.PolytopeFaceNonedges Papers.PolytopeFacetSurplus
open MatroidChecked.FacetBoundaryEncoding
open ChirotopeDensity LiteralMaskGeometry ActualFacetInducedGraph

def pairLabels {d n : ℕ} (P : ConvexPolytope d) (lab : P.vertices ≃ Fin n)
    (e : Sym2 P.vertices) : Finset (Fin n) := e.toFinset.image lab

@[simp] theorem mem_pairLabels {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (e : Sym2 P.vertices) (v : Fin n) :
    v ∈ pairLabels P lab e ↔ lab.symm v ∈ e := by
  constructor
  · intro h
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp h
    have hwv : w = lab.symm v := (lab.eq_symm_apply).mpr hwe
    simpa only [hwv, Sym2.mem_toFinset] using hw
  · intro h
    exact Finset.mem_image.mpr
      ⟨lab.symm v, Sym2.mem_toFinset.mpr h, lab.apply_symm_apply v⟩

theorem pairLabels_injective {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) : Function.Injective (pairLabels P lab) := by
  intro a b h
  apply Sym2.ext
  intro v
  have hv := Finset.ext_iff.mp h (lab v)
  simpa only [mem_pairLabels, lab.symm_apply_apply] using hv

theorem faceLabels_edgeFace {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (e : (vertexGraph P).edgeSet) :
    faceLabels P lab (edgeFace P e) = pairLabels P lab e.val := by
  ext v
  rw [mem_faceLabels_iff, edgeFace_vertex_iff, mem_pairLabels]

theorem pairLabels_mem_actualGraphEdges {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (e : Sym2 P.vertices) :
    pairLabels P lab e ∈ actualGraphEdges P lab ↔ e ∈ (vertexGraph P).edgeSet := by
  constructor
  · intro h
    obtain ⟨F, _, hF⟩ := Finset.mem_image.mp h
    obtain ⟨a, rfl⟩ := edgeFace_surjective P F
    rw [faceLabels_edgeFace] at hF
    have he := pairLabels_injective P lab hF
    exact he ▸ a.property
  · intro h
    exact Finset.mem_image.mpr
      ⟨edgeFace P ⟨e, h⟩, Finset.mem_univ _, faceLabels_edgeFace P lab ⟨e, h⟩⟩

theorem nonedge_pairLabels_card {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (e : Nonedge P) : (pairLabels P lab e.val).card = 2 := by
  have hne := (nonedge_out P e).1
  unfold pairLabels
  rw [← Sym2.mk_fst_out_snd_out e.val, Sym2.toFinset_mk_eq,
    Finset.image_insert, Finset.image_singleton]
  exact Finset.card_pair (lab.injective.ne hne)

theorem nonedge_pairLabels_not_edge {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (e : Nonedge P) :
    pairLabels P lab e.val ∉ actualGraphEdges P lab := by
  intro h
  have he := (pairLabels_mem_actualGraphEdges P lab e.val).mp h
  have hstep : GeneralVertexStep P e.val.out.1.val e.val.out.2.val :=
    edge_out_adj P ⟨e.val, he⟩
  exact (nonedge_out P e).2 hstep

theorem pairLabels_subset_face_iff {d n k : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (e : Nonedge P) (F : Face P k) :
    pairLabels P lab e.val ⊆ faceLabels P lab F ↔ Within P F.val.carrier e := by
  rw [within_iff]
  constructor
  · intro h v hv
    have hv' : lab v ∈ pairLabels P lab e.val := by
      simpa only [mem_pairLabels, lab.symm_apply_apply] using hv
    simpa only [mem_faceLabels_iff, lab.symm_apply_apply] using h hv'
  · intro h v hv
    exact (mem_faceLabels_iff P lab F v).mpr (h _ ((mem_pairLabels P lab e.val v).mp hv))

theorem exists_nonedge_of_pair_not_edge {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (S : Finset (Fin n)) (hS : S.card = 2)
    (hnon : S ∉ actualGraphEdges P lab) :
    ∃ e : Nonedge P, pairLabels P lab e.val = S := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  let x := lab.symm a
  let y := lab.symm b
  have hxy : x ≠ y := fun h => hab (lab.symm.injective h)
  have hlabel : pairLabels P lab s(x, y) = {a, b} := by
    simp only [pairLabels, Sym2.toFinset_mk_eq, Finset.image_insert, Finset.image_singleton,
      x, y, lab.apply_symm_apply]
  have he : s(x, y) ∉ (vertexGraph P).edgeSet := by
    intro h
    exact hnon (hlabel ▸ (pairLabels_mem_actualGraphEdges P lab s(x, y)).mpr h)
  have hc : s(x, y) ∈ (vertexGraph P)ᶜ.edgeSet := by
    change (vertexGraph P)ᶜ.Adj x y
    exact (SimpleGraph.compl_adj _ _ _).mpr ⟨hxy, he⟩
  exact ⟨⟨s(x, y), hc⟩, hlabel⟩

/-- A candidate's missing pairs use its complete induced edge graph. -/
def cellInternalNonedges {n : ℕ} (C : Cell n) : Finset (Finset (Fin n)) :=
  C.vertices.powersetCard 2 \ C.edges

theorem mem_actual_cellInternalNonedges {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) (F : Face P 3) (S : Finset (Fin n)) :
    S ∈ cellInternalNonedges (actualCell P lab F) ↔
      ∃ e : Nonedge P, Within P F.val.carrier e ∧ pairLabels P lab e.val = S := by
  constructor
  · intro h
    obtain ⟨hS, hnot⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
    have hglobal : S ∉ actualGraphEdges P lab := by
      intro h
      apply hnot
      rw [actual_facet_edges_induced]
      exact Finset.mem_filter.mpr ⟨h, hsub⟩
    obtain ⟨e, rfl⟩ := exists_nonedge_of_pair_not_edge P lab S hcard hglobal
    exact ⟨e, (pairLabels_subset_face_iff P lab e F).mp hsub, rfl⟩
  · rintro ⟨e, he, rfl⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_powersetCard.mpr
      ⟨(pairLabels_subset_face_iff P lab e F).mpr he, nonedge_pairLabels_card P lab e⟩, ?_⟩
    rw [actual_facet_edges_induced]
    exact fun h => nonedge_pairLabels_not_edge P lab e (Finset.mem_filter.mp h).1

theorem actual_internal_nonedge_labels {d n : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin n) :
    (Finset.univ : Finset (Face P 3)).biUnion
      (fun F => cellInternalNonedges (actualCell P lab F)) =
        (coveredNonedges P).image (fun e => pairLabels P lab e.val) := by
  ext S
  constructor
  · intro h
    obtain ⟨F, _, hF⟩ := Finset.mem_biUnion.mp h
    obtain ⟨e, he, rfl⟩ := (mem_actual_cellInternalNonedges P lab F S).mp hF
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩⟩, rfl⟩
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨F, hF⟩ := (Finset.mem_filter.mp he).2
    apply Finset.mem_biUnion.mpr
    exact ⟨F, Finset.mem_univ _, (mem_actual_cellInternalNonedges P lab F _).mpr
      ⟨e, (Finset.mem_filter.mp hF).2, rfl⟩⟩

theorem encoded_internal_nonedge_card_eq_covered {d n c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n}
    (E : Encoding P lab cells) :
    (E.family.biUnion fun i => cellInternalNonedges (cells i)).card =
      (coveredNonedges P).card := by
  have hunion : (E.family.biUnion fun i => cellInternalNonedges (cells i)) =
      (Finset.univ : Finset (Face P 3)).biUnion
        (fun F => cellInternalNonedges (actualCell P lab F)) := by
    ext S
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, hS⟩
      obtain ⟨F, rfl⟩ := (E.mem_family i).mp hi
      exact ⟨F, E.index_spec F ▸ hS⟩
    · rintro ⟨F, hS⟩
      exact ⟨E.index F, (E.mem_family _).mpr ⟨F, rfl⟩, (E.index_spec F).symm ▸ hS⟩
  rw [hunion, actual_internal_nonedge_labels,
    Finset.card_image_of_injective _ (fun a b h => Subtype.ext (pairLabels_injective P lab h))]

theorem encoded_internal_nonedge_card {d n c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin n} {cells : Fin c → Cell n}
    (E : Encoding P lab cells) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    (E.family.biUnion fun i => cellInternalNonedges (cells i)).card =
      (nonsimplicialFacets P).card := by
  rw [encoded_internal_nonedge_card_eq_covered E]
  exact small_facet_covered_nonedge_card P hP hfacets

/-- Executable mask description of all missing pairs inside a literal cell. -/
def cellInternalNonedgeMasks (C : ConcreteGrowth.Cell) : Finset ℕ :=
  (Finset.range 1024).filter fun e =>
    (maskSet e).card = 2 ∧ Nat.land e C.vertices = e ∧ e ∉ C.edges

def internalNonedgeMasks {c : ℕ} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : Finset (Fin c)) : Finset ℕ :=
  selected.biUnion fun i => cellInternalNonedgeMasks (cells i)

theorem cellInternalNonedgeMasks_image (C : ConcreteGrowth.Cell) (hC : WellFormed C) :
    (cellInternalNonedgeMasks C).image maskSet = cellInternalNonedges (decodeCell C) := by
  ext S
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hbound, hcard, hsub, hnot⟩ := Finset.mem_filter.mp he
    have hb : e < 1024 := Finset.mem_range.mp hbound
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_powersetCard.mpr ⟨(maskSet_subset_iff hb).mpr hsub, hcard⟩,
      fun h => hnot ((mask_mem_image_iff C.edges hC.edges_bound hb).mp h)⟩
  · intro h
    obtain ⟨hS, hnot⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
    let e : Fin 1024 := maskEquiv.symm S
    have he : maskSet e.val = S := maskEquiv.apply_symm_apply S
    refine Finset.mem_image.mpr ⟨e.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr e.isLt,
      ?_, ?_, ?_⟩, he⟩
    · simpa only [he] using hcard
    · exact (maskSet_subset_iff e.isLt).mp (he.symm ▸ hsub)
    · intro hm
      apply hnot
      rw [← he]
      exact (mask_mem_image_iff C.edges hC.edges_bound e.isLt).mpr hm

theorem internalNonedgeMasks_image {c : ℕ} (cells : Fin c → ConcreteGrowth.Cell)
    (selected : Finset (Fin c)) (hwell : ∀ i, WellFormed (cells i)) :
    (internalNonedgeMasks cells selected).image maskSet =
      selected.biUnion fun i => cellInternalNonedges (decodeCell (cells i)) := by
  rw [internalNonedgeMasks, Finset.biUnion_image]
  apply Finset.biUnion_congr rfl
  intro i _
  exact cellInternalNonedgeMasks_image (cells i) (hwell i)

/-- Every covered actual nonedge occurs exactly once in the literal union,
independently of the sizes of the actual facets. -/
theorem literal_internal_nonedge_card_eq_covered {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) :
    (internalNonedgeMasks cells E.family).card = (coveredNonedges P).card := by
  have hbound : ∀ e ∈ internalNonedgeMasks cells E.family, e < 1024 := by
    intro e he
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hinj : Set.InjOn maskSet (internalNonedgeMasks cells E.family) :=
    fun a ha b hb h => maskSet_injective (hbound a ha) (hbound b hb) h
  rw [← Finset.card_image_of_injOn hinj, internalNonedgeMasks_image cells E.family hwell]
  exact encoded_internal_nonedge_card_eq_covered E

/-- The finite graph search's full union of internal missing pairs has
exactly the actual nonsimplicial-facet count, with no search hypothesis. -/
theorem literal_internal_nonedge_card {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (hwell : ∀ i, WellFormed (cells i))
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    (internalNonedgeMasks cells E.family).card = (nonsimplicialFacets P).card := by
  rw [literal_internal_nonedge_card_eq_covered cells hwell E]
  exact small_facet_covered_nonedge_card P hP hfacets

end Papers.RationalityTen.EncodedNonedgeFacetCoverage

end
end
end BundlePart10

section BundlePart11
/- Source: FullSmallFacetActualCoverage.lean -/










@[expose] public section

/-!
# The full small-facet universe covers every actual boundary

The independent four- and five-vertex three-polytope classifications and
complete injection certificates cover all facets under any labeling of the
ten vertices. No distinguished facet, root compatibility or search success
is assumed. The resulting target also carries the exact induced graph and
the exact union of internal nonedges needed by graph-first pruning.
-/

noncomputable section
namespace Papers.RationalityTen.FullSmallFacetActualCoverage

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus
open ChirotopeDensity ActualSmallFacetClassification ActualFacetCatalogueTransport
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualFacetInducedGraph EncodedNonedgeFacetCoverage

private theorem face_polytope_vertex_card {d : ℕ} (P : ConvexPolytope d)
    (F : Face P 3) : (facePolytope P F.val.isFace).vertices.card = facetVertexCount P F := by
  simpa only [facetVertexCount, Nat.card_eq_fintype_card, Fintype.card_coe] using
    (Nat.card_congr (faceVerticesEquiv P F.val.isFace)).symm

private theorem face_polytope_dim {d : ℕ} (P : ConvexPolytope d)
    (F : Face P 3) : (facePolytope P F.val.isFace).dim = 3 := by
  change faceDim (facePolytope P F.val.isFace).toSet = 3
  rw [facePolytope_toSet]
  exact F.property

/-- Complete coverage of an arbitrary actual small facet in an arbitrary
labeling, preserving all its vertices, edges and polygon ridges. -/
theorem covers_facet {d : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin 10) (F : Face P 3) (hF : facetVertexCount P F ≤ 5) :
    ∃ i, decodeCell (FacetUniverses.FullSmall.cells i) = actualCell P lab F := by
  have hmin : 4 ≤ facetVertexCount P F :=
    Nat.succ_le_iff.mpr (Papers.PolytopeThreeIncidences.face_vertex_card_gt_dimension P 3 F)
  have hc : facetVertexCount P F = 4 ∨ facetVertexCount P F = 5 := by omega
  rcases hc with h4 | h5
  · obtain ⟨loc, i, hi⟩ := four_vertex_classification (facePolytope P F.val.isFace)
      (face_polytope_dim P F) ((face_polytope_vertex_card P F).trans h4)
    have hi0 : i = 0 := Fin.eq_zero i
    subst i
    have hcell := actualCell_of_template P lab F loc (FiniteCycleCandidates.N4.templates 0) hi
    obtain ⟨j, hj⟩ := FullSmallFacetEmbeddings.T0.covers
      (ActualFaceTransport.labelEmbedding P lab F loc)
    exact ⟨j, hj.trans hcell.symm⟩
  · obtain ⟨loc, i, hi⟩ := five_vertex_classification (facePolytope P F.val.isFace)
      (face_polytope_dim P F) ((face_polytope_vertex_card P F).trans h5)
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · have hcell := actualCell_of_template P lab F loc (FiniteCycleCandidates.N5.templates 0) hi
      obtain ⟨j, hj⟩ := FullSmallFacetEmbeddings.T1.covers
        (ActualFaceTransport.labelEmbedding P lab F loc)
      exact ⟨j, hj.trans hcell.symm⟩
    · have hcell := actualCell_of_template P lab F loc (FiniteCycleCandidates.N5.templates 1) hi
      obtain ⟨j, hj⟩ := FullSmallFacetEmbeddings.T2.covers
        (ActualFaceTransport.labelEmbedding P lab F loc)
      exact ⟨j, hj.trans hcell.symm⟩

theorem encoding_exists {d : ℕ} (P : ConvexPolytope d)
    (lab : P.vertices ≃ Fin 10)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    Nonempty (Encoding P lab (fun i => decodeCell (FacetUniverses.FullSmall.cells i))) :=
  encoding_of_coverage P lab _ (fun F => covers_facet P lab F (hfacets F))

/-- The complete literal target exists with the original labeling. The
kind quotas are exactly `T=m-E`, `BP=E-2q`, `SP=2q`. -/
theorem actual_growth_target {d : ℕ} (P : ConvexPolytope d) (hP : P.dim = 4)
    (lab : P.vertices ≃ Fin 10)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    ∃ E : Encoding P lab (fun i => decodeCell (FacetUniverses.FullSmall.cells i)),
      GrowthRenaming.Target (fun a => SparseGrowthDAG.has (FacetUniverses.FullSmall.ridgeList a))
        FacetUniverses.FullSmall.literalCompatible FacetUniverses.FullSmall.kind
        (FullSmallFacetTargetBudgets.quota (Nat.card (Face P 3))
          (nonsimplicialFacets P).card (quadrilateralFaces P).card) E.family.toList := by
  obtain ⟨E⟩ := encoding_exists P lab hfacets
  exact ⟨E, FullSmallFacetTargetBudgets.actual_literal_target FacetUniverses.FullSmall.cells
    E hP hfacets FacetUniverses.FullSmall.cells_wellFormed
    FacetUniverses.FullSmall.cells_kind_correct⟩

/-- The target additionally carries the graph-first search's exact global
edge count, induced facet graphs, and internal-nonedge union cardinality. -/
theorem actual_graph_target {d : ℕ} (P : ConvexPolytope d) (hP : P.dim = 4)
    (lab : P.vertices ≃ Fin 10)
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 5) :
    ∃ E : Encoding P lab (fun i => decodeCell (FacetUniverses.FullSmall.cells i)),
      GrowthRenaming.Target (fun a => SparseGrowthDAG.has (FacetUniverses.FullSmall.ridgeList a))
        FacetUniverses.FullSmall.literalCompatible FacetUniverses.FullSmall.kind
        (FullSmallFacetTargetBudgets.quota (Nat.card (Face P 3))
          (nonsimplicialFacets P).card (quadrilateralFaces P).card) E.family.toList ∧
      (literalGraphEdges FacetUniverses.FullSmall.cells E.family).card = Nat.card (Face P 1) ∧
      (∀ i ∈ E.family, (FacetUniverses.FullSmall.cells i).edges.toFinset =
        (literalGraphEdges FacetUniverses.FullSmall.cells E.family).filter
          fun e => Nat.land e (FacetUniverses.FullSmall.cells i).vertices = e) ∧
      (internalNonedgeMasks FacetUniverses.FullSmall.cells E.family).card =
        (nonsimplicialFacets P).card := by
  obtain ⟨E, hE⟩ := actual_growth_target P hP lab hfacets
  refine ⟨E, hE, literalGraphEdges_card _ FacetUniverses.FullSmall.cells_wellFormed E hP,
    ?_, literal_internal_nonedge_card _ FacetUniverses.FullSmall.cells_wellFormed E hP hfacets⟩
  exact fun i hi => literal_facet_edges_induced _ FacetUniverses.FullSmall.cells_wellFormed E hP i hi

end Papers.RationalityTen.FullSmallFacetActualCoverage

end
end
end BundlePart11
