module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_5632 : FiniteChecks.Interval recordTest 5632 5648 :=
      FiniteChecks.interval_of_check recordTest 5632 16 (by decide +kernel)
    
theorem records_5648 : FiniteChecks.Interval recordTest 5648 5664 :=
      FiniteChecks.interval_of_check recordTest 5648 16 (by decide +kernel)
    
theorem records_5664 : FiniteChecks.Interval recordTest 5664 5680 :=
      FiniteChecks.interval_of_check recordTest 5664 16 (by decide +kernel)
    
theorem records_5680 : FiniteChecks.Interval recordTest 5680 5696 :=
      FiniteChecks.interval_of_check recordTest 5680 16 (by decide +kernel)
    
theorem records_5696 : FiniteChecks.Interval recordTest 5696 5712 :=
      FiniteChecks.interval_of_check recordTest 5696 16 (by decide +kernel)
    
theorem records_5712 : FiniteChecks.Interval recordTest 5712 5728 :=
      FiniteChecks.interval_of_check recordTest 5712 16 (by decide +kernel)
    
theorem records_5728 : FiniteChecks.Interval recordTest 5728 5744 :=
      FiniteChecks.interval_of_check recordTest 5728 16 (by decide +kernel)
    
theorem records_5744 : FiniteChecks.Interval recordTest 5744 5760 :=
      FiniteChecks.interval_of_check recordTest 5744 16 (by decide +kernel)
    
theorem records_5760 : FiniteChecks.Interval recordTest 5760 5776 :=
      FiniteChecks.interval_of_check recordTest 5760 16 (by decide +kernel)
    
theorem records_5776 : FiniteChecks.Interval recordTest 5776 5792 :=
      FiniteChecks.interval_of_check recordTest 5776 16 (by decide +kernel)
    
theorem records_5792 : FiniteChecks.Interval recordTest 5792 5808 :=
      FiniteChecks.interval_of_check recordTest 5792 16 (by decide +kernel)
    
theorem records_5808 : FiniteChecks.Interval recordTest 5808 5824 :=
      FiniteChecks.interval_of_check recordTest 5808 16 (by decide +kernel)
    
theorem records_5824 : FiniteChecks.Interval recordTest 5824 5840 :=
      FiniteChecks.interval_of_check recordTest 5824 16 (by decide +kernel)
    
theorem records_5840 : FiniteChecks.Interval recordTest 5840 5856 :=
      FiniteChecks.interval_of_check recordTest 5840 16 (by decide +kernel)
    
theorem records_5856 : FiniteChecks.Interval recordTest 5856 5872 :=
      FiniteChecks.interval_of_check recordTest 5856 16 (by decide +kernel)
    
theorem records_5872 : FiniteChecks.Interval recordTest 5872 5888 :=
      FiniteChecks.interval_of_check recordTest 5872 16 (by decide +kernel)
    
theorem records_5888 : FiniteChecks.Interval recordTest 5888 5904 :=
      FiniteChecks.interval_of_check recordTest 5888 16 (by decide +kernel)
    
theorem records_5904 : FiniteChecks.Interval recordTest 5904 5920 :=
      FiniteChecks.interval_of_check recordTest 5904 16 (by decide +kernel)
    
theorem records_5920 : FiniteChecks.Interval recordTest 5920 5936 :=
      FiniteChecks.interval_of_check recordTest 5920 16 (by decide +kernel)
    
theorem records_5936 : FiniteChecks.Interval recordTest 5936 5952 :=
      FiniteChecks.interval_of_check recordTest 5936 16 (by decide +kernel)
    
theorem records_5952 : FiniteChecks.Interval recordTest 5952 5968 :=
      FiniteChecks.interval_of_check recordTest 5952 16 (by decide +kernel)
    
theorem records_5968 : FiniteChecks.Interval recordTest 5968 5984 :=
      FiniteChecks.interval_of_check recordTest 5968 16 (by decide +kernel)
    
theorem records_5984 : FiniteChecks.Interval recordTest 5984 6000 :=
      FiniteChecks.interval_of_check recordTest 5984 16 (by decide +kernel)
    
theorem records_6000 : FiniteChecks.Interval recordTest 6000 6016 :=
      FiniteChecks.interval_of_check recordTest 6000 16 (by decide +kernel)
    
theorem records_6016 : FiniteChecks.Interval recordTest 6016 6032 :=
      FiniteChecks.interval_of_check recordTest 6016 16 (by decide +kernel)
    
theorem records_6032 : FiniteChecks.Interval recordTest 6032 6048 :=
      FiniteChecks.interval_of_check recordTest 6032 16 (by decide +kernel)
    
theorem records_6048 : FiniteChecks.Interval recordTest 6048 6064 :=
      FiniteChecks.interval_of_check recordTest 6048 16 (by decide +kernel)
    
theorem records_6064 : FiniteChecks.Interval recordTest 6064 6080 :=
      FiniteChecks.interval_of_check recordTest 6064 16 (by decide +kernel)
    
theorem records_6080 : FiniteChecks.Interval recordTest 6080 6096 :=
      FiniteChecks.interval_of_check recordTest 6080 16 (by decide +kernel)
    
theorem records_6096 : FiniteChecks.Interval recordTest 6096 6112 :=
      FiniteChecks.interval_of_check recordTest 6096 16 (by decide +kernel)
    
theorem records_6112 : FiniteChecks.Interval recordTest 6112 6128 :=
      FiniteChecks.interval_of_check recordTest 6112 16 (by decide +kernel)
    
theorem records_6128 : FiniteChecks.Interval recordTest 6128 6144 :=
      FiniteChecks.interval_of_check recordTest 6128 16 (by decide +kernel)
    
theorem records_join_5632_5664 : FiniteChecks.Interval recordTest 5632 5664 :=
  FiniteChecks.interval_append recordTest 5632 5648 5664 records_5632 records_5648

theorem records_join_5664_5696 : FiniteChecks.Interval recordTest 5664 5696 :=
  FiniteChecks.interval_append recordTest 5664 5680 5696 records_5664 records_5680

theorem records_join_5632_5696 : FiniteChecks.Interval recordTest 5632 5696 :=
  FiniteChecks.interval_append recordTest 5632 5664 5696 records_join_5632_5664 records_join_5664_5696

theorem records_join_5696_5728 : FiniteChecks.Interval recordTest 5696 5728 :=
  FiniteChecks.interval_append recordTest 5696 5712 5728 records_5696 records_5712

theorem records_join_5728_5760 : FiniteChecks.Interval recordTest 5728 5760 :=
  FiniteChecks.interval_append recordTest 5728 5744 5760 records_5728 records_5744

theorem records_join_5696_5760 : FiniteChecks.Interval recordTest 5696 5760 :=
  FiniteChecks.interval_append recordTest 5696 5728 5760 records_join_5696_5728 records_join_5728_5760

theorem records_join_5632_5760 : FiniteChecks.Interval recordTest 5632 5760 :=
  FiniteChecks.interval_append recordTest 5632 5696 5760 records_join_5632_5696 records_join_5696_5760

theorem records_join_5760_5792 : FiniteChecks.Interval recordTest 5760 5792 :=
  FiniteChecks.interval_append recordTest 5760 5776 5792 records_5760 records_5776

theorem records_join_5792_5824 : FiniteChecks.Interval recordTest 5792 5824 :=
  FiniteChecks.interval_append recordTest 5792 5808 5824 records_5792 records_5808

theorem records_join_5760_5824 : FiniteChecks.Interval recordTest 5760 5824 :=
  FiniteChecks.interval_append recordTest 5760 5792 5824 records_join_5760_5792 records_join_5792_5824

theorem records_join_5824_5856 : FiniteChecks.Interval recordTest 5824 5856 :=
  FiniteChecks.interval_append recordTest 5824 5840 5856 records_5824 records_5840

theorem records_join_5856_5888 : FiniteChecks.Interval recordTest 5856 5888 :=
  FiniteChecks.interval_append recordTest 5856 5872 5888 records_5856 records_5872

theorem records_join_5824_5888 : FiniteChecks.Interval recordTest 5824 5888 :=
  FiniteChecks.interval_append recordTest 5824 5856 5888 records_join_5824_5856 records_join_5856_5888

theorem records_join_5760_5888 : FiniteChecks.Interval recordTest 5760 5888 :=
  FiniteChecks.interval_append recordTest 5760 5824 5888 records_join_5760_5824 records_join_5824_5888

theorem records_join_5632_5888 : FiniteChecks.Interval recordTest 5632 5888 :=
  FiniteChecks.interval_append recordTest 5632 5760 5888 records_join_5632_5760 records_join_5760_5888

theorem records_join_5888_5920 : FiniteChecks.Interval recordTest 5888 5920 :=
  FiniteChecks.interval_append recordTest 5888 5904 5920 records_5888 records_5904

theorem records_join_5920_5952 : FiniteChecks.Interval recordTest 5920 5952 :=
  FiniteChecks.interval_append recordTest 5920 5936 5952 records_5920 records_5936

theorem records_join_5888_5952 : FiniteChecks.Interval recordTest 5888 5952 :=
  FiniteChecks.interval_append recordTest 5888 5920 5952 records_join_5888_5920 records_join_5920_5952

theorem records_join_5952_5984 : FiniteChecks.Interval recordTest 5952 5984 :=
  FiniteChecks.interval_append recordTest 5952 5968 5984 records_5952 records_5968

theorem records_join_5984_6016 : FiniteChecks.Interval recordTest 5984 6016 :=
  FiniteChecks.interval_append recordTest 5984 6000 6016 records_5984 records_6000

theorem records_join_5952_6016 : FiniteChecks.Interval recordTest 5952 6016 :=
  FiniteChecks.interval_append recordTest 5952 5984 6016 records_join_5952_5984 records_join_5984_6016

theorem records_join_5888_6016 : FiniteChecks.Interval recordTest 5888 6016 :=
  FiniteChecks.interval_append recordTest 5888 5952 6016 records_join_5888_5952 records_join_5952_6016

theorem records_join_6016_6048 : FiniteChecks.Interval recordTest 6016 6048 :=
  FiniteChecks.interval_append recordTest 6016 6032 6048 records_6016 records_6032

theorem records_join_6048_6080 : FiniteChecks.Interval recordTest 6048 6080 :=
  FiniteChecks.interval_append recordTest 6048 6064 6080 records_6048 records_6064

theorem records_join_6016_6080 : FiniteChecks.Interval recordTest 6016 6080 :=
  FiniteChecks.interval_append recordTest 6016 6048 6080 records_join_6016_6048 records_join_6048_6080

theorem records_join_6080_6112 : FiniteChecks.Interval recordTest 6080 6112 :=
  FiniteChecks.interval_append recordTest 6080 6096 6112 records_6080 records_6096

theorem records_join_6112_6144 : FiniteChecks.Interval recordTest 6112 6144 :=
  FiniteChecks.interval_append recordTest 6112 6128 6144 records_6112 records_6128

theorem records_join_6080_6144 : FiniteChecks.Interval recordTest 6080 6144 :=
  FiniteChecks.interval_append recordTest 6080 6112 6144 records_join_6080_6112 records_join_6112_6144

theorem records_join_6016_6144 : FiniteChecks.Interval recordTest 6016 6144 :=
  FiniteChecks.interval_append recordTest 6016 6080 6144 records_join_6016_6080 records_join_6080_6144

theorem records_join_5888_6144 : FiniteChecks.Interval recordTest 5888 6144 :=
  FiniteChecks.interval_append recordTest 5888 6016 6144 records_join_5888_6016 records_join_6016_6144

theorem records_join_5632_6144 : FiniteChecks.Interval recordTest 5632 6144 :=
  FiniteChecks.interval_append recordTest 5632 5888 6144 records_join_5632_5888 records_join_5888_6144

theorem records_part_011 : FiniteChecks.Interval recordTest 5632 6144 := records_join_5632_6144
    end Papers.RationalityTen.FacetUniverses.FullSmall
    