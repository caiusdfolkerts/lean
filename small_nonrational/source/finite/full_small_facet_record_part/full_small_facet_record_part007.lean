module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_3584 : FiniteChecks.Interval recordTest 3584 3600 :=
      FiniteChecks.interval_of_check recordTest 3584 16 (by decide +kernel)
    
theorem records_3600 : FiniteChecks.Interval recordTest 3600 3616 :=
      FiniteChecks.interval_of_check recordTest 3600 16 (by decide +kernel)
    
theorem records_3616 : FiniteChecks.Interval recordTest 3616 3632 :=
      FiniteChecks.interval_of_check recordTest 3616 16 (by decide +kernel)
    
theorem records_3632 : FiniteChecks.Interval recordTest 3632 3648 :=
      FiniteChecks.interval_of_check recordTest 3632 16 (by decide +kernel)
    
theorem records_3648 : FiniteChecks.Interval recordTest 3648 3664 :=
      FiniteChecks.interval_of_check recordTest 3648 16 (by decide +kernel)
    
theorem records_3664 : FiniteChecks.Interval recordTest 3664 3680 :=
      FiniteChecks.interval_of_check recordTest 3664 16 (by decide +kernel)
    
theorem records_3680 : FiniteChecks.Interval recordTest 3680 3696 :=
      FiniteChecks.interval_of_check recordTest 3680 16 (by decide +kernel)
    
theorem records_3696 : FiniteChecks.Interval recordTest 3696 3712 :=
      FiniteChecks.interval_of_check recordTest 3696 16 (by decide +kernel)
    
theorem records_3712 : FiniteChecks.Interval recordTest 3712 3728 :=
      FiniteChecks.interval_of_check recordTest 3712 16 (by decide +kernel)
    
theorem records_3728 : FiniteChecks.Interval recordTest 3728 3744 :=
      FiniteChecks.interval_of_check recordTest 3728 16 (by decide +kernel)
    
theorem records_3744 : FiniteChecks.Interval recordTest 3744 3760 :=
      FiniteChecks.interval_of_check recordTest 3744 16 (by decide +kernel)
    
theorem records_3760 : FiniteChecks.Interval recordTest 3760 3776 :=
      FiniteChecks.interval_of_check recordTest 3760 16 (by decide +kernel)
    
theorem records_3776 : FiniteChecks.Interval recordTest 3776 3792 :=
      FiniteChecks.interval_of_check recordTest 3776 16 (by decide +kernel)
    
theorem records_3792 : FiniteChecks.Interval recordTest 3792 3808 :=
      FiniteChecks.interval_of_check recordTest 3792 16 (by decide +kernel)
    
theorem records_3808 : FiniteChecks.Interval recordTest 3808 3824 :=
      FiniteChecks.interval_of_check recordTest 3808 16 (by decide +kernel)
    
theorem records_3824 : FiniteChecks.Interval recordTest 3824 3840 :=
      FiniteChecks.interval_of_check recordTest 3824 16 (by decide +kernel)
    
theorem records_3840 : FiniteChecks.Interval recordTest 3840 3856 :=
      FiniteChecks.interval_of_check recordTest 3840 16 (by decide +kernel)
    
theorem records_3856 : FiniteChecks.Interval recordTest 3856 3872 :=
      FiniteChecks.interval_of_check recordTest 3856 16 (by decide +kernel)
    
theorem records_3872 : FiniteChecks.Interval recordTest 3872 3888 :=
      FiniteChecks.interval_of_check recordTest 3872 16 (by decide +kernel)
    
theorem records_3888 : FiniteChecks.Interval recordTest 3888 3904 :=
      FiniteChecks.interval_of_check recordTest 3888 16 (by decide +kernel)
    
theorem records_3904 : FiniteChecks.Interval recordTest 3904 3920 :=
      FiniteChecks.interval_of_check recordTest 3904 16 (by decide +kernel)
    
theorem records_3920 : FiniteChecks.Interval recordTest 3920 3936 :=
      FiniteChecks.interval_of_check recordTest 3920 16 (by decide +kernel)
    
theorem records_3936 : FiniteChecks.Interval recordTest 3936 3952 :=
      FiniteChecks.interval_of_check recordTest 3936 16 (by decide +kernel)
    
theorem records_3952 : FiniteChecks.Interval recordTest 3952 3968 :=
      FiniteChecks.interval_of_check recordTest 3952 16 (by decide +kernel)
    
theorem records_3968 : FiniteChecks.Interval recordTest 3968 3984 :=
      FiniteChecks.interval_of_check recordTest 3968 16 (by decide +kernel)
    
theorem records_3984 : FiniteChecks.Interval recordTest 3984 4000 :=
      FiniteChecks.interval_of_check recordTest 3984 16 (by decide +kernel)
    
theorem records_4000 : FiniteChecks.Interval recordTest 4000 4016 :=
      FiniteChecks.interval_of_check recordTest 4000 16 (by decide +kernel)
    
theorem records_4016 : FiniteChecks.Interval recordTest 4016 4032 :=
      FiniteChecks.interval_of_check recordTest 4016 16 (by decide +kernel)
    
theorem records_4032 : FiniteChecks.Interval recordTest 4032 4048 :=
      FiniteChecks.interval_of_check recordTest 4032 16 (by decide +kernel)
    
theorem records_4048 : FiniteChecks.Interval recordTest 4048 4064 :=
      FiniteChecks.interval_of_check recordTest 4048 16 (by decide +kernel)
    
theorem records_4064 : FiniteChecks.Interval recordTest 4064 4080 :=
      FiniteChecks.interval_of_check recordTest 4064 16 (by decide +kernel)
    
theorem records_4080 : FiniteChecks.Interval recordTest 4080 4096 :=
      FiniteChecks.interval_of_check recordTest 4080 16 (by decide +kernel)
    
theorem records_join_3584_3616 : FiniteChecks.Interval recordTest 3584 3616 :=
  FiniteChecks.interval_append recordTest 3584 3600 3616 records_3584 records_3600

theorem records_join_3616_3648 : FiniteChecks.Interval recordTest 3616 3648 :=
  FiniteChecks.interval_append recordTest 3616 3632 3648 records_3616 records_3632

theorem records_join_3584_3648 : FiniteChecks.Interval recordTest 3584 3648 :=
  FiniteChecks.interval_append recordTest 3584 3616 3648 records_join_3584_3616 records_join_3616_3648

theorem records_join_3648_3680 : FiniteChecks.Interval recordTest 3648 3680 :=
  FiniteChecks.interval_append recordTest 3648 3664 3680 records_3648 records_3664

theorem records_join_3680_3712 : FiniteChecks.Interval recordTest 3680 3712 :=
  FiniteChecks.interval_append recordTest 3680 3696 3712 records_3680 records_3696

theorem records_join_3648_3712 : FiniteChecks.Interval recordTest 3648 3712 :=
  FiniteChecks.interval_append recordTest 3648 3680 3712 records_join_3648_3680 records_join_3680_3712

theorem records_join_3584_3712 : FiniteChecks.Interval recordTest 3584 3712 :=
  FiniteChecks.interval_append recordTest 3584 3648 3712 records_join_3584_3648 records_join_3648_3712

theorem records_join_3712_3744 : FiniteChecks.Interval recordTest 3712 3744 :=
  FiniteChecks.interval_append recordTest 3712 3728 3744 records_3712 records_3728

theorem records_join_3744_3776 : FiniteChecks.Interval recordTest 3744 3776 :=
  FiniteChecks.interval_append recordTest 3744 3760 3776 records_3744 records_3760

theorem records_join_3712_3776 : FiniteChecks.Interval recordTest 3712 3776 :=
  FiniteChecks.interval_append recordTest 3712 3744 3776 records_join_3712_3744 records_join_3744_3776

theorem records_join_3776_3808 : FiniteChecks.Interval recordTest 3776 3808 :=
  FiniteChecks.interval_append recordTest 3776 3792 3808 records_3776 records_3792

theorem records_join_3808_3840 : FiniteChecks.Interval recordTest 3808 3840 :=
  FiniteChecks.interval_append recordTest 3808 3824 3840 records_3808 records_3824

theorem records_join_3776_3840 : FiniteChecks.Interval recordTest 3776 3840 :=
  FiniteChecks.interval_append recordTest 3776 3808 3840 records_join_3776_3808 records_join_3808_3840

theorem records_join_3712_3840 : FiniteChecks.Interval recordTest 3712 3840 :=
  FiniteChecks.interval_append recordTest 3712 3776 3840 records_join_3712_3776 records_join_3776_3840

theorem records_join_3584_3840 : FiniteChecks.Interval recordTest 3584 3840 :=
  FiniteChecks.interval_append recordTest 3584 3712 3840 records_join_3584_3712 records_join_3712_3840

theorem records_join_3840_3872 : FiniteChecks.Interval recordTest 3840 3872 :=
  FiniteChecks.interval_append recordTest 3840 3856 3872 records_3840 records_3856

theorem records_join_3872_3904 : FiniteChecks.Interval recordTest 3872 3904 :=
  FiniteChecks.interval_append recordTest 3872 3888 3904 records_3872 records_3888

theorem records_join_3840_3904 : FiniteChecks.Interval recordTest 3840 3904 :=
  FiniteChecks.interval_append recordTest 3840 3872 3904 records_join_3840_3872 records_join_3872_3904

theorem records_join_3904_3936 : FiniteChecks.Interval recordTest 3904 3936 :=
  FiniteChecks.interval_append recordTest 3904 3920 3936 records_3904 records_3920

theorem records_join_3936_3968 : FiniteChecks.Interval recordTest 3936 3968 :=
  FiniteChecks.interval_append recordTest 3936 3952 3968 records_3936 records_3952

theorem records_join_3904_3968 : FiniteChecks.Interval recordTest 3904 3968 :=
  FiniteChecks.interval_append recordTest 3904 3936 3968 records_join_3904_3936 records_join_3936_3968

theorem records_join_3840_3968 : FiniteChecks.Interval recordTest 3840 3968 :=
  FiniteChecks.interval_append recordTest 3840 3904 3968 records_join_3840_3904 records_join_3904_3968

theorem records_join_3968_4000 : FiniteChecks.Interval recordTest 3968 4000 :=
  FiniteChecks.interval_append recordTest 3968 3984 4000 records_3968 records_3984

theorem records_join_4000_4032 : FiniteChecks.Interval recordTest 4000 4032 :=
  FiniteChecks.interval_append recordTest 4000 4016 4032 records_4000 records_4016

theorem records_join_3968_4032 : FiniteChecks.Interval recordTest 3968 4032 :=
  FiniteChecks.interval_append recordTest 3968 4000 4032 records_join_3968_4000 records_join_4000_4032

theorem records_join_4032_4064 : FiniteChecks.Interval recordTest 4032 4064 :=
  FiniteChecks.interval_append recordTest 4032 4048 4064 records_4032 records_4048

theorem records_join_4064_4096 : FiniteChecks.Interval recordTest 4064 4096 :=
  FiniteChecks.interval_append recordTest 4064 4080 4096 records_4064 records_4080

theorem records_join_4032_4096 : FiniteChecks.Interval recordTest 4032 4096 :=
  FiniteChecks.interval_append recordTest 4032 4064 4096 records_join_4032_4064 records_join_4064_4096

theorem records_join_3968_4096 : FiniteChecks.Interval recordTest 3968 4096 :=
  FiniteChecks.interval_append recordTest 3968 4032 4096 records_join_3968_4032 records_join_4032_4096

theorem records_join_3840_4096 : FiniteChecks.Interval recordTest 3840 4096 :=
  FiniteChecks.interval_append recordTest 3840 3968 4096 records_join_3840_3968 records_join_3968_4096

theorem records_join_3584_4096 : FiniteChecks.Interval recordTest 3584 4096 :=
  FiniteChecks.interval_append recordTest 3584 3840 4096 records_join_3584_3840 records_join_3840_4096

theorem records_part_007 : FiniteChecks.Interval recordTest 3584 4096 := records_join_3584_4096
    end Papers.RationalityTen.FacetUniverses.FullSmall
    