module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_4608 : FiniteChecks.Interval recordTest 4608 4624 :=
      FiniteChecks.interval_of_check recordTest 4608 16 (by decide +kernel)
    
theorem records_4624 : FiniteChecks.Interval recordTest 4624 4640 :=
      FiniteChecks.interval_of_check recordTest 4624 16 (by decide +kernel)
    
theorem records_4640 : FiniteChecks.Interval recordTest 4640 4656 :=
      FiniteChecks.interval_of_check recordTest 4640 16 (by decide +kernel)
    
theorem records_4656 : FiniteChecks.Interval recordTest 4656 4672 :=
      FiniteChecks.interval_of_check recordTest 4656 16 (by decide +kernel)
    
theorem records_4672 : FiniteChecks.Interval recordTest 4672 4688 :=
      FiniteChecks.interval_of_check recordTest 4672 16 (by decide +kernel)
    
theorem records_4688 : FiniteChecks.Interval recordTest 4688 4704 :=
      FiniteChecks.interval_of_check recordTest 4688 16 (by decide +kernel)
    
theorem records_4704 : FiniteChecks.Interval recordTest 4704 4720 :=
      FiniteChecks.interval_of_check recordTest 4704 16 (by decide +kernel)
    
theorem records_4720 : FiniteChecks.Interval recordTest 4720 4736 :=
      FiniteChecks.interval_of_check recordTest 4720 16 (by decide +kernel)
    
theorem records_4736 : FiniteChecks.Interval recordTest 4736 4752 :=
      FiniteChecks.interval_of_check recordTest 4736 16 (by decide +kernel)
    
theorem records_4752 : FiniteChecks.Interval recordTest 4752 4768 :=
      FiniteChecks.interval_of_check recordTest 4752 16 (by decide +kernel)
    
theorem records_4768 : FiniteChecks.Interval recordTest 4768 4784 :=
      FiniteChecks.interval_of_check recordTest 4768 16 (by decide +kernel)
    
theorem records_4784 : FiniteChecks.Interval recordTest 4784 4800 :=
      FiniteChecks.interval_of_check recordTest 4784 16 (by decide +kernel)
    
theorem records_4800 : FiniteChecks.Interval recordTest 4800 4816 :=
      FiniteChecks.interval_of_check recordTest 4800 16 (by decide +kernel)
    
theorem records_4816 : FiniteChecks.Interval recordTest 4816 4832 :=
      FiniteChecks.interval_of_check recordTest 4816 16 (by decide +kernel)
    
theorem records_4832 : FiniteChecks.Interval recordTest 4832 4848 :=
      FiniteChecks.interval_of_check recordTest 4832 16 (by decide +kernel)
    
theorem records_4848 : FiniteChecks.Interval recordTest 4848 4864 :=
      FiniteChecks.interval_of_check recordTest 4848 16 (by decide +kernel)
    
theorem records_4864 : FiniteChecks.Interval recordTest 4864 4880 :=
      FiniteChecks.interval_of_check recordTest 4864 16 (by decide +kernel)
    
theorem records_4880 : FiniteChecks.Interval recordTest 4880 4896 :=
      FiniteChecks.interval_of_check recordTest 4880 16 (by decide +kernel)
    
theorem records_4896 : FiniteChecks.Interval recordTest 4896 4912 :=
      FiniteChecks.interval_of_check recordTest 4896 16 (by decide +kernel)
    
theorem records_4912 : FiniteChecks.Interval recordTest 4912 4928 :=
      FiniteChecks.interval_of_check recordTest 4912 16 (by decide +kernel)
    
theorem records_4928 : FiniteChecks.Interval recordTest 4928 4944 :=
      FiniteChecks.interval_of_check recordTest 4928 16 (by decide +kernel)
    
theorem records_4944 : FiniteChecks.Interval recordTest 4944 4960 :=
      FiniteChecks.interval_of_check recordTest 4944 16 (by decide +kernel)
    
theorem records_4960 : FiniteChecks.Interval recordTest 4960 4976 :=
      FiniteChecks.interval_of_check recordTest 4960 16 (by decide +kernel)
    
theorem records_4976 : FiniteChecks.Interval recordTest 4976 4992 :=
      FiniteChecks.interval_of_check recordTest 4976 16 (by decide +kernel)
    
theorem records_4992 : FiniteChecks.Interval recordTest 4992 5008 :=
      FiniteChecks.interval_of_check recordTest 4992 16 (by decide +kernel)
    
theorem records_5008 : FiniteChecks.Interval recordTest 5008 5024 :=
      FiniteChecks.interval_of_check recordTest 5008 16 (by decide +kernel)
    
theorem records_5024 : FiniteChecks.Interval recordTest 5024 5040 :=
      FiniteChecks.interval_of_check recordTest 5024 16 (by decide +kernel)
    
theorem records_5040 : FiniteChecks.Interval recordTest 5040 5056 :=
      FiniteChecks.interval_of_check recordTest 5040 16 (by decide +kernel)
    
theorem records_5056 : FiniteChecks.Interval recordTest 5056 5072 :=
      FiniteChecks.interval_of_check recordTest 5056 16 (by decide +kernel)
    
theorem records_5072 : FiniteChecks.Interval recordTest 5072 5088 :=
      FiniteChecks.interval_of_check recordTest 5072 16 (by decide +kernel)
    
theorem records_5088 : FiniteChecks.Interval recordTest 5088 5104 :=
      FiniteChecks.interval_of_check recordTest 5088 16 (by decide +kernel)
    
theorem records_5104 : FiniteChecks.Interval recordTest 5104 5120 :=
      FiniteChecks.interval_of_check recordTest 5104 16 (by decide +kernel)
    
theorem records_join_4608_4640 : FiniteChecks.Interval recordTest 4608 4640 :=
  FiniteChecks.interval_append recordTest 4608 4624 4640 records_4608 records_4624

theorem records_join_4640_4672 : FiniteChecks.Interval recordTest 4640 4672 :=
  FiniteChecks.interval_append recordTest 4640 4656 4672 records_4640 records_4656

theorem records_join_4608_4672 : FiniteChecks.Interval recordTest 4608 4672 :=
  FiniteChecks.interval_append recordTest 4608 4640 4672 records_join_4608_4640 records_join_4640_4672

theorem records_join_4672_4704 : FiniteChecks.Interval recordTest 4672 4704 :=
  FiniteChecks.interval_append recordTest 4672 4688 4704 records_4672 records_4688

theorem records_join_4704_4736 : FiniteChecks.Interval recordTest 4704 4736 :=
  FiniteChecks.interval_append recordTest 4704 4720 4736 records_4704 records_4720

theorem records_join_4672_4736 : FiniteChecks.Interval recordTest 4672 4736 :=
  FiniteChecks.interval_append recordTest 4672 4704 4736 records_join_4672_4704 records_join_4704_4736

theorem records_join_4608_4736 : FiniteChecks.Interval recordTest 4608 4736 :=
  FiniteChecks.interval_append recordTest 4608 4672 4736 records_join_4608_4672 records_join_4672_4736

theorem records_join_4736_4768 : FiniteChecks.Interval recordTest 4736 4768 :=
  FiniteChecks.interval_append recordTest 4736 4752 4768 records_4736 records_4752

theorem records_join_4768_4800 : FiniteChecks.Interval recordTest 4768 4800 :=
  FiniteChecks.interval_append recordTest 4768 4784 4800 records_4768 records_4784

theorem records_join_4736_4800 : FiniteChecks.Interval recordTest 4736 4800 :=
  FiniteChecks.interval_append recordTest 4736 4768 4800 records_join_4736_4768 records_join_4768_4800

theorem records_join_4800_4832 : FiniteChecks.Interval recordTest 4800 4832 :=
  FiniteChecks.interval_append recordTest 4800 4816 4832 records_4800 records_4816

theorem records_join_4832_4864 : FiniteChecks.Interval recordTest 4832 4864 :=
  FiniteChecks.interval_append recordTest 4832 4848 4864 records_4832 records_4848

theorem records_join_4800_4864 : FiniteChecks.Interval recordTest 4800 4864 :=
  FiniteChecks.interval_append recordTest 4800 4832 4864 records_join_4800_4832 records_join_4832_4864

theorem records_join_4736_4864 : FiniteChecks.Interval recordTest 4736 4864 :=
  FiniteChecks.interval_append recordTest 4736 4800 4864 records_join_4736_4800 records_join_4800_4864

theorem records_join_4608_4864 : FiniteChecks.Interval recordTest 4608 4864 :=
  FiniteChecks.interval_append recordTest 4608 4736 4864 records_join_4608_4736 records_join_4736_4864

theorem records_join_4864_4896 : FiniteChecks.Interval recordTest 4864 4896 :=
  FiniteChecks.interval_append recordTest 4864 4880 4896 records_4864 records_4880

theorem records_join_4896_4928 : FiniteChecks.Interval recordTest 4896 4928 :=
  FiniteChecks.interval_append recordTest 4896 4912 4928 records_4896 records_4912

theorem records_join_4864_4928 : FiniteChecks.Interval recordTest 4864 4928 :=
  FiniteChecks.interval_append recordTest 4864 4896 4928 records_join_4864_4896 records_join_4896_4928

theorem records_join_4928_4960 : FiniteChecks.Interval recordTest 4928 4960 :=
  FiniteChecks.interval_append recordTest 4928 4944 4960 records_4928 records_4944

theorem records_join_4960_4992 : FiniteChecks.Interval recordTest 4960 4992 :=
  FiniteChecks.interval_append recordTest 4960 4976 4992 records_4960 records_4976

theorem records_join_4928_4992 : FiniteChecks.Interval recordTest 4928 4992 :=
  FiniteChecks.interval_append recordTest 4928 4960 4992 records_join_4928_4960 records_join_4960_4992

theorem records_join_4864_4992 : FiniteChecks.Interval recordTest 4864 4992 :=
  FiniteChecks.interval_append recordTest 4864 4928 4992 records_join_4864_4928 records_join_4928_4992

theorem records_join_4992_5024 : FiniteChecks.Interval recordTest 4992 5024 :=
  FiniteChecks.interval_append recordTest 4992 5008 5024 records_4992 records_5008

theorem records_join_5024_5056 : FiniteChecks.Interval recordTest 5024 5056 :=
  FiniteChecks.interval_append recordTest 5024 5040 5056 records_5024 records_5040

theorem records_join_4992_5056 : FiniteChecks.Interval recordTest 4992 5056 :=
  FiniteChecks.interval_append recordTest 4992 5024 5056 records_join_4992_5024 records_join_5024_5056

theorem records_join_5056_5088 : FiniteChecks.Interval recordTest 5056 5088 :=
  FiniteChecks.interval_append recordTest 5056 5072 5088 records_5056 records_5072

theorem records_join_5088_5120 : FiniteChecks.Interval recordTest 5088 5120 :=
  FiniteChecks.interval_append recordTest 5088 5104 5120 records_5088 records_5104

theorem records_join_5056_5120 : FiniteChecks.Interval recordTest 5056 5120 :=
  FiniteChecks.interval_append recordTest 5056 5088 5120 records_join_5056_5088 records_join_5088_5120

theorem records_join_4992_5120 : FiniteChecks.Interval recordTest 4992 5120 :=
  FiniteChecks.interval_append recordTest 4992 5056 5120 records_join_4992_5056 records_join_5056_5120

theorem records_join_4864_5120 : FiniteChecks.Interval recordTest 4864 5120 :=
  FiniteChecks.interval_append recordTest 4864 4992 5120 records_join_4864_4992 records_join_4992_5120

theorem records_join_4608_5120 : FiniteChecks.Interval recordTest 4608 5120 :=
  FiniteChecks.interval_append recordTest 4608 4864 5120 records_join_4608_4864 records_join_4864_5120

theorem records_part_009 : FiniteChecks.Interval recordTest 4608 5120 := records_join_4608_5120
    end Papers.RationalityTen.FacetUniverses.FullSmall
    