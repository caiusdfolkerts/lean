module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_0512 : FiniteChecks.Interval recordTest 512 528 :=
      FiniteChecks.interval_of_check recordTest 512 16 (by decide +kernel)
    
theorem records_0528 : FiniteChecks.Interval recordTest 528 544 :=
      FiniteChecks.interval_of_check recordTest 528 16 (by decide +kernel)
    
theorem records_0544 : FiniteChecks.Interval recordTest 544 560 :=
      FiniteChecks.interval_of_check recordTest 544 16 (by decide +kernel)
    
theorem records_0560 : FiniteChecks.Interval recordTest 560 576 :=
      FiniteChecks.interval_of_check recordTest 560 16 (by decide +kernel)
    
theorem records_0576 : FiniteChecks.Interval recordTest 576 592 :=
      FiniteChecks.interval_of_check recordTest 576 16 (by decide +kernel)
    
theorem records_0592 : FiniteChecks.Interval recordTest 592 608 :=
      FiniteChecks.interval_of_check recordTest 592 16 (by decide +kernel)
    
theorem records_0608 : FiniteChecks.Interval recordTest 608 624 :=
      FiniteChecks.interval_of_check recordTest 608 16 (by decide +kernel)
    
theorem records_0624 : FiniteChecks.Interval recordTest 624 640 :=
      FiniteChecks.interval_of_check recordTest 624 16 (by decide +kernel)
    
theorem records_0640 : FiniteChecks.Interval recordTest 640 656 :=
      FiniteChecks.interval_of_check recordTest 640 16 (by decide +kernel)
    
theorem records_0656 : FiniteChecks.Interval recordTest 656 672 :=
      FiniteChecks.interval_of_check recordTest 656 16 (by decide +kernel)
    
theorem records_0672 : FiniteChecks.Interval recordTest 672 688 :=
      FiniteChecks.interval_of_check recordTest 672 16 (by decide +kernel)
    
theorem records_0688 : FiniteChecks.Interval recordTest 688 704 :=
      FiniteChecks.interval_of_check recordTest 688 16 (by decide +kernel)
    
theorem records_0704 : FiniteChecks.Interval recordTest 704 720 :=
      FiniteChecks.interval_of_check recordTest 704 16 (by decide +kernel)
    
theorem records_0720 : FiniteChecks.Interval recordTest 720 736 :=
      FiniteChecks.interval_of_check recordTest 720 16 (by decide +kernel)
    
theorem records_0736 : FiniteChecks.Interval recordTest 736 752 :=
      FiniteChecks.interval_of_check recordTest 736 16 (by decide +kernel)
    
theorem records_0752 : FiniteChecks.Interval recordTest 752 768 :=
      FiniteChecks.interval_of_check recordTest 752 16 (by decide +kernel)
    
theorem records_0768 : FiniteChecks.Interval recordTest 768 784 :=
      FiniteChecks.interval_of_check recordTest 768 16 (by decide +kernel)
    
theorem records_0784 : FiniteChecks.Interval recordTest 784 800 :=
      FiniteChecks.interval_of_check recordTest 784 16 (by decide +kernel)
    
theorem records_0800 : FiniteChecks.Interval recordTest 800 816 :=
      FiniteChecks.interval_of_check recordTest 800 16 (by decide +kernel)
    
theorem records_0816 : FiniteChecks.Interval recordTest 816 832 :=
      FiniteChecks.interval_of_check recordTest 816 16 (by decide +kernel)
    
theorem records_0832 : FiniteChecks.Interval recordTest 832 848 :=
      FiniteChecks.interval_of_check recordTest 832 16 (by decide +kernel)
    
theorem records_0848 : FiniteChecks.Interval recordTest 848 864 :=
      FiniteChecks.interval_of_check recordTest 848 16 (by decide +kernel)
    
theorem records_0864 : FiniteChecks.Interval recordTest 864 880 :=
      FiniteChecks.interval_of_check recordTest 864 16 (by decide +kernel)
    
theorem records_0880 : FiniteChecks.Interval recordTest 880 896 :=
      FiniteChecks.interval_of_check recordTest 880 16 (by decide +kernel)
    
theorem records_0896 : FiniteChecks.Interval recordTest 896 912 :=
      FiniteChecks.interval_of_check recordTest 896 16 (by decide +kernel)
    
theorem records_0912 : FiniteChecks.Interval recordTest 912 928 :=
      FiniteChecks.interval_of_check recordTest 912 16 (by decide +kernel)
    
theorem records_0928 : FiniteChecks.Interval recordTest 928 944 :=
      FiniteChecks.interval_of_check recordTest 928 16 (by decide +kernel)
    
theorem records_0944 : FiniteChecks.Interval recordTest 944 960 :=
      FiniteChecks.interval_of_check recordTest 944 16 (by decide +kernel)
    
theorem records_0960 : FiniteChecks.Interval recordTest 960 976 :=
      FiniteChecks.interval_of_check recordTest 960 16 (by decide +kernel)
    
theorem records_0976 : FiniteChecks.Interval recordTest 976 992 :=
      FiniteChecks.interval_of_check recordTest 976 16 (by decide +kernel)
    
theorem records_0992 : FiniteChecks.Interval recordTest 992 1008 :=
      FiniteChecks.interval_of_check recordTest 992 16 (by decide +kernel)
    
theorem records_1008 : FiniteChecks.Interval recordTest 1008 1024 :=
      FiniteChecks.interval_of_check recordTest 1008 16 (by decide +kernel)
    
theorem records_join_0512_0544 : FiniteChecks.Interval recordTest 512 544 :=
  FiniteChecks.interval_append recordTest 512 528 544 records_0512 records_0528

theorem records_join_0544_0576 : FiniteChecks.Interval recordTest 544 576 :=
  FiniteChecks.interval_append recordTest 544 560 576 records_0544 records_0560

theorem records_join_0512_0576 : FiniteChecks.Interval recordTest 512 576 :=
  FiniteChecks.interval_append recordTest 512 544 576 records_join_0512_0544 records_join_0544_0576

theorem records_join_0576_0608 : FiniteChecks.Interval recordTest 576 608 :=
  FiniteChecks.interval_append recordTest 576 592 608 records_0576 records_0592

theorem records_join_0608_0640 : FiniteChecks.Interval recordTest 608 640 :=
  FiniteChecks.interval_append recordTest 608 624 640 records_0608 records_0624

theorem records_join_0576_0640 : FiniteChecks.Interval recordTest 576 640 :=
  FiniteChecks.interval_append recordTest 576 608 640 records_join_0576_0608 records_join_0608_0640

theorem records_join_0512_0640 : FiniteChecks.Interval recordTest 512 640 :=
  FiniteChecks.interval_append recordTest 512 576 640 records_join_0512_0576 records_join_0576_0640

theorem records_join_0640_0672 : FiniteChecks.Interval recordTest 640 672 :=
  FiniteChecks.interval_append recordTest 640 656 672 records_0640 records_0656

theorem records_join_0672_0704 : FiniteChecks.Interval recordTest 672 704 :=
  FiniteChecks.interval_append recordTest 672 688 704 records_0672 records_0688

theorem records_join_0640_0704 : FiniteChecks.Interval recordTest 640 704 :=
  FiniteChecks.interval_append recordTest 640 672 704 records_join_0640_0672 records_join_0672_0704

theorem records_join_0704_0736 : FiniteChecks.Interval recordTest 704 736 :=
  FiniteChecks.interval_append recordTest 704 720 736 records_0704 records_0720

theorem records_join_0736_0768 : FiniteChecks.Interval recordTest 736 768 :=
  FiniteChecks.interval_append recordTest 736 752 768 records_0736 records_0752

theorem records_join_0704_0768 : FiniteChecks.Interval recordTest 704 768 :=
  FiniteChecks.interval_append recordTest 704 736 768 records_join_0704_0736 records_join_0736_0768

theorem records_join_0640_0768 : FiniteChecks.Interval recordTest 640 768 :=
  FiniteChecks.interval_append recordTest 640 704 768 records_join_0640_0704 records_join_0704_0768

theorem records_join_0512_0768 : FiniteChecks.Interval recordTest 512 768 :=
  FiniteChecks.interval_append recordTest 512 640 768 records_join_0512_0640 records_join_0640_0768

theorem records_join_0768_0800 : FiniteChecks.Interval recordTest 768 800 :=
  FiniteChecks.interval_append recordTest 768 784 800 records_0768 records_0784

theorem records_join_0800_0832 : FiniteChecks.Interval recordTest 800 832 :=
  FiniteChecks.interval_append recordTest 800 816 832 records_0800 records_0816

theorem records_join_0768_0832 : FiniteChecks.Interval recordTest 768 832 :=
  FiniteChecks.interval_append recordTest 768 800 832 records_join_0768_0800 records_join_0800_0832

theorem records_join_0832_0864 : FiniteChecks.Interval recordTest 832 864 :=
  FiniteChecks.interval_append recordTest 832 848 864 records_0832 records_0848

theorem records_join_0864_0896 : FiniteChecks.Interval recordTest 864 896 :=
  FiniteChecks.interval_append recordTest 864 880 896 records_0864 records_0880

theorem records_join_0832_0896 : FiniteChecks.Interval recordTest 832 896 :=
  FiniteChecks.interval_append recordTest 832 864 896 records_join_0832_0864 records_join_0864_0896

theorem records_join_0768_0896 : FiniteChecks.Interval recordTest 768 896 :=
  FiniteChecks.interval_append recordTest 768 832 896 records_join_0768_0832 records_join_0832_0896

theorem records_join_0896_0928 : FiniteChecks.Interval recordTest 896 928 :=
  FiniteChecks.interval_append recordTest 896 912 928 records_0896 records_0912

theorem records_join_0928_0960 : FiniteChecks.Interval recordTest 928 960 :=
  FiniteChecks.interval_append recordTest 928 944 960 records_0928 records_0944

theorem records_join_0896_0960 : FiniteChecks.Interval recordTest 896 960 :=
  FiniteChecks.interval_append recordTest 896 928 960 records_join_0896_0928 records_join_0928_0960

theorem records_join_0960_0992 : FiniteChecks.Interval recordTest 960 992 :=
  FiniteChecks.interval_append recordTest 960 976 992 records_0960 records_0976

theorem records_join_0992_1024 : FiniteChecks.Interval recordTest 992 1024 :=
  FiniteChecks.interval_append recordTest 992 1008 1024 records_0992 records_1008

theorem records_join_0960_1024 : FiniteChecks.Interval recordTest 960 1024 :=
  FiniteChecks.interval_append recordTest 960 992 1024 records_join_0960_0992 records_join_0992_1024

theorem records_join_0896_1024 : FiniteChecks.Interval recordTest 896 1024 :=
  FiniteChecks.interval_append recordTest 896 960 1024 records_join_0896_0960 records_join_0960_1024

theorem records_join_0768_1024 : FiniteChecks.Interval recordTest 768 1024 :=
  FiniteChecks.interval_append recordTest 768 896 1024 records_join_0768_0896 records_join_0896_1024

theorem records_join_0512_1024 : FiniteChecks.Interval recordTest 512 1024 :=
  FiniteChecks.interval_append recordTest 512 768 1024 records_join_0512_0768 records_join_0768_1024

theorem records_part_001 : FiniteChecks.Interval recordTest 512 1024 := records_join_0512_1024
    end Papers.RationalityTen.FacetUniverses.FullSmall
    