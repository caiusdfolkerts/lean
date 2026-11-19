module
prelude
public import FullSmallFacetRecordData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

theorem records_2560 : FiniteChecks.Interval recordTest 2560 2576 :=
      FiniteChecks.interval_of_check recordTest 2560 16 (by decide +kernel)
    
theorem records_2576 : FiniteChecks.Interval recordTest 2576 2592 :=
      FiniteChecks.interval_of_check recordTest 2576 16 (by decide +kernel)
    
theorem records_2592 : FiniteChecks.Interval recordTest 2592 2608 :=
      FiniteChecks.interval_of_check recordTest 2592 16 (by decide +kernel)
    
theorem records_2608 : FiniteChecks.Interval recordTest 2608 2624 :=
      FiniteChecks.interval_of_check recordTest 2608 16 (by decide +kernel)
    
theorem records_2624 : FiniteChecks.Interval recordTest 2624 2640 :=
      FiniteChecks.interval_of_check recordTest 2624 16 (by decide +kernel)
    
theorem records_2640 : FiniteChecks.Interval recordTest 2640 2656 :=
      FiniteChecks.interval_of_check recordTest 2640 16 (by decide +kernel)
    
theorem records_2656 : FiniteChecks.Interval recordTest 2656 2672 :=
      FiniteChecks.interval_of_check recordTest 2656 16 (by decide +kernel)
    
theorem records_2672 : FiniteChecks.Interval recordTest 2672 2688 :=
      FiniteChecks.interval_of_check recordTest 2672 16 (by decide +kernel)
    
theorem records_2688 : FiniteChecks.Interval recordTest 2688 2704 :=
      FiniteChecks.interval_of_check recordTest 2688 16 (by decide +kernel)
    
theorem records_2704 : FiniteChecks.Interval recordTest 2704 2720 :=
      FiniteChecks.interval_of_check recordTest 2704 16 (by decide +kernel)
    
theorem records_2720 : FiniteChecks.Interval recordTest 2720 2736 :=
      FiniteChecks.interval_of_check recordTest 2720 16 (by decide +kernel)
    
theorem records_2736 : FiniteChecks.Interval recordTest 2736 2752 :=
      FiniteChecks.interval_of_check recordTest 2736 16 (by decide +kernel)
    
theorem records_2752 : FiniteChecks.Interval recordTest 2752 2768 :=
      FiniteChecks.interval_of_check recordTest 2752 16 (by decide +kernel)
    
theorem records_2768 : FiniteChecks.Interval recordTest 2768 2784 :=
      FiniteChecks.interval_of_check recordTest 2768 16 (by decide +kernel)
    
theorem records_2784 : FiniteChecks.Interval recordTest 2784 2800 :=
      FiniteChecks.interval_of_check recordTest 2784 16 (by decide +kernel)
    
theorem records_2800 : FiniteChecks.Interval recordTest 2800 2816 :=
      FiniteChecks.interval_of_check recordTest 2800 16 (by decide +kernel)
    
theorem records_2816 : FiniteChecks.Interval recordTest 2816 2832 :=
      FiniteChecks.interval_of_check recordTest 2816 16 (by decide +kernel)
    
theorem records_2832 : FiniteChecks.Interval recordTest 2832 2848 :=
      FiniteChecks.interval_of_check recordTest 2832 16 (by decide +kernel)
    
theorem records_2848 : FiniteChecks.Interval recordTest 2848 2864 :=
      FiniteChecks.interval_of_check recordTest 2848 16 (by decide +kernel)
    
theorem records_2864 : FiniteChecks.Interval recordTest 2864 2880 :=
      FiniteChecks.interval_of_check recordTest 2864 16 (by decide +kernel)
    
theorem records_2880 : FiniteChecks.Interval recordTest 2880 2896 :=
      FiniteChecks.interval_of_check recordTest 2880 16 (by decide +kernel)
    
theorem records_2896 : FiniteChecks.Interval recordTest 2896 2912 :=
      FiniteChecks.interval_of_check recordTest 2896 16 (by decide +kernel)
    
theorem records_2912 : FiniteChecks.Interval recordTest 2912 2928 :=
      FiniteChecks.interval_of_check recordTest 2912 16 (by decide +kernel)
    
theorem records_2928 : FiniteChecks.Interval recordTest 2928 2944 :=
      FiniteChecks.interval_of_check recordTest 2928 16 (by decide +kernel)
    
theorem records_2944 : FiniteChecks.Interval recordTest 2944 2960 :=
      FiniteChecks.interval_of_check recordTest 2944 16 (by decide +kernel)
    
theorem records_2960 : FiniteChecks.Interval recordTest 2960 2976 :=
      FiniteChecks.interval_of_check recordTest 2960 16 (by decide +kernel)
    
theorem records_2976 : FiniteChecks.Interval recordTest 2976 2992 :=
      FiniteChecks.interval_of_check recordTest 2976 16 (by decide +kernel)
    
theorem records_2992 : FiniteChecks.Interval recordTest 2992 3008 :=
      FiniteChecks.interval_of_check recordTest 2992 16 (by decide +kernel)
    
theorem records_3008 : FiniteChecks.Interval recordTest 3008 3024 :=
      FiniteChecks.interval_of_check recordTest 3008 16 (by decide +kernel)
    
theorem records_3024 : FiniteChecks.Interval recordTest 3024 3040 :=
      FiniteChecks.interval_of_check recordTest 3024 16 (by decide +kernel)
    
theorem records_3040 : FiniteChecks.Interval recordTest 3040 3056 :=
      FiniteChecks.interval_of_check recordTest 3040 16 (by decide +kernel)
    
theorem records_3056 : FiniteChecks.Interval recordTest 3056 3072 :=
      FiniteChecks.interval_of_check recordTest 3056 16 (by decide +kernel)
    
theorem records_join_2560_2592 : FiniteChecks.Interval recordTest 2560 2592 :=
  FiniteChecks.interval_append recordTest 2560 2576 2592 records_2560 records_2576

theorem records_join_2592_2624 : FiniteChecks.Interval recordTest 2592 2624 :=
  FiniteChecks.interval_append recordTest 2592 2608 2624 records_2592 records_2608

theorem records_join_2560_2624 : FiniteChecks.Interval recordTest 2560 2624 :=
  FiniteChecks.interval_append recordTest 2560 2592 2624 records_join_2560_2592 records_join_2592_2624

theorem records_join_2624_2656 : FiniteChecks.Interval recordTest 2624 2656 :=
  FiniteChecks.interval_append recordTest 2624 2640 2656 records_2624 records_2640

theorem records_join_2656_2688 : FiniteChecks.Interval recordTest 2656 2688 :=
  FiniteChecks.interval_append recordTest 2656 2672 2688 records_2656 records_2672

theorem records_join_2624_2688 : FiniteChecks.Interval recordTest 2624 2688 :=
  FiniteChecks.interval_append recordTest 2624 2656 2688 records_join_2624_2656 records_join_2656_2688

theorem records_join_2560_2688 : FiniteChecks.Interval recordTest 2560 2688 :=
  FiniteChecks.interval_append recordTest 2560 2624 2688 records_join_2560_2624 records_join_2624_2688

theorem records_join_2688_2720 : FiniteChecks.Interval recordTest 2688 2720 :=
  FiniteChecks.interval_append recordTest 2688 2704 2720 records_2688 records_2704

theorem records_join_2720_2752 : FiniteChecks.Interval recordTest 2720 2752 :=
  FiniteChecks.interval_append recordTest 2720 2736 2752 records_2720 records_2736

theorem records_join_2688_2752 : FiniteChecks.Interval recordTest 2688 2752 :=
  FiniteChecks.interval_append recordTest 2688 2720 2752 records_join_2688_2720 records_join_2720_2752

theorem records_join_2752_2784 : FiniteChecks.Interval recordTest 2752 2784 :=
  FiniteChecks.interval_append recordTest 2752 2768 2784 records_2752 records_2768

theorem records_join_2784_2816 : FiniteChecks.Interval recordTest 2784 2816 :=
  FiniteChecks.interval_append recordTest 2784 2800 2816 records_2784 records_2800

theorem records_join_2752_2816 : FiniteChecks.Interval recordTest 2752 2816 :=
  FiniteChecks.interval_append recordTest 2752 2784 2816 records_join_2752_2784 records_join_2784_2816

theorem records_join_2688_2816 : FiniteChecks.Interval recordTest 2688 2816 :=
  FiniteChecks.interval_append recordTest 2688 2752 2816 records_join_2688_2752 records_join_2752_2816

theorem records_join_2560_2816 : FiniteChecks.Interval recordTest 2560 2816 :=
  FiniteChecks.interval_append recordTest 2560 2688 2816 records_join_2560_2688 records_join_2688_2816

theorem records_join_2816_2848 : FiniteChecks.Interval recordTest 2816 2848 :=
  FiniteChecks.interval_append recordTest 2816 2832 2848 records_2816 records_2832

theorem records_join_2848_2880 : FiniteChecks.Interval recordTest 2848 2880 :=
  FiniteChecks.interval_append recordTest 2848 2864 2880 records_2848 records_2864

theorem records_join_2816_2880 : FiniteChecks.Interval recordTest 2816 2880 :=
  FiniteChecks.interval_append recordTest 2816 2848 2880 records_join_2816_2848 records_join_2848_2880

theorem records_join_2880_2912 : FiniteChecks.Interval recordTest 2880 2912 :=
  FiniteChecks.interval_append recordTest 2880 2896 2912 records_2880 records_2896

theorem records_join_2912_2944 : FiniteChecks.Interval recordTest 2912 2944 :=
  FiniteChecks.interval_append recordTest 2912 2928 2944 records_2912 records_2928

theorem records_join_2880_2944 : FiniteChecks.Interval recordTest 2880 2944 :=
  FiniteChecks.interval_append recordTest 2880 2912 2944 records_join_2880_2912 records_join_2912_2944

theorem records_join_2816_2944 : FiniteChecks.Interval recordTest 2816 2944 :=
  FiniteChecks.interval_append recordTest 2816 2880 2944 records_join_2816_2880 records_join_2880_2944

theorem records_join_2944_2976 : FiniteChecks.Interval recordTest 2944 2976 :=
  FiniteChecks.interval_append recordTest 2944 2960 2976 records_2944 records_2960

theorem records_join_2976_3008 : FiniteChecks.Interval recordTest 2976 3008 :=
  FiniteChecks.interval_append recordTest 2976 2992 3008 records_2976 records_2992

theorem records_join_2944_3008 : FiniteChecks.Interval recordTest 2944 3008 :=
  FiniteChecks.interval_append recordTest 2944 2976 3008 records_join_2944_2976 records_join_2976_3008

theorem records_join_3008_3040 : FiniteChecks.Interval recordTest 3008 3040 :=
  FiniteChecks.interval_append recordTest 3008 3024 3040 records_3008 records_3024

theorem records_join_3040_3072 : FiniteChecks.Interval recordTest 3040 3072 :=
  FiniteChecks.interval_append recordTest 3040 3056 3072 records_3040 records_3056

theorem records_join_3008_3072 : FiniteChecks.Interval recordTest 3008 3072 :=
  FiniteChecks.interval_append recordTest 3008 3040 3072 records_join_3008_3040 records_join_3040_3072

theorem records_join_2944_3072 : FiniteChecks.Interval recordTest 2944 3072 :=
  FiniteChecks.interval_append recordTest 2944 3008 3072 records_join_2944_3008 records_join_3008_3072

theorem records_join_2816_3072 : FiniteChecks.Interval recordTest 2816 3072 :=
  FiniteChecks.interval_append recordTest 2816 2944 3072 records_join_2816_2944 records_join_2944_3072

theorem records_join_2560_3072 : FiniteChecks.Interval recordTest 2560 3072 :=
  FiniteChecks.interval_append recordTest 2560 2816 3072 records_join_2560_2816 records_join_2816_3072

theorem records_part_005 : FiniteChecks.Interval recordTest 2560 3072 := records_join_2560_3072
    end Papers.RationalityTen.FacetUniverses.FullSmall
    