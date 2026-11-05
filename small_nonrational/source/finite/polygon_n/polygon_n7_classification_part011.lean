module

public import PolygonN7ClassificationPart010

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_join_00640_00704 : FiniteChecks.Interval terminalTest 640 704 :=
  FiniteChecks.interval_append terminalTest 640 672 704 terminal_data_join_00640_00672 terminal_data_join_00672_00704

theorem terminal_data_join_00584_00704 : FiniteChecks.Interval terminalTest 584 704 :=
  FiniteChecks.interval_append terminalTest 584 640 704 terminal_data_join_00584_00640 terminal_data_join_00640_00704

theorem terminal_data_join_00472_00704 : FiniteChecks.Interval terminalTest 472 704 :=
  FiniteChecks.interval_append terminalTest 472 584 704 terminal_data_join_00472_00584 terminal_data_join_00584_00704

theorem terminal_data_join_00712_00728 : FiniteChecks.Interval terminalTest 712 728 :=
  FiniteChecks.interval_append terminalTest 712 720 728 terminal_data_00712 terminal_data_00720

theorem terminal_data_join_00704_00728 : FiniteChecks.Interval terminalTest 704 728 :=
  FiniteChecks.interval_append terminalTest 704 712 728 terminal_data_00704 terminal_data_join_00712_00728

theorem terminal_data_join_00728_00744 : FiniteChecks.Interval terminalTest 728 744 :=
  FiniteChecks.interval_append terminalTest 728 736 744 terminal_data_00728 terminal_data_00736

theorem terminal_data_join_00744_00760 : FiniteChecks.Interval terminalTest 744 760 :=
  FiniteChecks.interval_append terminalTest 744 752 760 terminal_data_00744 terminal_data_00752

theorem terminal_data_join_00728_00760 : FiniteChecks.Interval terminalTest 728 760 :=
  FiniteChecks.interval_append terminalTest 728 744 760 terminal_data_join_00728_00744 terminal_data_join_00744_00760

theorem terminal_data_join_00704_00760 : FiniteChecks.Interval terminalTest 704 760 :=
  FiniteChecks.interval_append terminalTest 704 728 760 terminal_data_join_00704_00728 terminal_data_join_00728_00760

theorem terminal_data_join_00760_00776 : FiniteChecks.Interval terminalTest 760 776 :=
  FiniteChecks.interval_append terminalTest 760 768 776 terminal_data_00760 terminal_data_00768

theorem terminal_data_join_00776_00792 : FiniteChecks.Interval terminalTest 776 792 :=
  FiniteChecks.interval_append terminalTest 776 784 792 terminal_data_00776 terminal_data_00784

theorem terminal_data_join_00760_00792 : FiniteChecks.Interval terminalTest 760 792 :=
  FiniteChecks.interval_append terminalTest 760 776 792 terminal_data_join_00760_00776 terminal_data_join_00776_00792

theorem terminal_data_join_00792_00808 : FiniteChecks.Interval terminalTest 792 808 :=
  FiniteChecks.interval_append terminalTest 792 800 808 terminal_data_00792 terminal_data_00800

theorem terminal_data_join_00808_00824 : FiniteChecks.Interval terminalTest 808 824 :=
  FiniteChecks.interval_append terminalTest 808 816 824 terminal_data_00808 terminal_data_00816

theorem terminal_data_join_00792_00824 : FiniteChecks.Interval terminalTest 792 824 :=
  FiniteChecks.interval_append terminalTest 792 808 824 terminal_data_join_00792_00808 terminal_data_join_00808_00824

theorem terminal_data_join_00760_00824 : FiniteChecks.Interval terminalTest 760 824 :=
  FiniteChecks.interval_append terminalTest 760 792 824 terminal_data_join_00760_00792 terminal_data_join_00792_00824

theorem terminal_data_join_00704_00824 : FiniteChecks.Interval terminalTest 704 824 :=
  FiniteChecks.interval_append terminalTest 704 760 824 terminal_data_join_00704_00760 terminal_data_join_00760_00824

theorem terminal_data_join_00832_00848 : FiniteChecks.Interval terminalTest 832 848 :=
  FiniteChecks.interval_append terminalTest 832 840 848 terminal_data_00832 terminal_data_00840

theorem terminal_data_join_00824_00848 : FiniteChecks.Interval terminalTest 824 848 :=
  FiniteChecks.interval_append terminalTest 824 832 848 terminal_data_00824 terminal_data_join_00832_00848

theorem terminal_data_join_00848_00864 : FiniteChecks.Interval terminalTest 848 864 :=
  FiniteChecks.interval_append terminalTest 848 856 864 terminal_data_00848 terminal_data_00856

theorem terminal_data_join_00864_00880 : FiniteChecks.Interval terminalTest 864 880 :=
  FiniteChecks.interval_append terminalTest 864 872 880 terminal_data_00864 terminal_data_00872

theorem terminal_data_join_00848_00880 : FiniteChecks.Interval terminalTest 848 880 :=
  FiniteChecks.interval_append terminalTest 848 864 880 terminal_data_join_00848_00864 terminal_data_join_00864_00880

theorem terminal_data_join_00824_00880 : FiniteChecks.Interval terminalTest 824 880 :=
  FiniteChecks.interval_append terminalTest 824 848 880 terminal_data_join_00824_00848 terminal_data_join_00848_00880

theorem terminal_data_join_00880_00896 : FiniteChecks.Interval terminalTest 880 896 :=
  FiniteChecks.interval_append terminalTest 880 888 896 terminal_data_00880 terminal_data_00888

theorem terminal_data_join_00896_00912 : FiniteChecks.Interval terminalTest 896 912 :=
  FiniteChecks.interval_append terminalTest 896 904 912 terminal_data_00896 terminal_data_00904

theorem terminal_data_join_00880_00912 : FiniteChecks.Interval terminalTest 880 912 :=
  FiniteChecks.interval_append terminalTest 880 896 912 terminal_data_join_00880_00896 terminal_data_join_00896_00912

theorem terminal_data_join_00912_00928 : FiniteChecks.Interval terminalTest 912 928 :=
  FiniteChecks.interval_append terminalTest 912 920 928 terminal_data_00912 terminal_data_00920

theorem terminal_data_join_00928_00944 : FiniteChecks.Interval terminalTest 928 944 :=
  FiniteChecks.interval_append terminalTest 928 936 944 terminal_data_00928 terminal_data_00936

theorem terminal_data_join_00912_00944 : FiniteChecks.Interval terminalTest 912 944 :=
  FiniteChecks.interval_append terminalTest 912 928 944 terminal_data_join_00912_00928 terminal_data_join_00928_00944

theorem terminal_data_join_00880_00944 : FiniteChecks.Interval terminalTest 880 944 :=
  FiniteChecks.interval_append terminalTest 880 912 944 terminal_data_join_00880_00912 terminal_data_join_00912_00944

theorem terminal_data_join_00824_00944 : FiniteChecks.Interval terminalTest 824 944 :=
  FiniteChecks.interval_append terminalTest 824 880 944 terminal_data_join_00824_00880 terminal_data_join_00880_00944

theorem terminal_data_join_00704_00944 : FiniteChecks.Interval terminalTest 704 944 :=
  FiniteChecks.interval_append terminalTest 704 824 944 terminal_data_join_00704_00824 terminal_data_join_00824_00944

theorem terminal_data_join_00472_00944 : FiniteChecks.Interval terminalTest 472 944 :=
  FiniteChecks.interval_append terminalTest 472 704 944 terminal_data_join_00472_00704 terminal_data_join_00704_00944

theorem terminal_data_join_00000_00944 : FiniteChecks.Interval terminalTest 0 944 :=
  FiniteChecks.interval_append terminalTest 0 472 944 terminal_data_join_00000_00472 terminal_data_join_00472_00944

theorem terminal_data_join_00952_00968 : FiniteChecks.Interval terminalTest 952 968 :=
  FiniteChecks.interval_append terminalTest 952 960 968 terminal_data_00952 terminal_data_00960

theorem terminal_data_join_00944_00968 : FiniteChecks.Interval terminalTest 944 968 :=
  FiniteChecks.interval_append terminalTest 944 952 968 terminal_data_00944 terminal_data_join_00952_00968

theorem terminal_data_join_00968_00984 : FiniteChecks.Interval terminalTest 968 984 :=
  FiniteChecks.interval_append terminalTest 968 976 984 terminal_data_00968 terminal_data_00976

theorem terminal_data_join_00984_01000 : FiniteChecks.Interval terminalTest 984 1000 :=
  FiniteChecks.interval_append terminalTest 984 992 1000 terminal_data_00984 terminal_data_00992

theorem terminal_data_join_00968_01000 : FiniteChecks.Interval terminalTest 968 1000 :=
  FiniteChecks.interval_append terminalTest 968 984 1000 terminal_data_join_00968_00984 terminal_data_join_00984_01000

theorem terminal_data_join_00944_01000 : FiniteChecks.Interval terminalTest 944 1000 :=
  FiniteChecks.interval_append terminalTest 944 968 1000 terminal_data_join_00944_00968 terminal_data_join_00968_01000

theorem terminal_data_join_01008_01024 : FiniteChecks.Interval terminalTest 1008 1024 :=
  FiniteChecks.interval_append terminalTest 1008 1016 1024 terminal_data_01008 terminal_data_01016

theorem terminal_data_join_01000_01024 : FiniteChecks.Interval terminalTest 1000 1024 :=
  FiniteChecks.interval_append terminalTest 1000 1008 1024 terminal_data_01000 terminal_data_join_01008_01024

theorem terminal_data_join_01024_01040 : FiniteChecks.Interval terminalTest 1024 1040 :=
  FiniteChecks.interval_append terminalTest 1024 1032 1040 terminal_data_01024 terminal_data_01032

theorem terminal_data_join_01040_01056 : FiniteChecks.Interval terminalTest 1040 1056 :=
  FiniteChecks.interval_append terminalTest 1040 1048 1056 terminal_data_01040 terminal_data_01048

theorem terminal_data_join_01024_01056 : FiniteChecks.Interval terminalTest 1024 1056 :=
  FiniteChecks.interval_append terminalTest 1024 1040 1056 terminal_data_join_01024_01040 terminal_data_join_01040_01056

theorem terminal_data_join_01000_01056 : FiniteChecks.Interval terminalTest 1000 1056 :=
  FiniteChecks.interval_append terminalTest 1000 1024 1056 terminal_data_join_01000_01024 terminal_data_join_01024_01056

theorem terminal_data_join_00944_01056 : FiniteChecks.Interval terminalTest 944 1056 :=
  FiniteChecks.interval_append terminalTest 944 1000 1056 terminal_data_join_00944_01000 terminal_data_join_01000_01056

theorem terminal_data_join_01064_01080 : FiniteChecks.Interval terminalTest 1064 1080 :=
  FiniteChecks.interval_append terminalTest 1064 1072 1080 terminal_data_01064 terminal_data_01072

theorem terminal_data_join_01056_01080 : FiniteChecks.Interval terminalTest 1056 1080 :=
  FiniteChecks.interval_append terminalTest 1056 1064 1080 terminal_data_01056 terminal_data_join_01064_01080

theorem terminal_data_join_01080_01096 : FiniteChecks.Interval terminalTest 1080 1096 :=
  FiniteChecks.interval_append terminalTest 1080 1088 1096 terminal_data_01080 terminal_data_01088

theorem terminal_data_join_01096_01112 : FiniteChecks.Interval terminalTest 1096 1112 :=
  FiniteChecks.interval_append terminalTest 1096 1104 1112 terminal_data_01096 terminal_data_01104

theorem terminal_data_join_01080_01112 : FiniteChecks.Interval terminalTest 1080 1112 :=
  FiniteChecks.interval_append terminalTest 1080 1096 1112 terminal_data_join_01080_01096 terminal_data_join_01096_01112

theorem terminal_data_join_01056_01112 : FiniteChecks.Interval terminalTest 1056 1112 :=
  FiniteChecks.interval_append terminalTest 1056 1080 1112 terminal_data_join_01056_01080 terminal_data_join_01080_01112

theorem terminal_data_join_01112_01128 : FiniteChecks.Interval terminalTest 1112 1128 :=
  FiniteChecks.interval_append terminalTest 1112 1120 1128 terminal_data_01112 terminal_data_01120

theorem terminal_data_join_01128_01144 : FiniteChecks.Interval terminalTest 1128 1144 :=
  FiniteChecks.interval_append terminalTest 1128 1136 1144 terminal_data_01128 terminal_data_01136

theorem terminal_data_join_01112_01144 : FiniteChecks.Interval terminalTest 1112 1144 :=
  FiniteChecks.interval_append terminalTest 1112 1128 1144 terminal_data_join_01112_01128 terminal_data_join_01128_01144

theorem terminal_data_join_01144_01160 : FiniteChecks.Interval terminalTest 1144 1160 :=
  FiniteChecks.interval_append terminalTest 1144 1152 1160 terminal_data_01144 terminal_data_01152

theorem terminal_data_join_01160_01176 : FiniteChecks.Interval terminalTest 1160 1176 :=
  FiniteChecks.interval_append terminalTest 1160 1168 1176 terminal_data_01160 terminal_data_01168

theorem terminal_data_join_01144_01176 : FiniteChecks.Interval terminalTest 1144 1176 :=
  FiniteChecks.interval_append terminalTest 1144 1160 1176 terminal_data_join_01144_01160 terminal_data_join_01160_01176

theorem terminal_data_join_01112_01176 : FiniteChecks.Interval terminalTest 1112 1176 :=
  FiniteChecks.interval_append terminalTest 1112 1144 1176 terminal_data_join_01112_01144 terminal_data_join_01144_01176

theorem terminal_data_join_01056_01176 : FiniteChecks.Interval terminalTest 1056 1176 :=
  FiniteChecks.interval_append terminalTest 1056 1112 1176 terminal_data_join_01056_01112 terminal_data_join_01112_01176

theorem terminal_data_join_00944_01176 : FiniteChecks.Interval terminalTest 944 1176 :=
  FiniteChecks.interval_append terminalTest 944 1056 1176 terminal_data_join_00944_01056 terminal_data_join_01056_01176

theorem terminal_data_join_01184_01200 : FiniteChecks.Interval terminalTest 1184 1200 :=
  FiniteChecks.interval_append terminalTest 1184 1192 1200 terminal_data_01184 terminal_data_01192

theorem terminal_data_join_01176_01200 : FiniteChecks.Interval terminalTest 1176 1200 :=
  FiniteChecks.interval_append terminalTest 1176 1184 1200 terminal_data_01176 terminal_data_join_01184_01200


end Papers.RationalityTen.ConcretePolygonClassification.N7
