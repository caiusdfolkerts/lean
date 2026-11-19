module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart010

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data_join 00640 00704 640 704 672 00672
cert_terminal_data_join 00584 00704 584 704 640 00640
cert_terminal_data_join 00472 00704 472 704 584 00584
cert_terminal_data_join_2 00712 00728 712 728 720 00720
cert_terminal_data_join_3 00704 00728 704 728 712 00712
cert_terminal_data_join_2 00728 00744 728 744 736 00736
cert_terminal_data_join_2 00744 00760 744 760 752 00752
cert_terminal_data_join 00728 00760 728 760 744 00744
cert_terminal_data_join 00704 00760 704 760 728 00728
cert_terminal_data_join_2 00760 00776 760 776 768 00768
cert_terminal_data_join_2 00776 00792 776 792 784 00784
cert_terminal_data_join 00760 00792 760 792 776 00776
cert_terminal_data_join_2 00792 00808 792 808 800 00800
cert_terminal_data_join_2 00808 00824 808 824 816 00816
cert_terminal_data_join 00792 00824 792 824 808 00808
cert_terminal_data_join 00760 00824 760 824 792 00792
cert_terminal_data_join 00704 00824 704 824 760 00760
cert_terminal_data_join_2 00832 00848 832 848 840 00840
cert_terminal_data_join_3 00824 00848 824 848 832 00832
cert_terminal_data_join_2 00848 00864 848 864 856 00856
cert_terminal_data_join_2 00864 00880 864 880 872 00872
cert_terminal_data_join 00848 00880 848 880 864 00864
cert_terminal_data_join 00824 00880 824 880 848 00848
cert_terminal_data_join_2 00880 00896 880 896 888 00888
cert_terminal_data_join_2 00896 00912 896 912 904 00904
cert_terminal_data_join 00880 00912 880 912 896 00896
cert_terminal_data_join_2 00912 00928 912 928 920 00920
cert_terminal_data_join_2 00928 00944 928 944 936 00936
cert_terminal_data_join 00912 00944 912 944 928 00928
cert_terminal_data_join 00880 00944 880 944 912 00912
cert_terminal_data_join 00824 00944 824 944 880 00880
cert_terminal_data_join 00704 00944 704 944 824 00824
cert_terminal_data_join 00472 00944 472 944 704 00704
cert_terminal_data_join 00000 00944 0 944 472 00472
cert_terminal_data_join_2 00952 00968 952 968 960 00960
cert_terminal_data_join_3 00944 00968 944 968 952 00952
cert_terminal_data_join_2 00968 00984 968 984 976 00976
cert_terminal_data_join_2 00984 01000 984 1000 992 00992
cert_terminal_data_join 00968 01000 968 1000 984 00984
cert_terminal_data_join 00944 01000 944 1000 968 00968
cert_terminal_data_join_2 01008 01024 1008 1024 1016 01016
cert_terminal_data_join_3 01000 01024 1000 1024 1008 01008
cert_terminal_data_join_2 01024 01040 1024 1040 1032 01032
cert_terminal_data_join_2 01040 01056 1040 1056 1048 01048
cert_terminal_data_join 01024 01056 1024 1056 1040 01040
cert_terminal_data_join 01000 01056 1000 1056 1024 01024
cert_terminal_data_join 00944 01056 944 1056 1000 01000
cert_terminal_data_join_2 01064 01080 1064 1080 1072 01072
cert_terminal_data_join_3 01056 01080 1056 1080 1064 01064
cert_terminal_data_join_2 01080 01096 1080 1096 1088 01088
cert_terminal_data_join_2 01096 01112 1096 1112 1104 01104
cert_terminal_data_join 01080 01112 1080 1112 1096 01096
cert_terminal_data_join 01056 01112 1056 1112 1080 01080
cert_terminal_data_join_2 01112 01128 1112 1128 1120 01120
cert_terminal_data_join_2 01128 01144 1128 1144 1136 01136
cert_terminal_data_join 01112 01144 1112 1144 1128 01128
cert_terminal_data_join_2 01144 01160 1144 1160 1152 01152
cert_terminal_data_join_2 01160 01176 1160 1176 1168 01168
cert_terminal_data_join 01144 01176 1144 1176 1160 01160
cert_terminal_data_join 01112 01176 1112 1176 1144 01144
cert_terminal_data_join 01056 01176 1056 1176 1112 01112
cert_terminal_data_join 00944 01176 944 1176 1056 01056
cert_terminal_data_join_2 01184 01200 1184 1200 1192 01192
theorem terminal_data_join_01176_01200 : FiniteChecks.Interval terminalTest 1176 1200 :=
  FiniteChecks.interval_append terminalTest 1176 1184 1200 terminal_data_01176 terminal_data_join_01184_01200


end Papers.RationalityTen.ConcretePolygonClassification.N7
