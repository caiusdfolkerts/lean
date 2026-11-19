module
prelude
public meta import LowerSchemas.FinitePolygonN
public import PolygonN7DAGTests

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

cert_nodes_part 003 00768 768 776 8
cert_nodes_part 003 00776 776 784 8
cert_nodes_part 003 00784 784 792 8
cert_nodes_part 003 00792 792 800 8
cert_nodes_part 003 00800 800 808 8
cert_nodes_part 003 00808 808 816 8
cert_nodes_part 003 00816 816 824 8
cert_nodes_part 003 00824 824 832 8
cert_nodes_part 003 00832 832 840 8
cert_nodes_part 003 00840 840 848 8
cert_nodes_part 003 00848 848 856 8
cert_nodes_part 003 00856 856 864 8
cert_nodes_part 003 00864 864 872 8
cert_nodes_part 003 00872 872 880 8
cert_nodes_part 003 00880 880 888 8
cert_nodes_part 003 00888 888 896 8
cert_nodes_part 003 00896 896 904 8
cert_nodes_part 003 00904 904 912 8
cert_nodes_part 003 00912 912 920 8
cert_nodes_part 003 00920 920 928 8
cert_nodes_part 003 00928 928 936 8
cert_nodes_part 003 00936 936 944 8
cert_nodes_part 003 00944 944 952 8
cert_nodes_part 003 00952 952 960 8
cert_nodes_part 003 00960 960 968 8
cert_nodes_part 003 00968 968 976 8
cert_nodes_part 003 00976 976 984 8
cert_nodes_part 003 00984 984 992 8
cert_nodes_part 003 00992 992 1000 8
cert_nodes_part 003 01000 1000 1008 8
cert_nodes_part 003 01008 1008 1016 8
cert_nodes_part 003 01016 1016 1024 8
cert_nodes_part_join_2 003 00768 00784 768 784 776 00776
cert_nodes_part_join_2 003 00784 00800 784 800 792 00792
cert_nodes_part_join 003 00768 00800 768 800 784 00784
cert_nodes_part_join_2 003 00800 00816 800 816 808 00808
cert_nodes_part_join_2 003 00816 00832 816 832 824 00824
cert_nodes_part_join 003 00800 00832 800 832 816 00816
cert_nodes_part_join 003 00768 00832 768 832 800 00800
cert_nodes_part_join_2 003 00832 00848 832 848 840 00840
cert_nodes_part_join_2 003 00848 00864 848 864 856 00856
cert_nodes_part_join 003 00832 00864 832 864 848 00848
cert_nodes_part_join_2 003 00864 00880 864 880 872 00872
cert_nodes_part_join_2 003 00880 00896 880 896 888 00888
cert_nodes_part_join 003 00864 00896 864 896 880 00880
cert_nodes_part_join 003 00832 00896 832 896 864 00864
cert_nodes_part_join 003 00768 00896 768 896 832 00832
cert_nodes_part_join_2 003 00896 00912 896 912 904 00904
cert_nodes_part_join_2 003 00912 00928 912 928 920 00920
cert_nodes_part_join 003 00896 00928 896 928 912 00912
cert_nodes_part_join_2 003 00928 00944 928 944 936 00936
cert_nodes_part_join_2 003 00944 00960 944 960 952 00952
cert_nodes_part_join 003 00928 00960 928 960 944 00944
cert_nodes_part_join 003 00896 00960 896 960 928 00928
cert_nodes_part_join_2 003 00960 00976 960 976 968 00968
cert_nodes_part_join_2 003 00976 00992 976 992 984 00984
cert_nodes_part_join 003 00960 00992 960 992 976 00976
cert_nodes_part_join_2 003 00992 01008 992 1008 1000 01000
cert_nodes_part_join_2 003 01008 01024 1008 1024 1016 01016
cert_nodes_part_join 003 00992 01024 992 1024 1008 01008
cert_nodes_part_join 003 00960 01024 960 1024 992 00992
cert_nodes_part_join 003 00896 01024 896 1024 960 00960
cert_nodes_part_join 003 00768 01024 768 1024 896 00896
end Papers.RationalityTen.PolygonGrowth.N7
