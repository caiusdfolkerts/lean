module
prelude
public import SharedSmallGraphData

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem ridges_006_b768 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 768 772 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 768 4 (by decide +kernel)

theorem ridges_006_b772 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 772 776 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 772 4 (by decide +kernel)

theorem ridges_006_b776 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 776 780 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 776 4 (by decide +kernel)

theorem ridges_006_b780 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 780 784 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 780 4 (by decide +kernel)

theorem ridges_006_b784 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 784 788 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 784 4 (by decide +kernel)

theorem ridges_006_b788 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 788 792 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 788 4 (by decide +kernel)

theorem ridges_006_b792 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 792 796 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 792 4 (by decide +kernel)

theorem ridges_006_b796 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 796 800 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 796 4 (by decide +kernel)

theorem ridges_006_b800 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 800 804 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 800 4 (by decide +kernel)

theorem ridges_006_b804 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 804 808 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 804 4 (by decide +kernel)

theorem ridges_006_b808 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 808 812 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 808 4 (by decide +kernel)

theorem ridges_006_b812 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 812 816 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 812 4 (by decide +kernel)

theorem ridges_006_b816 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 816 820 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 816 4 (by decide +kernel)

theorem ridges_006_b820 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 820 824 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 820 4 (by decide +kernel)

theorem ridges_006_b824 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 824 828 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 824 4 (by decide +kernel)

theorem ridges_006_b828 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 828 832 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 828 4 (by decide +kernel)

theorem ridges_006_b832 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 832 836 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 832 4 (by decide +kernel)

theorem ridges_006_b836 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 836 840 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 836 4 (by decide +kernel)

theorem ridges_006_b840 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 840 844 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 840 4 (by decide +kernel)

theorem ridges_006_b844 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 844 848 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 844 4 (by decide +kernel)

theorem ridges_006_b848 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 848 852 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 848 4 (by decide +kernel)

theorem ridges_006_b852 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 852 856 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 852 4 (by decide +kernel)

theorem ridges_006_b856 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 856 860 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 856 4 (by decide +kernel)

theorem ridges_006_b860 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 860 864 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 860 4 (by decide +kernel)

theorem ridges_006_b864 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 864 868 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 864 4 (by decide +kernel)

theorem ridges_006_b868 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 868 872 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 868 4 (by decide +kernel)

theorem ridges_006_b872 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 872 876 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 872 4 (by decide +kernel)

theorem ridges_006_b876 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 876 880 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 876 4 (by decide +kernel)

theorem ridges_006_b880 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 880 884 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 880 4 (by decide +kernel)

theorem ridges_006_b884 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 884 888 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 884 4 (by decide +kernel)

theorem ridges_006_b888 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 888 892 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 888 4 (by decide +kernel)

theorem ridges_006_b892 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 892 896 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 892 4 (by decide +kernel)

theorem ridges_006 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 768 896 :=
  (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 768 832 896
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 768 800 832
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 768 784 800
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 768 776 784
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 768 772 776
 ridges_006_b768
 ridges_006_b772)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 776 780 784
 ridges_006_b776
 ridges_006_b780))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 784 792 800
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 784 788 792
 ridges_006_b784
 ridges_006_b788)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 792 796 800
 ridges_006_b792
 ridges_006_b796)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 800 816 832
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 800 808 816
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 800 804 808
 ridges_006_b800
 ridges_006_b804)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 808 812 816
 ridges_006_b808
 ridges_006_b812))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 816 824 832
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 816 820 824
 ridges_006_b816
 ridges_006_b820)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 824 828 832
 ridges_006_b824
 ridges_006_b828))))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 832 864 896
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 832 848 864
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 832 840 848
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 832 836 840
 ridges_006_b832
 ridges_006_b836)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 840 844 848
 ridges_006_b840
 ridges_006_b844))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 848 856 864
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 848 852 856
 ridges_006_b848
 ridges_006_b852)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 856 860 864
 ridges_006_b856
 ridges_006_b860)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 864 880 896
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 864 872 880
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 864 868 872
 ridges_006_b864
 ridges_006_b868)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 872 876 880
 ridges_006_b872
 ridges_006_b876))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 880 888 896
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 880 884 888
 ridges_006_b880
 ridges_006_b884)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 888 892 896
 ridges_006_b888
 ridges_006_b892)))))
end Papers.RationalityTen.SharedSmallGraph
