module
public import cubical_indecomposability.face_data_checks.cube_complete.PalomarPart001
import all cubical_indecomposability.face_data_checks.cube_complete.PalomarPart001
public import cubical_indecomposability.face_data_checks.anchors
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Every face inside a listed facet has a cube code

An arbitrary catalogue face is nonempty. Choose one of its vertices, and
test containment only in the facets incident to that vertex. The exact
vertex/facet transpose and the anchor membership are proved below. Thus
the sparse search still covers every face and every facet.

The final numerical certificate traverses only the 3510 actual incidences.
Its explicit `Finset.decidableDforallFinset` instance recurses over the
members of the small finite set, and an explicit cube-code witness avoids
searching over the 27 possible codes. All numerical checks use Lean's
ordinary kernel reduction; the proposed data have no trusted status.

Regenerate with `python3 scripts/sparse_cube_complete.py`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability

private theorem cofacetGroup0028 (i : Fin 1069)
    (hlo : 896 ≤ i.val) (hhi : i.val < 928) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h912 : i.val < 912
  ·
    by_cases h904 : i.val < 904
    ·
      by_cases h900 : i.val < 900
      ·
        by_cases h898 : i.val < 898
        ·
          by_cases h897 : i.val < 897
          ·
            have he : (⟨896, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 896 = i.val
              omega
            simpa only [he] using cofacet0896
          ·
            have he : (⟨897, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 897 = i.val
              omega
            simpa only [he] using cofacet0897
        ·
          by_cases h899 : i.val < 899
          ·
            have he : (⟨898, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 898 = i.val
              omega
            simpa only [he] using cofacet0898
          ·
            have he : (⟨899, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 899 = i.val
              omega
            simpa only [he] using cofacet0899
      ·
        by_cases h902 : i.val < 902
        ·
          by_cases h901 : i.val < 901
          ·
            have he : (⟨900, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 900 = i.val
              omega
            simpa only [he] using cofacet0900
          ·
            have he : (⟨901, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 901 = i.val
              omega
            simpa only [he] using cofacet0901
        ·
          by_cases h903 : i.val < 903
          ·
            have he : (⟨902, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 902 = i.val
              omega
            simpa only [he] using cofacet0902
          ·
            have he : (⟨903, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 903 = i.val
              omega
            simpa only [he] using cofacet0903
    ·
      by_cases h908 : i.val < 908
      ·
        by_cases h906 : i.val < 906
        ·
          by_cases h905 : i.val < 905
          ·
            have he : (⟨904, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 904 = i.val
              omega
            simpa only [he] using cofacet0904
          ·
            have he : (⟨905, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 905 = i.val
              omega
            simpa only [he] using cofacet0905
        ·
          by_cases h907 : i.val < 907
          ·
            have he : (⟨906, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 906 = i.val
              omega
            simpa only [he] using cofacet0906
          ·
            have he : (⟨907, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 907 = i.val
              omega
            simpa only [he] using cofacet0907
      ·
        by_cases h910 : i.val < 910
        ·
          by_cases h909 : i.val < 909
          ·
            have he : (⟨908, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 908 = i.val
              omega
            simpa only [he] using cofacet0908
          ·
            have he : (⟨909, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 909 = i.val
              omega
            simpa only [he] using cofacet0909
        ·
          by_cases h911 : i.val < 911
          ·
            have he : (⟨910, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 910 = i.val
              omega
            simpa only [he] using cofacet0910
          ·
            have he : (⟨911, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 911 = i.val
              omega
            simpa only [he] using cofacet0911
  ·
    by_cases h920 : i.val < 920
    ·
      by_cases h916 : i.val < 916
      ·
        by_cases h914 : i.val < 914
        ·
          by_cases h913 : i.val < 913
          ·
            have he : (⟨912, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 912 = i.val
              omega
            simpa only [he] using cofacet0912
          ·
            have he : (⟨913, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 913 = i.val
              omega
            simpa only [he] using cofacet0913
        ·
          by_cases h915 : i.val < 915
          ·
            have he : (⟨914, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 914 = i.val
              omega
            simpa only [he] using cofacet0914
          ·
            have he : (⟨915, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 915 = i.val
              omega
            simpa only [he] using cofacet0915
      ·
        by_cases h918 : i.val < 918
        ·
          by_cases h917 : i.val < 917
          ·
            have he : (⟨916, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 916 = i.val
              omega
            simpa only [he] using cofacet0916
          ·
            have he : (⟨917, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 917 = i.val
              omega
            simpa only [he] using cofacet0917
        ·
          by_cases h919 : i.val < 919
          ·
            have he : (⟨918, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 918 = i.val
              omega
            simpa only [he] using cofacet0918
          ·
            have he : (⟨919, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 919 = i.val
              omega
            simpa only [he] using cofacet0919
    ·
      by_cases h924 : i.val < 924
      ·
        by_cases h922 : i.val < 922
        ·
          by_cases h921 : i.val < 921
          ·
            have he : (⟨920, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 920 = i.val
              omega
            simpa only [he] using cofacet0920
          ·
            have he : (⟨921, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 921 = i.val
              omega
            simpa only [he] using cofacet0921
        ·
          by_cases h923 : i.val < 923
          ·
            have he : (⟨922, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 922 = i.val
              omega
            simpa only [he] using cofacet0922
          ·
            have he : (⟨923, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 923 = i.val
              omega
            simpa only [he] using cofacet0923
      ·
        by_cases h926 : i.val < 926
        ·
          by_cases h925 : i.val < 925
          ·
            have he : (⟨924, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 924 = i.val
              omega
            simpa only [he] using cofacet0924
          ·
            have he : (⟨925, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 925 = i.val
              omega
            simpa only [he] using cofacet0925
        ·
          by_cases h927 : i.val < 927
          ·
            have he : (⟨926, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 926 = i.val
              omega
            simpa only [he] using cofacet0926
          ·
            have he : (⟨927, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 927 = i.val
              omega
            simpa only [he] using cofacet0927

private theorem cofacetGroup0029 (i : Fin 1069)
    (hlo : 928 ≤ i.val) (hhi : i.val < 960) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h944 : i.val < 944
  ·
    by_cases h936 : i.val < 936
    ·
      by_cases h932 : i.val < 932
      ·
        by_cases h930 : i.val < 930
        ·
          by_cases h929 : i.val < 929
          ·
            have he : (⟨928, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 928 = i.val
              omega
            simpa only [he] using cofacet0928
          ·
            have he : (⟨929, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 929 = i.val
              omega
            simpa only [he] using cofacet0929
        ·
          by_cases h931 : i.val < 931
          ·
            have he : (⟨930, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 930 = i.val
              omega
            simpa only [he] using cofacet0930
          ·
            have he : (⟨931, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 931 = i.val
              omega
            simpa only [he] using cofacet0931
      ·
        by_cases h934 : i.val < 934
        ·
          by_cases h933 : i.val < 933
          ·
            have he : (⟨932, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 932 = i.val
              omega
            simpa only [he] using cofacet0932
          ·
            have he : (⟨933, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 933 = i.val
              omega
            simpa only [he] using cofacet0933
        ·
          by_cases h935 : i.val < 935
          ·
            have he : (⟨934, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 934 = i.val
              omega
            simpa only [he] using cofacet0934
          ·
            have he : (⟨935, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 935 = i.val
              omega
            simpa only [he] using cofacet0935
    ·
      by_cases h940 : i.val < 940
      ·
        by_cases h938 : i.val < 938
        ·
          by_cases h937 : i.val < 937
          ·
            have he : (⟨936, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 936 = i.val
              omega
            simpa only [he] using cofacet0936
          ·
            have he : (⟨937, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 937 = i.val
              omega
            simpa only [he] using cofacet0937
        ·
          by_cases h939 : i.val < 939
          ·
            have he : (⟨938, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 938 = i.val
              omega
            simpa only [he] using cofacet0938
          ·
            have he : (⟨939, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 939 = i.val
              omega
            simpa only [he] using cofacet0939
      ·
        by_cases h942 : i.val < 942
        ·
          by_cases h941 : i.val < 941
          ·
            have he : (⟨940, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 940 = i.val
              omega
            simpa only [he] using cofacet0940
          ·
            have he : (⟨941, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 941 = i.val
              omega
            simpa only [he] using cofacet0941
        ·
          by_cases h943 : i.val < 943
          ·
            have he : (⟨942, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 942 = i.val
              omega
            simpa only [he] using cofacet0942
          ·
            have he : (⟨943, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 943 = i.val
              omega
            simpa only [he] using cofacet0943
  ·
    by_cases h952 : i.val < 952
    ·
      by_cases h948 : i.val < 948
      ·
        by_cases h946 : i.val < 946
        ·
          by_cases h945 : i.val < 945
          ·
            have he : (⟨944, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 944 = i.val
              omega
            simpa only [he] using cofacet0944
          ·
            have he : (⟨945, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 945 = i.val
              omega
            simpa only [he] using cofacet0945
        ·
          by_cases h947 : i.val < 947
          ·
            have he : (⟨946, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 946 = i.val
              omega
            simpa only [he] using cofacet0946
          ·
            have he : (⟨947, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 947 = i.val
              omega
            simpa only [he] using cofacet0947
      ·
        by_cases h950 : i.val < 950
        ·
          by_cases h949 : i.val < 949
          ·
            have he : (⟨948, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 948 = i.val
              omega
            simpa only [he] using cofacet0948
          ·
            have he : (⟨949, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 949 = i.val
              omega
            simpa only [he] using cofacet0949
        ·
          by_cases h951 : i.val < 951
          ·
            have he : (⟨950, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 950 = i.val
              omega
            simpa only [he] using cofacet0950
          ·
            have he : (⟨951, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 951 = i.val
              omega
            simpa only [he] using cofacet0951
    ·
      by_cases h956 : i.val < 956
      ·
        by_cases h954 : i.val < 954
        ·
          by_cases h953 : i.val < 953
          ·
            have he : (⟨952, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 952 = i.val
              omega
            simpa only [he] using cofacet0952
          ·
            have he : (⟨953, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 953 = i.val
              omega
            simpa only [he] using cofacet0953
        ·
          by_cases h955 : i.val < 955
          ·
            have he : (⟨954, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 954 = i.val
              omega
            simpa only [he] using cofacet0954
          ·
            have he : (⟨955, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 955 = i.val
              omega
            simpa only [he] using cofacet0955
      ·
        by_cases h958 : i.val < 958
        ·
          by_cases h957 : i.val < 957
          ·
            have he : (⟨956, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 956 = i.val
              omega
            simpa only [he] using cofacet0956
          ·
            have he : (⟨957, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 957 = i.val
              omega
            simpa only [he] using cofacet0957
        ·
          by_cases h959 : i.val < 959
          ·
            have he : (⟨958, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 958 = i.val
              omega
            simpa only [he] using cofacet0958
          ·
            have he : (⟨959, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 959 = i.val
              omega
            simpa only [he] using cofacet0959

private theorem cofacetGroup0030 (i : Fin 1069)
    (hlo : 960 ≤ i.val) (hhi : i.val < 992) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h976 : i.val < 976
  ·
    by_cases h968 : i.val < 968
    ·
      by_cases h964 : i.val < 964
      ·
        by_cases h962 : i.val < 962
        ·
          by_cases h961 : i.val < 961
          ·
            have he : (⟨960, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 960 = i.val
              omega
            simpa only [he] using cofacet0960
          ·
            have he : (⟨961, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 961 = i.val
              omega
            simpa only [he] using cofacet0961
        ·
          by_cases h963 : i.val < 963
          ·
            have he : (⟨962, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 962 = i.val
              omega
            simpa only [he] using cofacet0962
          ·
            have he : (⟨963, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 963 = i.val
              omega
            simpa only [he] using cofacet0963
      ·
        by_cases h966 : i.val < 966
        ·
          by_cases h965 : i.val < 965
          ·
            have he : (⟨964, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 964 = i.val
              omega
            simpa only [he] using cofacet0964
          ·
            have he : (⟨965, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 965 = i.val
              omega
            simpa only [he] using cofacet0965
        ·
          by_cases h967 : i.val < 967
          ·
            have he : (⟨966, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 966 = i.val
              omega
            simpa only [he] using cofacet0966
          ·
            have he : (⟨967, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 967 = i.val
              omega
            simpa only [he] using cofacet0967
    ·
      by_cases h972 : i.val < 972
      ·
        by_cases h970 : i.val < 970
        ·
          by_cases h969 : i.val < 969
          ·
            have he : (⟨968, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 968 = i.val
              omega
            simpa only [he] using cofacet0968
          ·
            have he : (⟨969, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 969 = i.val
              omega
            simpa only [he] using cofacet0969
        ·
          by_cases h971 : i.val < 971
          ·
            have he : (⟨970, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 970 = i.val
              omega
            simpa only [he] using cofacet0970
          ·
            have he : (⟨971, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 971 = i.val
              omega
            simpa only [he] using cofacet0971
      ·
        by_cases h974 : i.val < 974
        ·
          by_cases h973 : i.val < 973
          ·
            have he : (⟨972, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 972 = i.val
              omega
            simpa only [he] using cofacet0972
          ·
            have he : (⟨973, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 973 = i.val
              omega
            simpa only [he] using cofacet0973
        ·
          by_cases h975 : i.val < 975
          ·
            have he : (⟨974, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 974 = i.val
              omega
            simpa only [he] using cofacet0974
          ·
            have he : (⟨975, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 975 = i.val
              omega
            simpa only [he] using cofacet0975
  ·
    by_cases h984 : i.val < 984
    ·
      by_cases h980 : i.val < 980
      ·
        by_cases h978 : i.val < 978
        ·
          by_cases h977 : i.val < 977
          ·
            have he : (⟨976, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 976 = i.val
              omega
            simpa only [he] using cofacet0976
          ·
            have he : (⟨977, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 977 = i.val
              omega
            simpa only [he] using cofacet0977
        ·
          by_cases h979 : i.val < 979
          ·
            have he : (⟨978, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 978 = i.val
              omega
            simpa only [he] using cofacet0978
          ·
            have he : (⟨979, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 979 = i.val
              omega
            simpa only [he] using cofacet0979
      ·
        by_cases h982 : i.val < 982
        ·
          by_cases h981 : i.val < 981
          ·
            have he : (⟨980, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 980 = i.val
              omega
            simpa only [he] using cofacet0980
          ·
            have he : (⟨981, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 981 = i.val
              omega
            simpa only [he] using cofacet0981
        ·
          by_cases h983 : i.val < 983
          ·
            have he : (⟨982, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 982 = i.val
              omega
            simpa only [he] using cofacet0982
          ·
            have he : (⟨983, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 983 = i.val
              omega
            simpa only [he] using cofacet0983
    ·
      by_cases h988 : i.val < 988
      ·
        by_cases h986 : i.val < 986
        ·
          by_cases h985 : i.val < 985
          ·
            have he : (⟨984, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 984 = i.val
              omega
            simpa only [he] using cofacet0984
          ·
            have he : (⟨985, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 985 = i.val
              omega
            simpa only [he] using cofacet0985
        ·
          by_cases h987 : i.val < 987
          ·
            have he : (⟨986, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 986 = i.val
              omega
            simpa only [he] using cofacet0986
          ·
            have he : (⟨987, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 987 = i.val
              omega
            simpa only [he] using cofacet0987
      ·
        by_cases h990 : i.val < 990
        ·
          by_cases h989 : i.val < 989
          ·
            have he : (⟨988, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 988 = i.val
              omega
            simpa only [he] using cofacet0988
          ·
            have he : (⟨989, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 989 = i.val
              omega
            simpa only [he] using cofacet0989
        ·
          by_cases h991 : i.val < 991
          ·
            have he : (⟨990, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 990 = i.val
              omega
            simpa only [he] using cofacet0990
          ·
            have he : (⟨991, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 991 = i.val
              omega
            simpa only [he] using cofacet0991

private theorem cofacetGroup0031 (i : Fin 1069)
    (hlo : 992 ≤ i.val) (hhi : i.val < 1024) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h1008 : i.val < 1008
  ·
    by_cases h1000 : i.val < 1000
    ·
      by_cases h996 : i.val < 996
      ·
        by_cases h994 : i.val < 994
        ·
          by_cases h993 : i.val < 993
          ·
            have he : (⟨992, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 992 = i.val
              omega
            simpa only [he] using cofacet0992
          ·
            have he : (⟨993, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 993 = i.val
              omega
            simpa only [he] using cofacet0993
        ·
          by_cases h995 : i.val < 995
          ·
            have he : (⟨994, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 994 = i.val
              omega
            simpa only [he] using cofacet0994
          ·
            have he : (⟨995, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 995 = i.val
              omega
            simpa only [he] using cofacet0995
      ·
        by_cases h998 : i.val < 998
        ·
          by_cases h997 : i.val < 997
          ·
            have he : (⟨996, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 996 = i.val
              omega
            simpa only [he] using cofacet0996
          ·
            have he : (⟨997, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 997 = i.val
              omega
            simpa only [he] using cofacet0997
        ·
          by_cases h999 : i.val < 999
          ·
            have he : (⟨998, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 998 = i.val
              omega
            simpa only [he] using cofacet0998
          ·
            have he : (⟨999, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 999 = i.val
              omega
            simpa only [he] using cofacet0999
    ·
      by_cases h1004 : i.val < 1004
      ·
        by_cases h1002 : i.val < 1002
        ·
          by_cases h1001 : i.val < 1001
          ·
            have he : (⟨1000, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1000 = i.val
              omega
            simpa only [he] using cofacet1000
          ·
            have he : (⟨1001, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1001 = i.val
              omega
            simpa only [he] using cofacet1001
        ·
          by_cases h1003 : i.val < 1003
          ·
            have he : (⟨1002, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1002 = i.val
              omega
            simpa only [he] using cofacet1002
          ·
            have he : (⟨1003, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1003 = i.val
              omega
            simpa only [he] using cofacet1003
      ·
        by_cases h1006 : i.val < 1006
        ·
          by_cases h1005 : i.val < 1005
          ·
            have he : (⟨1004, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1004 = i.val
              omega
            simpa only [he] using cofacet1004
          ·
            have he : (⟨1005, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1005 = i.val
              omega
            simpa only [he] using cofacet1005
        ·
          by_cases h1007 : i.val < 1007
          ·
            have he : (⟨1006, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1006 = i.val
              omega
            simpa only [he] using cofacet1006
          ·
            have he : (⟨1007, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1007 = i.val
              omega
            simpa only [he] using cofacet1007
  ·
    by_cases h1016 : i.val < 1016
    ·
      by_cases h1012 : i.val < 1012
      ·
        by_cases h1010 : i.val < 1010
        ·
          by_cases h1009 : i.val < 1009
          ·
            have he : (⟨1008, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1008 = i.val
              omega
            simpa only [he] using cofacet1008
          ·
            have he : (⟨1009, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1009 = i.val
              omega
            simpa only [he] using cofacet1009
        ·
          by_cases h1011 : i.val < 1011
          ·
            have he : (⟨1010, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1010 = i.val
              omega
            simpa only [he] using cofacet1010
          ·
            have he : (⟨1011, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1011 = i.val
              omega
            simpa only [he] using cofacet1011
      ·
        by_cases h1014 : i.val < 1014
        ·
          by_cases h1013 : i.val < 1013
          ·
            have he : (⟨1012, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1012 = i.val
              omega
            simpa only [he] using cofacet1012
          ·
            have he : (⟨1013, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1013 = i.val
              omega
            simpa only [he] using cofacet1013
        ·
          by_cases h1015 : i.val < 1015
          ·
            have he : (⟨1014, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1014 = i.val
              omega
            simpa only [he] using cofacet1014
          ·
            have he : (⟨1015, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1015 = i.val
              omega
            simpa only [he] using cofacet1015
    ·
      by_cases h1020 : i.val < 1020
      ·
        by_cases h1018 : i.val < 1018
        ·
          by_cases h1017 : i.val < 1017
          ·
            have he : (⟨1016, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1016 = i.val
              omega
            simpa only [he] using cofacet1016
          ·
            have he : (⟨1017, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1017 = i.val
              omega
            simpa only [he] using cofacet1017
        ·
          by_cases h1019 : i.val < 1019
          ·
            have he : (⟨1018, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1018 = i.val
              omega
            simpa only [he] using cofacet1018
          ·
            have he : (⟨1019, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1019 = i.val
              omega
            simpa only [he] using cofacet1019
      ·
        by_cases h1022 : i.val < 1022
        ·
          by_cases h1021 : i.val < 1021
          ·
            have he : (⟨1020, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1020 = i.val
              omega
            simpa only [he] using cofacet1020
          ·
            have he : (⟨1021, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1021 = i.val
              omega
            simpa only [he] using cofacet1021
        ·
          by_cases h1023 : i.val < 1023
          ·
            have he : (⟨1022, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1022 = i.val
              omega
            simpa only [he] using cofacet1022
          ·
            have he : (⟨1023, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1023 = i.val
              omega
            simpa only [he] using cofacet1023

private theorem cofacetGroup0032 (i : Fin 1069)
    (hlo : 1024 ≤ i.val) (hhi : i.val < 1056) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h1040 : i.val < 1040
  ·
    by_cases h1032 : i.val < 1032
    ·
      by_cases h1028 : i.val < 1028
      ·
        by_cases h1026 : i.val < 1026
        ·
          by_cases h1025 : i.val < 1025
          ·
            have he : (⟨1024, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1024 = i.val
              omega
            simpa only [he] using cofacet1024
          ·
            have he : (⟨1025, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1025 = i.val
              omega
            simpa only [he] using cofacet1025
        ·
          by_cases h1027 : i.val < 1027
          ·
            have he : (⟨1026, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1026 = i.val
              omega
            simpa only [he] using cofacet1026
          ·
            have he : (⟨1027, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1027 = i.val
              omega
            simpa only [he] using cofacet1027
      ·
        by_cases h1030 : i.val < 1030
        ·
          by_cases h1029 : i.val < 1029
          ·
            have he : (⟨1028, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1028 = i.val
              omega
            simpa only [he] using cofacet1028
          ·
            have he : (⟨1029, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1029 = i.val
              omega
            simpa only [he] using cofacet1029
        ·
          by_cases h1031 : i.val < 1031
          ·
            have he : (⟨1030, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1030 = i.val
              omega
            simpa only [he] using cofacet1030
          ·
            have he : (⟨1031, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1031 = i.val
              omega
            simpa only [he] using cofacet1031
    ·
      by_cases h1036 : i.val < 1036
      ·
        by_cases h1034 : i.val < 1034
        ·
          by_cases h1033 : i.val < 1033
          ·
            have he : (⟨1032, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1032 = i.val
              omega
            simpa only [he] using cofacet1032
          ·
            have he : (⟨1033, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1033 = i.val
              omega
            simpa only [he] using cofacet1033
        ·
          by_cases h1035 : i.val < 1035
          ·
            have he : (⟨1034, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1034 = i.val
              omega
            simpa only [he] using cofacet1034
          ·
            have he : (⟨1035, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1035 = i.val
              omega
            simpa only [he] using cofacet1035
      ·
        by_cases h1038 : i.val < 1038
        ·
          by_cases h1037 : i.val < 1037
          ·
            have he : (⟨1036, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1036 = i.val
              omega
            simpa only [he] using cofacet1036
          ·
            have he : (⟨1037, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1037 = i.val
              omega
            simpa only [he] using cofacet1037
        ·
          by_cases h1039 : i.val < 1039
          ·
            have he : (⟨1038, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1038 = i.val
              omega
            simpa only [he] using cofacet1038
          ·
            have he : (⟨1039, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1039 = i.val
              omega
            simpa only [he] using cofacet1039
  ·
    by_cases h1048 : i.val < 1048
    ·
      by_cases h1044 : i.val < 1044
      ·
        by_cases h1042 : i.val < 1042
        ·
          by_cases h1041 : i.val < 1041
          ·
            have he : (⟨1040, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1040 = i.val
              omega
            simpa only [he] using cofacet1040
          ·
            have he : (⟨1041, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1041 = i.val
              omega
            simpa only [he] using cofacet1041
        ·
          by_cases h1043 : i.val < 1043
          ·
            have he : (⟨1042, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1042 = i.val
              omega
            simpa only [he] using cofacet1042
          ·
            have he : (⟨1043, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1043 = i.val
              omega
            simpa only [he] using cofacet1043
      ·
        by_cases h1046 : i.val < 1046
        ·
          by_cases h1045 : i.val < 1045
          ·
            have he : (⟨1044, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1044 = i.val
              omega
            simpa only [he] using cofacet1044
          ·
            have he : (⟨1045, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1045 = i.val
              omega
            simpa only [he] using cofacet1045
        ·
          by_cases h1047 : i.val < 1047
          ·
            have he : (⟨1046, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1046 = i.val
              omega
            simpa only [he] using cofacet1046
          ·
            have he : (⟨1047, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1047 = i.val
              omega
            simpa only [he] using cofacet1047
    ·
      by_cases h1052 : i.val < 1052
      ·
        by_cases h1050 : i.val < 1050
        ·
          by_cases h1049 : i.val < 1049
          ·
            have he : (⟨1048, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1048 = i.val
              omega
            simpa only [he] using cofacet1048
          ·
            have he : (⟨1049, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1049 = i.val
              omega
            simpa only [he] using cofacet1049
        ·
          by_cases h1051 : i.val < 1051
          ·
            have he : (⟨1050, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1050 = i.val
              omega
            simpa only [he] using cofacet1050
          ·
            have he : (⟨1051, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1051 = i.val
              omega
            simpa only [he] using cofacet1051
      ·
        by_cases h1054 : i.val < 1054
        ·
          by_cases h1053 : i.val < 1053
          ·
            have he : (⟨1052, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1052 = i.val
              omega
            simpa only [he] using cofacet1052
          ·
            have he : (⟨1053, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1053 = i.val
              omega
            simpa only [he] using cofacet1053
        ·
          by_cases h1055 : i.val < 1055
          ·
            have he : (⟨1054, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1054 = i.val
              omega
            simpa only [he] using cofacet1054
          ·
            have he : (⟨1055, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1055 = i.val
              omega
            simpa only [he] using cofacet1055

private theorem cofacetGroup0033 (i : Fin 1069)
    (hlo : 1056 ≤ i.val) (hhi : i.val < 1069) :
    cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h1062 : i.val < 1062
  ·
    by_cases h1059 : i.val < 1059
    ·
      by_cases h1057 : i.val < 1057
      ·
        have he : (⟨1056, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1056 = i.val
          omega
        simpa only [he] using cofacet1056
      ·
        by_cases h1058 : i.val < 1058
        ·
          have he : (⟨1057, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1057 = i.val
            omega
          simpa only [he] using cofacet1057
        ·
          have he : (⟨1058, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1058 = i.val
            omega
          simpa only [he] using cofacet1058
    ·
      by_cases h1060 : i.val < 1060
      ·
        have he : (⟨1059, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1059 = i.val
          omega
        simpa only [he] using cofacet1059
      ·
        by_cases h1061 : i.val < 1061
        ·
          have he : (⟨1060, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1060 = i.val
            omega
          simpa only [he] using cofacet1060
        ·
          have he : (⟨1061, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1061 = i.val
            omega
          simpa only [he] using cofacet1061
  ·
    by_cases h1065 : i.val < 1065
    ·
      by_cases h1063 : i.val < 1063
      ·
        have he : (⟨1062, by decide⟩ : Fin 1069) = i := by
          apply Fin.ext
          change 1062 = i.val
          omega
        simpa only [he] using cofacet1062
      ·
        by_cases h1064 : i.val < 1064
        ·
          have he : (⟨1063, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1063 = i.val
            omega
          simpa only [he] using cofacet1063
        ·
          have he : (⟨1064, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1064 = i.val
            omega
          simpa only [he] using cofacet1064
    ·
      by_cases h1067 : i.val < 1067
      ·
        by_cases h1066 : i.val < 1066
        ·
          have he : (⟨1065, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1065 = i.val
            omega
          simpa only [he] using cofacet1065
        ·
          have he : (⟨1066, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1066 = i.val
            omega
          simpa only [he] using cofacet1066
      ·
        by_cases h1068 : i.val < 1068
        ·
          have he : (⟨1067, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1067 = i.val
            omega
          simpa only [he] using cofacet1067
        ·
          have he : (⟨1068, by decide⟩ : Fin 1069) = i := by
            apply Fin.ext
            change 1068 = i.val
            omega
          simpa only [he] using cofacet1068

private theorem cubeCofacetCertificate_all : ∀ i : Fin 1069,
    cubeCofacetCertificate i := by
  intro i
  have hi_bound := i.isLt
  by_cases h544 : i.val < 544
  ·
    by_cases h256 : i.val < 256
    ·
      by_cases h128 : i.val < 128
      ·
        by_cases h64 : i.val < 64
        ·
          by_cases h32 : i.val < 32
          ·
            exact cofacetGroup0000 i (by omega) (by omega)
          ·
            exact cofacetGroup0001 i (by omega) (by omega)
        ·
          by_cases h96 : i.val < 96
          ·
            exact cofacetGroup0002 i (by omega) (by omega)
          ·
            exact cofacetGroup0003 i (by omega) (by omega)
      ·
        by_cases h192 : i.val < 192
        ·
          by_cases h160 : i.val < 160
          ·
            exact cofacetGroup0004 i (by omega) (by omega)
          ·
            exact cofacetGroup0005 i (by omega) (by omega)
        ·
          by_cases h224 : i.val < 224
          ·
            exact cofacetGroup0006 i (by omega) (by omega)
          ·
            exact cofacetGroup0007 i (by omega) (by omega)
    ·
      by_cases h384 : i.val < 384
      ·
        by_cases h320 : i.val < 320
        ·
          by_cases h288 : i.val < 288
          ·
            exact cofacetGroup0008 i (by omega) (by omega)
          ·
            exact cofacetGroup0009 i (by omega) (by omega)
        ·
          by_cases h352 : i.val < 352
          ·
            exact cofacetGroup0010 i (by omega) (by omega)
          ·
            exact cofacetGroup0011 i (by omega) (by omega)
      ·
        by_cases h448 : i.val < 448
        ·
          by_cases h416 : i.val < 416
          ·
            exact cofacetGroup0012 i (by omega) (by omega)
          ·
            exact cofacetGroup0013 i (by omega) (by omega)
        ·
          by_cases h480 : i.val < 480
          ·
            exact cofacetGroup0014 i (by omega) (by omega)
          ·
            by_cases h512 : i.val < 512
            ·
              exact cofacetGroup0015 i (by omega) (by omega)
            ·
              exact cofacetGroup0016 i (by omega) (by omega)
  ·
    by_cases h800 : i.val < 800
    ·
      by_cases h672 : i.val < 672
      ·
        by_cases h608 : i.val < 608
        ·
          by_cases h576 : i.val < 576
          ·
            exact cofacetGroup0017 i (by omega) (by omega)
          ·
            exact cofacetGroup0018 i (by omega) (by omega)
        ·
          by_cases h640 : i.val < 640
          ·
            exact cofacetGroup0019 i (by omega) (by omega)
          ·
            exact cofacetGroup0020 i (by omega) (by omega)
      ·
        by_cases h736 : i.val < 736
        ·
          by_cases h704 : i.val < 704
          ·
            exact cofacetGroup0021 i (by omega) (by omega)
          ·
            exact cofacetGroup0022 i (by omega) (by omega)
        ·
          by_cases h768 : i.val < 768
          ·
            exact cofacetGroup0023 i (by omega) (by omega)
          ·
            exact cofacetGroup0024 i (by omega) (by omega)
    ·
      by_cases h928 : i.val < 928
      ·
        by_cases h864 : i.val < 864
        ·
          by_cases h832 : i.val < 832
          ·
            exact cofacetGroup0025 i (by omega) (by omega)
          ·
            exact cofacetGroup0026 i (by omega) (by omega)
        ·
          by_cases h896 : i.val < 896
          ·
            exact cofacetGroup0027 i (by omega) (by omega)
          ·
            exact cofacetGroup0028 i (by omega) (by omega)
      ·
        by_cases h992 : i.val < 992
        ·
          by_cases h960 : i.val < 960
          ·
            exact cofacetGroup0029 i (by omega) (by omega)
          ·
            exact cofacetGroup0030 i (by omega) (by omega)
        ·
          by_cases h1024 : i.val < 1024
          ·
            exact cofacetGroup0031 i (by omega) (by omega)
          ·
            by_cases h1056 : i.val < 1056
            ·
              exact cofacetGroup0032 i (by omega) (by omega)
            ·
              exact cofacetGroup0033 i (by omega) (by omega)

/-- All catalogue faces contained in a facet occur among that facet's
27 nonempty standard cube-face codes. No geometric condition is assumed. -/
theorem codeFace_complete : ∀ (f : Fin 130) (i : Fin 1069),
    faceMask i ⊆ facetLabels f → ∃ c : Fin 27, codeFace f c = i := by
  intro f i h
  apply Exists.intro (cubeCofacetCode i f)
  exact cubeCofacetCertificate_all i f ((cubeCofacets_iff i f).mpr h)

end CubicalIndecomposability
