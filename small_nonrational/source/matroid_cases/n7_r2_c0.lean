module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N7R2C0

kernel_lrat_refutation extension
  "p cnf 21 21\n-7 0\n-8 0\n-9 0\n-10 0\n11 0\n12 0\n13 0\n14 0\n15 0\n-20 -11 7 16 0\n-20 -12 8 17 0\n-20 -13 9 18 0\n-20 -14 10 19 0\n-16 -15 7 20 0\n-17 -15 8 20 0\n-18 -15 9 20 0\n-19 -15 10 20 0\n16 17 18 19 20 21 0\n-21 16 17 18 19 20 0\n-20 -19 -18 -17 -16 21 0\n-21 -20 -19 -18 -17 -16 0\n"
  "22 20 0 9 4 3 2 1 14 15 16 17 19 18 0\n23 16 0 22 5 1 10 0\n24 17 0 22 6 2 11 0\n25 18 0 22 7 3 12 0\n26 19 0 22 8 4 13 0\n27 -21 0 22 26 25 24 23 21 0\n28 0 22 26 25 24 23 27 20 0\n"

end Papers.RationalityTen.MatroidCases.N7R2C0
