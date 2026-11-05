module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N7R2C2

kernel_lrat_refutation extension
  "p cnf 21 29\n-2 0\n-3 0\n-6 0\n7 0\n8 0\n9 0\n10 0\n11 0\n12 0\n13 0\n14 0\n15 0\n-18 -7 2 16 0\n-18 -8 3 17 0\n-16 -9 2 18 0\n-17 -9 3 18 0\n-19 -9 6 18 0\n-18 -10 6 19 0\n-18 -15 20 21 0\n-20 -11 16 21 0\n-20 -12 17 21 0\n-20 -13 18 21 0\n-20 -14 19 21 0\n-21 -9 18 20 0\n16 17 18 19 20 21 0\n-21 -20 16 17 18 19 0\n-21 -19 -18 -17 -16 20 0\n-20 -19 -18 -17 -16 21 0\n-21 -20 -19 -18 -17 -16 0\n"
  "30 18 20 0 6 3 2 1 15 16 17 24 25 0\n31 20 0 12 7 3 5 2 4 1 30 13 14 18 19 27 0\n32 -18 -21 0 31 7 3 5 2 4 1 13 14 18 29 0\n33 -21 0 31 6 3 2 1 32 15 16 17 26 0\n34 18 0 31 10 33 22 0\n35 19 0 31 11 33 23 0\n36 17 0 31 9 33 21 0\n37 16 0 31 8 33 20 0\n38 0 31 35 34 36 37 33 28 0\n"

end Papers.RationalityTen.MatroidCases.N7R2C2
