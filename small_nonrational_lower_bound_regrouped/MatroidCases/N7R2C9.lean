module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N7R2C9

kernel_lrat_refutation extension
  "p cnf 21 41\n1 0\n2 0\n3 0\n4 0\n5 0\n6 0\n7 0\n8 0\n9 0\n10 0\n11 0\n12 0\n13 0\n14 0\n15 0\n-16 -3 17 18 0\n-16 -5 17 19 0\n-16 -8 17 20 0\n-16 -12 17 21 0\n-16 -13 18 21 0\n-16 -14 19 21 0\n-16 -15 20 21 0\n-17 -2 16 18 0\n-17 -4 16 19 0\n-17 -7 16 20 0\n-17 -9 18 20 0\n-17 -10 19 20 0\n-17 -11 16 21 0\n-18 -1 16 17 0\n-19 -3 17 18 0\n-20 -3 17 18 0\n-20 -6 18 19 0\n-21 -3 17 18 0\n16 17 18 19 20 21 0\n-21 -20 -19 -18 -17 16 0\n-21 -20 -19 -18 -16 17 0\n-21 -20 -19 -17 -16 18 0\n-21 -20 -18 -17 -16 19 0\n-21 -19 -18 -17 -16 20 0\n-20 -19 -18 -17 -16 21 0\n-21 -20 -19 -18 -17 -16 0\n"
  "42 17 16 0 3 1 29 30 31 33 34 0\n43 16 0 11 7 4 2 42 23 24 25 28 35 0\n44 -19 -20 -21 -17 0 43 37 41 0\n45 -20 -17 -21 0 43 6 44 32 38 0\n46 -17 -21 0 43 9 10 45 27 26 39 0\n47 -21 0 43 8 5 3 46 16 17 18 36 0\n48 17 0 43 12 47 19 0\n49 18 0 43 13 47 20 0\n50 19 0 43 14 47 21 0\n51 20 0 43 15 47 22 0\n52 0 51 50 49 48 43 47 40 0\n"

end Papers.RationalityTen.MatroidCases.N7R2C9
