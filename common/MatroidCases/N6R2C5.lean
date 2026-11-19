module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N6R2C5

kernel_lrat_refutation extension
  "p cnf 15 29\n1 0\n2 0\n3 0\n4 0\n5 0\n6 0\n7 0\n8 0\n9 0\n10 0\n-11 -3 12 13 0\n-11 -5 12 14 0\n-11 -8 12 15 0\n-11 -9 13 15 0\n-11 -10 14 15 0\n-12 -6 13 14 0\n-12 -7 11 15 0\n-13 -7 11 15 0\n-14 -7 11 15 0\n-15 -1 11 12 0\n-15 -2 11 13 0\n-15 -4 11 14 0\n11 12 13 14 15 0\n-15 -14 -13 -12 11 0\n-15 -14 -13 -11 12 0\n-15 -14 -12 -11 13 0\n-15 -13 -12 -11 14 0\n-14 -13 -12 -11 15 0\n-15 -14 -13 -12 -11 0\n"
  "30 15 11 0 7 19 18 17 23 0\n31 11 0 4 2 1 30 20 21 22 24 0\n32 -14 -12 -15 0 31 29 26 0\n33 -12 -15 0 31 6 32 16 27 0\n34 -15 0 31 5 3 33 11 12 25 0\n35 12 0 31 8 34 13 0\n36 13 0 31 9 34 14 0\n37 14 0 31 10 34 15 0\n38 0 37 36 35 31 34 28 0\n"

end Papers.RationalityTen.MatroidCases.N6R2C5
