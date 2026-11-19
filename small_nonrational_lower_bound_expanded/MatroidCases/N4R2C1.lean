module
public import Papers.RationalityTenLratKernelRefutation

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.MatroidCases.N4R2C1

kernel_lrat_refutation extension
  "p cnf 6 11\n1 0\n2 0\n3 0\n-4 -3 5 6 0\n-5 -2 4 6 0\n-6 -1 4 5 0\n4 5 6 0\n-6 -5 4 0\n-6 -4 5 0\n-5 -4 6 0\n-6 -5 -4 0\n"
  "12 5 4 0 1 7 6 0\n13 4 0 2 12 5 8 0\n14 -6 0 13 11 9 0\n15 -5 0 13 14 10 0\n16 0 13 3 15 14 4 0\n"

end Papers.RationalityTen.MatroidCases.N4R2C1
