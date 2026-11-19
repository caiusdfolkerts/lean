module
public import Papers.GPFiniteGeometryData

@[expose] public section
noncomputable section
namespace Papers.RationalityTen.GPFiniteGeometry.Literal.PrismNine
open Papers.RationalityTen.PureGP
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
/- Generated finite source. -/

def permutation00 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation01 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 4, 3]
  invFun := ![0, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation02 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 4, 2]
  invFun := ![0, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation03 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 4, 1]
  invFun := ![0, 4, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation04 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 3, 4, 0]
  invFun := ![4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

end Papers.RationalityTen.GPFiniteGeometry.Literal.PrismNine
