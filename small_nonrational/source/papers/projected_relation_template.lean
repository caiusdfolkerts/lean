module
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-! The label-only relation template, shared by finite certificates and geometry. -/

namespace Papers.RationalityTen.ChirotopeDensity

structure ProjectedRelationTemplate (n : ℕ) where
  frameSize : ℕ
  frame : Fin frameSize → Fin n
  vertex : Fin n
  deriving DecidableEq

end Papers.RationalityTen.ChirotopeDensity
