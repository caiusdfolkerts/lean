module

public import PaperVerification.AlternatingFormsDuality
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import TauCeti.Algebra.Module.GradedModule.Shift
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Fintype.Powerset
import Lean.Elab.Tactic.Omega

/-!
# The actual integer grading of the exterior algebra

Natural exterior degrees are extended by zero in negative degrees.  The
internal direct-sum assertion is proved, so subsequent shifted Koszul
gradings are genuine gradings of the original modules.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms

section IntegerExtension

variable {K A : Type*} [Field K] [AddCommGroup A] [Module K A]

def nonnegativePiece (G : TauCeti.InternalGrading K A ℕ) (q : ℤ) : Submodule K A :=
  if 0 ≤ q then G.piece q.toNat else ⊥

@[simp] theorem nonnegativePiece_nat (G : TauCeti.InternalGrading K A ℕ) (q : ℕ) :
    nonnegativePiece G (q : ℤ) = G.piece q := by
  simp only [nonnegativePiece, Nat.cast_nonneg, if_pos, Int.toNat_natCast]

theorem nonnegativePiece_negative (G : TauCeti.InternalGrading K A ℕ)
    {q : ℤ} (hq : q < 0) : nonnegativePiece G q = ⊥ := by
  simp only [nonnegativePiece, if_neg (not_le_of_gt hq)]

/-- Extension by zero from natural to integer indices, with the direct-sum
property justified from the original homogeneous decomposition. -/
noncomputable def integerExtension (G : TauCeti.InternalGrading K A ℕ) :
    TauCeti.InternalGrading K A where
  piece := nonnegativePiece G
  isInternal := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · intro q
      by_cases hq : 0 ≤ q
      · rw [nonnegativePiece, if_pos hq]
        apply (G.isInternal.submodule_iSupIndep q.toNat).mono_right
        apply iSup_le
        intro r
        apply iSup_le
        intro hrq
        by_cases hr : 0 ≤ r
        · rw [nonnegativePiece, if_pos hr]
          exact le_iSup_of_le r.toNat (le_iSup_of_le (by omega : r.toNat ≠ q.toNat) le_rfl)
        · rw [nonnegativePiece, if_neg hr]
          exact bot_le
      · rw [nonnegativePiece, if_neg hq]
        exact disjoint_bot_left
    · apply top_unique
      rw [← G.isInternal.submodule_iSup_eq_top]
      exact iSup_le fun q => le_iSup_of_le (q : ℤ) (by rw [nonnegativePiece_nat])

@[simp] theorem integerExtension_piece (G : TauCeti.InternalGrading K A ℕ) (q : ℤ) :
    (integerExtension G).piece q = nonnegativePiece G q := rfl

/-- Finite-dimensional graded modules have genuine Laurent-polynomial Hilbert
series.  Finiteness of the support follows from the internal grading. -/
noncomputable def finiteHilbertLaurent (G : TauCeti.InternalGrading K A)
    [FiniteDimensional K A] : LaurentPolynomial ℤ :=
  AddMonoidAlgebra.ofCoeff <| Finsupp.ofSupportFinite
    (fun q => (Module.finrank K (G.piece q) : ℤ))
    (G.finite_piece_ne_bot.subset (by
      intro q hq
      change (Module.finrank K (G.piece q) : ℤ) ≠ 0 at hq
      intro hbot
      rw [hbot, finrank_bot, Nat.cast_zero] at hq
      exact hq rfl))

@[simp] theorem finiteHilbertLaurent_coeff (G : TauCeti.InternalGrading K A)
    [FiniteDimensional K A] (q : ℤ) :
    (finiteHilbertLaurent G).coeff q = (Module.finrank K (G.piece q) : ℤ) := rfl

end IntegerExtension

section ExteriorIntegerGrading

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The whole exterior algebra has a finite basis, indexed by the subsets
of a finite basis of the original vector space. -/
instance exteriorAlgebra_finite [FiniteDimensional K M] :
    FiniteDimensional K (ExteriorAlgebra K M) :=
  Module.Finite.of_basis (Module.finBasis K M).ExteriorAlgebra

noncomputable def exteriorNaturalGrading :
    TauCeti.InternalGrading K (ExteriorAlgebra K M) ℕ :=
  .ofDecomposition (fun q : ℕ => ⋀[K]^q M)

noncomputable def exteriorIntegerGrading : TauCeti.InternalGrading K (ExteriorAlgebra K M) :=
  integerExtension (exteriorNaturalGrading (K := K) (M := M))

@[simp] theorem exteriorIntegerGrading_piece_nat (q : ℕ) :
    (exteriorIntegerGrading (K := K) (M := M)).piece (q : ℤ) = ⋀[K]^q M := by
  simp only [exteriorIntegerGrading, integerExtension_piece, nonnegativePiece_nat,
    exteriorNaturalGrading, TauCeti.InternalGrading.ofDecomposition_piece]

theorem exteriorIntegerGrading_piece_negative {q : ℤ} (hq : q < 0) :
    (exteriorIntegerGrading (K := K) (M := M)).piece q = ⊥ :=
  nonnegativePiece_negative _ hq

theorem exteriorIntegerGrading_piece_of_nonneg {q : ℤ} (hq : 0 ≤ q) :
    (exteriorIntegerGrading (K := K) (M := M)).piece q = ⋀[K]^q.toNat M := by
  simp only [exteriorIntegerGrading, integerExtension_piece, nonnegativePiece, if_pos hq,
    exteriorNaturalGrading, TauCeti.InternalGrading.ofDecomposition_piece]

def twoFormMultiplication (f : ⋀[K]^2 M) : Module.End K (ExteriorAlgebra K M) :=
  LinearMap.mulLeft K (f : ExteriorAlgebra K M)

theorem twoFormMultiplication_homogeneous (f : ⋀[K]^2 M) :
    TauCeti.LinearMap.IsHomogeneous (twoFormMultiplication f)
      exteriorIntegerGrading.piece exteriorIntegerGrading.piece 2 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q a ha
  by_cases hq : 0 ≤ q
  · rw [exteriorIntegerGrading_piece_of_nonneg hq] at ha
    rw [exteriorIntegerGrading_piece_of_nonneg (by omega : 0 ≤ q + 2)]
    have hd : (q + 2).toNat = 2 + q.toNat := by omega
    rw [hd]
    exact SetLike.mul_mem_graded f.property ha
  · rw [exteriorIntegerGrading_piece_negative (by omega : q < 0)] at ha
    have ha0 : a = 0 := ha
    rw [ha0, map_zero]
    exact Submodule.zero_mem _

theorem twoFormMultiplication_commute (f g : ⋀[K]^2 M) :
    Commute (twoFormMultiplication f) (twoFormMultiplication g) := by
  change twoFormMultiplication f * twoFormMultiplication g=
    twoFormMultiplication g * twoFormMultiplication f
  apply LinearMap.ext
  intro a
  change (f : ExteriorAlgebra K M) * (g * a) = (g : ExteriorAlgebra K M) * (f * a)
  rw [← mul_assoc, (twoForm_commute f g).eq, mul_assoc]

variable [FiniteDimensional K M]

theorem exteriorIntegerGrading_piece_above {q : ℤ}
    (hq : (Module.finrank K M : ℤ) < q) :
    (exteriorIntegerGrading (K := K) (M := M)).piece q = ⊥ := by
  rw [exteriorIntegerGrading_piece_of_nonneg (by omega : 0 ≤ q)]
  apply Submodule.finrank_eq_zero.mp
  rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt (by omega)]

theorem exteriorIntegerGrading_finrank (q : ℤ) :
    Module.finrank K ((exteriorIntegerGrading (K := K) (M := M)).piece q) =
      if 0 ≤ q then (Module.finrank K M).choose q.toNat else 0 := by
  by_cases hq : 0 ≤ q
  · rw [if_pos hq, exteriorIntegerGrading_piece_of_nonneg hq, exteriorPower.finrank_eq]
  · rw [if_neg hq, exteriorIntegerGrading_piece_negative (by omega : q < 0), finrank_bot]

end ExteriorIntegerGrading

end PaperVerification.AlternatingForms
