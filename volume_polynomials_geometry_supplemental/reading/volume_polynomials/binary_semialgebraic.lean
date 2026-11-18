module

public import VolumePolynomials.BinaryCoordinates
public import VolumePolynomials.BinaryRealizationCriterion
public import VolumePolynomials.OneBody
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! The complete semialgebraic side of Theorem 1.1, in the actual homogeneous
coefficient space. The binary set is given by the finite quadratic
inequalities of Appendix A, with its normalization justified explicitly. -/

open Set MvPolynomial

namespace VolumePolynomials

def binaryCoordinatePolynomial (d : ℕ) (i : Fin (d + 1)) :
    MvPolynomial (MultiIndex 2 d) ℝ :=
  C (1 / (d.choose i.val : ℝ)) * X (binaryIndex d i)

theorem eval_binaryCoordinatePolynomial {d : ℕ} (c : Coefficients 2 d)
    (i : Fin (d + 1)) :
    MvPolynomial.eval c (binaryCoordinatePolynomial d i) = binaryNormalizedSequence c i.val := by
  first
  | rw [binaryNormalizedSequence_apply]
    simp only [binaryCoordinatePolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    ring

abbrev BinaryAdmissiblePair (d : ℕ) :=
  {p : Fin (d + 1) × Fin (d + 1) // 1 ≤ p.1.val ∧ p.1.val ≤ p.2.val ∧ p.2.val < d}

def binaryLeftPolynomial (d : ℕ) (p : BinaryAdmissiblePair d) :
    MvPolynomial (MultiIndex 2 d) ℝ :=
  binaryCoordinatePolynomial d ⟨p.1.1.val - 1, by have h := p.1.1.isLt; omega⟩ *
    binaryCoordinatePolynomial d ⟨p.1.2.val + 1, by have h := p.2.2.2; omega⟩

def binaryRightPolynomial (d : ℕ) (p : BinaryAdmissiblePair d) :
    MvPolynomial (MultiIndex 2 d) ℝ :=
  binaryCoordinatePolynomial d p.1.1 * binaryCoordinatePolynomial d p.1.2

theorem binaryCriterion_set_eq (d : ℕ) :
    {c : Coefficients 2 d | BinarySequences.Criterion d (binaryNormalizedSequence c)} =
      (⋂ i : Fin (d + 1), {c | 0 ≤ MvPolynomial.eval c (binaryCoordinatePolynomial d i)}) ∩
      (⋂ p : BinaryAdmissiblePair d,
        {c | MvPolynomial.eval c (binaryLeftPolynomial d p) ≤
          MvPolynomial.eval c (binaryRightPolynomial d p)}) := by
  first
  | ext c
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      eval_binaryCoordinatePolynomial, binaryLeftPolynomial, binaryRightPolynomial,
      MvPolynomial.eval_mul]
    constructor
    · intro h
      refine ⟨fun i => h.1 i.val (Nat.le_of_lt_succ i.isLt), ?_⟩
      intro p
      simpa only [eval_binaryCoordinatePolynomial] using
        h.2 p.1.1.val p.1.2.val p.2.1 p.2.2.1 p.2.2.2
    · rintro ⟨hn, hp⟩
      constructor
      · intro i hid
        exact hn ⟨i, Nat.lt_succ_of_le hid⟩
      · intro i j hi hij hjd
        let p : BinaryAdmissiblePair d :=
          ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), hi, hij, hjd⟩
        simpa only [p, eval_binaryCoordinatePolynomial] using hp p

theorem isSemialgebraic_binaryCriterion (d : ℕ) :
    TauCeti.IsSemialgebraic
      {c : Coefficients 2 d | BinarySequences.Criterion d (binaryNormalizedSequence c)} := by
  first
  | rw [binaryCriterion_set_eq]
    apply TauCeti.IsSemialgebraic.inter
    · exact TauCeti.IsSemialgebraic.iInter (fun i =>
        TauCeti.isSemialgebraic_eval_nonneg (binaryCoordinatePolynomial d i))
    · exact TauCeti.IsSemialgebraic.iInter (fun p =>
        TauCeti.isSemialgebraic_eval_le (binaryLeftPolynomial d p) (binaryRightPolynomial d p))

theorem twoBody_realizable_iff {d : ℕ} (hd : 0 < d) (c : Coefficients 2 d) :
    c ∈ VolumeLocus 2 d ↔ BinarySequences.Criterion d (binaryNormalizedSequence c) := by
  first
  | rw [binary_volumeLocus_iff, BinarySimplex.appendix_A_realization_iff hd]

theorem isSemialgebraic_twoBody {d : ℕ} (hd : 0 < d) :
    TauCeti.IsSemialgebraic (VolumeLocus 2 d) := by
  first
  | have heq : VolumeLocus 2 d =
        {c | BinarySequences.Criterion d (binaryNormalizedSequence c)} := by
      first
      | ext c
        exact twoBody_realizable_iff hd c
    rw [heq]
    exact isSemialgebraic_binaryCriterion d

theorem isSemialgebraic_oneBody {d : ℕ} (hd : 0 < d) :
    TauCeti.IsSemialgebraic (VolumeLocus 1 d) := by
  first
  | have heq : VolumeLocus 1 d = {c | 0 ≤ c (oneIndex d)} := by
      first
      | ext c
        exact oneBody_realizable_iff hd c
    rw [heq]
    simpa only [MvPolynomial.eval_X] using
      TauCeti.isSemialgebraic_eval_nonneg (MvPolynomial.X (oneIndex d) : MvPolynomial (MultiIndex 1 d) ℝ)

theorem isSemialgebraic_volumeLocus_of_le_two {n d : ℕ}
    (hn : 1 ≤ n) (hd : 0 < d) (hn2 : n ≤ 2) :
    TauCeti.IsSemialgebraic (VolumeLocus n d) := by
  first
  | have h : n = 1 ∨ n = 2 := by omega
    rcases h with rfl | rfl
    · exact isSemialgebraic_oneBody hd
    · exact isSemialgebraic_twoBody hd

end VolumePolynomials
