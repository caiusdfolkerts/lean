module

public import ToricPower.DivisorWeightAlgebra

/-!
# The full lattice action on power residues, with integral carries

All identities are consequences of the proved Euclidean-division
equivalence of the entire lattice. Negative translations and arbitrary
positive exponents are included.
-/

@[expose] public noncomputable section

namespace ToricPower

variable {κ : Type*} [Fintype κ] (ell : ℕ) (positive : 0 < ell)

def latticeResidueTranslate (a : κ → ℤ) (r : LatticeResidues κ ell) : LatticeResidues κ ell :=
  ((latticeResidueEquiv ell positive).symm (latticeResidueRepresentative r + a)).1

def latticeResidueCarry (a : κ → ℤ) (r : LatticeResidues κ ell) : κ → ℤ :=
  ((latticeResidueEquiv ell positive).symm (latticeResidueRepresentative r + a)).2

/-- The literal residue and carry reconstruct the translated lattice point. -/
theorem latticeResidueTranslate_carry (a : κ → ℤ) (r : LatticeResidues κ ell) :
    latticeResidueRepresentative r + a =
      latticeResidueRepresentative (latticeResidueTranslate ell positive a r) +
        (ell : ℤ) • latticeResidueCarry ell positive a r :=
  ((latticeResidueEquiv ell positive).apply_symm_apply _).symm

theorem latticeResidueTranslate_of_carry (a : κ → ℤ) (r t : LatticeResidues κ ell)
    (b : κ → ℤ)
    (h : latticeResidueRepresentative r + a = latticeResidueRepresentative t + (ell : ℤ) • b) :
    latticeResidueTranslate ell positive a r = t ∧ latticeResidueCarry ell positive a r = b := by
  have equality := congrArg (latticeResidueEquiv ell positive).symm h
  change (latticeResidueEquiv ell positive).symm (latticeResidueRepresentative r + a) =
    (latticeResidueEquiv ell positive).symm ((latticeResidueEquiv ell positive) (t,b)) at equality
  rw [Equiv.symm_apply_apply] at equality
  exact ⟨congrArg Prod.fst equality, congrArg Prod.snd equality⟩

@[simp] theorem latticeResidueTranslate_zero (r : LatticeResidues κ ell) :
    latticeResidueTranslate ell positive 0 r = r :=
  (latticeResidueTranslate_of_carry ell positive 0 r r 0 (by simp)).1

@[simp] theorem latticeResidueCarry_zero (r : LatticeResidues κ ell) :
    latticeResidueCarry ell positive 0 r = 0 :=
  (latticeResidueTranslate_of_carry ell positive 0 r r 0 (by simp)).2

theorem latticeResidueTranslate_add_pair (a b : κ → ℤ) (r : LatticeResidues κ ell) :
    latticeResidueTranslate ell positive (a+b) r =
      latticeResidueTranslate ell positive b (latticeResidueTranslate ell positive a r) ∧
    latticeResidueCarry ell positive (a+b) r = latticeResidueCarry ell positive a r +
      latticeResidueCarry ell positive b (latticeResidueTranslate ell positive a r) := by
  apply latticeResidueTranslate_of_carry
  have first := latticeResidueTranslate_carry ell positive a r
  have second := latticeResidueTranslate_carry ell positive b
    (latticeResidueTranslate ell positive a r)
  rw [smul_add]
  calc
    latticeResidueRepresentative r + (a+b) =
        (latticeResidueRepresentative r + a) + b := (add_assoc _ _ _).symm
    _ = (latticeResidueRepresentative (latticeResidueTranslate ell positive a r) + b) +
        (ell : ℤ) • latticeResidueCarry ell positive a r := by rw [first]; abel
    _ = _ := by rw [second]; abel

theorem latticeResidueTranslate_add (a b : κ → ℤ) (r : LatticeResidues κ ell) :
    latticeResidueTranslate ell positive (a+b) r =
      latticeResidueTranslate ell positive b (latticeResidueTranslate ell positive a r) :=
  (latticeResidueTranslate_add_pair ell positive a b r).1

theorem latticeResidueCarry_add (a b : κ → ℤ) (r : LatticeResidues κ ell) :
    latticeResidueCarry ell positive (a+b) r = latticeResidueCarry ell positive a r +
      latticeResidueCarry ell positive b (latticeResidueTranslate ell positive a r) :=
  (latticeResidueTranslate_add_pair ell positive a b r).2

/-- Every lattice translation is a permutation of the complete residue set. -/
def latticeResidueTranslateEquiv (a : κ → ℤ) : LatticeResidues κ ell ≃ LatticeResidues κ ell where
  toFun := latticeResidueTranslate ell positive a
  invFun := latticeResidueTranslate ell positive (-a)
  left_inv r := by rw [← latticeResidueTranslate_add, add_neg_cancel, latticeResidueTranslate_zero]
  right_inv r := by rw [← latticeResidueTranslate_add, neg_add_cancel, latticeResidueTranslate_zero]

end ToricPower

end
