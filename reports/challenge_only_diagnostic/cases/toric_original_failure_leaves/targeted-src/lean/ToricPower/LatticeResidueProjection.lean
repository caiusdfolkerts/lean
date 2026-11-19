module

public import ToricPower.LatticeResidueAction

/-!
# Euclidean residue and quotient of every lattice point

These identities retain negative lattice vectors and arbitrary positive
exponents. They connect the categorical residue action with the literal
translation and scaling used on the universal arrangement.
-/

@[expose] public noncomputable section

namespace ToricPower

variable {κ : Type*} [Fintype κ] (ell : ℕ) (positive : 0 < ell)

def latticeResidueOf (a : κ → ℤ) : LatticeResidues κ ell :=
  ((latticeResidueEquiv ell positive).symm a).1

def latticeQuotientOf (a : κ → ℤ) : κ → ℤ :=
  ((latticeResidueEquiv ell positive).symm a).2

theorem latticeResidueOf_reconstruct (a : κ → ℤ) :
    a = latticeResidueRepresentative (latticeResidueOf ell positive a) +
      (ell : ℤ) • latticeQuotientOf ell positive a :=
  ((latticeResidueEquiv ell positive).apply_symm_apply a).symm

/-- Translating a lattice point gives the actual residue permutation
and the original integral carry, together. -/
theorem latticeResidueOf_add_pair (a b : κ → ℤ) :
    latticeResidueOf ell positive (a + b) =
        latticeResidueTranslate ell positive b (latticeResidueOf ell positive a) ∧
      latticeQuotientOf ell positive (a + b) =
        latticeQuotientOf ell positive a +
          latticeResidueCarry ell positive b (latticeResidueOf ell positive a) := by
  have reconstruction : a + b =
      latticeResidueRepresentative
          (latticeResidueTranslate ell positive b (latticeResidueOf ell positive a)) +
        (ell : ℤ) • (latticeQuotientOf ell positive a +
          latticeResidueCarry ell positive b (latticeResidueOf ell positive a)) := by
    conv_lhs => rw [latticeResidueOf_reconstruct ell positive a]
    have carry := latticeResidueTranslate_carry ell positive b (latticeResidueOf ell positive a)
    rw [smul_add]
    calc
      _ = (latticeResidueRepresentative (latticeResidueOf ell positive a) + b) +
          (ell : ℤ) • latticeQuotientOf ell positive a := by abel
      _ = _ := by rw [carry]; abel
  have h := congrArg (latticeResidueEquiv ell positive).symm reconstruction
  change (latticeResidueEquiv ell positive).symm (a+b) =
    (latticeResidueEquiv ell positive).symm ((latticeResidueEquiv ell positive)
      (latticeResidueTranslate ell positive b (latticeResidueOf ell positive a),
       latticeQuotientOf ell positive a +
         latticeResidueCarry ell positive b (latticeResidueOf ell positive a))) at h
  rw [Equiv.symm_apply_apply] at h
  have first := congrArg (fun p : LatticeResidues κ ell × (κ → ℤ) => p.1) h
  have second := congrArg (fun p : LatticeResidues κ ell × (κ → ℤ) => p.2) h
  exact ⟨first,second⟩

theorem latticeResidueOf_add (a b : κ → ℤ) :
    latticeResidueOf ell positive (a+b) =
      latticeResidueTranslate ell positive b (latticeResidueOf ell positive a) :=
  (latticeResidueOf_add_pair ell positive a b).1

theorem latticeQuotientOf_add (a b : κ → ℤ) :
    latticeQuotientOf ell positive (a+b) = latticeQuotientOf ell positive a +
      latticeResidueCarry ell positive b (latticeResidueOf ell positive a) :=
  (latticeResidueOf_add_pair ell positive a b).2

end ToricPower

end
