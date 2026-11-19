module

public import ToricPower.ArrangementPowerCells
public import ToricPower.LatticeResidueAction
public import Mathlib.CategoryTheory.Elements

/-!
# The actual finite covering incidence category of a positive power

Each base cell has one object for every character residue. Its incidence
maps permute those residues by the actual lattice translation. The
inverse-branch functor records the integral carry as its actual target
incidence, including repeated endpoints and cells lying on walls.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (ell : ℕ) (positive : 0 < ell)

include positive

/-- The actual residue permutation on every quotient-cell incidence. -/
def powerResidueFunctor : IncidenceObject A ⥤ Type where
  obj _ := LatticeResidues (Fin n) ell
  map f := ↾(latticeResidueTranslate ell positive f.val)
  map_id c := by
    apply ConcreteCategory.hom_ext
    intro r
    exact latticeResidueTranslate_zero ell positive r
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro r
    exact latticeResidueTranslate_add ell positive f.val g.val r

/-- No residue sheets are omitted. -/
abbrev PowerIncidenceObject := (powerResidueFunctor A ell positive).Elements

theorem powerInverseBranchPoint_carry (u v a t : Fin n → ℤ)
    (carry : u + a = v + (ell : ℤ) • t) (x : Fin n → ℝ) :
    powerInverseBranchPoint ell (-v) (x + latticeLift a) =
      powerInverseBranchPoint ell (-u) x + latticeLift t := by
  funext j
  have equality := congrFun carry j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at equality
  have realEquality : (u j : ℝ) + a j = v j + (ell : ℝ) * t j := by
    exact_mod_cast equality
  have nonzero : (ell : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  change (ell : ℝ)⁻¹ * (x j + (a j : ℝ) + ((-v) j : ℝ)) =
    (ell : ℝ)⁻¹ * (x j + ((-u) j : ℝ)) + (t j : ℝ)
  simp only [Pi.neg_apply, Int.cast_neg]
  field_simp
  nlinarith

/-- The actual branch-cell incidence forced by a literal carry equation. -/
def normalizedPowerBranchHom {c d : IncidenceObject A} (f : c ⟶ d)
    (r t : LatticeResidues (Fin n) ell) (a : Fin n → ℤ)
    (carry : latticeResidueRepresentative r + f.val =
      latticeResidueRepresentative t + (ell : ℤ) • a) :
    normalizedPowerBranch A ell positive r c ⟶ normalizedPowerBranch A ell positive t d := by
  let p := cellCenter (augmentedForms A) c.2.val
  let q := powerInverseBranchPoint ell (-latticeResidueRepresentative r) p
  have targetOriginal : p + latticeLift f.val ∈ incidenceClosedCell A d :=
    f.property p (cell_subset_closedCell _ _ _ (cellCenter_mem _ c.2.val))
  have target := powerInverseBranchCell_closed A ell positive
    (-latticeResidueRepresentative t) ⟨d.1,d.2.val⟩ targetOriginal
  rw [powerInverseBranchPoint_carry ell positive _ _ _ _ carry] at target
  have shifted : q + latticeLift a ∈ cell (augmentedForms A)
      ((normalizedPowerBranch A ell positive r c).2.val.val.1 + augmentedLatticePairing A a)
      (normalizedPowerBranch A ell positive r c).2.val.val.2 :=
    (add_mem_cell_iff _ _ _ _ _ (augmentedForms_latticeLift A a) q).mpr
      (mem_cell_self _ q)
  have containing := closedCell_of_point_subset (augmentedForms A) _ _ target
  have ceilings : ceilingVector (augmentedForms A) (q + latticeLift a) =
      (normalizedPowerBranch A ell positive r c).2.val.val.1 + augmentedLatticePairing A a :=
    funext (fun j => ceil_eq_of_mem_cell _ _ _ shifted j)
  have active := integralIndices_eq_of_mem_cell _ _ _ shifted
  change closedCell (augmentedForms A)
      (ceilingVector (augmentedForms A) (q+latticeLift a))
      (integralIndices (augmentedForms A) (q+latticeLift a)) ⊆
    incidenceClosedCell A (normalizedPowerBranch A ell positive t d) at containing
  rw [ceilings, active] at containing
  refine ⟨a, fun x hx => containing ?_⟩
  exact (add_mem_closedCell_iff _ _ _ _ _ (augmentedForms_latticeLift A a) x).mpr hx

/-- The true inverse-branch functor from the finite covering category. -/
def powerBranchFunctor : PowerIncidenceObject A ell positive ⥤ IncidenceObject A where
  obj c := normalizedPowerBranch A ell positive c.val c.obj
  map {c d} f := normalizedPowerBranchHom A ell positive f.hom c.val d.val
    (latticeResidueCarry ell positive f.hom.val c.val) (by
      have h := latticeResidueTranslate_carry ell positive f.hom.val c.val
      have residue : latticeResidueTranslate ell positive f.hom.val c.val = d.val := f.map_val
      rwa [residue] at h)
  map_id c := by
    apply Subtype.ext
    exact latticeResidueCarry_zero ell positive c.val
  map_comp {c d e} f g := by
    apply Subtype.ext
    change latticeResidueCarry ell positive (f.hom.val+g.hom.val) c.val =
      latticeResidueCarry ell positive f.hom.val c.val +
        latticeResidueCarry ell positive g.hom.val d.val
    have carry := latticeResidueCarry_add ell positive f.hom.val g.hom.val c.val
    have residue : latticeResidueTranslate ell positive f.hom.val c.val = d.val := f.map_val
    simpa only [residue] using carry

end ToricPower.IntegralArrangement

end
