module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# A quasi-isomorphism to a single complex is an epimorphism

At the surviving degree, surjectivity follows from the actual
homology map and the canonical cycle and homology maps of the single
complex. Every other target term is zero. No bound on the source is
needed.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower

theorem quasiIso_to_single_epi
    {B : Type*} [Category* B] [Abelian B]
    {ι : Type*} [DecidableEq ι] (shape : ComplexShape ι)
    {K : HomologicalComplex B shape} (M : B) (n : ι)
    (φ : K ⟶ (HomologicalComplex.single B shape n).obj M) [QuasiIso φ] : Epi φ := by
  apply epi_of_epi_f
  intro q
  by_cases same : q = n
  · subst q
    let L := (HomologicalComplex.single B shape n).obj M
    haveI : IsIso (L.homologyπ n) :=
      L.isIso_homologyπ (shape.prev n) n rfl (by simp [L])
    haveI : IsIso (L.iCycles n) :=
      L.isIso_iCycles n (shape.next n) rfl (by simp [L])
    haveI : Epi (cyclesMap φ n ≫ L.homologyπ n) := by
      rw [← homologyπ_naturality]
      infer_instance
    haveI : Epi (cyclesMap φ n) :=
      (epi_comp_iff_of_isIso _ (L.homologyπ n)).mp inferInstance
    exact epi_of_epi_fac (cyclesMap_i φ n).symm
  · exact (isZero_single_obj_X shape n M q same).epi _

end ToricPower
end
