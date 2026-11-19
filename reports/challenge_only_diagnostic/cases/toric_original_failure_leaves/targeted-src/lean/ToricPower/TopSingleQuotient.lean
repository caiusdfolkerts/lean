module

public import ToricPower.TopHomologyAugmentation
public import ToricPower.SingleComplexQuasiIso

/-!
# Coordinates of the canonical top quotient

For an actual map to a single complex, its induced homology map and
its original top component agree after the genuine top quotient. This
retains the specified map when passing from an affine augmentation to
the top-homology frame used by the global diagonal construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K : CochainComplex C ℕ} {M : C} {n : ℕ}
  (outgoing : K.d n (n+1) = 0)
  (f : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M)

/-- The quotient-to-homology description preserves the original
component of the specified augmentation. -/
theorem topHomologyQuotient_toSingle :
    K.pOpcycles n ≫ (K.isoHomologyι n (n+1) (by simp) outgoing).inv ≫
        HomologicalComplex.homologyMap f n ≫
          (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) n M).hom =
      f.f n ≫ (HomologicalComplex.singleObjXSelf (.up ℕ) n M).hom := by
  letI : IsIso (K.iCycles n) := K.isIso_iCycles n (n+1) (by simp) outgoing
  apply (cancel_epi (K.iCycles n)).mp
  rw [← HomologicalComplex.homology_π_ι_assoc]
  simp only [Category.assoc, HomologicalComplex.isoHomologyι_hom_inv_id_assoc]
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom,
    HomologicalComplex.cyclesMap_i_assoc]

/-- The concrete frame induced by a quasi-isomorphism has precisely
the original top-component coordinates. -/
theorem homologyIsoOfQuasiIsoToSingle_topQuotient [QuasiIso f] :
    K.pOpcycles n ≫ (K.isoHomologyι n (n+1) (by simp) outgoing).inv ≫
        (homologyIsoOfQuasiIsoToSingle f).hom =
      f.f n ≫ (HomologicalComplex.singleObjXSelf (.up ℕ) n M).hom :=
  topHomologyQuotient_toSingle outgoing f

end ToricPower

end
