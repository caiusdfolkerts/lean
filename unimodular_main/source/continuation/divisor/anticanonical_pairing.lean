module

public import Continuation.Divisor.RecoveredCanonical
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.FanPurity

/-!
# The unit boundary is the tensor inverse of the intrinsic canonical sheaf

The canonical sheaf is the ordinary top exterior power of the universal
Kähler sheaf.  Its identification with coefficient −1 is the recovered
calculation of actual differential transition functions.  Here the
coefficient +1 sheaf is proved to be its tensor inverse by multiplying the
actual fractional local generators.  No canonical-divisor formula is an
assumption of this comparison.
-/

@[expose] public section
noncomputable section

universe u
namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricGeometry
open scoped Classical

section Inverse
variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

/-- Multiplication of a Cartier cocycle by its inverse gives the actual
structure sheaf, including on empty opens. -/
theorem mul_inv_isSection_iff (U : X.Opens) (s : Γ(rationalFunctions X, U)) :
    (C.mul C.inv).IsSection U s ↔
      (RationalCartierCocycle.principal (X := X) 1).IsSection U s := by
  constructor
  · intro hs i x hx
    obtain ⟨j, hj⟩ := C.covers x.val
    have h := hs (j, j) x ⟨hj, hj⟩
    simpa only [RationalCartierCocycle.mul, RationalCartierCocycle.inv,
      RationalCartierCocycle.principal, Units.val_mul, Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ (Units.ne_zero _), Units.val_one] using h
  · intro hs ij x hx
    have hregular : rationalValueAt X U x s ∈ regularAtSubring X x.val := by
      simpa only [RationalCartierCocycle.principal, Units.val_one, div_one] using
        hs PUnit.unit x trivial
    have htransition := C.transition ij.2 ij.1 x.val hx.2 hx.1
    have h := (regularAtSubring X x.val).mul_mem hregular htransition
    simp only [RationalCartierCocycle.mul, RationalCartierCocycle.inv,
      Units.val_mul, Units.val_inv_eq_inv_val]
    change rationalValueAt X U x s /
      ((C.generator ij.1 : X.functionField) * (C.generator ij.2 : X.functionField)⁻¹) ∈
      regularAtSubring X x.val
    convert h using 1 <;> field_simp [Units.ne_zero]
    <;> ring

/-- Tensoring with the inverse fractional sheaf gives the tensor unit. -/
def cocycleTensorInverseIso :
    tensorSheaf C.sheaf C.inv.sheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  C.tensorSheafMulIso C.inv ≪≫
    (C.mul C.inv).sheafIsoOfIsSectionIff
      (RationalCartierCocycle.principal (X := X) 1) (mul_inv_isSection_iff C) ≪≫
    RationalCartierCocycle.principalSheafIsoUnit (X := X) 1
end Inverse

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

lemma cartierLatticePoint_neg (a : Lattice n → ℤ) (s : F.fullCones) :
    F.cartierLatticePoint (-a) s = -F.cartierLatticePoint a s := by
  simp only [PaperVerification.ToricGeometry.SmoothCompleteFan.cartierLatticePoint,
    Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, neg_neg]

lemma rationalCharacter_neg (m : Lattice n) :
    F.rationalCharacter k (-m) = (F.rationalCharacter k m)⁻¹ := by
  simpa only [zero_sub, F.rationalCharacter_zero k, one_div] using
    F.rationalCharacter_sub k 0 m

/-- Negating all support coefficients inverts the ordinary Cartier sheaf. -/
def inverseFanSheafIso (a : Lattice n → ℤ) :
    (F.fanCartierCocycle k F.isPure a).inv.sheaf ≅
      (F.fanCartierData k F.isPure (-a)).sheaf :=
  (F.fanCartierCocycle k F.isPure a).inv.sheafIsoOfIsSectionIff
    (F.fanCartierCocycle k F.isPure (-a)) (by
      intro U s
      simp only [RationalCartierCocycle.IsSection, RationalCartierCocycle.inv,
        PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierCocycle,
        cartierLatticePoint_neg, rationalCharacter_neg, Units.val_inv_eq_inv_val])

/-- The actual canonical sheaf tensored with the unit-boundary sheaf is
trivial. This is the defining tensor-inverse property of the
anticanonical line bundle. -/
def intrinsicCanonical_unitBoundary_tensorIso :
    tensorSheaf (topDifferentialSheaf k (F.fanScheme k) n)
      (F.fanCartierData k F.isPure (fun _ => (1 : ℤ))).sheaf ≅
        SheafOfModules.unit (F.fanScheme k).ringCatSheaf := by
  let C := F.fanCartierCocycle k F.isPure (fun _ => (-1 : ℤ))
  let e : C.inv.sheaf ≅
      (F.fanCartierData k F.isPure (fun _ => (1 : ℤ))).sheaf := by
    have heq : -(fun _ : Lattice n => (-1 : ℤ)) = (fun _ => (1 : ℤ)) := by
      funext u; simp
    simpa only [C, heq] using inverseFanSheafIso F k (fun _ => (-1 : ℤ))
  exact tensorSheafIso
      (F.intrinsicCanonicalFanIso k F.isPure (Pi.basisFun ℤ (Fin n))) e.symm ≪≫
    cocycleTensorInverseIso C

#print axioms intrinsicCanonical_unitBoundary_tensorIso

end Unimodular.NefBig
