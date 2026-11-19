module

public import ToricPower.FiniteHomTotalCoordinates
public import ToricPower.NegativeFunctorTotalCoordinates

/-! # Differential of the full finite-source Hom complex -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CochainComplex HomComplex

namespace ToricPower

universe u v r
variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  (K I : CochainComplex C ℤ) (width : ℕ)

open NegativeFunctorTotal

theorem cochain_single_v_target {p t s : ℤ} (f : K.X p ⟶ I.X t)
    (a : ℤ) (relation : p+a=s) (equal : t=s) :
    (Cochain.single f a).v p s relation = f ≫ eqToHom (congrArg I.X equal) := by
  subst t
  simp only [Cochain.single_v,eqToHom_refl,Category.comp_id]

theorem finiteHomTotalSign_vertical_product (p : ℕ) (a : ℤ) :
    finiteHomTotalSign p (a+1) * finiteHomTotalSign p a = (p : ℤ).negOnePow := by
  rw [← finiteHomTotalSign_vertical p a,← mul_assoc,Int.units_mul_self,one_mul]

theorem finiteHomTotalDifferential_self (a : ℤ) (p : Fin width)
    (f : K.X (chainDegree p : ℤ) ⟶ I.X (a+(chainDegree p : ℤ))) :
    finiteHomTotalProjection R K I width (a+1) p
      (δ a (a+1) (finiteHomTotalInclusion R K I width a p f)) =
        (chainDegree p : ℤ).negOnePow •
          (f ≫ I.d (a+(chainDegree p : ℤ)) (a+1+(chainDegree p : ℤ))) := by
  change finiteHomTotalSign (chainDegree p) (a+1) •
    (δ a (a+1) (finiteHomTotalSign (chainDegree p) a • Cochain.single f a)).v
      (chainDegree p : ℤ) (a+1+(chainDegree p : ℤ)) (by omega) = _
  rw [δ_units_smul,Cochain.units_smul_v,
    δ_v a (a+1) rfl _ _ _ _ (a+(chainDegree p : ℤ)) ((chainDegree p : ℤ)+1)
      (by omega) rfl,Cochain.single_v,
    Cochain.single_v_eq_zero f a _ _ _ (by omega)]
  simp only [comp_zero,smul_zero,add_zero,smul_smul,finiteHomTotalSign_vertical_product]

theorem finiteHomTotalDifferential_next (a : ℤ) (p q : Fin width)
    (next : chainDegree p=chainDegree q+1)
    (f : K.X (chainDegree p : ℤ) ⟶ I.X (a+(chainDegree p : ℤ))) :
    finiteHomTotalProjection R K I width (a+1) q
      (δ a (a+1) (finiteHomTotalInclusion R K I width a p f)) =
        K.d (chainDegree q : ℤ) (chainDegree p : ℤ) ≫ f ≫
          eqToHom (congrArg I.X
            (show a+(chainDegree p : ℤ)=a+1+(chainDegree q : ℤ) by omega)) := by
  change finiteHomTotalSign (chainDegree q) (a+1) •
    (δ a (a+1) (finiteHomTotalSign (chainDegree p) a • Cochain.single f a)).v
      (chainDegree q : ℤ) (a+1+(chainDegree q : ℤ)) (by omega) = _
  rw [δ_units_smul,Cochain.units_smul_v,
    δ_v a (a+1) rfl _ _ _ _ (a+(chainDegree q : ℤ)) (chainDegree p : ℤ)
      (by omega) (by omega),
    Cochain.single_v_eq_zero f a _ _ _ (by omega),zero_comp,zero_add,
    cochain_single_v_target K I f a _ (by omega)]
  simp only [smul_smul]
  have sign :
      finiteHomTotalSign (chainDegree q) (a+1) *
        (finiteHomTotalSign (chainDegree p) a * (a+1).negOnePow) = 1 := by
    rw [next,finiteHomTotalSign_horizontal,Int.units_mul_self]
  simpa only [mul_assoc,one_smul] using congrArg
    (fun c : ℤˣ => c • (K.d (chainDegree q : ℤ) (chainDegree p : ℤ) ≫ f ≫
      eqToHom (congrArg I.X (show a+(chainDegree p : ℤ)=a+1+(chainDegree q : ℤ) by omega)))) sign

theorem finiteHomTotalDifferential_other (a : ℤ) (p q : Fin width)
    (different : p ≠ q) (notNext : ¬ chainDegree p=chainDegree q+1)
    (f : K.X (chainDegree p : ℤ) ⟶ I.X (a+(chainDegree p : ℤ))) :
    finiteHomTotalProjection R K I width (a+1) q
      (δ a (a+1) (finiteHomTotalInclusion R K I width a p f)) = 0 := by
  have unequal : (chainDegree q : ℤ) ≠ (chainDegree p : ℤ) := by
    intro equal
    exact different ((negativeChainDegree_injective width (Int.ofNat_inj.mp equal)).symm)
  change finiteHomTotalSign (chainDegree q) (a+1) •
    (δ a (a+1) (finiteHomTotalSign (chainDegree p) a • Cochain.single f a)).v
      (chainDegree q : ℤ) (a+1+(chainDegree q : ℤ)) (by omega) = _
  rw [δ_units_smul,Cochain.units_smul_v,
    δ_v a (a+1) rfl _ _ _ _ (a+(chainDegree q : ℤ)) ((chainDegree q : ℤ)+1)
      (by omega) rfl,
    Cochain.single_v_eq_zero f a _ _ _ unequal,
    Cochain.single_v_eq_zero f a _ _ _ (by omega)]
  simp only [zero_comp,comp_zero,smul_zero,add_zero]

theorem finiteSourceHomCoefficients_transport (x y : ℤ) (equal : x=y) (q : ℕ)
    (f : K.X (q : ℤ) ⟶ I.X x) :
    (eqToHom (congrArg (fun a : ℤ =>
        ((finiteSourceHomCoefficients R K).obj (I.X a)).X q) equal)) f =
      f ≫ eqToHom (congrArg I.X equal) := by
  subst y
  simp only [eqToHom_refl,ModuleCat.id_apply,Category.comp_id]

theorem finiteSourceHomCoefficients_offEntry (a : ℤ) (p q : Fin width)
    (next : chainDegree p=chainDegree q+1)
    (f : K.X (chainDegree p : ℤ) ⟶ I.X (a+(chainDegree p : ℤ))) :
    offEntry (finiteSourceHomCoefficients R K) I a p q f =
      K.d (chainDegree q : ℤ) (chainDegree p : ℤ) ≫ f ≫
        eqToHom (congrArg I.X
          (show a+(chainDegree p : ℤ)=a+1+(chainDegree q : ℤ) by omega)) := by
  simp only [offEntry,dif_pos next,transportedHorizontal]
  change (eqToHom (congrArg (fun x : ℤ =>
      ((finiteSourceHomCoefficients R K).obj (I.X x)).X (chainDegree q))
        (show a+(chainDegree p : ℤ)=a+1+(chainDegree q : ℤ) by omega)))
      (K.d (chainDegree q : ℤ) (chainDegree p : ℤ) ≫ f) = _
  rw [finiteSourceHomCoefficients_transport R K I _ _ (by omega)]
  exact Category.assoc _ _ _

end ToricPower

end

