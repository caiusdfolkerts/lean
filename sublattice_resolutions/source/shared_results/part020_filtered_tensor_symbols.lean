module
public import graph_foundation.part014
public import shared_results.part019

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FilteredTensorSymbols -/
section

/-! # gr(K(A)) is the literal tensor Koszul algebra of gr(A)

The mutually inverse maps take each exterior coordinate to its actual
coefficient symbol, with the exterior weight subtracted. Their inverses
are constructed on the actual successive quotients of the coefficient
filtration. Multiplication is checked on the exterior monomials and actual
coefficient symbols. This is an algebra equivalence, not a comparison
postulated as part of the filtration data.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.FilteredTensorKoszul

open Classical CommAlg TensorExteriorKoszul IntegerFiltered
open scoped TensorProduct BigOperators

universe u
variable {K A V : Type u} [CommRing K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V]
  (F : MultiplicativeFiltration K A) (w : V → ℤ)

local notation "T" => filtration F w
local notation "B" => F.AssociatedGraded
local notation "TB" => B ⊗[K] Simplicial.Ambient V K

def levelCoefficient (n : ℤ) (s : Finset V) : (T).level n →ₗ[K] F.level (n-faceWeight w s) :=
  ((coefficient s).domRestrict ((T).level n)).codRestrict _
    (fun x => (mem_level F w n x.val).mp x.property s)

def tensorAt (s : Finset V) : B →ₗ[K] TB :=
  (TensorProduct.mk K B (Simplicial.Ambient V K)).flip (Simplicial.basis s)

def levelSymbol (n : ℤ) : (T).level n →ₗ[K] TB :=
  ∑ s : Finset V, (tensorAt F s).comp
    ((F.symbol (n-faceWeight w s)).comp (levelCoefficient F w n s))

theorem levelSymbol_apply (n : ℤ) (a : (T).level n) :
    levelSymbol F w n a = ∑ s : Finset V,
      F.symbol (n-faceWeight w s) (levelCoefficient F w n s a) ⊗ₜ[K] Simplicial.basis s := by
  simp only [levelSymbol,LinearMap.sum_apply,LinearMap.comp_apply,tensorAt,
    LinearMap.flip_apply,TensorProduct.mk_apply]

theorem levelSymbol_lower (n : ℤ) : (T).lower n ≤ LinearMap.ker (levelSymbol F w n) := by
  intro a ha
  rw [LinearMap.mem_ker,levelSymbol_apply]
  apply Finset.sum_eq_zero
  intro s _
  have hzero : F.symbol (n-faceWeight w s) (levelCoefficient F w n s a)=0 := by
    rw [F.symbol_eq_zero]
    have h := (mem_level F w (n-1) a.val).mp ha s
    have he : n-1-faceWeight w s=n-faceWeight w s-1 := by omega
    simpa only [levelCoefficient,LinearMap.codRestrict_apply,LinearMap.domRestrict_apply,he] using h
  rw [hzero,TensorProduct.zero_tmul]

def gradeSymbol (n : ℤ) : (T).Grade n →ₗ[K] TB :=
  ((T).lower n).liftQ (levelSymbol F w n) (levelSymbol_lower F w n)

def associatedLinear : (T).AssociatedGraded →ₗ[K] TB :=
  (DirectSum.toModule K ℤ TB (gradeSymbol F w)).comp (T).associatedGradedEquiv.toLinearMap

@[simp] theorem associatedLinear_symbol (n : ℤ) (a : (T).level n) :
    associatedLinear F w ((T).symbol n a)=levelSymbol F w n a := by
  simp only [associatedLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,
    MultiplicativeFiltration.associatedGradedEquiv_symbol]
  change (DirectSum.toModule K ℤ TB (gradeSymbol F w))
    (DirectSum.lof K ℤ (fun n => (T).Grade n) n (Submodule.Quotient.mk a)) = _
  rw [DirectSum.toModule_lof]
  rfl

def insertLevel (n : ℤ) (s : Finset V) : F.level n →ₗ[K] (T).level (n+faceWeight w s) where
  toFun a := ⟨a.val ⊗ₜ[K] Simplicial.basis s,tmul_basis_mem F w _ s a.val
    (by simpa only [add_sub_cancel_right] using a.property)⟩
  map_add' a b := Subtype.ext (TensorProduct.add_tmul _ _ _)
  map_smul' c a := Subtype.ext (TensorProduct.smul_tmul' _ _ _)

def atom (n : ℤ) (s : Finset V) : F.level n →ₗ[K] (T).AssociatedGraded :=
  ((T).symbol (n+faceWeight w s)).comp (insertLevel F w n s)

theorem atom_congr (i j : ℤ) (hij : i=j) (s : Finset V)
    (a : F.level i) (b : F.level j) (hab : a.val=b.val) :
    atom F w i s a=atom F w j s b := by
  subst j
  exact congrArg (atom F w i s) (Subtype.ext hab)

theorem atom_lower (n : ℤ) (s : Finset V) : F.lower n ≤ LinearMap.ker (atom F w n s) := by
  intro a ha
  rw [LinearMap.mem_ker]
  change (T).symbol (n+faceWeight w s) (insertLevel F w n s a)=0
  rw [(T).symbol_eq_zero]
  apply tmul_basis_mem
  have he : n+faceWeight w s-1-faceWeight w s=n-1 := by omega
  change a.val ∈ F.level (n-1) at ha
  simpa only [he] using ha

def insertGrade (s : Finset V) (n : ℤ) : F.Grade n →ₗ[K] (T).AssociatedGraded :=
  (F.lower n).liftQ (atom F w n s) (atom_lower F w n s)

def insertSymbol (s : Finset V) : B →ₗ[K] (T).AssociatedGraded :=
  (DirectSum.toModule K ℤ (T).AssociatedGraded (insertGrade F w s)).comp
    F.associatedGradedEquiv.toLinearMap

@[simp] theorem insertSymbol_symbol (s : Finset V) (n : ℤ) (a : F.level n) :
    insertSymbol F w s (F.symbol n a)=atom F w n s a := by
  simp only [insertSymbol,LinearMap.comp_apply,LinearEquiv.coe_coe,
    MultiplicativeFiltration.associatedGradedEquiv_symbol]
  change (DirectSum.toModule K ℤ (T).AssociatedGraded (insertGrade F w s))
    (DirectSum.lof K ℤ (fun n => F.Grade n) n (Submodule.Quotient.mk a)) = _
  rw [DirectSum.toModule_lof]
  rfl

def associatedInverse : TB →ₗ[K] (T).AssociatedGraded :=
  (Finsupp.lsum K (insertSymbol F w)).comp TensorExteriorKoszul.coordinates.toLinearMap

@[simp] theorem associatedInverse_tmul_basis (s : Finset V) (a : B) :
    associatedInverse F w (a ⊗ₜ[K] Simplicial.basis s)=insertSymbol F w s a := by
  simp only [associatedInverse,LinearMap.comp_apply,LinearEquiv.coe_coe,
    coordinates_tmul_basis,Finsupp.lsum_single]

theorem associatedLinear_atom (n : ℤ) (s : Finset V) (a : F.level n) :
    associatedLinear F w (atom F w n s a)=F.symbol n a ⊗ₜ[K] Simplicial.basis s := by
  rw [atom,LinearMap.comp_apply,associatedLinear_symbol,levelSymbol_apply]
  rw [Finset.sum_eq_single s]
  · congr 1
    apply F.symbol_congr _ _ (add_sub_cancel_right _ _) _ a
    exact coefficient_tmul_basis s s a.val |>.trans (if_pos rfl)
  · intro t _ hts
    have hz : levelCoefficient F w (n+faceWeight w s) t (insertLevel F w n s a)=0 := by
      apply Subtype.ext
      change coefficient t (a.val ⊗ₜ[K] Simplicial.basis s)=0
      simp only [coefficient_tmul_basis,if_neg (Ne.symm hts)]
    rw [hz,map_zero,TensorProduct.zero_tmul]
  · intro h
    exact (h (Finset.mem_univ s)).elim

theorem symbol_exterior_decomposition (n : ℤ) (a : (T).level n) :
    (T).symbol n a=∑ s : Finset V,
      atom F w (n-faceWeight w s) s (levelCoefficient F w n s a) := by
  let t (s : Finset V) : (T).level n :=
    ⟨coefficient s a.val ⊗ₜ[K] Simplicial.basis s,tmul_basis_mem F w n s _
      ((mem_level F w n a.val).mp a.property s)⟩
  have hs : ∑ s : Finset V,t s=a := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, t] using sum_coefficients (K:=K) (A:=A) (V:=V) a.val
  calc
    (T).symbol n a=(T).symbol n (∑ s : Finset V,t s) := congrArg ((T).symbol n) hs.symm
    _ = ∑ s : Finset V,(T).symbol n (t s) := map_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      apply (T).symbol_congr n ((n-faceWeight w s)+faceWeight w s) (by omega)
      rfl

@[elab_as_elim] theorem associated_tensor_induction (P : (T).AssociatedGraded → Prop)
    (h0 : P 0) (hadd : ∀ a b,P a→P b→P (a+b))
    (hatom : ∀ n s a,P (atom F w n s a)) (x : (T).AssociatedGraded) : P x := by
  apply (T).associated_induction P h0 hadd _ x
  intro n a
  rw [symbol_exterior_decomposition F w n a]
  apply Finset.sum_induction
  · exact fun a b ha hb => hadd a b ha hb
  · exact h0
  · intro s _
    exact hatom _ s _

theorem associatedInverse_left (x : (T).AssociatedGraded) :
    associatedInverse F w (associatedLinear F w x)=x := by
  apply associated_tensor_induction F w (fun x => associatedInverse F w (associatedLinear F w x)=x)
    (by simp only [map_zero]) (fun a b ha hb => by simp only [map_add,ha,hb]) _ x
  intro n s a
  rw [associatedLinear_atom,associatedInverse_tmul_basis,insertSymbol_symbol]

theorem associatedInverse_right (x : TB) :
    associatedLinear F w (associatedInverse F w x)=x := by
  rw [← sum_coefficients (K:=K) (A:=F.AssociatedGraded) (V:=V) x,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [associatedInverse_tmul_basis]
  apply F.associated_induction
    (fun a => associatedLinear F w (insertSymbol F w s a)=a ⊗ₜ[K] Simplicial.basis s)
    (by simp only [map_zero,TensorProduct.zero_tmul])
    (fun a b ha hb => by simp only [map_add,ha,hb,TensorProduct.add_tmul])
  intro n a
  rw [insertSymbol_symbol,associatedLinear_atom]

def associatedEquiv : (T).AssociatedGraded ≃ₗ[K] TB where
  toLinearMap := associatedLinear F w
  invFun := associatedInverse F w
  left_inv := associatedInverse_left F w
  right_inv := associatedInverse_right F w

theorem atom_mul_of_disjoint (n m : ℤ) (s t : Finset V) (hst : Disjoint s t)
    (a : F.level n) (b : F.level m) :
    atom F w n s a*atom F w m t b =
      Sublattice.faceWedgeSign s t hst • atom F w (n+m) (s∪t)
        ⟨a.val*b.val,F.mul_mem n m _ a.property _ b.property⟩ := by
  change (T).symbol _ _ * (T).symbol _ _ = _
  rw [(T).symbol_mul]
  change (T).symbol _ _ = _ • (T).symbol _ _
  rw [← map_zsmul_unit]
  apply (T).symbol_congr _ _ (by rw [faceWeight_union w s t hst]; omega)
  change (a.val ⊗ₜ[K] Simplicial.basis (k:=K) s) * (b.val ⊗ₜ[K] Simplicial.basis (k:=K) t) =
    Sublattice.faceWedgeSign s t hst • ((a.val*b.val) ⊗ₜ[K] Simplicial.basis (k:=K) (s∪t))
  rw [Algebra.TensorProduct.tmul_mul_tmul,Sublattice.faceBasis_mul_of_disjoint s t hst,
    TensorProduct.tmul_smul]

theorem atom_mul_of_not_disjoint (n m : ℤ) (s t : Finset V) (hst : ¬Disjoint s t)
    (a : F.level n) (b : F.level m) :
    atom F w n s a*atom F w m t b=0 := by
  change (T).symbol _ _*(T).symbol _ _=0
  rw [(T).symbol_mul]
  have hz : (⟨(insertLevel F w n s a).val*(insertLevel F w m t b).val,
      (T).mul_mem _ _ _ (insertLevel F w n s a).property _ (insertLevel F w m t b).property⟩ :
      (T).level ((n+faceWeight w s)+(m+faceWeight w t)))=0 := by
    apply Subtype.ext
    change (a.val ⊗ₜ[K] Simplicial.basis (k:=K) s) * (b.val ⊗ₜ[K] Simplicial.basis (k:=K) t) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul,
      Sublattice.faceBasis_mul_of_not_disjoint s t hst,TensorProduct.tmul_zero]
  rw [hz,map_zero]

theorem associatedLinear_mul (x y : (T).AssociatedGraded) :
    associatedLinear F w (x*y)=associatedLinear F w x*associatedLinear F w y := by
  apply associated_tensor_induction F w
    (fun x => associatedLinear F w (x*y)=associatedLinear F w x*associatedLinear F w y)
    (by simp) (fun a b ha hb => by simp only [add_mul,map_add,ha,hb]) _ x
  intro n s a
  apply associated_tensor_induction F w
    (fun y => associatedLinear F w (atom F w n s a*y)=
      associatedLinear F w (atom F w n s a)*associatedLinear F w y)
    (by simp) (fun b c hb hc => by simp only [mul_add,map_add,hb,hc]) _ y
  intro m t b
  rw [associatedLinear_atom,associatedLinear_atom,Algebra.TensorProduct.tmul_mul_tmul]
  by_cases hst : Disjoint s t
  · rw [atom_mul_of_disjoint F w n m s t hst,map_zsmul_unit,associatedLinear_atom,
      Sublattice.faceBasis_mul_of_disjoint s t hst,TensorProduct.tmul_smul,F.symbol_mul]
  · rw [atom_mul_of_not_disjoint F w n m s t hst,map_zero,
      Sublattice.faceBasis_mul_of_not_disjoint s t hst,TensorProduct.tmul_zero]

theorem associatedLinear_one : associatedLinear F w 1=1 := by
  have he : atom F w 0 ∅ ⟨1,F.one_mem⟩=1 := by
    calc
      atom F w 0 ∅ ⟨1,F.one_mem⟩ = (T).symbol 0 ⟨1,(T).one_mem⟩ := by
        change (T).symbol (0+faceWeight w ∅) _ = _
        apply (T).symbol_congr _ _ (by simp only [faceWeight_empty,add_zero])
        change (1:A) ⊗ₜ[K] Simplicial.basis (k:=K) (∅ : Finset V) = 1
        simp [Simplicial.basis,Module.Basis.exteriorAlgebra_eq_prod_map_sort,
          Algebra.TensorProduct.one_def]
      _ = 1 := (T).symbol_one
  rw [← he,associatedLinear_atom,F.symbol_one]
  simp [Simplicial.basis,Module.Basis.exteriorAlgebra_eq_prod_map_sort,
    Algebra.TensorProduct.one_def]

/-- The actual associated algebra of K(A) is the actual tensor exterior
algebra with coefficients in gr(A), with no basis-adapted filtration premise. -/
def associatedAlgebraEquiv : (T).AssociatedGraded ≃ₐ[K] TB :=
  AlgEquiv.ofLinearEquiv (associatedEquiv F w) (associatedLinear_one F w)
    (associatedLinear_mul F w)

@[simp] theorem associatedAlgebraEquiv_apply (z : (T).AssociatedGraded) :
    associatedAlgebraEquiv F w z = associatedLinear F w z := rfl

end FourPapers.FilteredTensorKoszul

end
end
end


end
