module
public import graph_foundation.part014
public import shared_results.part020_filtered_tensor_symbols

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FilteredTensorDifferential -/
section

/-! # The associated differential is the actual Koszul differential of gr(A) -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.FilteredTensorKoszul

open Classical CommAlg TensorExteriorKoszul IntegerFiltered
open scoped TensorProduct BigOperators

universe u
variable {K A V : Type u} [CommRing K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V]
  (F : MultiplicativeFiltration K A) (w : V → ℤ)
  (x : V → A) (hx : ∀ v,x v ∈ F.level (w v))

local notation "T" => filtration F w
local notation "D" => parityDifferential (K:=K) x
local notation "DB" => parityDifferential (K:=K) (leadingVariable F w x hx)

theorem differential_tmul_exterior (a : A) (s : Finset V) :
    differential x (a ⊗ₜ[K] Simplicial.basis s)=
      ∑ v : {v // v∈s},TauCeti.ExteriorAlgebra.basisEraseSign v.val s •
        ((x v.val*a) ⊗ₜ[K] Simplicial.basis (s.erase v.val)) := by
  rw [differential_tmul]
  calc
    (∑ v : V,(x v • a) ⊗ₜ[K] Simplicial.contraction v (Simplicial.basis s))=
        ∑ v∈s,(x v • a) ⊗ₜ[K] Simplicial.contraction v (Simplicial.basis s) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      rw [Simplicial.contraction_basis,if_neg hv,TensorProduct.tmul_zero]
    _ = ∑ v : {v // v∈s},(x v.val • a) ⊗ₜ[K]
        Simplicial.contraction v.val (Simplicial.basis s) :=
      Finset.sum_subtype s (fun _ => Iff.rfl) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Simplicial.contraction_basis,if_pos v.property,TensorProduct.tmul_smul]
      rfl

theorem associated_d_symbol (n : ℤ) (a : (T).level n) :
    (associatedKoszulDGA F w x hx).d ((T).symbol n a)=
      (T).symbol n ⟨(D).d a.val,differential_preserves F w x hx n a.val a.property⟩ := by
  change ((T).associatedDGA D _ _).d ((T).leadingMap ((T).monomial n a))=_
  rw [(T).leadingMap_intertwines,(T).reesDGA_d_monomial]
  rfl

#check associated_d_symbol

theorem associated_d_atom (n : ℤ) (s : Finset V) (a : F.level n) :
    (associatedKoszulDGA F w x hx).d (atom F w n s a)=
      ∑ v : {v // v∈s},TauCeti.ExteriorAlgebra.basisEraseSign v.val s •
        atom F w (w v.val+n) (s.erase v.val)
          ⟨x v.val*a.val,F.mul_mem (w v.val) n _ (hx v.val) _ a.property⟩ := by
  let z (v : {v // v∈s}) : (T).level (n+faceWeight w s) :=
    ⟨(x v.val*a.val) ⊗ₜ[K] Simplicial.basis (s.erase v.val),
      tmul_basis_mem F w _ _ _ (by
        have he : n+faceWeight w s-faceWeight w (s.erase v.val)=w v.val+n := by
          rw [faceWeight_erase w s v.val v.property]
          omega
        rw [he]
        exact F.mul_mem (w v.val) n _ (hx v.val) _ a.property)⟩
  have hsum : (⟨(D).d (insertLevel F w n s a).val,
      differential_preserves F w x hx _ _ (insertLevel F w n s a).property⟩ :
      (T).level (n+faceWeight w s)) =
        ∑ v : {v // v∈s},TauCeti.ExteriorAlgebra.basisEraseSign v.val s • z v := by
    apply Subtype.ext
    simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower]
    change differential (K:=K) x (a.val ⊗ₜ[K] Simplicial.basis (k:=K) s) =
      ∑ v : {v // v∈s}, TauCeti.ExteriorAlgebra.basisEraseSign v.val s •
        ((x v.val*a.val) ⊗ₜ[K] Simplicial.basis (k:=K) (s.erase v.val))
    exact differential_tmul_exterior (K:=K) x a.val s
  change (associatedKoszulDGA F w x hx).d ((T).symbol _ _)=_
  rw [associated_d_symbol,hsum,map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_zsmul_unit]
  congr 1
  apply (T).symbol_congr _ _ (by rw [faceWeight_erase w s v.val v.property]; omega)
  rfl

#check associated_d_atom
set_option maxHeartbeats 150000 in
set_option diagnostics true in
/-- Differential compatibility on a single coefficient symbol and exterior
basis vector. Keeping this calculation separate gives the global induction
an opaque, already checked algebraic equality. -/
theorem associatedLinear_d_atom (n : ℤ) (s : Finset V) (a : F.level n) :
    associatedLinear F w ((associatedKoszulDGA F w x hx).d (atom F w n s a)) =
      (DB).d (associatedLinear F w (atom F w n s a)) := by
  rw [associated_d_atom,map_sum,associatedLinear_atom]
  change _ = differential (K:=K) (leadingVariable F w x hx)
    (F.symbol n a ⊗ₜ[K] Simplicial.basis (k:=K) s)
  rw [differential_tmul_exterior (K:=K) (leadingVariable F w x hx) (F.symbol n a) s]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_zsmul_unit,associatedLinear_atom]
  exact congrArg
    (fun b : F.AssociatedGraded =>
      TauCeti.ExteriorAlgebra.basisEraseSign v.val s •
        (b ⊗ₜ[K] Simplicial.basis (k:=K) (s.erase v.val)))
    (F.symbol_mul (w v.val) n ⟨x v.val,hx v.val⟩ a).symm

#check associatedLinear_d_atom

/-- The explicitly constructed algebra equivalence commutes with the
literal Koszul differential, assigning each variable its coefficient symbol. -/
theorem associatedLinear_differential (z : (T).AssociatedGraded) :
    associatedLinear F w ((associatedKoszulDGA F w x hx).d z) =
      (DB).d (associatedLinear F w z) := by
  apply associated_tensor_induction F w
    (fun z => associatedLinear F w ((associatedKoszulDGA F w x hx).d z) =
      (DB).d (associatedLinear F w z))
    (by simp only [map_zero]) (fun a b ha hb => by simp only [map_add,ha,hb])
    (associatedLinear_d_atom F w x hx) z

#check associatedLinear_differential

/-- The actual coefficient-symbol algebra equivalence is a chain map. -/
theorem associatedAlgebraEquiv_differential (z : (T).AssociatedGraded) :
    associatedAlgebraEquiv F w ((associatedKoszulDGA F w x hx).d z) =
      (DB).d (associatedAlgebraEquiv F w z) := by
  rw [associatedAlgebraEquiv_apply, associatedAlgebraEquiv_apply]
  exact associatedLinear_differential F w x hx z

/-- A constructed algebra equivalence between the homology of the actual
associated Koszul complex and H_R(gr(A)). -/
def associatedKoszulHomologyEquiv :
    (associatedKoszulDGA F w x hx).Homology ≃ₐ[K] (DB).Homology :=
  ParityDifferential.homologyEquiv (associatedKoszulDGA F w x hx) DB
    (associatedAlgebraEquiv F w) (associatedAlgebraEquiv_differential F w x hx)


end FourPapers.FilteredTensorKoszul

end
end
end


end
