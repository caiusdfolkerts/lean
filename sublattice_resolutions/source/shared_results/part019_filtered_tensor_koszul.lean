module
public import graph_foundation.part013
public import shared_results.part019_integer_filtered_coordinates

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FilteredTensorKoszul -/
section

/-! # The weight filtration on the actual tensor Koszul algebra

For a filtered coefficient algebra A, the exterior generator e_v is given
the weight of z_v. The level-n condition is imposed directly on its actual
exterior coordinates: the coefficient of e_F lies in F_(n−weight(F)) A.
Exhaustiveness, separatedness, multiplication, parity and the actual Koszul
differential are proved from the coefficient filtration.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.FilteredTensorKoszul

open Classical CommAlg TensorExteriorKoszul IntegerFiltered
open scoped TensorProduct BigOperators

universe u
variable {K A V : Type u} [CommRing K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V]
  (F : MultiplicativeFiltration K A) (w : V → ℤ)

abbrev Total := A ⊗[K] Simplicial.Ambient V K

def faceWeight (s : Finset V) : ℤ := ∑ v ∈ s, w v

@[simp] theorem faceWeight_empty : faceWeight w ∅ = 0 := by simp [faceWeight]

theorem faceWeight_union (s t : Finset V) (h : Disjoint s t) :
    faceWeight w (s ∪ t) = faceWeight w s + faceWeight w t :=
  Finset.sum_union h

theorem faceWeight_erase (s : Finset V) (v : V) (hv : v ∈ s) :
    faceWeight w (s.erase v) = faceWeight w s - w v := by
  have h := Finset.sum_erase_add s w hv
  change faceWeight w (s.erase v) + w v = faceWeight w s at h
  omega

def coefficient (s : Finset V) : Total (K:=K) (A:=A) (V:=V) →ₗ[K] A :=
  (Finsupp.lapply s).comp TensorExteriorKoszul.coordinates.toLinearMap

@[simp] theorem coefficient_tmul_basis (s t : Finset V) (a : A) :
    coefficient s (a ⊗ₜ[K] Simplicial.basis t) = if t=s then a else 0 := by
  simp only [coefficient,LinearMap.comp_apply,Finsupp.lapply_apply,
    LinearEquiv.coe_coe,coordinates_tmul_basis,Finsupp.single_apply]

theorem sum_coefficients (x : Total (K:=K) (A:=A) (V:=V)) :
    ∑ s : Finset V, coefficient s x ⊗ₜ[K] Simplicial.basis s = x := by
  apply TensorExteriorKoszul.coordinates.injective
  ext t
  simp [coefficient,coordinates_tmul_basis,Finsupp.single_apply]

def level (n : ℤ) : Submodule K (Total (K:=K) (A:=A) (V:=V)) :=
  ⨅ s : Finset V, (F.level (n-faceWeight w s)).comap (coefficient s)

theorem mem_level (n : ℤ) (x : Total (K:=K) (A:=A) (V:=V)) :
    x ∈ level F w n ↔ ∀ s, coefficient s x ∈ F.level (n-faceWeight w s) := by
  simp only [level,Submodule.mem_iInf,Submodule.mem_comap]

theorem tmul_basis_mem (n : ℤ) (s : Finset V) (a : A)
    (ha : a ∈ F.level (n-faceWeight w s)) :
    a ⊗ₜ[K] Simplicial.basis s ∈ level F w n := by
  rw [mem_level]
  intro t
  rw [coefficient_tmul_basis]
  split_ifs with h
  · subst t
    exact ha
  · exact (F.level _).zero_mem

theorem level_mono : Monotone (level F w) := by
  intro i j hij x hx
  rw [mem_level] at hx ⊢
  intro s
  exact F.mono (sub_le_sub_right hij _) (hx s)

theorem exhaustive (x : Total (K:=K) (A:=A) (V:=V)) : ∃ n, x ∈ level F w n := by
  choose n hn using fun s : Finset V => F.exhaustive (coefficient s x)
  let N := Finset.univ.sup' Finset.univ_nonempty (fun s : Finset V => n s+faceWeight w s)
  refine ⟨N, (mem_level F w N x).mpr ?_⟩
  intro s
  apply F.mono (show n s ≤ N-faceWeight w s from ?_) (hn s)
  have hs : n s+faceWeight w s ≤ N := Finset.le_sup' (fun t : Finset V => n t+faceWeight w t) (Finset.mem_univ s)
  omega

theorem separated (x : Total (K:=K) (A:=A) (V:=V))
    (hx : ∀ n, x ∈ level F w n) : x=0 := by
  apply TensorExteriorKoszul.coordinates.injective
  ext s
  change coefficient s x = 0
  apply F.separated
  intro n
  have h := (mem_level F w (n+faceWeight w s) x).mp (hx _) s
  simpa only [add_sub_cancel_right] using h

private theorem exterior_empty : Simplicial.basis (V:=V) (k:=K) ∅ = 1 := by
  simp [Simplicial.basis,Module.Basis.exteriorAlgebra_eq_prod_map_sort]

theorem one_mem : (1 : Total (K:=K) (A:=A) (V:=V)) ∈ level F w 0 := by
  rw [Algebra.TensorProduct.one_def,← exterior_empty]
  apply tmul_basis_mem
  simpa only [faceWeight_empty,sub_zero] using F.one_mem

theorem mul_mem (i j : ℤ) (x y : Total (K:=K) (A:=A) (V:=V))
    (hx : x ∈ level F w i) (hy : y ∈ level F w j) : x*y ∈ level F w (i+j) := by
  rw [← sum_coefficients x,← sum_coefficients y,Finset.sum_mul]
  apply Submodule.sum_mem
  intro s _
  rw [Finset.mul_sum]
  apply Submodule.sum_mem
  intro t _
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  by_cases hst : Disjoint s t
  · rw [Sublattice.faceBasis_mul_of_disjoint s t hst,TensorProduct.tmul_smul]
    apply (level F w (i+j)).smul_of_tower_mem
    apply tmul_basis_mem
    have h := F.mul_mem (i-faceWeight w s) (j-faceWeight w t)
      _ ((mem_level F w i x).mp hx s) _ ((mem_level F w j y).mp hy t)
    have he : i+j-faceWeight w (s∪t) =
        (i-faceWeight w s)+(j-faceWeight w t) := by
      rw [faceWeight_union w s t hst]
      omega
    simpa only [he] using h
  · rw [Sublattice.faceBasis_mul_of_not_disjoint s t hst,TensorProduct.tmul_zero]
    exact Submodule.zero_mem _

/-- The filtration induced on the literal algebra A⊗Λ(V). Its separation
and exhaustion follow from the actual coefficient filtration. -/
def filtration : MultiplicativeFiltration K (Total (K:=K) (A:=A) (V:=V)) where
  level := level F w
  mono := level_mono F w
  exhaustive := exhaustive F w
  separated := separated F w
  one_mem := one_mem F w
  mul_mem := fun i j x hx y hy => FourPapers.FilteredTensorKoszul.mul_mem F w i j x y hx hy

variable (x : V → A) (hx : ∀ v, x v ∈ F.level (w v))

include hx in
theorem differential_preserves (n : ℤ) (z : Total (K:=K) (A:=A) (V:=V))
    (hz : z ∈ level F w n) : differential x z ∈ level F w n := by
  rw [← sum_coefficients z,map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [differential_tmul]
  apply Submodule.sum_mem
  intro v _
  rw [Simplicial.contraction_basis]
  split_ifs with hv
  · rw [TensorProduct.tmul_smul]
    apply (level F w n).smul_of_tower_mem
    apply tmul_basis_mem
    have h := F.mul_mem (w v) (n-faceWeight w s) _ (hx v)
      _ ((mem_level F w n z).mp hz s)
    have he : w v+(n-faceWeight w s)=n-faceWeight w (s.erase v) := by
      rw [faceWeight_erase w s v hv]
      omega
    simpa only [smul_eq_mul,he] using h
  · rw [TensorProduct.tmul_zero]
    exact Submodule.zero_mem _

theorem parity_preserves (n : ℤ) (z : Total (K:=K) (A:=A) (V:=V))
    (hz : z ∈ level F w n) : involute z ∈ level F w n := by
  rw [← sum_coefficients z,map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [involute_tmul]
  change _ ⊗ₜ[K] CliffordAlgebra.involute ((Pi.basisFun K V).ExteriorAlgebra s) ∈ _
  rw [TauCeti.ExteriorAlgebra.involute_basis,TensorProduct.tmul_smul]
  exact (level F w n).smul_of_tower_mem _ (tmul_basis_mem F w n s _ ((mem_level F w n z).mp hz s))

def associatedKoszulDGA : ParityDifferential K (filtration F w).AssociatedGraded :=
  (filtration F w).associatedDGA (parityDifferential x)
    (differential_preserves F w x hx) (parity_preserves F w)

/-- The original polynomial variable acts on gr(A) by its actual leading
class. These are the coefficient multipliers in K_R(gr(A)). -/
def leadingVariable (v : V) : F.AssociatedGraded :=
  F.leadingMap (F.monomial (w v) ⟨x v,hx v⟩)

end FourPapers.FilteredTensorKoszul

end
end
end


end
