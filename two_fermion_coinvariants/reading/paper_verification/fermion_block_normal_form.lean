module

public import PaperVerification.FermionBlockInitial

/-!
# Actual block normal forms and the descending filtration

Triangular tests show that the quotient's actual descending filtration is
exactly the tail filtration of its established basis. They also construct
the complete diagonal-kernel quotient bases and the complete initial
quotient basis. These statements are derived from the presentation; block
spanning and filtered normal-form bounds are not additional assumptions.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BlockInitial

open scoped BigOperators

variable {K P M N Q J : Type*} [CommRing K] [CommRing P] [Algebra K P]
  [AddCommGroup M] [Module P M] [Module K M] [IsScalarTower K P M]
  [AddCommGroup N] [Module K N] [AddCommGroup Q] [Module K Q] [Fintype J]
  {b : Module.Basis J P M} {weight : J → ℕ} {q : M →ₗ[K] Q}
  {D : J → Type*} [∀ j,Fintype (D j)]
  (h : TriangularPresentation (N := N) b weight q D)

def lowerSubmodule (b : Module.Basis J P M) (weight : J → ℕ) (r : ℕ) : Submodule P M where
  carrier := {x | LowerBound b weight r x}
  zero_mem' := by intro i hi; exact (hi (by simp)).elim
  add_mem' := by
    intro x y hx hy i hi
    by_cases hxi : b.repr x i=0
    · apply hy i
      simpa only [map_add,Finsupp.add_apply,hxi,zero_add] using hi
    · exact hx i hxi
  smul_mem' := by
    intro c x hx i hi
    apply hx i
    intro hz
    exact hi (by simp only [map_smul,Finsupp.smul_apply,hz,smul_zero])

theorem lowerBound_single (j : J) (p : P) :
    LowerBound b weight (weight j) (p • b j) := by
  classical
  intro t ht
  by_cases htj : t=j
  · exact le_of_eq (congrArg weight htj.symm)
  · exact (ht (by simp only [map_smul,Finsupp.smul_apply,Module.Basis.repr_self,
      Finsupp.single_eq_of_ne htj,smul_zero])).elim

namespace TriangularPresentation

theorem test_eq_zero_of_lowerBound (x : M) (r : ℕ)
    (hx : LowerBound b weight r x) (j : J) (hj : weight j<r) : h.test j x=0 := by
  classical
  conv_lhs => rw [←b.sum_repr x,map_sum]
  apply Finset.sum_eq_zero
  intro t ht
  by_cases hc : b.repr x t=0
  · rw [hc,zero_smul,map_zero]
  · have hw : weight j<weight t := hj.trans_le (hx t hc)
    exact h.test_higher j t (fun he ↦ (Nat.lt_irrefl _ (he ▸ hw))) hw.le _

theorem normalForm_coefficients_zero_below (x : M) (r : ℕ)
    (hx : LowerBound b weight r x) (j : J) (hj : weight j<r) (e : D j) :
    h.basis.repr (q x) ⟨j,e⟩=0 := by
  apply h.normalForm_coefficients_zero_through x (weight j)
    (fun t ht ↦ h.test_eq_zero_of_lowerBound x r hx t (ht.trans_lt hj)) j le_rfl e

def normalLift : Q →ₗ[K] M := h.basis.constr K h.representative

@[simp] theorem normalLift_basis (z : Sigma D) :
    h.normalLift (h.basis z)=h.representative z := h.basis.constr_basis K _ z

theorem quotient_normalLift (z : Q) : q (h.normalLift z)=z := by
  have he : q.comp h.normalLift=LinearMap.id := by
    apply h.basis.ext
    intro i
    rw [LinearMap.comp_apply,h.normalLift_basis,LinearMap.id_apply]
    exact (h.basis_apply i).symm
  exact LinearMap.congr_fun he z

theorem normalLift_eq_sum (z : Q) :
    h.normalLift z=∑ i:Sigma D,h.basis.repr z i • h.representative i := by
  conv_lhs => rw [←h.basis.sum_repr z,map_sum]
  simp only [map_smul,h.normalLift_basis]

theorem normalForm_eq_normalLift (x : M) : h.normalForm x=h.normalLift (q x) :=
  (h.normalLift_eq_sum (q x)).symm

theorem normalLift_coordinate (z : Q) (j : J) :
    b.repr (h.normalLift z) j=∑ e:D j,h.basis.repr z ⟨j,e⟩ • h.polynomial j e := by
  have hh := h.normalForm_coordinate (h.normalLift z) j
  rw [h.normalForm_eq_normalLift,h.quotient_normalLift] at hh
  exact hh

/-- This identifies the filtration defined by actual ambient representatives,
not merely a filtration newly assigned to a chosen quotient basis. -/
theorem actual_descending_filtration_iff (r : ℕ) (z : Q) :
    (∃ x,LowerBound b weight r x ∧ q x=z) ↔
      LowerBound h.basis (fun i : Sigma D ↦ weight i.1) r z := by
  constructor
  · rintro ⟨x,hx,rfl⟩ i hi
    by_contra hn
    exact hi (h.normalForm_coefficients_zero_below x r hx i.1
      (Nat.lt_of_not_ge hn) i.2)
  · intro hz
    refine ⟨h.normalLift z,?_,h.quotient_normalLift z⟩
    intro j hj
    by_contra hn
    have hw : weight j<r := Nat.lt_of_not_ge hn
    apply hj
    rw [h.normalLift_coordinate]
    apply Finset.sum_eq_zero
    intro e he
    have hc : h.basis.repr z ⟨j,e⟩=0 := by
      by_contra hc
      exact Nat.not_lt_of_ge (hz ⟨j,e⟩ hc) hw
    rw [hc,zero_smul]

theorem diagonal_normalForm (j : J) (p : P) :
    h.diagonal j p=
      ∑ e:D j,h.basis.repr (q (p • b j)) ⟨j,e⟩ • h.diagonal j (h.polynomial j e) := by
  classical
  have hz := h.test_normalForm j (p • b j)
  rw [h.test_same] at hz
  rw [←hz]
  unfold normalForm representative
  rw [map_sum,Fintype.sum_sigma]
  simp_rw [map_smul]
  rw [Finset.sum_eq_single j]
  · simp only [h.test_same]
  · intro t ht htj
    apply Finset.sum_eq_zero
    intro e he
    by_cases hw : weight t<weight j
    · rw [h.normalForm_coefficients_zero_below (p • b j) (weight j)
        (lowerBound_single (b := b) (weight := weight) j p) t hw e,zero_smul]
    · rw [h.test_higher j t htj.symm (Nat.le_of_not_gt hw) _,smul_zero]
  · simp only [Finset.mem_univ,not_true_eq_false,false_implies]

theorem diagonal_quotient_span (j : J) :
    Submodule.span K (Set.range (fun e:D j ↦ (h.diagonal j).ker.mkQ (h.polynomial j e)))=⊤ := by
  classical
  apply top_unique
  intro z hz
  obtain ⟨p,rfl⟩ := (h.diagonal j).ker.mkQ_surjective z
  let c (e : D j) := h.basis.repr (q (p • b j)) ⟨j,e⟩
  have hk : p-∑ e:D j,c e • h.polynomial j e∈(h.diagonal j).ker := by
    rw [LinearMap.mem_ker,map_sub,map_sum]
    simp_rw [map_smul]
    exact sub_eq_zero.mpr (h.diagonal_normalForm j p)
  have he : (h.diagonal j).ker.mkQ p=
      ∑ e:D j,c e • (h.diagonal j).ker.mkQ (h.polynomial j e) := by
    have hh := (Submodule.Quotient.mk_eq_zero _).mpr hk
    change (h.diagonal j).ker.mkQ (p-∑ e:D j,c e • h.polynomial j e)=0 at hh
    rw [map_sub,map_sum] at hh
    simp_rw [map_smul] at hh
    exact sub_eq_zero.mp hh
  rw [he]
  apply Submodule.sum_mem
  intro e he
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e,rfl⟩)

theorem diagonal_quotient_linearIndependent (j : J) :
    LinearIndependent K (fun e:D j ↦ (h.diagonal j).ker.mkQ (h.polynomial j e)) := by
  apply LinearIndependent.of_comp ((h.diagonal j).ker.liftQ (h.diagonal j) le_rfl)
  exact h.independent j

def diagonalQuotientBasis (j : J) :
    Module.Basis (D j) K (P ⧸ (h.diagonal j).ker) :=
  Module.Basis.mk (h.diagonal_quotient_linearIndependent j) (h.diagonal_quotient_span j).ge

@[simp] theorem diagonalQuotientBasis_apply (j : J) (e : D j) :
    h.diagonalQuotientBasis j e=(h.diagonal j).ker.mkQ (h.polynomial j e) :=
  Module.Basis.mk_apply _ _ e

theorem initial_quotient_linearIndependent :
    LinearIndependent K (fun z:Sigma D ↦
      (initialMin b weight q.ker).mkQ (h.representative z)) := by
  classical
  let test (j : J) : M →ₗ[K] N := (h.diagonal j).comp ((b.coord j).restrictScalars K)
  apply linearIndependent_quotient_of_triangular_test_maps D (initialMin b weight q.ker)
    (fun j e ↦ h.polynomial j e • b j) test weight
  · intro j x hx
    rw [h.initialMin_eq_blockKernel] at hx
    exact (mem_blockKernel b h.diagonal x).mp hx j
  · intro j t hjt hwt e
    change h.diagonal j (b.repr (h.polynomial t e • b t) j)=0
    simp only [map_smul,Finsupp.smul_apply,Module.Basis.repr_self,
      Finsupp.single_eq_of_ne hjt,smul_zero,map_zero]
  · intro j
    change LinearIndependent K (fun e ↦ h.diagonal j (b.repr (h.polynomial j e • b j) j))
    simpa only [map_smul,Finsupp.smul_apply,Module.Basis.repr_self,
      Finsupp.single_eq_same,smul_eq_mul,mul_one] using h.independent j

theorem initial_quotient_span :
    Submodule.span K (Set.range (fun z:Sigma D ↦
      (initialMin b weight q.ker).mkQ (h.representative z)))=⊤ := by
  classical
  let I := initialMin b weight q.ker
  let S := Submodule.span K (Set.range (fun z:Sigma D ↦ I.mkQ (h.representative z)))
  have hblock (j : J) (p : P) : I.mkQ (p • b j)∈S := by
    let c (e : D j) := h.basis.repr (q (p • b j)) ⟨j,e⟩
    let a : P := ∑ e:D j,c e • h.polynomial j e
    have hk : h.diagonal j (p-a)=0 := by
      rw [map_sub]
      change h.diagonal j p-h.diagonal j (∑ e:D j,c e • h.polynomial j e)=0
      rw [map_sum]
      simp_rw [map_smul]
      exact sub_eq_zero.mpr (h.diagonal_normalForm j p)
    obtain ⟨x,hx,hb,hc⟩ := h.kernel_element_has_lowest_relation j (p-a) hk
    have hmem : (p-a) • b j∈I := Submodule.subset_span ⟨x,hx,weight j,hb,hc⟩
    have he : I.mkQ (p • b j)=I.mkQ (a • b j) := by
      have hh := (Submodule.Quotient.mk_eq_zero I).mpr hmem
      change I.mkQ ((p-a) • b j)=0 at hh
      rw [sub_smul,map_sub] at hh
      exact sub_eq_zero.mp hh
    rw [he]
    change I.mkQ ((∑ e:D j,c e • h.polynomial j e) • b j)∈S
    rw [Finset.sum_smul,map_sum]
    apply Submodule.sum_mem
    intro e he
    rw [smul_assoc,map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j,e⟩,rfl⟩)
  apply top_unique
  intro z hz
  obtain ⟨x,rfl⟩ := I.mkQ_surjective z
  rw [←b.sum_repr x,map_sum]
  exact Submodule.sum_mem S (fun j hj ↦ hblock j (b.repr x j))

/-- The original specified representatives are a complete basis of the
actual initial quotient, with no dimension premise. -/
def initialQuotientBasis : Module.Basis (Sigma D) K (M ⧸ initialMin b weight q.ker) :=
  Module.Basis.mk h.initial_quotient_linearIndependent h.initial_quotient_span.ge

@[simp] theorem initialQuotientBasis_apply (z : Sigma D) :
    h.initialQuotientBasis z=(initialMin b weight q.ker).mkQ (h.representative z) :=
  Module.Basis.mk_apply _ _ z

end TriangularPresentation

end PaperVerification.Fermion.BlockInitial
