module

public import PaperVerification.FermionFilteredInitial
public import PaperVerification.FermionTriangularIndependence

/-!
# Smallest-weight relations from an actual triangular quotient basis

The ambient module has a finite basis over its coefficient algebra. Its
quotient has an independently established basis of specified polynomial
multiples of those vectors. Triangular tests then identify the actual
smallest-weight initial relation module, block by block, with the kernels
of the diagonal coefficient maps.

The proof constructs relation lifts by taking the actual quotient normal
form. It does not assume an initial-ideal equality, a block dimension, or
the desired colon-ideal spanning assertion.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

section TriangularCoefficients

variable {K M N J : Type*} [Ring K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [Fintype J]

/-- Vanishing of the tests through a specified weight forces all normal
form coefficients through that weight to vanish. Equal-weight off-diagonal
blocks are covered by the triangular hypothesis. -/
theorem triangular_coefficients_zero_through
    (D : J → Type*) [∀ j,Fintype (D j)]
    (v : (j : J) → D j → M) (test : J → M →ₗ[K] N) (weight : J → ℕ)
    (htri : ∀ j t,j≠t → weight j≤weight t → ∀ e,test j (v t e)=0)
    (hdiag : ∀ j,LinearIndependent K (fun e ↦ test j (v j e)))
    (c : Sigma D → K) (r : ℕ)
    (htest : ∀ j,weight j≤r → test j (∑ p : Sigma D,c p • v p.1 p.2)=0) :
    ∀ j,weight j≤r → ∀ e,c ⟨j,e⟩=0 := by
  classical
  have hblock : ∀ m : ℕ,m≤r → ∀ j : J,weight j=m → ∀ e:D j,c ⟨j,e⟩=0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hmr j hj
      have hsum : (∑ e:D j,c ⟨j,e⟩ • test j (v j e))=0 := by
        have hother (t : J) (ht : t≠j) :
            (∑ e:D t,c ⟨t,e⟩ • test j (v t e))=0 := by
          apply Finset.sum_eq_zero
          intro e he
          by_cases hlow : weight t<m
          · rw [ih (weight t) hlow (hlow.le.trans hmr) t rfl e,zero_smul]
          · rw [htri j t ht.symm (by rw [hj]; exact Nat.le_of_not_gt hlow) e,smul_zero]
        have he : (∑ t:J,∑ e:D t,c ⟨t,e⟩ • test j (v t e))=
            ∑ e:D j,c ⟨j,e⟩ • test j (v j e) := by
          apply Finset.sum_eq_single j
          · intro t ht hne
            exact hother t hne
          · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
        rw [←he]
        have hh := htest j (by simpa only [hj] using hmr)
        simpa only [map_sum,map_smul,Fintype.sum_sigma] using hh
      exact Fintype.linearIndependent_iff.mp (hdiag j) (fun e ↦ c ⟨j,e⟩) hsum
  intro j hj e
  exact hblock (weight j) hj j rfl e

end TriangularCoefficients

namespace BlockInitial

open BasisFiltered

variable {K P M N Q J : Type*} [CommRing K] [CommRing P] [Algebra K P]
  [AddCommGroup M] [Module P M] [Module K M] [IsScalarTower K P M]
  [AddCommGroup N] [Module K N] [AddCommGroup Q] [Module K Q] [Fintype J]
  (b : Module.Basis J P M) (weight : J → ℕ)

/-- Every nonzero coefficient is at least the displayed weight. -/
def LowerBound (r : ℕ) (x : M) : Prop :=
  ∀ j,b.repr x j≠0 → r≤weight j

/-- Smallest-weight initial vectors of actual relations, with the convention
that a component at a lower, absent degree is zero. -/
def initialMin (I : Submodule K M) : Submodule K M :=
  Submodule.span K {y | ∃ x∈I,∃ r,LowerBound b weight r x ∧ component b weight r x=y}

/-- A block kernel is imposed on each literal polynomial coefficient. -/
def blockKernel (diagonal : J → P →ₗ[K] N) : Submodule K M :=
  ⨅ j,(diagonal j |>.comp ((b.coord j).restrictScalars K)).ker

theorem mem_blockKernel (diagonal : J → P →ₗ[K] N) (x : M) :
    x∈blockKernel b diagonal ↔ ∀ j,diagonal j (b.repr x j)=0 := by
  simp only [blockKernel,Submodule.mem_iInf,LinearMap.mem_ker,LinearMap.comp_apply,
    LinearMap.restrictScalars_apply,Module.Basis.coord_apply]

variable (q : M →ₗ[K] Q) (D : J → Type*) [∀ j,Fintype (D j)]

/-- The inputs are actual vectors, maps, and a basis of the actual quotient.
In applications each field is constructed independently before this transfer
is invoked. In particular, no initial relation space is a structure field. -/
structure TriangularPresentation where
  polynomial : (j : J) → D j → P
  basis : Module.Basis (Sigma D) K Q
  basis_apply : ∀ z,basis z=q (polynomial z.1 z.2 • b z.1)
  test : J → M →ₗ[K] N
  diagonal : J → P →ₗ[K] N
  test_same : ∀ j p,test j (p • b j)=diagonal j p
  test_higher : ∀ j t,j≠t → weight j≤weight t → ∀ p : P,test j (p • b t)=0
  kill : ∀ j,q.ker≤(test j).ker
  independent : ∀ j,LinearIndependent K (fun e ↦ diagonal j (polynomial j e))

variable {b weight q D}
variable (h : TriangularPresentation (N := N) b weight q D)

namespace TriangularPresentation

def representative (z : Sigma D) : M := h.polynomial z.1 z.2 • b z.1

def normalForm (x : M) : M :=
  ∑ z:Sigma D,h.basis.repr (q x) z • h.representative z

theorem quotient_normalForm (x : M) : q (h.normalForm x)=q x := by
  unfold normalForm representative
  rw [map_sum]
  simp_rw [map_smul,←h.basis_apply]
  exact h.basis.sum_repr (q x)

theorem subtract_normalForm_mem_kernel (x : M) : x-h.normalForm x∈q.ker := by
  rw [LinearMap.mem_ker,map_sub,h.quotient_normalForm,sub_self]

theorem test_normalForm (j : J) (x : M) : h.test j (h.normalForm x)=h.test j x := by
  have hz := h.kill j (h.subtract_normalForm_mem_kernel x)
  change h.test j (x-h.normalForm x)=0 at hz
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

theorem normalForm_coordinate (x : M) (j : J) :
    b.repr (h.normalForm x) j=
      ∑ e:D j,h.basis.repr (q x) ⟨j,e⟩ • h.polynomial j e := by
  classical
  change ((b.coord j).restrictScalars K) (h.normalForm x)=_
  unfold normalForm representative
  rw [map_sum,Fintype.sum_sigma]
  simp_rw [map_smul]
  rw [Finset.sum_eq_single j]
  · apply Finset.sum_congr rfl
    intro e he
    congr 1
    change b.coord j (h.polynomial j e • b j)=h.polynomial j e
    simp only [map_smul,Module.Basis.coord_apply,Module.Basis.repr_self,
      Finsupp.single_eq_same,smul_eq_mul,mul_one]
  · intro t ht htj
    apply Finset.sum_eq_zero
    intro e he
    have hz : ((b.coord j).restrictScalars K) (h.polynomial t e • b t)=0 := by
      change b.coord j (h.polynomial t e • b t)=0
      simp only [map_smul,Module.Basis.coord_apply,Module.Basis.repr_self,
        Finsupp.single_eq_of_ne htj.symm,smul_zero]
    rw [hz,smul_zero]
  · simp only [Finset.mem_univ,not_true_eq_false,false_implies]

/-- Every relation supported at and above a block has its bottom coefficient
in that block's actual diagonal kernel. -/
theorem diagonal_of_lowest_relation (x : M) (hx : x∈q.ker) (r : ℕ)
    (hb : LowerBound b weight r x) (j : J) (hj : weight j=r) :
    h.diagonal j (b.repr x j)=0 := by
  classical
  have ht : h.test j x=0 := h.kill j hx
  have he : h.test j x=h.diagonal j (b.repr x j) := by
    conv_lhs => rw [←b.sum_repr x,map_sum]
    rw [Finset.sum_eq_single j]
    · exact h.test_same j _
    · intro t ht htj
      by_cases hcoef : b.repr x t=0
      · rw [hcoef,zero_smul,map_zero]
      · exact h.test_higher j t htj.symm (by simpa only [hj] using hb t hcoef) _
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
  rw [he] at ht
  exact ht

theorem initialMin_le_blockKernel :
    initialMin b weight q.ker≤blockKernel b h.diagonal := by
  apply Submodule.span_le.mpr
  rintro y ⟨x,hx,r,hb,rfl⟩
  apply (mem_blockKernel b h.diagonal _).mpr
  intro j
  rw [repr_component]
  split_ifs with hj
  · exact h.diagonal_of_lowest_relation x hx r hb j hj
  · exact map_zero _

theorem normalForm_coefficients_zero_through (x : M) (r : ℕ)
    (htest : ∀ j,weight j≤r → h.test j x=0) :
    ∀ j,weight j≤r → ∀ e:D j,h.basis.repr (q x) ⟨j,e⟩=0 := by
  apply triangular_coefficients_zero_through D
    (fun j e ↦ h.polynomial j e • b j) h.test weight
    (fun j t hjt hwt e ↦ h.test_higher j t hjt hwt _)
  · intro j
    simpa only [h.test_same] using h.independent j
  · intro j hj
    change h.test j (h.normalForm x)=0
    rw [h.test_normalForm,htest j hj]

/-- A diagonal-kernel element has an actual relation lift with precisely
that lowest block. All lower and equal-weight normal-form blocks disappear. -/
theorem kernel_element_has_lowest_relation (j : J) (p : P)
    (hp : h.diagonal j p=0) :
    ∃ x∈q.ker,LowerBound b weight (weight j) x ∧
      component b weight (weight j) x=p • b j := by
  classical
  let z : M := p • b j
  have hz (t : J) (ht : weight t≤weight j) : h.test t z=0 := by
    by_cases htj : t=j
    · subst t
      exact (h.test_same j p).trans hp
    · exact h.test_higher t j htj ht p
  have hc := h.normalForm_coefficients_zero_through z (weight j) hz
  have hn (t : J) (ht : weight t≤weight j) : b.repr (h.normalForm z) t=0 := by
    rw [h.normalForm_coordinate]
    apply Finset.sum_eq_zero
    intro e he
    rw [hc t ht e,zero_smul]
  refine ⟨z-h.normalForm z,h.subtract_normalForm_mem_kernel z,?_,?_⟩
  · intro t ht
    by_contra hlt
    have hw : weight t<weight j := Nat.lt_of_not_ge hlt
    have htj : t≠j := fun he ↦ (Nat.lt_irrefl _ (he ▸ hw))
    apply ht
    simp only [map_sub,Finsupp.sub_apply,hn t hw.le,sub_zero,z,map_smul,
      Finsupp.smul_apply,Module.Basis.repr_self,Finsupp.single_eq_of_ne htj,smul_zero]
  · apply b.repr.injective
    ext t
    rw [repr_component,map_sub,Finsupp.sub_apply]
    by_cases ht : weight t=weight j
    · rw [if_pos ht,hn t ht.le,sub_zero]
    · rw [if_neg ht]
      have htj : t≠j := fun he ↦ ht (congrArg weight he)
      simp only [z,map_smul,Finsupp.smul_apply,Module.Basis.repr_self,
        Finsupp.single_eq_of_ne htj,smul_zero]

/-- The whole smallest-weight initial module is the direct coefficientwise
kernel module, proved from actual relation lifts and the actual quotient basis. -/
theorem initialMin_eq_blockKernel :
    initialMin b weight q.ker=blockKernel b h.diagonal := by
  apply le_antisymm h.initialMin_le_blockKernel
  intro x hx
  have hh := (mem_blockKernel b h.diagonal x).mp hx
  rw [←b.sum_repr x]
  apply Submodule.sum_mem
  intro j hj
  obtain ⟨z,hz,hb,hc⟩ := h.kernel_element_has_lowest_relation j (b.repr x j) (hh j)
  exact Submodule.subset_span ⟨z,hz,weight j,hb,hc⟩

end TriangularPresentation

end BlockInitial
end PaperVerification.Fermion
