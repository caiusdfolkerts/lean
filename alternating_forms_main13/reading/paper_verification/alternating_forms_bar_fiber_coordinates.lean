module

public import PaperVerification.AlternatingFormsBarLeadingExact
public import PaperVerification.AlternatingFormsBarCutTransport

/-!
# The cut decomposition in literal tensor coordinates

The inclusion of a fixed-word fiber sends each factorization to its
actual positive-basis tensor word. Its coordinates are a single outer
fiber. Consequently the leading degree differential has exactly the
normal adjacent-merge formula on each original tensor basis vector.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.BarCompositions

open BarCoefficientFormula

variable {K C J : Type*} [CommRing K] [Preorder J] [Fintype J]
  (e : C ≃ PositiveNormalWord J)

theorem internalDegreeFiberCoordinates_apply (r N : ℕ)
    (z : internalDegreePiece (K := K) e r N)
    (W : {W : List J // W.length=N}) (L : BarIndex (·≤·) W.val r) :
    internalDegreeFiberCoordinates e r N z W L=
      z.val (factorizationBarWord e W.val L.val) := by
  rfl

theorem factorizationBarWord_injective (W : List J) (r : ℕ) :
    Function.Injective (fun L : BarIndex (·≤·) W r ↦ factorizationBarWord e W L.val) := by
  intro L M h
  apply (actualBarIndexEquiv e W r).symm.injective
  apply Subtype.ext
  change factorizationBarWord e W L.val = factorizationBarWord e W M.val
  exact h

theorem barWordMap_mem_internalDegree (r N : ℕ)
    (W : {W : List J // W.length=N}) (z : BarIndex (·≤·) W.val r →₀ K) :
    barWordMap e W.val r z∈internalDegreePiece (K := K) e r N := by
  induction z using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (internalDegreePiece (K := K) e r N).zero_mem
  | add z w hz hw => simpa only [map_add] using
      (internalDegreePiece (K := K) e r N).add_mem hz hw
  | single L c =>
    rw [barWordMap_single]
    apply Finsupp.single_mem_supported K c
    exact ⟨(factorizationBarWord_length e W.val L.val).trans L.property,
      by rw [factorizationBarWord_flatten]; exact W.property⟩

def fiberInclusion (r N : ℕ) (W : {W : List J // W.length=N}) :
    (BarIndex (·≤·) W.val r →₀ K) →ₗ[K] internalDegreePiece (K := K) e r N :=
  LinearMap.codRestrict _ (barWordMap e W.val r) (barWordMap_mem_internalDegree e r N W)

@[simp] theorem fiberInclusion_val (r N : ℕ) (W : {W : List J // W.length=N})
    (z : BarIndex (·≤·) W.val r →₀ K) :
    (fiberInclusion e r N W z).val=barWordMap e W.val r z := rfl

theorem internalDegreeFiberCoordinates_fiberInclusion (r N : ℕ)
    (W : {W : List J // W.length=N}) (z : BarIndex (·≤·) W.val r →₀ K) :
    internalDegreeFiberCoordinates e r N (fiberInclusion e r N W z)=Pi.single W z := by
  funext V
  ext L
  rw [internalDegreeFiberCoordinates_apply]
  change (Finsupp.mapDomain (fun T : BarIndex (·≤·) W.val r ↦
    factorizationBarWord e W.val T.val) z) (factorizationBarWord e V.val L.val)=_
  by_cases h : V=W
  · subst V
    rw [Finsupp.mapDomain_apply_of_injective (factorizationBarWord_injective e W.val r),
      Pi.single_eq_same]
  · have hn : factorizationBarWord e V.val L.val∉
        Set.range (fun T : BarIndex (·≤·) W.val r ↦ factorizationBarWord e W.val T.val) := by
      rintro ⟨T,hT⟩
      apply h
      apply Subtype.ext
      have hh := congrArg (flattenBarWord e) hT
      rw [factorizationBarWord_flatten,factorizationBarWord_flatten] at hh
      exact hh.symm
    rw [Finsupp.mapDomain_of_notMem_range _ _ hn,Pi.single_eq_of_ne h,Finsupp.zero_apply]

set_option maxHeartbeats 800000 in
theorem leadingDegreeDifferential_fiberInclusion (r N : ℕ)
    (W : {W : List J // W.length=N}) (z : BarIndex (·≤·) W.val (r+1) →₀ K) :
    leadingDegreeDifferential e r N (fiberInclusion e (r+1) N W z)=
      fiberInclusion e r N W (cutModelDifferential (·≤·) W.val r z) := by
  apply (internalDegreeFiberCoordinates e r N).injective
  rw [leadingDegreeDifferential_comm,internalDegreeFiberCoordinates_fiberInclusion,
    internalDegreeFiberCoordinates_fiberInclusion]
  exact leadingFiberDifferential_single r N W z

def tensorBasis (r N : ℕ) :
    Module.Basis (InternalDegreeIndex e r N) K (internalDegreePiece (K := K) e r N) :=
  .ofRepr (internalDegreeCoordinates e r N)

@[simp] theorem tensorBasis_val (r N : ℕ) (L : InternalDegreeIndex e r N) :
    (tensorBasis (K := K) e r N L).val=Finsupp.single L.val 1 := by
  change ((Finsupp.supportedEquivFinsupp (M := K) (R := K)
    {T : List C | T.length=r ∧ (flattenBarWord e T).length=N}).symm
      (Finsupp.single L 1)).val=Finsupp.single L.val 1
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

@[simp] theorem tensorBasis_repr_apply (r N : ℕ)
    (z : internalDegreePiece (K := K) e r N) (L : InternalDegreeIndex e r N) :
    (tensorBasis e r N).repr z L=z.val L.val := rfl

theorem tensorBasis_repr_sub (r N : ℕ)
    (x y : internalDegreePiece (K := K) e r N) (L : InternalDegreeIndex e r N) :
    (tensorBasis e r N).repr (x-y) L=x.val L.val-y.val L.val := rfl

theorem tensorBasis_eq_fiberInclusion (r N : ℕ) (L : InternalDegreeIndex e r N) :
    tensorBasis (K := K) e r N L=
      fiberInclusion e r N ⟨flattenBarWord e L.val,L.property.2⟩
        (Finsupp.single (actualFactorization e (flattenBarWord e L.val) r
          ⟨L.val,rfl,L.property.1⟩) 1) := by
  apply Subtype.ext
  rw [tensorBasis_val,fiberInclusion_val,barWordMap_single]
  congr 1
  have h := (actualBarIndexEquiv e (flattenBarWord e L.val) r).left_inv
    ⟨L.val,rfl,L.property.1⟩
  have hw := congrArg
    (fun T : ActualBarIndex e (flattenBarWord e L.val) r => T.val) h
  exact hw.symm

/-- Coordinates of the leading operator on every original tensor. -/
theorem leadingDegreeDifferential_tensorBasis_val (r N : ℕ)
    (L : InternalDegreeIndex e (r+1) N) :
    (leadingDegreeDifferential e r N (tensorBasis (K := K) e (r+1) N L)).val=
      -basisDifferential (normalProduct e) L.val := by
  rw [tensorBasis_eq_fiberInclusion,leadingDegreeDifferential_fiberInclusion,
    fiberInclusion_val]
  exact cutDifferential_transport_basis e (flattenBarWord e L.val) r
    ⟨L.val,rfl,L.property.1⟩

end PaperVerification.AlternatingForms.BarCompositions
