module

public import PaperVerification.QuadraticWordBarFibers
public import Mathlib.LinearAlgebra.Finsupp.SumProd

/-!
# Exactness of the quadratic monomial bar complex

There are finitely many literal generator words of a fixed length. The
normal-block tensor module splits over these words, and the cut
differential acts separately on each fiber. The actual cut contraction
therefore proves exactness of this full leading complex away from the
diagonal, with no rank or acyclicity hypothesis.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.QuadraticWordBar

open PaperVerification.AlternatingForms.BarCompositions

variable {C J : Type*} [Fintype J]
  {R : J → J → Prop} (e : C ≃ PositiveWord R)

instance fixedWordFintype (N : ℕ) : Fintype {W : List J // W.length=N} := by
  apply Fintype.ofSurjective
    (fun f : Fin N → J ↦ (⟨List.ofFn f,List.length_ofFn⟩ : {W : List J // W.length=N}))
  intro W
  rcases W with ⟨W,hW⟩
  subst N
  refine ⟨W.get,?_⟩
  apply Subtype.ext
  exact List.ofFn_get W

variable {K : Type*} [CommRing K]

def internalDegreeFiberCoordinates (r N : ℕ) :
    internalDegreePiece (K := K) e r N ≃ₗ[K]
      (W : {W : List J // W.length=N}) → (BarIndex R W.val r →₀ K) :=
  (internalDegreeCutCoordinates e r N).trans (Finsupp.sigmaFinsuppLEquivPiFinsupp K)

def leadingFiberDifferential (r N : ℕ) :
    ((W : {W : List J // W.length=N}) → (BarIndex R W.val (r+1) →₀ K)) →ₗ[K]
      ((W : {W : List J // W.length=N}) → (BarIndex R W.val r →₀ K)) where
  toFun z W := cutModelDifferential R W.val r (z W)
  map_add' z w := by
    funext W
    exact map_add (cutModelDifferential (K := K) R W.val r) (z W) (w W)
  map_smul' a z := by
    funext W
    simpa only [Pi.smul_apply,RingHom.id_apply] using
      map_smul (cutModelDifferential (K := K) R W.val r) a (z W)

theorem leadingFiberDifferential_apply (r N : ℕ)
    (z : (W : {W : List J // W.length=N}) → (BarIndex R W.val (r+1) →₀ K))
    (W : {W : List J // W.length=N}) :
    leadingFiberDifferential (K := K) (J := J) (R := R) r N z W=
      cutModelDifferential (K := K) R W.val r (z W) := rfl

def leadingDegreeDifferential (r N : ℕ) :
    internalDegreePiece (K := K) e (r+1) N →ₗ[K] internalDegreePiece (K := K) e r N :=
  (internalDegreeFiberCoordinates e r N).symm.toLinearMap.comp
    ((leadingFiberDifferential r N).comp
      (internalDegreeFiberCoordinates e (r+1) N).toLinearMap)

theorem leadingDegreeDifferential_comm (r N : ℕ)
    (z : internalDegreePiece (K := K) e (r+1) N) :
    internalDegreeFiberCoordinates e r N (leadingDegreeDifferential e r N z)=
      leadingFiberDifferential r N (internalDegreeFiberCoordinates e (r+1) N z) := by
  simp only [leadingDegreeDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem leadingFiberDifferential_squared (r N : ℕ)
    (z : (W : {W : List J // W.length=N}) → (BarIndex R W.val (r+2) →₀ K)) :
    leadingFiberDifferential r N (leadingFiberDifferential (K := K) (r+1) N z)=0 := by
  funext W
  exact cutModelDifferential_squared R W.val r (z W)

theorem leadingFiber_range_eq_ker (r N : ℕ) (hr : r+1≠N) :
    (leadingFiberDifferential (K := K) (J := J) (R := R) (r+1) N).range=
      (leadingFiberDifferential (K := K) (J := J) (R := R) r N).ker := by
  ext z
  constructor
  · rintro ⟨y,rfl⟩
    exact LinearMap.mem_ker.mpr (leadingFiberDifferential_squared r N y)
  · intro hz
    have hc : ∀ W : {W : List J // W.length=N},
        ∃ y : BarIndex R W.val (r+2) →₀ K,
          cutModelDifferential R W.val (r+1) y=z W := by
      intro W
      apply cutModel_cycle_is_boundary R W.val (r+1)
        (by simpa only [W.property] using hr) (z W)
      have he := congrFun (LinearMap.mem_ker.mp hz) W
      change cutModelDifferential R W.val r (z W)=0 at he
      have he' := congrArg (barExteriorMap (K := K) R W.val r) he
      rw [barExteriorMap_differential,map_zero] at he'
      exact he'
    refine ⟨fun W ↦ Classical.choose (hc W),?_⟩
    funext W
    exact Classical.choose_spec (hc W)

theorem leadingDegree_range_eq_ker (r N : ℕ) (hr : r+1≠N) :
    (leadingDegreeDifferential (K := K) e (r+1) N).range=
      (leadingDegreeDifferential (K := K) e r N).ker := by
  ext z
  constructor
  · rintro ⟨y,rfl⟩
    apply LinearMap.mem_ker.mpr
    apply (internalDegreeFiberCoordinates e r N).injective
    rw [leadingDegreeDifferential_comm,leadingDegreeDifferential_comm,map_zero]
    exact leadingFiberDifferential_squared r N _
  · intro hz
    have hc : internalDegreeFiberCoordinates e (r+1) N z∈
        (leadingFiberDifferential (K := K) (J := J) (R := R) r N).ker := by
      apply LinearMap.mem_ker.mpr
      rw [←leadingDegreeDifferential_comm,LinearMap.mem_ker.mp hz,map_zero]
    rw [←leadingFiber_range_eq_ker r N hr] at hc
    obtain ⟨y,hy⟩ := hc
    refine ⟨(internalDegreeFiberCoordinates e (r+2) N).symm y,?_⟩
    apply (internalDegreeFiberCoordinates e (r+1) N).injective
    rw [leadingDegreeDifferential_comm,LinearEquiv.apply_symm_apply,hy]

end PaperVerification.QuadraticWordBar

