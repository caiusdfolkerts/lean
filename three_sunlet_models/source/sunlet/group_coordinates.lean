module

public import sunlet.polynomial_image
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring

/-!
# The literal six-family group model and the constrained Fourier indices

These bridges concern the entire affine parameter image.  They make no
assumption that an edge parameter is nonzero.  No dimension theorem is
assumed or asserted in this module.
-/

@[expose] public section
noncomputable section

namespace Sunlet

variable {G : Type*} [AddCommGroup G]

/-- Translation by a group element, as the permutation used in the Latin map. -/
def addTranslationPerm (a : G) : Equiv.Perm G where
  toFun b := a + b
  invFun b := -a + b
  left_inv b := by simp [← add_assoc]
  right_inv b := by simp [← add_assoc]

@[simp] theorem addTranslationPerm_apply (a b : G) : addTranslationPerm a b = a + b := rfl

end Sunlet

namespace Sunlet.GroupCoordinates

variable {K G : Type*} [Field K] [AddCommGroup G]

abbrev Parameters := Fin 6 → G → K

/-- Six independent Fourier edge families, in the order of the manuscript. -/
def coordinate (w : Parameters (K := K) (G := G)) (a b c : G) : K :=
  w 0 a * w 1 b * w 2 c * (w 3 (a + b) * w 4 a + w 3 b * w 5 a)

def parameterMap (w : Parameters (K := K) (G := G)) (ab : G × G) : K :=
  coordinate w ab.1 ab.2 (-(ab.1 + ab.2))

abbrev FlowIndex (G : Type*) [AddCommGroup G] :=
  {abc : G × G × G // abc.1 + abc.2.1 + abc.2.2 = 0}

/-- Eliminating the third Fourier index is a genuine bijection. -/
def flowIndexEquiv : FlowIndex G ≃ G × G where
  toFun abc := (abc.val.1, abc.val.2.1)
  invFun ab := ⟨(ab.1, ab.2, -(ab.1 + ab.2)), add_neg_cancel _⟩
  left_inv abc := by
    apply Subtype.ext
    rcases abc with ⟨⟨a,b,c⟩,h⟩
    have hc : c = -(a + b) := eq_neg_of_add_eq_zero_right h
    simp only [hc]
  right_inv _ := rfl

theorem coordinate_flow (w : Parameters (K := K) (G := G)) (a b c : G)
    (habc : a + b + c = 0) : coordinate w a b c = parameterMap w (a,b) := by
  have hc : c = -(a + b) := eq_neg_of_add_eq_zero_right habc
  rw [hc]
  rfl

/-- The literal map with the paper's constraint `a+b+c=0`. -/
def tripleParameterMap (w : Parameters (K := K) (G := G)) (abc : FlowIndex G) : K :=
  coordinate w abc.val.1 abc.val.2.1 abc.val.2.2

theorem tripleParameterMap_eq (w : Parameters (K := K) (G := G)) :
    tripleParameterMap w = parameterMap w ∘ flowIndexEquiv := by
  funext abc
  exact coordinate_flow w _ _ _ abc.property

/-- Absorb the first edge family and negate the third leaf index. -/
def collapse (w : Parameters (K := K) (G := G)) : Sunlet.Parameters K G G where
  s := w 1
  t b := w 2 (-b)
  h := w 3
  u a := w 0 a * w 4 a
  v a := w 0 a * w 5 a

/-- Every five-family parameter occurs, by taking the first family to be one. -/
def expand (p : Sunlet.Parameters K G G) : Parameters (K := K) (G := G) :=
  ![fun _ => 1, p.s, fun b => p.t (-b), p.h, p.u, p.v]

theorem collapse_expand (p : Sunlet.Parameters K G G) : collapse (expand p) = p := by
  cases p
  simp [collapse, expand]

theorem parameterMap_eq_fiveFamily (w : Parameters (K := K) (G := G)) :
    parameterMap w = Sunlet.parameterMap addTranslationPerm (collapse w) := by
  funext ab
  simp only [parameterMap, coordinate, Sunlet.parameterMap, Sunlet.coordinate,
    collapse, addTranslationPerm_apply]
  ring

/-- Equality of the entire images, with no nonzero-parameter assumption. -/
theorem range_eq_fiveFamily :
    Set.range (parameterMap (K := K) (G := G)) =
      Set.range (Sunlet.parameterMap (K := K) addTranslationPerm) := by
  ext q
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨collapse w, (parameterMap_eq_fiveFamily w).symm⟩
  · rintro ⟨p,rfl⟩
    refine ⟨expand p, ?_⟩
    rw [parameterMap_eq_fiveFamily, collapse_expand]

def imageClosure : Set (G × G → K) :=
  MvPolynomial.zeroLocus K
    (MvPolynomial.vanishingIdeal K (Set.range (parameterMap (K := K) (G := G))))

def tripleImageClosure : Set (FlowIndex G → K) :=
  MvPolynomial.zeroLocus K
    (MvPolynomial.vanishingIdeal K (Set.range (tripleParameterMap (K := K) (G := G))))

theorem imageClosure_eq_fiveFamily [Infinite K] :
    imageClosure (K := K) (G := G) =
      Sunlet.imageClosure (K := K) addTranslationPerm := by
  rw [imageClosure, range_eq_fiveFamily, Sunlet.parameterImage_eq_polynomialImage,
    Sunlet.imageClosure, PolynomialImage.closure,
    PolynomialImage.definingIdeal_eq_vanishingIdeal]

/-- Taking the algebraic closure of a set does not change its equations. -/
theorem closure_vanishingIdeal {σ : Type*} (S : Set (σ → K)) :
    MvPolynomial.vanishingIdeal K
      (MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S)) =
        MvPolynomial.vanishingIdeal K S := by
  exact le_antisymm
    (MvPolynomial.vanishingIdeal_anti_mono (MvPolynomial.zeroLocus_vanishingIdeal_le S))
    (MvPolynomial.le_vanishingIdeal_zeroLocus _)

def flowPolynomialEquiv : MvPolynomial (FlowIndex G) K ≃ₐ[K] MvPolynomial (G × G) K :=
  MvPolynomial.renameEquiv K flowIndexEquiv

theorem flowPolynomialEquiv_mem (p : MvPolynomial (FlowIndex G) K) :
    flowPolynomialEquiv p ∈
        MvPolynomial.vanishingIdeal K (Set.range (parameterMap (K := K) (G := G))) ↔
      p ∈ MvPolynomial.vanishingIdeal K (Set.range (tripleParameterMap (K := K) (G := G))) := by
  simp only [MvPolynomial.mem_vanishingIdeal_iff, Set.forall_mem_range,
    flowPolynomialEquiv, MvPolynomial.renameEquiv_apply, MvPolynomial.aeval_rename,
    tripleParameterMap_eq]

theorem flow_vanishingIdeal_map :
    MvPolynomial.vanishingIdeal K (Set.range (parameterMap (K := K) (G := G))) =
      (MvPolynomial.vanishingIdeal K (Set.range (tripleParameterMap (K := K) (G := G)))).map
        (flowPolynomialEquiv (K := K) (G := G)).toRingHom := by
  ext p
  rw [Ideal.mem_map_iff_of_surjective
    (flowPolynomialEquiv (K := K) (G := G)).toRingHom flowPolynomialEquiv.surjective]
  constructor
  · intro hp
    refine ⟨flowPolynomialEquiv.symm p, ?_, flowPolynomialEquiv.apply_symm_apply p⟩
    apply (flowPolynomialEquiv_mem _).mp
    simpa only [AlgEquiv.apply_symm_apply] using hp
  · rintro ⟨q,hq,rfl⟩
    exact (flowPolynomialEquiv_mem q).mpr hq

/-- The original triple-index and eliminated-index coordinate rings are isomorphic. -/
def flowCoordinateRingEquiv :
    (MvPolynomial (FlowIndex G) K ⧸
      MvPolynomial.vanishingIdeal K (tripleImageClosure (K := K) (G := G))) ≃ₐ[K]
    (MvPolynomial (G × G) K ⧸
      MvPolynomial.vanishingIdeal K (imageClosure (K := K) (G := G))) := by
  rw [tripleImageClosure, imageClosure, closure_vanishingIdeal, closure_vanishingIdeal]
  exact Ideal.quotientEquivAlg _ _ flowPolynomialEquiv flow_vanishingIdeal_map

end Sunlet.GroupCoordinates
