module

public import TauCeti.Algebra.Module.GradedModule.Quotient
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The actual quotient algebra by a homogeneous ideal

The homogeneous pieces are the images of the original pieces under the
literal ideal quotient map. This construction allows a general graded
coefficient algebra, including the weighted Rees image with a degree-zero
parameter.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace PaperVerification.GradedAlgebraQuotient

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem quotientMap_ker (Q : Ideal A) :
    (Ideal.Quotient.mkₐ K Q).toLinearMap.ker = Q.restrictScalars K := by
  ext a
  exact Ideal.Quotient.eq_zero_iff_mem

def quotientToRingEquiv (Q : Ideal A) : (A ⧸ Q.restrictScalars K) ≃ₗ[K] (A ⧸ Q) :=
  (Submodule.quotEquivOfEq _ _ (quotientMap_ker Q).symm).trans
    ((Ideal.Quotient.mkₐ K Q).toLinearMap.quotKerEquivOfSurjective
      (Ideal.Quotient.mkₐ_surjective K Q))

@[simp] theorem quotientToRingEquiv_mk (Q : Ideal A) (a : A) :
    quotientToRingEquiv (K := K) Q (Submodule.Quotient.mk a) = Ideal.Quotient.mk Q a := by
  simp only [quotientToRingEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

def grading (G : TauCeti.InternalGrading K A ℕ) (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) :
    TauCeti.InternalGrading K (A ⧸ Q) ℕ :=
  (G.quotient (Q.restrictScalars K) hQ).map (quotientToRingEquiv Q)

theorem grading_piece (G : TauCeti.InternalGrading K A ℕ) (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) (d : ℕ) :
    (grading G Q hQ).piece d = (G.piece d).map (Ideal.Quotient.mkₐ K Q).toLinearMap := by
  simp only [grading, TauCeti.InternalGrading.map_piece,
    TauCeti.InternalGrading.quotient_piece, LinearMap.restrictScalars_self,
    ← Submodule.map_comp]
  have he : (quotientToRingEquiv (K := K) Q).toLinearMap.comp
      (Q.restrictScalars K).mkQ = (Ideal.Quotient.mkₐ K Q).toLinearMap := by
    apply LinearMap.ext
    intro a
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Submodule.mkQ_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] using quotientToRingEquiv_mk (K := K) Q a
  rw [he]

theorem mk_mem (G : TauCeti.InternalGrading K A ℕ) (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) {d : ℕ} {a : A}
    (ha : a ∈ G.piece d) : Ideal.Quotient.mk Q a ∈ (grading G Q hQ).piece d := by
  rw [grading_piece]
  exact ⟨a, ha, rfl⟩

theorem quotientMap_homogeneous (G : TauCeti.InternalGrading K A ℕ) (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) :
    TauCeti.LinearMap.IsHomogeneous (Ideal.Quotient.mkₐ K Q).toLinearMap
      G.piece (grading G Q hQ).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d a ha
  simpa only [add_zero, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk] using mk_mem G Q hQ ha

instance gradedMonoid (G : TauCeti.InternalGrading K A ℕ)
    [SetLike.GradedMonoid G.piece] (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) :
    SetLike.GradedMonoid (grading G Q hQ).piece where
  one_mem := by
    simpa only [map_one] using mk_mem G Q hQ
      (SetLike.GradedOne.one_mem : (1 : A) ∈ G.piece 0)
  mul_mem := by
    intro a b x y hx hy
    rw [grading_piece] at hx hy ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    exact ⟨p * q, SetLike.GradedMul.mul_mem hp hq,
      (Ideal.Quotient.mkₐ K Q).map_mul p q⟩

instance gradedAlgebra (G : TauCeti.InternalGrading K A ℕ)
    [SetLike.GradedMonoid G.piece] (Q : Ideal A)
    (hQ : DirectSum.SetLike.IsHomogeneous G.piece Q) :
    GradedAlgebra (grading G Q hQ).piece :=
  (grading G Q hQ).isInternal.gradedAlgebra

section Equivalence

variable {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- A bijective homogeneous linear map identifies entire homogeneous pieces. -/
theorem homogeneousEquiv_map_piece
    (G : TauCeti.InternalGrading K M ℕ) (H : TauCeti.InternalGrading K N ℕ)
    (e : M ≃ₗ[K] N)
    (he : TauCeti.LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0) (d : ℕ) :
    (G.piece d).map e.toLinearMap = H.piece d := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    simpa only [add_zero] using he.map_mem hx
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e.symm y ∈ G.piece d
    simpa only [add_zero, LinearEquiv.coe_toLinearMap] using he.linearEquiv_symm.map_mem hy

end Equivalence

end PaperVerification.GradedAlgebraQuotient
