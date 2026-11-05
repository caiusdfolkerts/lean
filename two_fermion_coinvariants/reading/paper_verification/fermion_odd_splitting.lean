module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.Abel

/-!
# A literal two-copy splitting from an odd contraction

If two square-zero operators anticommute to the identity, the ambient module
is the direct sum of two copies of the contraction kernel. A quotient whose
kernel is the creation image is canonically that contraction kernel. This is
the module-theoretic core of the strict-family exterior-factor argument.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.OddSplitting

variable {R M Q : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]
  (C D : Module.End R M) (hC : C*C=0) (hD : D*D=0) (hCD : D*C+C*D=1)

include hC in
theorem creation_square_apply (x : M) : C (C x)=0 :=
  LinearMap.congr_fun hC x

include hD in
theorem contraction_square_apply (x : M) : D (D x)=0 :=
  LinearMap.congr_fun hD x

include hCD in
theorem contraction_creation_apply (x : M) : D (C x)+C (D x)=x :=
  LinearMap.congr_fun hCD x

/-- Two actual components in the contraction kernel, with explicit inverse. -/
def kernelCopiesEquiv : M ≃ₗ[R] D.ker × D.ker where
  toFun x := (⟨D (C x),contraction_square_apply D hD (C x)⟩,
    ⟨D x,contraction_square_apply D hD x⟩)
  invFun x := x.1.val+C x.2.val
  left_inv x := contraction_creation_apply C D hCD x
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_add,creation_square_apply C hC,map_zero,add_zero]
      have h := contraction_creation_apply C D hCD x.1.val
      simpa only [LinearMap.mem_ker.mp x.1.property,map_zero,add_zero] using h
    · apply Subtype.ext
      simp only [map_add,LinearMap.mem_ker.mp x.1.property,zero_add]
      have h := contraction_creation_apply C D hCD x.2.val
      simpa only [LinearMap.mem_ker.mp x.2.property,map_zero,add_zero] using h
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change D (C (x+y))=D (C x)+D (C y)
      simp only [map_add]
    · apply Subtype.ext
      change D (x+y)=D x+D y
      exact map_add D x y
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      change D (C (c • x))=((RingHom.id R) c) • D (C x)
      simp only [map_smul,RingHom.id_apply]
    · apply Subtype.ext
      change D (c • x)=((RingHom.id R) c) • D x
      simp only [map_smul,RingHom.id_apply]

variable (q : M →ₗ[R] Q) (hq : Function.Surjective q) (hker : q.ker=C.range)

include hC hD hCD hq hker in
/-- Restricting the actual quotient map to the contraction kernel is bijective. -/
theorem quotient_restrict_bijective : Function.Bijective (q.domRestrict D.ker) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hqx : q x.val=0 := hx
    have hxrange : x.val ∈ C.range := by
      rw [← hker]
      exact LinearMap.mem_ker.mpr hqx
    obtain ⟨y,hy⟩ := hxrange
    have hDC : D (C y)=0 := by rw [hy]; exact x.property
    have he : C (D y)=y := by
      simpa only [hDC,zero_add] using contraction_creation_apply C D hCD y
    have hCy : C y=0 := by
      rw [← he,creation_square_apply C hC]
    exact Subtype.ext (hy.symm.trans hCy)
  · intro y
    obtain ⟨x,rfl⟩ := hq y
    refine ⟨⟨D (C x),contraction_square_apply D hD (C x)⟩,?_⟩
    have hzero : q (C (D x))=0 := by
      apply LinearMap.mem_ker.mp
      rw [hker]
      exact ⟨D x,rfl⟩
    have h := congrArg q (contraction_creation_apply C D hCD x)
    change q (D (C x))=q x
    simpa only [map_add,hzero,add_zero] using h

def kernelQuotientEquiv : D.ker ≃ₗ[R] Q :=
  LinearEquiv.ofBijective (q.domRestrict D.ker)
    (quotient_restrict_bijective C D hC hD hCD q hq hker)

/-- The actual quotient appears twice. In particular, no freeness of this
quotient is inferred merely from its being a direct summand. -/
def quotientCopiesEquiv : M ≃ₗ[R] Q × Q :=
  (kernelCopiesEquiv C D hC hD hCD).trans
    (LinearEquiv.prodCongr (kernelQuotientEquiv C D hC hD hCD q hq hker)
      (kernelQuotientEquiv C D hC hD hCD q hq hker))

end PaperVerification.Fermion.OddSplitting

namespace PaperVerification.Fermion.OddSplitting

variable {K M Q : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup Q] [Module K Q] [Module.Finite K M]

/-- Over a field, the literal splitting supplies the exact upper bound needed
for the strict basis, independently of any proposed strict monomials. -/
theorem finrank_eq_twice_quotient
    (C D : Module.End K M) (hC : C*C=0) (hD : D*D=0) (hCD : D*C+C*D=1)
    (q : M →ₗ[K] Q) (hq : Function.Surjective q) (hker : q.ker=C.range) :
    Module.finrank K M=2*Module.finrank K Q := by
  letI : Module.Finite K Q := Module.Finite.of_surjective q hq
  have he := (quotientCopiesEquiv C D hC hD hCD q hq hker).finrank_eq
  rw [Module.finrank_prod] at he
  simpa only [two_mul] using he

end PaperVerification.Fermion.OddSplitting
