module

public import TauCeti.Algebra.Module.GradedModule.Quotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.PowerSeries.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Hilbert series after a homogeneous regular map

Every coefficient is the dimension of an actual homogeneous subspace. The
kernel calculation is proved by homogeneous projection, including degrees
below the shift, and rank-nullity proves the formal power-series identity.
No Hilbert-function identity is supplied as a hypothesis.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.GradedHilbert

open scoped BigOperators

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

def projection (G : TauCeti.InternalGrading K M ℕ) (d : ℕ) : Module.End K M where
  toFun x := (DirectSum.decompose G.piece x d : M)
  map_add' x y := by
    simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
  map_smul' a x := by
    simp only [DirectSum.decompose_smul, DirectSum.smul_apply,
      Submodule.coe_smul, RingHom.id_apply]

theorem projection_self (G : TauCeti.InternalGrading K M ℕ) {d : ℕ} {x : M}
    (hx : x ∈ G.piece d) : projection G d x = x :=
  DirectSum.decompose_of_mem_same G.piece hx

theorem projection_zero (G : TauCeti.InternalGrading K M ℕ) {d e : ℕ} {x : M}
    (hx : x ∈ G.piece e) (hed : e ≠ d) : projection G d x = 0 :=
  DirectSum.decompose_of_mem_ne G.piece hx hed

variable (G : TauCeti.InternalGrading K M ℕ) (f : Module.End K M) (d : ℕ)
    (hf : TauCeti.LinearMap.IsHomogeneous f G.piece G.piece d)

include hf in
/-- An image under a degree-`d` map has no homogeneous component below `d`. -/
theorem projection_image_eq_zero_of_lt (e : ℕ) (he : e < d) (x : M) :
    projection G e (f x) = 0 := by
  have h : (projection G e).comp f = 0 := by
    apply G.linearMap_ext
    intro p y hy
    change projection G e (f y) = 0
    have hyf : f y ∈ G.piece (p + d) := hf.map_mem hy
    exact projection_zero G hyf (by omega)
  exact LinearMap.congr_fun h x

include hf in
/-- The image in degree `e ≥ d` comes exactly from degree `e-d`. -/
theorem image_piece_eq_range_inf (e : ℕ) (he : d ≤ e) :
    (G.piece (e - d)).map f = LinearMap.range f ⊓ G.piece e := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    change f x∈G.piece e
    simpa only [Nat.sub_add_cancel he] using hf.map_mem hx
  · rintro y ⟨⟨x, hxy⟩, hy⟩
    refine ⟨(DirectSum.decompose G.piece x (e - d) : M),
      (DirectSum.decompose G.piece x (e - d)).property, ?_⟩
    have h := hf.map_decompose (e - d) x
    rw [Nat.sub_add_cancel he, hxy, DirectSum.decompose_of_mem_same G.piece hy] at h
    exact h

include hf in
theorem range_inf_piece_eq_bot_of_lt (e : ℕ) (he : e < d) :
    LinearMap.range f ⊓ G.piece e = ⊥ := by
  apply eq_bot_iff.mpr
  rintro y ⟨⟨x, hxy⟩, hy⟩
  change y = 0
  rw [← projection_self G hy, ← hxy]
  exact projection_image_eq_zero_of_lt G f d hf e he x

/-- The quotient carries precisely the grading by images of the old pieces. -/
def cokernelGrading : TauCeti.InternalGrading K (M ⧸ LinearMap.range f) ℕ :=
  G.quotient (LinearMap.range f) hf.isHomogeneous_range

@[simp] theorem cokernelGrading_piece (e : ℕ) :
    (cokernelGrading G f d hf).piece e = (G.piece e).map (LinearMap.range f).mkQ := by
  simp only [cokernelGrading, TauCeti.InternalGrading.quotient_piece,
    LinearMap.restrictScalars_self]

theorem cokernel_piece_finite (hfinite : ∀ e, Module.Finite K (G.piece e)) (e : ℕ) :
    Module.Finite K ((cokernelGrading G f d hf).piece e) := by
  letI := hfinite e
  rw [cokernelGrading_piece]
  infer_instance

/-- Rank-nullity on the literal homogeneous quotient map. -/
theorem piece_dimension_add_range_intersection
    (hfinite : ∀ e, Module.Finite K (G.piece e)) (e : ℕ) :
    Module.finrank K (G.piece e) =
      Module.finrank K ((cokernelGrading G f d hf).piece e) +
      Module.finrank K ↥(LinearMap.range f ⊓ G.piece e) := by
  let P := G.piece e
  let q := (LinearMap.range f).mkQ.domRestrict P
  letI := hfinite e
  have hrange : LinearMap.range q = (cokernelGrading G f d hf).piece e := by
    rw [cokernelGrading_piece]
    dsimp only [q, LinearMap.domRestrict, P]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hkernel : (LinearMap.ker q).map P.subtype = LinearMap.range f ⊓ P := by
    dsimp only [q, LinearMap.domRestrict]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ,
      Submodule.map_comap_subtype, inf_comm]
  have h := q.finrank_range_add_finrank_ker
  rw [hrange, ← Submodule.finrank_map_subtype_eq P (LinearMap.ker q), hkernel] at h
  exact h.symm

/-- The complete coefficient recurrence for a homogeneous injective map. -/
theorem regular_map_hilbert_recurrence
    (hfinite : ∀ e, Module.Finite K (G.piece e)) (hinj : Function.Injective f) (e : ℕ) :
    Module.finrank K (G.piece e) =
      Module.finrank K ((cokernelGrading G f d hf).piece e) +
      if d ≤ e then Module.finrank K (G.piece (e - d)) else 0 := by
  have h := piece_dimension_add_range_intersection G f d hf hfinite e
  by_cases he : d ≤ e
  · rw [if_pos he]
    have hmap : Module.finrank K ((G.piece (e - d)).map f) =
        Module.finrank K (G.piece (e - d)) :=
      (Submodule.equivMapOfInjective f hinj (G.piece (e - d))).finrank_eq.symm
    rw [← image_piece_eq_range_inf G f d hf e he, hmap] at h
    exact h
  · rw [if_neg he]
    rw [range_inf_piece_eq_bot_of_lt G f d hf e (Nat.lt_of_not_ge he),
      finrank_bot] at h
    exact h

/-- Hilbert series of the actual graded pieces, with integer coefficients. -/
def series (G : TauCeti.InternalGrading K M ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun e ↦ (Module.finrank K (G.piece e) : ℤ)

@[simp] theorem coeff_series (e : ℕ) :
    PowerSeries.coeff e (series G) = (Module.finrank K (G.piece e) : ℤ) :=
  PowerSeries.coeff_mk _ _

/-- Quotienting by an actual homogeneous regular map multiplies the Hilbert
series by `1-X^d`. Finite dimensionality is proved/assumed only for each
actual homogeneous component, so no infinite component is interpreted as zero. -/
theorem regular_map_hilbert_series
    (hfinite : ∀ e, Module.Finite K (G.piece e)) (hinj : Function.Injective f) :
    series (cokernelGrading G f d hf) = (1 - PowerSeries.X ^ d) * series G := by
  ext e
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  have h := congrArg (fun z : ℕ ↦ (z : ℤ))
    (regular_map_hilbert_recurrence G f d hf hfinite hinj e)
  by_cases he : d ≤ e
  · simp only [if_pos he, Nat.cast_add, coeff_series] at h ⊢
    omega
  · simp only [if_neg he, add_zero, sub_zero, coeff_series] at h ⊢
    exact h.symm

section ExactSequence

variable {N : Type*} [AddCommGroup N] [Module K N]
variable (H : TauCeti.InternalGrading K N ℕ) (q : M →ₗ[K] N)
variable (hq : TauCeti.LinearMap.IsHomogeneous q G.piece H.piece 0)

include hq in
/-- A surjective degree-zero map is surjective on each actual homogeneous
component. The preimage is obtained by projecting any preimage. -/
theorem homogeneous_surjection_piece (hsurj : Function.Surjective q) (e : ℕ) :
    (G.piece e).map q = H.piece e := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    simpa only [add_zero] using hq.map_mem hx
  · intro y hy
    obtain ⟨x, hxy⟩ := hsurj y
    refine ⟨(DirectSum.decompose G.piece x e : M),
      (DirectSum.decompose G.piece x e).property, ?_⟩
    have h := hq.map_decompose e x
    rw [add_zero, hxy, DirectSum.decompose_of_mem_same H.piece hy] at h
    exact h

include hq in
theorem homogeneous_surjection_piece_finite
    (hfinite : ∀ e, Module.Finite K (G.piece e))
    (hsurj : Function.Surjective q) (e : ℕ) : Module.Finite K (H.piece e) := by
  letI := hfinite e
  rw [← homogeneous_surjection_piece G H q hq hsurj e]
  infer_instance

include hq in
/-- Degreewise rank-nullity for a homogeneous quotient map, stated without
choosing a presentation of its target as a quotient type. -/
theorem surjection_piece_dimension_add_kernel_intersection
    (hfinite : ∀ e, Module.Finite K (G.piece e))
    (hsurj : Function.Surjective q) (e : ℕ) :
    Module.finrank K (G.piece e) = Module.finrank K (H.piece e) +
      Module.finrank K ↥(LinearMap.ker q ⊓ G.piece e) := by
  let P := G.piece e
  let qe := q.domRestrict P
  letI := hfinite e
  have hrange : LinearMap.range qe = H.piece e := by
    dsimp only [qe, LinearMap.domRestrict, P]
    rw [LinearMap.range_comp, Submodule.range_subtype,
      homogeneous_surjection_piece G H q hq hsurj e]
  have hkernel : (LinearMap.ker qe).map P.subtype = LinearMap.ker q ⊓ P := by
    dsimp only [qe, LinearMap.domRestrict]
    rw [LinearMap.ker_comp, Submodule.map_comap_subtype, inf_comm]
  have h := qe.finrank_range_add_finrank_ker
  rw [hrange, ← Submodule.finrank_map_subtype_eq P (LinearMap.ker qe), hkernel] at h
  exact h.symm

include hf hq in
/-- A genuine exact homogeneous sequence has the expected Hilbert recurrence.
Both injectivity and the literal equality of image with kernel are proved by
the caller; no dimension or Hilbert assertion is assumed. -/
theorem exact_hilbert_recurrence
    (hfinite : ∀ e, Module.Finite K (G.piece e))
    (hinj : Function.Injective f) (hsurj : Function.Surjective q)
    (hexact : LinearMap.ker q = LinearMap.range f) (e : ℕ) :
    Module.finrank K (G.piece e) = Module.finrank K (H.piece e) +
      if d ≤ e then Module.finrank K (G.piece (e - d)) else 0 := by
  have h := surjection_piece_dimension_add_kernel_intersection G H q hq hfinite hsurj e
  rw [hexact] at h
  by_cases he : d ≤ e
  · rw [if_pos he]
    have hmap : Module.finrank K ((G.piece (e - d)).map f) =
        Module.finrank K (G.piece (e - d)) :=
      (Submodule.equivMapOfInjective f hinj (G.piece (e - d))).finrank_eq.symm
    rw [← image_piece_eq_range_inf G f d hf e he, hmap] at h
    exact h
  · rw [if_neg he]
    rw [range_inf_piece_eq_bot_of_lt G f d hf e (Nat.lt_of_not_ge he),
      finrank_bot] at h
    exact h

include hf hq in
/-- The Hilbert series identity for an actual homogeneous regular quotient.
This version applies directly to successive ideals inside one polynomial ring. -/
theorem exact_hilbert_series
    (hfinite : ∀ e, Module.Finite K (G.piece e))
    (hinj : Function.Injective f) (hsurj : Function.Surjective q)
    (hexact : LinearMap.ker q = LinearMap.range f) :
    series H = (1 - PowerSeries.X ^ d) * series G := by
  ext e
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  have h := congrArg (fun z : ℕ ↦ (z : ℤ))
    (exact_hilbert_recurrence G f d hf H q hq hfinite hinj hsurj hexact e)
  by_cases he : d ≤ e
  · simp only [if_pos he, Nat.cast_add, coeff_series] at h ⊢
    omega
  · simp only [if_neg he, add_zero, sub_zero, coeff_series] at h ⊢
    exact h.symm

end ExactSequence

end PaperVerification.GradedHilbert
