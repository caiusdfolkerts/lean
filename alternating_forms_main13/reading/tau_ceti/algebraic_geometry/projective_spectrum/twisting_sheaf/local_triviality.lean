/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic

/-!
# The original local trivializations of Proj twisting sheaves

This component retains the exact chart-generator, section-coordinate and
chart-isomorphism bodies from TauCeti's LocalTriviality module. It omits only
the later global-invertibility corollaries for symmetric algebras, which are
not used by the actual tautological determinant comparison. In particular,
the twisting sheaf remains the original homogeneous-fraction construction.
The retained construction works for every integer twist and arbitrary
commutative coefficient rings, including rings with nilpotents.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

namespace twistingSheaf

variable (n : ℤ) (f : A) (hf : f ∈ 𝒜 1) (U : (Proj 𝒜).Opens)
  (hU : U ≤ basicOpen 𝒜 f)

/-- The standard basis section `fⁿ` of `𝒪(n)` on an open contained in `D₊(f)`, for
a homogeneous element `f` of degree one. -/
def chartGenerator : Γ(twistingSheaf 𝒜 n, U) :=
  const (i := (-n).toNat) (j := n.toNat) (by omega)
    (f ^ n.toNat) (f ^ (-n).toNat)
    (by simpa using SetLike.pow_mem_graded n.toNat hf)
    (by simpa using SetLike.pow_mem_graded (-n).toNat hf) U
    (fun x hx ↦ fun h ↦ hU hx (x.isPrime.mem_of_pow_mem _ h))

/-- The standard basis section is the fraction `f ^ n.toNat / f ^ (-n).toNat`. -/
@[simp]
theorem chartGenerator_apply (x : U) :
    (chartGenerator n f hf U hU).1 x =
      Localization.mk (f ^ n.toNat)
        ⟨f ^ (-n).toNat, fun h ↦ hU x.2 (x.1.isPrime.mem_of_pow_mem _ h)⟩ :=
  (rfl)

/-- The standard basis sections commute with restriction. -/
@[simp]
theorem res_chartGenerator {V : (Proj 𝒜).Opens} (i : V ⟶ U) :
    (twistingSheaf 𝒜 n).presheaf.map i.op (chartGenerator n f hf U hU) =
      chartGenerator n f hf V (i.le.trans hU) :=
  (rfl)

/-- Multiplication of standard basis sections adds their degrees. -/
@[simp↓]
theorem mul_chartGenerator_apply (m : ℤ) (x : U) :
    (mul 𝒜 U m n (chartGenerator m f hf U hU) (chartGenerator n f hf U hU)).1 x =
      (chartGenerator (m + n) f hf U hU).1 x := by
  let := x.1.isPrime
  simp only [mul_apply, chartGenerator_apply, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  -- Here `change` reduces the denominator subtype projections and `Submonoid.mul`,
  -- exposing the cross-multiplied equality in `A` for the exponent calculation.
  change f ^ (-(m + n)).toNat * (f ^ m.toNat * f ^ n.toNat) =
    (f ^ (-m).toNat * f ^ (-n).toNat) * f ^ (m + n).toNat
  simp only [← pow_add]
  congr 1
  omega

/-- The product of the standard basis sections of `𝒪(m)` and `𝒪(n)` is the standard basis
section of `𝒪(m + n)`. -/
@[simp]
theorem mul_chartGenerator (m : ℤ) :
    mul 𝒜 U m n (chartGenerator m f hf U hU) (chartGenerator n f hf U hU) =
      chartGenerator (m + n) f hf U hU :=
  ext fun x ↦ mul_chartGenerator_apply n f hf U hU m x

/-- The standard basis sections in opposite degrees multiply to one in each localization. -/
theorem chartGenerator_apply_mul_chartGenerator_neg_apply (x : U) :
    (chartGenerator n f hf U hU).1 x * (chartGenerator (-n) f hf U hU).1 x = 1 := by
  let := x.1.isPrime
  simp only [chartGenerator_apply, neg_neg]
  rw [Localization.mk_mul, mul_comm (f ^ n.toNat)]
  exact Localization.mk_self
    (⟨f ^ (-n).toNat, fun h ↦ hU x.2 (x.1.isPrime.mem_of_pow_mem _ h)⟩ *
      ⟨f ^ n.toNat, fun h ↦ hU x.2 (x.1.isPrime.mem_of_pow_mem _ h)⟩ :
        x.1.asHomogeneousIdeal.toIdeal.primeCompl)

end twistingSheaf

namespace twistingSheaf

open ProjectiveSpectrum.TwistingSheaf

variable (n : ℤ) (f : A) (hf : f ∈ 𝒜 1) (U : (Proj 𝒜).Opens)
  (hU : U ≤ basicOpen 𝒜 f)

private def chartInverse (s : Γ(twistingSheaf 𝒜 n, U)) : Γ(twistingSheaf 𝒜 0, U) :=
  ⟨s.1 * (chartGenerator (-n) f hf U hU).1, by
    apply (mem_sectionsAddSubgroup_iff _).mpr
    simpa only [add_neg_cancel] using
      isLocallyFraction_mul s.2 (chartGenerator (-n) f hf U hU).2⟩

private theorem chartInverse_apply (s : Γ(twistingSheaf 𝒜 n, U)) (x : U) :
    (chartInverse n f hf U hU s).1 x =
      s.1 x * (chartGenerator (-n) f hf U hU).1 x :=
  (rfl)

/-- Multiplication by `fⁿ` trivializes the sections of `𝒪(n)` on every open contained in
the degree-one chart `D₊(f)`. -/
def chartSectionsLinearEquiv :
    Γ(Proj 𝒜, U) ≃ₗ[Γ(Proj 𝒜, U)] Γ(twistingSheaf 𝒜 n, U) where
  toFun a := a • chartGenerator n f hf U hU
  map_add' a b := add_smul a b _
  map_smul' a b := mul_smul a b _
  invFun s := (sectionsLinearEquivTwistingSheafZero 𝒜 U).symm (chartInverse n f hf U hU s)
  left_inv a := Subtype.ext <| funext fun x ↦ HomogeneousLocalization.val_injective _ <| by
    simp only [sectionsLinearEquivTwistingSheafZero_symm_apply_val U _ x,
      chartInverse_apply n f hf U hU _ x, smul_apply a _ x,
      mul_assoc, chartGenerator_apply_mul_chartGenerator_neg_apply n f hf U hU x, mul_one]
  right_inv s := ext fun x ↦ by
    simp only [smul_apply _ _ x, sectionsLinearEquivTwistingSheafZero_symm_apply_val U _ x,
      chartInverse_apply n f hf U hU s x, mul_assoc,
      mul_comm ((chartGenerator (-n) f hf U hU).1 x),
      chartGenerator_apply_mul_chartGenerator_neg_apply n f hf U hU x, mul_one]

/-- In standard chart coordinates the forward map multiplies by the basis section. -/
theorem chartSectionsLinearEquiv_apply (a : Γ(Proj 𝒜, U)) :
    chartSectionsLinearEquiv n f hf U hU a = a • chartGenerator n f hf U hU :=
  (rfl)

/-- The forward chart coordinate map is multiplication by `fⁿ` in each localization. -/
@[simp]
theorem chartSectionsLinearEquiv_apply_apply (a : Γ(Proj 𝒜, U)) (x : U) :
    (chartSectionsLinearEquiv n f hf U hU a).1 x =
      (a.1 x).val * (chartGenerator n f hf U hU).1 x :=
  (rfl)

/-- The inverse chart coordinate is multiplication by `f⁻ⁿ` in the localizations. -/
@[simp]
theorem chartSectionsLinearEquiv_symm_apply_val (s : Γ(twistingSheaf 𝒜 n, U)) (x : U) :
    (((chartSectionsLinearEquiv n f hf U hU).symm s).1 x).val =
      s.1 x * (chartGenerator (-n) f hf U hU).1 x :=
  sectionsLinearEquivTwistingSheafZero_symm_apply_val _ _ _

/-- The chart coordinate isomorphisms commute with restriction to smaller opens. -/
theorem res_chartSectionsLinearEquiv {V : (Proj 𝒜).Opens} (i : V ⟶ U)
    (a : Γ(Proj 𝒜, U)) :
    (twistingSheaf 𝒜 n).presheaf.map i.op (chartSectionsLinearEquiv n f hf U hU a) =
      chartSectionsLinearEquiv n f hf V (i.le.trans hU) ((Proj 𝒜).presheaf.map i.op a) :=
  (rfl)

/-- The twisting sheaf `𝒪(n)` is trivial on the standard open of a degree-one element,
for every integer `n`. -/
def chartIso :
    SheafOfModules.unit ((Proj 𝒜).ringCatSheaf.over (basicOpen 𝒜 f)) ≅
      (twistingSheaf 𝒜 n).over (basicOpen 𝒜 f) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <| PresheafOfModules.isoMk
    (fun V ↦ (chartSectionsLinearEquiv n f hf V.unop.left V.unop.hom.le).toModuleIso)
    (fun _ _ _ ↦ rfl)

/-- On each smaller open the standard sheaf trivialization is multiplication by `fⁿ`. -/
theorem chartIso_hom_app_apply
    (V : Over (basicOpen 𝒜 f)) (a : Γ(Proj 𝒜, V.left)) :
    (chartIso n f hf).hom.val.app (Opposite.op V) a =
      chartSectionsLinearEquiv n f hf V.left V.hom.le a :=
  (rfl)

/-- The inverse standard sheaf trivialization gives the chart coordinate of a section. -/
theorem chartIso_inv_app_apply
    (V : Over (basicOpen 𝒜 f)) (s : Γ(twistingSheaf 𝒜 n, V.left)) :
    (chartIso n f hf).inv.val.app (Opposite.op V) s =
      (chartSectionsLinearEquiv n f hf V.left V.hom.le).symm s :=
  (rfl)

/-- The standard sheaf trivialization multiplies values by `fⁿ`. -/
@[simp]
theorem chartIso_hom_app_apply_apply
    (V : Over (basicOpen 𝒜 f)) (a : Γ(Proj 𝒜, V.left)) (x : V.left) :
    ((chartIso n f hf).hom.val.app (Opposite.op V) a).1 x =
      (a.1 x).val * (chartGenerator n f hf V.left V.hom.le).1 x :=
  (rfl)

/-- The inverse standard sheaf trivialization multiplies values by `f⁻ⁿ`. -/
@[simp]
theorem chartIso_inv_app_apply_val
    (V : Over (basicOpen 𝒜 f)) (s : Γ(twistingSheaf 𝒜 n, V.left)) (x : V.left) :
    (((chartIso n f hf).inv.val.app (Opposite.op V) s).1 x).val =
      s.1 x * (chartGenerator (-n) f hf V.left V.hom.le).1 x :=
  chartSectionsLinearEquiv_symm_apply_val n f hf V.left V.hom.le s x

end twistingSheaf

end AlgebraicGeometry.Proj

end
end
