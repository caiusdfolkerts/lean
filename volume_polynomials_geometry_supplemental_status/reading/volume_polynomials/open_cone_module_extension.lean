module

public import VolumePolynomials.OpenConeExtension
public import Mathlib.LinearAlgebra.Multilinear.Curry

@[expose] public section
set_option autoImplicit false

/-! # Linear extension from an open cone with an arbitrary module as target

The target needs no topology. This permits finite multilinear maps to be
constructed one argument at a time, without analytic or infinite-dimensional
extension theorems.
-/

noncomputable section
open Set

namespace VolumePolynomials.OpenConeModuleExtension

open OpenConeExtension

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup W] [Module ℝ W]
  (C : ConvexCone ℝ V) (hopen : IsOpen (C : Set V)) (hne : (C : Set V).Nonempty)

def AdditiveOn (f : V → W) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, f (a + b) = f a + f b

def PositiveHomogeneousOn (f : V → W) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x ∈ C, f (r • x) = r • f x

def extension (f : V → W) (x : V) : W :=
  f (positivePart C hopen hne x) - f (negativePart C hopen hne x)

theorem extension_sub (f : V → W) (hf : AdditiveOn C f)
    {a b : V} (ha : a ∈ C) (hb : b ∈ C) :
    extension C hopen hne f (a - b) = f a - f b := by
  first
  | let p := positivePart C hopen hne (a - b)
    let q := negativePart C hopen hne (a - b)
    have hp : p ∈ C := positivePart_mem C hopen hne _
    have hq : q ∈ C := negativePart_mem C hopen hne _
    have he : p - q = a - b := positivePart_sub_negativePart C hopen hne _
    have hadd : p + b = a + q := sub_eq_sub_iff_add_eq_add.mp he
    have hval := congrArg f hadd
    rw [hf p hp b hb, hf a ha q hq] at hval
    exact sub_eq_sub_iff_add_eq_add.mpr hval

theorem extension_eq (f : V → W) (hf : AdditiveOn C f) {x : V} (hx : x ∈ C) :
    extension C hopen hne f x = f x := by
  first
  | let p : V := Classical.choose hne
    have hp : p ∈ C := Classical.choose_spec hne
    have he := extension_sub C hopen hne f hf (C.add_mem hx hp) hp
    rw [add_sub_cancel_right, hf x hx p hp] at he
    simpa only [add_sub_cancel_right] using he

theorem extension_zero (f : V → W) (hf : AdditiveOn C f) :
    extension C hopen hne f 0 = 0 := by
  first
  | let p : V := Classical.choose hne
    have hp : p ∈ C := Classical.choose_spec hne
    simpa only [sub_self] using extension_sub C hopen hne f hf hp hp

theorem extension_add (f : V → W) (hf : AdditiveOn C f) (x y : V) :
    extension C hopen hne f (x + y) =
      extension C hopen hne f x + extension C hopen hne f y := by
  first
  | obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
    obtain ⟨c, hc, d, hd, rfl⟩ := exists_difference C hopen hne y
    rw [extension_sub C hopen hne f hf ha hb, extension_sub C hopen hne f hf hc hd,
      show (a - b) + (c - d) = (a + c) - (b + d) by abel,
      extension_sub C hopen hne f hf (C.add_mem ha hc) (C.add_mem hb hd),
      hf a ha c hc, hf b hb d hd]
    abel

theorem extension_smul (f : V → W) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) (r : ℝ) (x : V) :
    extension C hopen hne f (r • x) = r • extension C hopen hne f x := by
  first
  | rcases lt_trichotomy r 0 with hr | rfl | hr
    · have hpos : 0 < -r := neg_pos.mpr hr
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
      rw [show r • (a - b) = (-r) • b - (-r) • a by
        rw [neg_smul, neg_smul, neg_sub_neg, smul_sub],
        extension_sub C hopen hne f hf (C.smul_mem hpos hb) (C.smul_mem hpos ha),
        hh (-r) hpos b hb, hh (-r) hpos a ha,
        extension_sub C hopen hne f hf ha hb,
        neg_smul, neg_smul, neg_sub_neg, smul_sub]
    · rw [zero_smul, extension_zero C hopen hne f hf, zero_smul]
    · obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
      rw [smul_sub, extension_sub C hopen hne f hf (C.smul_mem hr ha) (C.smul_mem hr hb),
        hh r hr a ha, hh r hr b hb, extension_sub C hopen hne f hf ha hb, smul_sub]

def linearExtension (f : V → W) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) : V →ₗ[ℝ] W where
  toFun := extension C hopen hne f
  map_add' := extension_add C hopen hne f hf
  map_smul' := extension_smul C hopen hne f hf hh

theorem linearExtension_eq (f : V → W) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) {x : V} (hx : x ∈ C) :
    linearExtension C hopen hne f hf hh x = f x := extension_eq C hopen hne f hf hx

include hopen hne in
theorem linearMap_ext_of_eq_on_cone {F G : V →ₗ[ℝ] W}
    (hFG : ∀ x ∈ C, F x = G x) : F = G := by
  first
  | ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
    rw [map_sub, map_sub, hFG a ha, hFG b hb]

include hopen hne in
/-- Agreement on all genuine cone tuples determines a multilinear map on the
entire vector space. -/
theorem multilinearMap_ext_of_eq_on_cone {n : ℕ}
    {F G : MultilinearMap ℝ (fun _ : Fin n => V) W}
    (hFG : ∀ x : Fin n → V, (∀ i, x i ∈ C) → F x = G x) : F = G := by
  first
  | induction n with
    | zero =>
        ext x
        exact hFG x (fun i => Fin.elim0 i)
    | succ n ih =>
        have he : F.curryLeft = G.curryLeft := by
          apply linearMap_ext_of_eq_on_cone C hopen hne
          intro a ha
          apply ih
          intro x hx
          exact hFG (Fin.cons a x) (fun i => Fin.cases ha hx i)
        ext x
        have he' := congrArg
          (fun T : V →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => V) W =>
            T (x 0) (Fin.tail x)) he
        simpa only [MultilinearMap.curryLeft_apply, Fin.cons_self_tail] using he'

end VolumePolynomials.OpenConeModuleExtension
