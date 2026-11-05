module

public import Mathlib.Geometry.Convex.Cone.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false

/-!
# Extending additive functionals from a nonempty open convex cone

Every vector is an actual difference of two cone elements. Additivity makes
the difference of functional values independent of the representation. The
construction extends linear and bilinear mixed-support functionals to all
real support vectors, including directions that are not support functions.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace VolumePolynomials.OpenConeExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (C : ConvexCone ℝ V) (hopen : IsOpen (C : Set V)) (hne : (C : Set V).Nonempty)

include hopen in
theorem exists_pos_sub_mem {h : V} (hh : h ∈ C) (x : V) :
    ∃ ε : ℝ, 0 < ε ∧ h - ε • x ∈ C := by
  first
  | have ht : Tendsto (fun t : ℝ => h - t • x) (𝓝 0) (𝓝 h) := by
      first
      | have hc : Continuous (fun t : ℝ => h - t • x) := by fun_prop
        simpa only [zero_smul, sub_zero] using
          hc.tendsto (0 : ℝ)
    obtain ⟨r, hr, hs⟩ := Metric.eventually_nhds_iff.mp
      (ht.eventually (hopen.mem_nhds hh))
    refine ⟨r / 2, half_pos hr, hs ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith

include hopen in
theorem exists_pos_sub_all {κ : Type*} [Finite κ]
    (h : κ → V) (hh : ∀ i, h i ∈ C) (x : V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, h i - ε • x ∈ C := by
  first
  | have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, h i - t • x ∈ C := by
      first
      | apply Filter.eventually_all.mpr
        intro i
        have ht : Tendsto (fun t : ℝ => h i - t • x) (𝓝 0) (𝓝 (h i)) := by
          have hc : Continuous (fun t : ℝ => h i - t • x) := by fun_prop
          simpa only [zero_smul, sub_zero] using
            hc.tendsto (0 : ℝ)
        exact ht.eventually (hopen.mem_nhds (hh i))
    obtain ⟨r, hr, hs⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨r / 2, half_pos hr, hs ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith

include hopen hne in
theorem exists_difference (x : V) : ∃ a ∈ C, ∃ b ∈ C, a - b = x := by
  first
  | obtain ⟨p, hp⟩ := hne
    have ht : Tendsto (fun t : ℝ => p + t • x) (𝓝 0) (𝓝 p) := by
      first
      | have hc : Continuous (fun t : ℝ => p + t • x) := by fun_prop
        simpa only [zero_smul, add_zero] using
          hc.tendsto (0 : ℝ)
    obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp (ht.eventually (hopen.mem_nhds hp))
    have heps : dist (ε / 2) 0 < ε := by
      first
      | rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
        linarith
    refine ⟨(ε / 2)⁻¹ • (p + (ε / 2) • x),
      C.smul_mem (inv_pos.mpr (half_pos hε)) (hsmall heps),
      (ε / 2)⁻¹ • p, C.smul_mem (inv_pos.mpr (half_pos hε)) hp, ?_⟩
    rw [smul_add, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ (half_pos hε).ne', one_smul]

def positivePart (x : V) : V := Classical.choose (exists_difference C hopen hne x)

def negativePart (x : V) : V :=
  Classical.choose (Classical.choose_spec (exists_difference C hopen hne x)).2

theorem positivePart_mem (x : V) : positivePart C hopen hne x ∈ C :=
  (Classical.choose_spec (exists_difference C hopen hne x)).1

theorem negativePart_mem (x : V) : negativePart C hopen hne x ∈ C :=
  (Classical.choose_spec (Classical.choose_spec (exists_difference C hopen hne x)).2).1

theorem positivePart_sub_negativePart (x : V) :
    positivePart C hopen hne x - negativePart C hopen hne x = x :=
  (Classical.choose_spec (Classical.choose_spec (exists_difference C hopen hne x)).2).2

/-- This operation is defined for every function. Its linearity in the
function is unconditional; linearity in the vector will use cone additivity. -/
def extension (f : V → ℝ) (x : V) : ℝ :=
  f (positivePart C hopen hne x) - f (negativePart C hopen hne x)

theorem extension_add_function (f g : V → ℝ) (x : V) :
    extension C hopen hne (fun y => f y + g y) x =
      extension C hopen hne f x + extension C hopen hne g x := by
  first
  | unfold extension
    ring

theorem extension_smul_function (r : ℝ) (f : V → ℝ) (x : V) :
    extension C hopen hne (fun y => r * f y) x = r * extension C hopen hne f x := by
  first
  | unfold extension
    ring

theorem extension_congr {f g : V → ℝ} (hfg : ∀ x ∈ C, f x = g x) (x : V) :
    extension C hopen hne f x = extension C hopen hne g x := by
  first
  | rw [extension, extension, hfg _ (positivePart_mem C hopen hne x),
      hfg _ (negativePart_mem C hopen hne x)]

def AdditiveOn (f : V → ℝ) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, f (a + b) = f a + f b

def PositiveHomogeneousOn (f : V → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x ∈ C, f (r • x) = r * f x

theorem extension_sub (f : V → ℝ) (hf : AdditiveOn C f)
    {a b : V} (ha : a ∈ C) (hb : b ∈ C) :
    extension C hopen hne f (a - b) = f a - f b := by
  first
  | let p := positivePart C hopen hne (a - b)
    let q := negativePart C hopen hne (a - b)
    have hp : p ∈ C := positivePart_mem C hopen hne _
    have hq : q ∈ C := negativePart_mem C hopen hne _
    have he : p - q = a - b := positivePart_sub_negativePart C hopen hne _
    have hadd : p + b = a + q := by
      first
      | have := sub_eq_sub_iff_add_eq_add.mp he
        simpa only [add_comm, add_left_comm, add_assoc] using this
    have hval := congrArg f hadd
    rw [hf p hp b hb, hf a ha q hq] at hval
    change f p - f q = f a - f b
    linarith

theorem extension_eq (f : V → ℝ) (hf : AdditiveOn C f) {x : V} (hx : x ∈ C) :
    extension C hopen hne f x = f x := by
  first
  | let p : V := Classical.choose hne
    have hp : p ∈ C := Classical.choose_spec hne
    have he := extension_sub C hopen hne f hf (C.add_mem hx hp) hp
    rw [add_sub_cancel_right, hf x hx p hp] at he
    simpa only [add_sub_cancel_right] using he

theorem extension_zero (f : V → ℝ) (hf : AdditiveOn C f) :
    extension C hopen hne f 0 = 0 := by
  first
  | let p : V := Classical.choose hne
    have hp : p ∈ C := Classical.choose_spec hne
    simpa only [sub_self] using extension_sub C hopen hne f hf hp hp

theorem extension_add (f : V → ℝ) (hf : AdditiveOn C f) (x y : V) :
    extension C hopen hne f (x + y) =
      extension C hopen hne f x + extension C hopen hne f y := by
  first
  | obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
    obtain ⟨c, hc, d, hd, rfl⟩ := exists_difference C hopen hne y
    rw [extension_sub C hopen hne f hf ha hb, extension_sub C hopen hne f hf hc hd,
      show (a - b) + (c - d) = (a + c) - (b + d) by abel,
      extension_sub C hopen hne f hf (C.add_mem ha hc) (C.add_mem hb hd),
      hf a ha c hc, hf b hb d hd]
    ring

theorem extension_neg (f : V → ℝ) (hf : AdditiveOn C f) (x : V) :
    extension C hopen hne f (-x) = -extension C hopen hne f x := by
  first
  | have he := extension_add C hopen hne f hf x (-x)
    rw [add_neg_cancel, extension_zero C hopen hne f hf] at he
    linarith

theorem extension_smul (f : V → ℝ) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) (r : ℝ) (x : V) :
    extension C hopen hne f (r • x) = r * extension C hopen hne f x := by
  first
  | rcases lt_trichotomy r 0 with hr | rfl | hr
    · have hpos : 0 < -r := neg_pos.mpr hr
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
      rw [show r • (a - b) = (-r) • b - (-r) • a by
        rw [neg_smul, neg_smul, neg_sub_neg, smul_sub],
        extension_sub C hopen hne f hf (C.smul_mem hpos hb) (C.smul_mem hpos ha),
        hh (-r) hpos b hb, hh (-r) hpos a ha,
        extension_sub C hopen hne f hf ha hb]
      ring
    · rw [zero_smul, extension_zero C hopen hne f hf, zero_mul]
    · obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
      rw [smul_sub, extension_sub C hopen hne f hf (C.smul_mem hr ha) (C.smul_mem hr hb),
        hh r hr a ha, hh r hr b hb, extension_sub C hopen hne f hf ha hb]
      ring

def linearExtension (f : V → ℝ) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) : V →ₗ[ℝ] ℝ where
  toFun := extension C hopen hne f
  map_add' := extension_add C hopen hne f hf
  map_smul' := extension_smul C hopen hne f hf hh

theorem linearExtension_eq (f : V → ℝ) (hf : AdditiveOn C f)
    (hh : PositiveHomogeneousOn C f) {x : V} (hx : x ∈ C) :
    linearExtension C hopen hne f hf hh x = f x := extension_eq C hopen hne f hf hx

include hopen hne in
theorem linearMap_ext_of_eq_on_cone {F G : V →ₗ[ℝ] ℝ}
    (hFG : ∀ x ∈ C, F x = G x) : F = G := by
  first
  | ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_difference C hopen hne x
    rw [map_sub, map_sub, hFG a ha, hFG b hb]

/-- The two-variable extension is the actual four-term polarization of pairs
of cone elements. -/
def bilinearExtensionValue (f : V → V → ℝ) (x y : V) : ℝ :=
  extension C hopen hne (fun a => extension C hopen hne (f a) y) x

theorem bilinearExtensionValue_add_function (f g : V → V → ℝ) (x y : V) :
    bilinearExtensionValue C hopen hne (fun a b => f a b + g a b) x y =
      bilinearExtensionValue C hopen hne f x y + bilinearExtensionValue C hopen hne g x y := by
  first
  | simp only [bilinearExtensionValue, extension_add_function]

theorem bilinearExtensionValue_smul_function (r : ℝ) (f : V → V → ℝ) (x y : V) :
    bilinearExtensionValue C hopen hne (fun a b => r * f a b) x y =
      r * bilinearExtensionValue C hopen hne f x y := by
  first
  | simp only [bilinearExtensionValue, extension_smul_function]

include hopen in
theorem bilinear_reference_inequality_of_cone
    (B : LinearMap.BilinForm ℝ V) (hsym : ∀ x y, B x y = B y x)
    {h : V} (hh : h ∈ C)
    (hineq : ∀ y ∈ C, B y y * B h h ≤ B y h ^ 2) (x : V) :
    B x x * B h h ≤ B x h ^ 2 := by
  first
  | obtain ⟨ε, hε, hy⟩ := exists_pos_sub_mem C hopen hh (-x)
    rw [smul_neg, sub_neg_eq_add] at hy
    have hi := hineq _ hy
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hsym h x] at hi
    have he : ε ^ 2 * (B x x * B h h - B x h ^ 2) ≤ 0 := by nlinarith
    have he' : ε ^ 2 * (B x x * B h h - B x h ^ 2) ≤ ε ^ 2 * 0 := by
      simpa only [mul_zero] using he
    exact sub_nonpos.mp (Iff.mp (mul_le_mul_iff_right₀ (sq_pos_of_pos hε)) he')

theorem bilinearExtensionValue_symmetric (f : V → V → ℝ)
    (hs : ∀ x ∈ C, ∀ y ∈ C, f x y = f y x) (x y : V) :
    bilinearExtensionValue C hopen hne f x y = bilinearExtensionValue C hopen hne f y x := by
  first
  | unfold bilinearExtensionValue extension
    dsimp only
    rw [hs _ (positivePart_mem C hopen hne x) _ (positivePart_mem C hopen hne y),
      hs _ (positivePart_mem C hopen hne x) _ (negativePart_mem C hopen hne y),
      hs _ (negativePart_mem C hopen hne x) _ (positivePart_mem C hopen hne y),
      hs _ (negativePart_mem C hopen hne x) _ (negativePart_mem C hopen hne y)]
    ring

theorem bilinearExtensionValue_eq (f : V → V → ℝ)
    (ha : ∀ y ∈ C, AdditiveOn C (fun x => f x y))
    (hb : ∀ x ∈ C, AdditiveOn C (f x))
    {x y : V} (hx : x ∈ C) (hy : y ∈ C) :
    bilinearExtensionValue C hopen hne f x y = f x y := by
  first
  | unfold bilinearExtensionValue
    have he : extension C hopen hne (fun a => extension C hopen hne (f a) y) x =
        extension C hopen hne (fun a => f a y) x :=
      extension_congr C hopen hne (fun a ha => extension_eq C hopen hne (f a) (hb a ha) hy) x
    rw [he, extension_eq C hopen hne _ (ha y hy) hx]

def bilinearExtension (f : V → V → ℝ)
    (ha : ∀ y ∈ C, AdditiveOn C (fun x => f x y))
    (hha : ∀ y ∈ C, PositiveHomogeneousOn C (fun x => f x y))
    (hb : ∀ x ∈ C, AdditiveOn C (f x))
    (hhb : ∀ x ∈ C, PositiveHomogeneousOn C (f x)) : LinearMap.BilinForm ℝ V := by
  first
  | let F := bilinearExtensionValue C hopen hne f
    have hleftadd (x z y : V) : F (x + z) y = F x y + F z y := by
      first
      | apply extension_add C hopen hne
        intro a ha' b hb'
        apply Eq.trans (extension_congr C hopen hne
          (fun u hu => ha u hu a ha' b hb') y)
        exact extension_add_function C hopen hne (f a) (f b) y
    have hleftsmul (r : ℝ) (x y : V) : F (r • x) y = r * F x y := by
      first
      | apply extension_smul C hopen hne
        · intro a ha' b hb'
          exact Eq.trans (extension_congr C hopen hne (fun u hu => ha u hu a ha' b hb') y)
            (extension_add_function C hopen hne (f a) (f b) y)
        · intro t ht a ha'
          exact Eq.trans (extension_congr C hopen hne (fun u hu => hha u hu t ht a ha') y)
            (extension_smul_function C hopen hne t (f a) y)
    have hrightadd (x y z : V) : F x (y + z) = F x y + F x z := by
      first
      | exact Eq.trans (extension_congr C hopen hne
          (fun a ha' => extension_add C hopen hne (f a) (hb a ha') y z) x)
            (extension_add_function C hopen hne _ _ x)
    have hrightsmul (r : ℝ) (x y : V) : F x (r • y) = r * F x y := by
      first
      | exact Eq.trans (extension_congr C hopen hne
          (fun a ha' => extension_smul C hopen hne (f a) (hb a ha') (hhb a ha') r y) x)
            (extension_smul_function C hopen hne r _ x)
    exact {
      toFun := fun x => {
        toFun := F x
        map_add' := hrightadd x
        map_smul' := fun r y => hrightsmul r x y
      }
      map_add' := fun x y => LinearMap.ext (hleftadd x y)
      map_smul' := fun r x => LinearMap.ext (hleftsmul r x)
    }

end VolumePolynomials.OpenConeExtension
