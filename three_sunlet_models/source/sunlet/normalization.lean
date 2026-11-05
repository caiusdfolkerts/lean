module

public import sunlet.polynomial_image
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Diagonal and gauge normalization

The normalized coordinates use one diagonal variable per position, two units
per non-base position, and two affine variables per non-identity color.  The
identities in this module are actual identities of the coordinate maps.  They
are preparatory to the localization comparison of their defining ideals.
-/

@[expose] public section
noncomputable section

namespace Sunlet.Normalization

variable {K ι Ω : Type*} [DecidableEq ι]

/-- Normalized parameters, with both unit families fixed to one at the base. -/
structure Parameters (K ι Ω : Type*) [CommRing K] (e : ι) (o : Ω) where
  z : Ω → K
  k : Ω → Kˣ
  l : Ω → Kˣ
  u : {a : ι // a ≠ e} → K
  v : {a : ι // a ≠ e} → K
  k_base : k o = 1
  l_base : l o = 1

section CommutativeRing

variable [CommRing K] {e : ι} {o : Ω}

/-- The identity-color coordinates are the free diagonal coordinates. -/
def coordinate (π : ι → Equiv.Perm Ω) (p : Parameters K ι Ω e o)
    (a : ι) (b : Ω) : K :=
  if ha : a = e then p.z b else
    p.z (π a b) *
      (p.u ⟨a, ha⟩ * (p.k b : K) * ((p.k (π a b))⁻¹ : Kˣ) +
        p.v ⟨a, ha⟩ * (p.l b : K) * ((p.l (π a b))⁻¹ : Kˣ))

def parameterMap (π : ι → Equiv.Perm Ω) (p : Parameters K ι Ω e o)
    (ab : ι × Ω) : K :=
  coordinate π p ab.1 ab.2

/-- Every normalized parameter point has an explicit five-family realization. -/
def expand (p : Parameters K ι Ω e o) : Sunlet.Parameters K ι Ω where
  s b := p.k b
  h b := (p.l b : K) * ((p.k b)⁻¹ : Kˣ)
  t b := p.z b * ((p.l b)⁻¹ : Kˣ)
  u a := if ha : a = e then 1 else p.u ⟨a, ha⟩
  v a := if ha : a = e then 0 else p.v ⟨a, ha⟩

theorem expand_coordinate (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω)
    (p : Parameters K ι Ω e o) (a : ι) (b : Ω) :
    Sunlet.coordinate π (expand p) a b = coordinate π p a b := by
  by_cases ha : a = e
  · subst a
    simp [Sunlet.coordinate, expand, coordinate, he]
    calc
      _ = p.z b * ((p.k b : K) * ((p.k b)⁻¹ : Kˣ)) *
          ((p.l b : K) * ((p.l b)⁻¹ : Kˣ)) := by ring
      _ = _ := by simp
  · simp only [Sunlet.coordinate, expand, coordinate, dite_eq_right ha]
    calc
      _ = p.z (π a b) *
          (p.u ⟨a, ha⟩ * (p.k b : K) *
              ((p.l (π a b) : K) * ((p.l (π a b))⁻¹ : Kˣ)) *
                ((p.k (π a b))⁻¹ : Kˣ) +
            p.v ⟨a, ha⟩ * ((p.k b : K) * ((p.k b)⁻¹ : Kˣ)) *
              (p.l b : K) * ((p.l (π a b))⁻¹ : Kˣ)) := by ring
      _ = _ := by simp

theorem expand_parameterMap (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω)
    (p : Parameters K ι Ω e o) :
    Sunlet.parameterMap π (expand p) = parameterMap π p := by
  funext ab
  exact expand_coordinate π he p ab.1 ab.2

end CommutativeRing

section Field

variable [Field K] {e : ι} {o : Ω}

/-- Normalization is defined on the open set where the required gauges are units. -/
def normalize (p : Sunlet.Parameters K ι Ω)
    (hs : ∀ b, p.s b ≠ 0) (hh : ∀ b, p.h b ≠ 0)
    (_hγ : p.u e + p.v e ≠ 0) : Parameters K ι Ω e o where
  z b := (p.u e + p.v e) * p.s b * p.t b * p.h b
  k b := Units.mk0 (p.s b / p.s o) (div_ne_zero (hs b) (hs o))
  l b := Units.mk0 (p.s b * p.h b / (p.s o * p.h o))
    (div_ne_zero (mul_ne_zero (hs b) (hh b)) (mul_ne_zero (hs o) (hh o)))
  u a := p.u a / (p.u e + p.v e)
  v a := p.v a / (p.u e + p.v e)
  k_base := by ext; simp [hs o]
  l_base := by ext; simp [hs o, hh o]

theorem normalize_coordinate (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω)
    (p : Sunlet.Parameters K ι Ω)
    (hs : ∀ b, p.s b ≠ 0) (hh : ∀ b, p.h b ≠ 0)
    (hγ : p.u e + p.v e ≠ 0) (a : ι) (b : Ω) :
    coordinate π (normalize (o := o) p hs hh hγ) a b = Sunlet.coordinate π p a b := by
  by_cases ha : a = e
  · subst a
    simp only [coordinate, dite_eq_left rfl, normalize, Sunlet.coordinate, he, Equiv.refl_apply]
    ring
  · simp only [coordinate, dite_eq_right ha, normalize, Units.val_mk0, Units.val_inv_eq_inv_val,
      Sunlet.coordinate]
    field_simp [hs o, hs (π a b), hh o, hh (π a b), hγ]

theorem normalize_parameterMap (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω)
    (p : Sunlet.Parameters K ι Ω)
    (hs : ∀ b, p.s b ≠ 0) (hh : ∀ b, p.h b ≠ 0)
    (hγ : p.u e + p.v e ≠ 0) :
    parameterMap π (normalize (o := o) p hs hh hγ) = Sunlet.parameterMap π p := by
  funext ab
  exact normalize_coordinate π he p hs hh hγ ab.1 ab.2

end Field

end Sunlet.Normalization
