module
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import sunlet.group_coordinates
public import sunlet.verified_toric_geometry

@[expose] public section
noncomputable section
set_option Elab.async false

#check "SUNLET_VerifiedFiberGeometry_IMPORTS_READY"

section Stage_NormalizationFibers



/-!
# The three gauge units and the identity-coefficient split

These inverse formulas are valid over every commutative ring, including
rings with nilpotents.  Thus the continuous fiber calculation retains the
algebraic structure that would be lost by a calculation only with complex
closed points.
-/

noncomputable section

namespace Sunlet.NormalizationFibers

variable {R ι Ω : Type*} [CommRing R] [DecidableEq ι]
  (e : ι) (o : Ω)

/-- The original five-family parameter space restricted to the open set
where every diagonal factor and their common coefficient sum are units. -/
@[ext] structure Original where
  s : Ω → Rˣ
  t : Ω → Rˣ
  h : Ω → Rˣ
  u : ι → R
  v : ι → R
  gamma : Rˣ
  gamma_eq : gamma.val = u e + v e

/-- The normalized open parameter space. -/
@[ext] structure Normalized where
  z : Ω → Rˣ
  k : Ω → Rˣ
  l : Ω → Rˣ
  u : {a : ι // a ≠ e} → R
  v : {a : ι // a ≠ e} → R
  k_base : k o = 1
  l_base : l o = 1

@[ext] structure Gauges where
  S : Rˣ
  H : Rˣ
  Gamma : Rˣ
  T : R

def Original.toParameters (p : Original (R := R) (Ω := Ω) e) : Sunlet.Parameters R ι Ω where
  s b := (p.s b).val
  t b := (p.t b).val
  h b := (p.h b).val
  u := p.u
  v := p.v

theorem Original.toParameters_injective :
    Function.Injective (Original.toParameters (R := R) (Ω := Ω) (e := e)) := by
  intro p q h
  apply Original.ext
  · funext b
    apply Units.ext
    exact congrArg (fun r : Sunlet.Parameters R ι Ω => r.s b) h
  · funext b
    apply Units.ext
    exact congrArg (fun r : Sunlet.Parameters R ι Ω => r.t b) h
  · funext b
    apply Units.ext
    exact congrArg (fun r : Sunlet.Parameters R ι Ω => r.h b) h
  · exact congrArg Sunlet.Parameters.u h
  · exact congrArg Sunlet.Parameters.v h
  · apply Units.ext
    rw [p.gamma_eq, q.gamma_eq]
    exact congrArg (fun r : Sunlet.Parameters R ι Ω => r.u e + r.v e) h

def Normalized.toParameters (q : Normalized (R := R) e o) :
    Sunlet.Normalization.Parameters R ι Ω e o where
  z b := (q.z b).val
  k := q.k
  l := q.l
  u := q.u
  v := q.v
  k_base := q.k_base
  l_base := q.l_base

def normalize (p : Original (R := R) (Ω := Ω) e) : Normalized (R := R) e o where
  z b := p.gamma * p.s b * p.t b * p.h b
  k b := p.s b / p.s o
  l b := (p.s b * p.h b) / (p.s o * p.h o)
  u a := p.u a * (p.gamma⁻¹).val
  v a := p.v a * (p.gamma⁻¹).val
  k_base := div_self' _
  l_base := div_self' _

def gauges (p : Original (R := R) (Ω := Ω) e) : Gauges (R := R) where
  S := p.s o
  H := p.h o
  Gamma := p.gamma
  T := p.u e

def expand (q : Normalized (R := R) e o) (g : Gauges (R := R)) :
    Original (R := R) (Ω := Ω) e where
  s b := g.S * q.k b
  h b := g.H * q.l b / q.k b
  t b := q.z b / (g.Gamma * g.S * g.H * q.l b)
  u a := if ha : a = e then g.T else g.Gamma.val * q.u ⟨a, ha⟩
  v a := if ha : a = e then g.Gamma.val - g.T else g.Gamma.val * q.v ⟨a, ha⟩
  gamma := g.Gamma
  gamma_eq := by simp

theorem normalize_expand (q : Normalized (R := R) e o) (g : Gauges (R := R)) :
    normalize e o (expand e o q g) = q := by
  cases q with
  | mk z k l u v hk hl =>
    apply Normalized.ext
    · funext b
      dsimp [normalize, expand]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
      abel
    · funext b
      simp only [normalize, expand, hk, mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
      abel
    · funext b
      simp only [normalize, expand, hk, hl, mul_one, div_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
      abel
    · funext a
      change (if ha : a.val = e then g.T else g.Gamma.val * u ⟨a.val, ha⟩) *
        (g.Gamma⁻¹).val = u a
      rw [dif_neg a.property]
      calc
        (g.Gamma.val * u a) * (g.Gamma⁻¹).val =
            u a * (g.Gamma.val * (g.Gamma⁻¹).val) := by ac_rfl
        _ = u a := by rw [Units.mul_inv, mul_one]
    · funext a
      change (if ha : a.val = e then g.Gamma.val - g.T else g.Gamma.val * v ⟨a.val, ha⟩) *
        (g.Gamma⁻¹).val = v a
      rw [dif_neg a.property]
      calc
        (g.Gamma.val * v a) * (g.Gamma⁻¹).val =
            v a * (g.Gamma.val * (g.Gamma⁻¹).val) := by ac_rfl
        _ = v a := by rw [Units.mul_inv, mul_one]

theorem gauges_expand (q : Normalized (R := R) e o) (g : Gauges (R := R)) :
    gauges e o (expand e o q g) = g := by
  cases g
  simp [gauges, expand, q.k_base, q.l_base]

theorem expand_normalize (p : Original (R := R) (Ω := Ω) e) :
    expand e o (normalize e o p) (gauges e o p) = p := by
  cases p with
  | mk s t h u v gamma hgamma =>
    apply Original.ext
    · funext b
      dsimp [expand, normalize, gauges]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
      abel
    · funext b
      dsimp [expand, normalize, gauges]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
      abel
    · funext b
      dsimp [expand, normalize, gauges]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
      abel
    · funext a
      by_cases ha : a = e
      · subst a
        simp [expand, normalize, gauges]
      · simp only [expand, normalize, gauges, dif_neg ha]
        calc
          gamma.val * (u a * (gamma⁻¹).val) =
              u a * (gamma.val * (gamma⁻¹).val) := by ac_rfl
          _ = u a := by rw [Units.mul_inv, mul_one]
    · funext a
      by_cases ha : a = e
      · subst a
        simp [expand, normalize, gauges, hgamma]
      · simp only [expand, normalize, gauges, dif_neg ha]
        calc
          gamma.val * (v a * (gamma⁻¹).val) =
              v a * (gamma.val * (gamma⁻¹).val) := by ac_rfl
          _ = v a := by rw [Units.mul_inv, mul_one]
    · rfl

/-- The actual inverse parameter formulas, with the three independent
unit gauges and the unrestricted affine identity split. -/
def normalizationEquiv : Original (R := R) (Ω := Ω) e ≃
    Normalized (R := R) e o × Gauges (R := R) where
  toFun p := (normalize e o p, gauges e o p)
  invFun qg := expand e o qg.1 qg.2
  left_inv := expand_normalize e o
  right_inv qg := Prod.ext (normalize_expand e o qg.1 qg.2)
    (gauges_expand e o qg.1 qg.2)

section Naturality

variable {R' : Type*} [CommRing R']

def Original.map (f : R →+* R') (p : Original (R := R) (Ω := Ω) e) : Original (R := R') (Ω := Ω) e where
  s b := Units.map f.toMonoidHom (p.s b)
  t b := Units.map f.toMonoidHom (p.t b)
  h b := Units.map f.toMonoidHom (p.h b)
  u a := f (p.u a)
  v a := f (p.v a)
  gamma := Units.map f.toMonoidHom p.gamma
  gamma_eq := by simpa using congrArg f p.gamma_eq

def Normalized.map (f : R →+* R') (q : Normalized (R := R) e o) :
    Normalized (R := R') e o where
  z b := Units.map f.toMonoidHom (q.z b)
  k b := Units.map f.toMonoidHom (q.k b)
  l b := Units.map f.toMonoidHom (q.l b)
  u a := f (q.u a)
  v a := f (q.v a)
  k_base := by simp [q.k_base]
  l_base := by simp [q.l_base]

def Gauges.map (f : R →+* R') (g : Gauges (R := R)) : Gauges (R := R') where
  S := Units.map f.toMonoidHom g.S
  H := Units.map f.toMonoidHom g.H
  Gamma := Units.map f.toMonoidHom g.Gamma
  T := f g.T

theorem normalize_map (f : R →+* R') (p : Original (R := R) (Ω := Ω) e) :
    normalize e o (Original.map e f p) = Normalized.map e o f (normalize e o p) := by
  apply Normalized.ext <;> funext a <;> simp [normalize, Original.map, Normalized.map]

theorem gauges_map (f : R →+* R') (p : Original (R := R) (Ω := Ω) e) :
    gauges e o (Original.map e f p) = Gauges.map f (gauges e o p) := rfl

theorem expand_map (f : R →+* R') (q : Normalized (R := R) e o) (g : Gauges (R := R)) :
    expand e o (Normalized.map e o f q) (Gauges.map f g) =
      Original.map e f (expand e o q g) := by
  apply Original.ext
  · funext b
    simp [expand, Original.map, Normalized.map, Gauges.map]
  · funext b
    simp [expand, Original.map, Normalized.map, Gauges.map]
  · funext b
    simp [expand, Original.map, Normalized.map, Gauges.map]
  · funext a
    by_cases ha : a = e <;>
      simp [expand, Original.map, Normalized.map, Gauges.map, ha]
  · funext a
    by_cases ha : a = e <;>
      simp [expand, Original.map, Normalized.map, Gauges.map, ha]
  · rfl

end Naturality

end Sunlet.NormalizationFibers
end
end Stage_NormalizationFibers

#check "SUNLET_NormalizationFibers_READY"

section Stage_FiberNormalization



/-!
# Normalization on the entire affine fiber

The formulas are valid over arbitrary commutative rings.  In particular they
retain infinitesimal points.  Nonzero diagonal coordinates over a field, or
unit diagonal coordinates over a ring, force all denominators to be units.
No original affine parameter is excluded by an additional torus hypothesis.
-/

noncomputable section

namespace Sunlet.NormalizationFibers

variable {R ι Ω : Type*} [CommRing R] [DecidableEq ι]
  (e : ι) (o : Ω) (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω)

include he in
theorem identity_coordinate (p : Sunlet.Parameters R ι Ω) (b : Ω) :
    Sunlet.parameterMap π p (e, b) = (p.u e + p.v e) * p.s b * p.t b * p.h b := by
  simp only [Sunlet.parameterMap, Sunlet.coordinate, he, Equiv.refl_apply]
  ring

include o he in
theorem diagonal_units (p : Sunlet.Parameters R ι Ω)
    (hd : ∀ b, IsUnit (Sunlet.parameterMap π p (e, b))) :
    IsUnit (p.u e + p.v e) ∧ (∀ b, IsUnit (p.s b)) ∧
      (∀ b, IsUnit (p.t b)) ∧ (∀ b, IsUnit (p.h b)) := by
  have h (b : Ω) : IsUnit (p.u e + p.v e) ∧ IsUnit (p.s b) ∧
      IsUnit (p.t b) ∧ IsUnit (p.h b) := by
    have hb := hd b
    rw [identity_coordinate e π he p b] at hb
    simpa only [IsUnit.mul_iff, and_assoc] using hb
  exact ⟨(h o).1, fun b => (h b).2.1, fun b => (h b).2.2.1,
    fun b => (h b).2.2.2⟩

def ofDiagonalUnits (p : Sunlet.Parameters R ι Ω)
    (hd : ∀ b, IsUnit (Sunlet.parameterMap π p (e, b))) : Original (R := R) (Ω := Ω) e where
  s b := ((diagonal_units e o π he p hd).2.1 b).unit
  t b := ((diagonal_units e o π he p hd).2.2.1 b).unit
  h b := ((diagonal_units e o π he p hd).2.2.2 b).unit
  u := p.u
  v := p.v
  gamma := (diagonal_units e o π he p hd).1.unit
  gamma_eq := IsUnit.unit_spec _

@[simp] theorem ofDiagonalUnits_toParameters (p : Sunlet.Parameters R ι Ω)
    (hd : ∀ b, IsUnit (Sunlet.parameterMap π p (e, b))) :
    (ofDiagonalUnits e o π he p hd).toParameters = p := by
  cases p
  simp [ofDiagonalUnits, Original.toParameters, IsUnit.unit_spec]

include he in
theorem Original.diagonal_isUnit (p : Original (R := R) (Ω := Ω) e) (b : Ω) :
    IsUnit (Sunlet.parameterMap π p.toParameters (e, b)) := by
  rw [identity_coordinate e π he]
  change IsUnit ((p.u e + p.v e) * (p.s b).val * (p.t b).val * (p.h b).val)
  rw [← p.gamma_eq]
  exact (((p.gamma.isUnit.mul (p.s b).isUnit).mul (p.t b).isUnit).mul (p.h b).isUnit)

@[simp] theorem ofDiagonalUnits_original (p : Original (R := R) (Ω := Ω) e) :
    ofDiagonalUnits e o π he p.toParameters (p.diagonal_isUnit e π he) = p := by
  apply Original.ext
  · funext b; apply Units.ext; simp [ofDiagonalUnits, Original.toParameters]
  · funext b; apply Units.ext; simp [ofDiagonalUnits, Original.toParameters]
  · funext b; apply Units.ext; simp [ofDiagonalUnits, Original.toParameters]
  · rfl
  · rfl
  · apply Units.ext
    simpa only [ofDiagonalUnits, IsUnit.unit_spec, Original.toParameters] using p.gamma_eq.symm

include he in
/-- Expanding the normalized point with arbitrary gauges leaves every
coordinate unchanged.  All cancellations are cancellations of units. -/
theorem expand_coordinate (q : Normalized (R := R) e o) (g : Gauges (R := R))
    (a : ι) (b : Ω) :
    Sunlet.coordinate π (expand e o q g).toParameters a b =
      Normalization.coordinate π q.toParameters a b := by
  by_cases ha : a = e
  · subst a
    simp only [Normalization.coordinate, dif_pos rfl, Normalized.toParameters]
    change Sunlet.parameterMap π (expand e o q g).toParameters (e, b) =
      (q.z b : R)
    rw [identity_coordinate e π he]
    change ((expand e o q g).u e + (expand e o q g).v e) *
      ((expand e o q g).s b : R) * ((expand e o q g).t b : R) *
      ((expand e o q g).h b : R) = (q.z b : R)
    rw [← (expand e o q g).gamma_eq]
    have h := congrArg (fun p : Normalized (R := R) e o => (p.z b : R))
      (normalize_expand e o q g)
    simpa only [normalize, Units.val_mul] using h
  · have hu : (expand e o q g).s b * (expand e o q g).t (π a b) *
          g.Gamma * (expand e o q g).h (π a b) =
          q.z (π a b) * q.k b / q.k (π a b) := by
      dsimp [expand]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
      abel
    have hv : (expand e o q g).s b * (expand e o q g).t (π a b) *
          g.Gamma * (expand e o q g).h b =
          q.z (π a b) * q.l b / q.l (π a b) := by
      dsimp [expand]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
      abel
    simp only [Sunlet.coordinate, Original.toParameters, Normalization.coordinate,
      Normalized.toParameters, expand, dif_neg ha]
    change ((expand e o q g).s b : R) * ((expand e o q g).t (π a b) : R) *
      ((g.Gamma : R) * q.u ⟨a, ha⟩ * ((expand e o q g).h (π a b) : R) +
        (g.Gamma : R) * q.v ⟨a, ha⟩ * ((expand e o q g).h b : R)) = _
    calc
      _ = q.u ⟨a, ha⟩ *
            (((expand e o q g).s b * (expand e o q g).t (π a b) *
              g.Gamma * (expand e o q g).h (π a b) : Rˣ) : R) +
          q.v ⟨a, ha⟩ *
            (((expand e o q g).s b * (expand e o q g).t (π a b) *
              g.Gamma * (expand e o q g).h b : Rˣ) : R) := by
        simp only [Units.val_mul]
        ring
      _ = _ := by
        rw [hu, hv]
        simp only [div_eq_mul_inv, Units.val_mul]
        ring

include he in
theorem expand_parameterMap (q : Normalized (R := R) e o) (g : Gauges (R := R)) :
    Sunlet.parameterMap π (expand e o q g).toParameters =
      Normalization.parameterMap π q.toParameters := by
  funext ab
  exact expand_coordinate e o π he q g ab.1 ab.2

include he in
theorem normalize_parameterMap (p : Original (R := R) (Ω := Ω) e) :
    Normalization.parameterMap π (normalize e o p).toParameters =
      Sunlet.parameterMap π p.toParameters := by
  have h := expand_parameterMap e o π he (normalize e o p) (gauges e o p)
  rw [expand_normalize] at h
  exact h.symm

abbrev AffineFiber (q : ι × Ω → R) :=
  {p : Sunlet.Parameters R ι Ω // Sunlet.parameterMap π p = q}

abbrev NormalizedFiber (q : ι × Ω → R) :=
  {p : Normalized (R := R) e o // Normalization.parameterMap π p.toParameters = q}

/-- The whole original affine fiber is the normalized fiber times the
three gauge tori and the unrestricted identity-coefficient line. -/
def fiberEquiv (q : ι × Ω → R) (hq : ∀ b, IsUnit (q (e, b))) :
    AffineFiber π q ≃ NormalizedFiber e o π q × Gauges (R := R) where
  toFun p :=
    let p' := ofDiagonalUnits e o π he p.val (fun b => by
      simpa only [p.property] using hq b)
    (⟨normalize e o p', by
      rw [normalize_parameterMap e o π he, ofDiagonalUnits_toParameters]
      exact p.property⟩, gauges e o p')
  invFun qg := ⟨(expand e o qg.1.val qg.2).toParameters, by
    rw [expand_parameterMap e o π he]
    exact qg.1.property⟩
  left_inv p := by
    apply Subtype.ext
    dsimp
    rw [expand_normalize, ofDiagonalUnits_toParameters]
  right_inv qg := by
    rcases qg with ⟨q', g⟩
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      rw [ofDiagonalUnits_original, normalize_expand]
    · dsimp
      rw [ofDiagonalUnits_original, gauges_expand]

end Sunlet.NormalizationFibers
end
end Stage_FiberNormalization

#check "SUNLET_FiberNormalization_READY"

section Stage_FiberPoints



/-!
# The discrete part of the actual parameter fiber

Coefficient parameters remain affine.  Their nonvanishing is deduced from
the recovered toric point.  A point fiber is then identified, by explicit
mutually inverse formulas, with the character group of the loop.
-/

noncomputable section

namespace Sunlet.FiberPoints

open ToricPairAlgebra

variable {K ι Ω : Type*} [Field K] [DecidableEq Ω]

@[ext] structure Parameters (K ι Ω : Type*) [Field K] (o : Ω) where
  coefficient : ι → K
  torus : Ω → Kˣ
  base : torus o = 1

variable (L : LoopData Ω) (e : ι ≃ {x : Ω // x ≠ L.identity})
  (π : ι → Equiv.Perm Ω) (hπ : ∀ a, π a = L.left (e a))

def Parameters.point (p : Parameters K ι Ω L.identity) : ι × Ω → K :=
  toricPoint π p.coefficient p.torus

theorem Parameters.point_ne_zero (p : Parameters K ι Ω L.identity)
    (hp : ∀ a, p.coefficient a ≠ 0) (ax : ι × Ω) : p.point L π ax ≠ 0 := by
  exact mul_ne_zero (hp ax.1)
    (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))

theorem Parameters.coefficient_ne_zero_of_point_eq
    (p q : Parameters K ι Ω L.identity)
    (hp : ∀ a, p.coefficient a ≠ 0) (hq : q.point L π = p.point L π) :
    ∀ a, q.coefficient a ≠ 0 := by
  intro a ha
  have hz : q.point L π (a, L.identity) = 0 := by
    simp [Parameters.point, toricPoint, ToricDifferential.coordinate,
      ToricDifferential.ratio, ha]
  rw [hq] at hz
  exact p.point_ne_zero L π hp (a, L.identity) hz

def Parameters.act (p : Parameters K ι Ω L.identity)
    (χ : L.characterSubgroup (M := Kˣ)) : Parameters K ι Ω L.identity where
  coefficient a := p.coefficient a * (χ.val (e a)).val
  torus x := p.torus x * χ.val x
  base := by rw [p.base, χ.property.1, mul_one]

include hπ in
theorem Parameters.act_point (p : Parameters K ι Ω L.identity)
    (χ : L.characterSubgroup (M := Kˣ)) : (p.act L e χ).point L π = p.point L π :=
  L.character_action_point e π hπ p.coefficient p.torus χ

abbrev PointFiber (p : Parameters K ι Ω L.identity) :=
  {q : Parameters K ι Ω L.identity // q.point L π = p.point L π}

/-- A whole normalized toric-point fiber, with no extra nonvanishing
hypotheses imposed on its members, is the loop character group. -/
def pointFiberEquiv (p : Parameters K ι Ω L.identity)
    (hp : ∀ a, p.coefficient a ≠ 0) :
    PointFiber L π p ≃ L.characterSubgroup (M := Kˣ) where
  toFun q := L.characterOfPointEquality e π hπ p.coefficient q.val.coefficient
    p.torus q.val.torus hp (p.coefficient_ne_zero_of_point_eq L π q.val hp q.property)
    p.base q.val.base q.property.symm
  invFun χ := ⟨p.act L e χ, p.act_point L e π hπ χ⟩
  left_inv q := by
    apply Subtype.ext
    apply Parameters.ext
    · funext a
      exact (L.coefficient_of_point_equality e π hπ p.coefficient q.val.coefficient
        p.torus q.val.torus hp
        (p.coefficient_ne_zero_of_point_eq L π q.val hp q.property)
        p.base q.val.base q.property.symm a).symm
    · funext x
      exact (L.torus_of_point_equality e π hπ p.coefficient q.val.coefficient
        p.torus q.val.torus hp
        (p.coefficient_ne_zero_of_point_eq L π q.val hp q.property)
        p.base q.val.base q.property.symm x).symm
  right_inv χ := by
    apply Subtype.ext
    funext x
    change (p.torus x * χ.val x) / p.torus x = χ.val x
    simp [mul_comm]

abbrev PairFiber (p q : Parameters K ι Ω L.identity) :=
  {r : Parameters K ι Ω L.identity × Parameters K ι Ω L.identity //
    r.1.point L π + r.2.point L π = p.point L π + q.point L π}

/-- Unordered uniqueness separates the full pair fiber into its two
ordered components.  Distinctness prevents any overlap. -/
def pairFiberOrderedEquiv (p q : Parameters K ι Ω L.identity)
    (hne : p.point L π ≠ q.point L π)
    (huniq : ∀ r : PairFiber L π p q,
      (r.val.1.point L π = p.point L π ∧ r.val.2.point L π = q.point L π) ∨
      (r.val.1.point L π = q.point L π ∧ r.val.2.point L π = p.point L π)) :
    PairFiber L π p q ≃
      (PointFiber L π p × PointFiber L π q) ⊕
      (PointFiber L π q × PointFiber L π p) := by
  classical
  exact {
    toFun r := if h : r.val.1.point L π = p.point L π then
      Sum.inl (⟨r.val.1, h⟩, ⟨r.val.2, by
        have hh := r.property
        rw [h] at hh
        exact add_left_cancel hh⟩)
      else Sum.inr (⟨r.val.1, (huniq r).resolve_left (fun hh => h hh.1) |>.1⟩,
        ⟨r.val.2, (huniq r).resolve_left (fun hh => h hh.1) |>.2⟩)
    invFun := fun
      | .inl r => ⟨(r.1.val, r.2.val), by rw [r.1.property, r.2.property]⟩
      | .inr r => ⟨(r.1.val, r.2.val), by rw [r.1.property, r.2.property, add_comm]⟩
    left_inv r := by
      by_cases h : r.val.1.point L π = p.point L π
      · simp only [dif_pos h]
      · simp only [dif_neg h]
    right_inv r := by
      rcases r with r | r
      · simp only [dif_pos r.1.property]
      · have h : r.1.val.point L π ≠ p.point L π := by
          rw [r.1.property]
          exact Ne.symm hne
        simp only [dif_neg h]
  }

/-- The two character choices are independent, and the two possible
orders are disjoint. -/
def pairFiberCharacterEquiv (p q : Parameters K ι Ω L.identity)
    (hp : ∀ a, p.coefficient a ≠ 0) (hq : ∀ a, q.coefficient a ≠ 0)
    (hne : p.point L π ≠ q.point L π)
    (huniq : ∀ r : PairFiber L π p q,
      (r.val.1.point L π = p.point L π ∧ r.val.2.point L π = q.point L π) ∨
      (r.val.1.point L π = q.point L π ∧ r.val.2.point L π = p.point L π)) :
    PairFiber L π p q ≃
      (L.characterSubgroup (M := Kˣ) × L.characterSubgroup (M := Kˣ)) ⊕
      (L.characterSubgroup (M := Kˣ) × L.characterSubgroup (M := Kˣ)) :=
  (pairFiberOrderedEquiv L π p q hne huniq).trans
    (Equiv.sumCongr
      (Equiv.prodCongr (pointFiberEquiv L e π hπ p hp) (pointFiberEquiv L e π hπ q hq))
      (Equiv.prodCongr (pointFiberEquiv L e π hπ q hq) (pointFiberEquiv L e π hπ p hp)))

include hπ in
theorem pairFiber_card [Finite Ω] [IsAlgClosed K] [CharZero K]
    (p q : Parameters K ι Ω L.identity)
    (hp : ∀ a, p.coefficient a ≠ 0) (hq : ∀ a, q.coefficient a ≠ 0)
    (hne : p.point L π ≠ q.point L π)
    (huniq : ∀ r : PairFiber L π p q,
      (r.val.1.point L π = p.point L π ∧ r.val.2.point L π = q.point L π) ∨
      (r.val.1.point L π = q.point L π ∧ r.val.2.point L π = p.point L π)) :
    Nat.card (PairFiber L π p q) = 2 * Nat.card L.AbelianGroup ^ 2 := by
  rw [Nat.card_congr (pairFiberCharacterEquiv L e π hπ p q hp hq hne huniq),
    Nat.card_sum, Nat.card_prod, L.character_card (K := K)]
  ring

end Sunlet.FiberPoints
end
end Stage_FiberPoints

#check "SUNLET_FiberPoints_READY"

section Stage_NormalizedFiberPoints



/-!
# Restoring the fixed diagonal in a normalized parameter fiber

The diagonal entries determine the diagonal parameters.  Their being
units allows cancellation in every remaining coordinate.  This gives an
explicit equivalence between a whole normalized fiber and the fiber of
the sum of the two displayed toric points.
-/

noncomputable section

namespace Sunlet.NormalizedLatinSystem

open FiberPoints ToricPairAlgebra

variable {K ι Ω : Type*} [Field K]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

abbrev FiberPointParameters := FiberPoints.Parameters K L.NonidentityColor Ω o

def pairOfNormalized (p : NormalizationFibers.Normalized (R := K) L.identity o) :
    L.FiberPointParameters (K := K) o × L.FiberPointParameters (K := K) o :=
  (⟨p.u, p.k, p.k_base⟩, ⟨p.v, p.l, p.l_base⟩)

def normalizedOfPair (z : Ω → Kˣ)
    (r : L.FiberPointParameters (K := K) o × L.FiberPointParameters (K := K) o) :
    NormalizationFibers.Normalized (R := K) L.identity o where
  z := z
  k := r.1.torus
  l := r.2.torus
  u := r.1.coefficient
  v := r.2.coefficient
  k_base := r.1.base
  l_base := r.2.base

@[simp] theorem pairOfNormalized_normalizedOfPair (z : Ω → Kˣ)
    (r : L.FiberPointParameters (K := K) o × L.FiberPointParameters (K := K) o) :
    L.pairOfNormalized o (L.normalizedOfPair o z r) = r := by
  rcases r with ⟨⟨u, k, hk⟩, ⟨v, l, hl⟩⟩
  rfl

@[simp] theorem normalizedOfPair_pairOfNormalized
    (p : NormalizationFibers.Normalized (R := K) L.identity o) :
    L.normalizedOfPair o p.z (L.pairOfNormalized o p) = p := by
  cases p
  rfl

theorem normalized_coordinate_identity
    (p : NormalizationFibers.Normalized (R := K) L.identity o) (b : Ω) :
    Normalization.parameterMap L.perm p.toParameters (L.identity, b) = (p.z b : K) := by
  simp [Normalization.parameterMap, Normalization.coordinate,
    NormalizationFibers.Normalized.toParameters]

theorem normalized_coordinate_nonidentity
    (p : NormalizationFibers.Normalized (R := K) L.identity o)
    (a : L.NonidentityColor) (b : Ω) :
    Normalization.parameterMap L.perm p.toParameters (a.val, b) =
      (p.z (L.nonidentityPerm a b) : K) *
        (((L.pairOfNormalized o p).1.point (L.loopAt o) L.nonidentityPerm) (a, b) +
          ((L.pairOfNormalized o p).2.point (L.loopAt o) L.nonidentityPerm) (a, b)) := by
  simp [Normalization.parameterMap, Normalization.coordinate, a.property,
    NormalizationFibers.Normalized.toParameters, pairOfNormalized,
    FiberPoints.Parameters.point, toricPoint, ToricDifferential.coordinate,
    ToricDifferential.ratio, div_eq_mul_inv, Units.val_inv_eq_inv_val, mul_assoc,
    nonidentityPerm]

theorem normalized_fiber_diagonal
    (p : NormalizationFibers.Normalized (R := K) L.identity o)
    (r : NormalizationFibers.NormalizedFiber L.identity o L.perm
      (Normalization.parameterMap L.perm p.toParameters)) : r.val.z = p.z := by
  funext b
  apply Units.ext
  have h := congrFun r.property (L.identity, b)
  simpa only [L.normalized_coordinate_identity o] using h

/-- This is a fiber equivalence for the literal normalized coordinate
map, rather than for a renamed or unscaled surrogate. -/
def normalizedFiberPairEquiv
    (p : NormalizationFibers.Normalized (R := K) L.identity o) :
    NormalizationFibers.NormalizedFiber L.identity o L.perm
      (Normalization.parameterMap L.perm p.toParameters) ≃
    FiberPoints.PairFiber (L.loopAt o) L.nonidentityPerm
      (L.pairOfNormalized o p).1 (L.pairOfNormalized o p).2 where
  toFun r := ⟨L.pairOfNormalized o r.val, by
    funext ax
    have h := congrFun r.property (ax.1.val, ax.2)
    rw [L.normalized_coordinate_nonidentity o, L.normalized_coordinate_nonidentity o,
      L.normalized_fiber_diagonal o p r] at h
    exact mul_left_cancel₀ (Units.ne_zero _) h⟩
  invFun r := ⟨L.normalizedOfPair o p.z r.val, by
    funext ab
    by_cases ha : ab.1 = L.identity
    · rcases ab with ⟨a, b⟩
      dsimp at ha
      subst a
      simp only [L.normalized_coordinate_identity o]
      rfl
    · let a : L.NonidentityColor := ⟨ab.1, ha⟩
      have h := congrFun r.property (a, ab.2)
      change Normalization.parameterMap L.perm
        (L.normalizedOfPair o p.z r.val).toParameters (a.val, ab.2) =
          Normalization.parameterMap L.perm p.toParameters (a.val, ab.2)
      erw [L.normalized_coordinate_nonidentity o, L.normalized_coordinate_nonidentity o,
        L.pairOfNormalized_normalizedOfPair o]
      exact congrArg (fun x => (p.z (L.nonidentityPerm a ab.2) : K) * x) h⟩
  left_inv r := by
    apply Subtype.ext
    change L.normalizedOfPair o p.z (L.pairOfNormalized o r.val) = r.val
    rw [← L.normalized_fiber_diagonal o p r, L.normalizedOfPair_pairOfNormalized o]
  right_inv r := by
    apply Subtype.ext
    exact L.pairOfNormalized_normalizedOfPair o p.z r.val

end Sunlet.NormalizedLatinSystem
end
end Stage_NormalizedFiberPoints

#check "SUNLET_NormalizedFiberPoints_READY"

section Stage_GenericFiberConclusions



/-!
# Whole affine fibers above the open secant locus

The parameter space in the statement is the original affine five-family
space.  The torus restrictions on the three gauge families are consequences
of the nonzero diagonal output, not additional source hypotheses.
-/

noncomputable section

namespace Sunlet.NormalizedLatinSystem

open FiberPoints ToricPairAlgebra

variable {K ι Ω : Type*} [Field K] [CharZero K]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

abbrev DiscreteFiber :=
  ((L.loopAt o).characterSubgroup (M := Kˣ) × (L.loopAt o).characterSubgroup (M := Kˣ)) ⊕
  ((L.loopAt o).characterSubgroup (M := Kˣ) × (L.loopAt o).characterSubgroup (M := Kˣ))

theorem discreteFiber_card [IsAlgClosed K] :
    Nat.card (L.DiscreteFiber (K := K) o) =
      2 * Nat.card (L.loopAt o).AbelianGroup ^ 2 := by
  rw [Nat.card_sum, Nat.card_prod, (L.loopAt o).character_card (K := K)]
  ring

def normalizedFiberCharacterEquiv
    (p : NormalizationFibers.Normalized (R := K) L.identity o)
    (hu : ∀ a, p.u a ≠ 0) (hv : ∀ a, p.v a ≠ 0)
    (hne : (L.pairOfNormalized o p).1.point (L.loopAt o) L.nonidentityPerm ≠
      (L.pairOfNormalized o p).2.point (L.loopAt o) L.nonidentityPerm)
    (huniq : ∀ r : FiberPoints.PairFiber (L.loopAt o) L.nonidentityPerm
        (L.pairOfNormalized o p).1 (L.pairOfNormalized o p).2,
      (r.val.1.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).1.point (L.loopAt o) L.nonidentityPerm ∧
        r.val.2.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).2.point (L.loopAt o) L.nonidentityPerm) ∨
      (r.val.1.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).2.point (L.loopAt o) L.nonidentityPerm ∧
        r.val.2.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).1.point (L.loopAt o) L.nonidentityPerm)) :
    NormalizationFibers.NormalizedFiber L.identity o L.perm
      (Normalization.parameterMap L.perm p.toParameters) ≃ L.DiscreteFiber (K := K) o :=
  (L.normalizedFiberPairEquiv o p).trans
    (FiberPoints.pairFiberCharacterEquiv (L.loopAt o) (L.loopColorEquiv o).symm
      L.nonidentityPerm (L.loop_colors_compatible o)
      (L.pairOfNormalized o p).1 (L.pairOfNormalized o p).2 hu hv hne huniq)

def affineFiberCharacterEquiv
    (p : NormalizationFibers.Normalized (R := K) L.identity o)
    (hu : ∀ a, p.u a ≠ 0) (hv : ∀ a, p.v a ≠ 0)
    (hne : (L.pairOfNormalized o p).1.point (L.loopAt o) L.nonidentityPerm ≠
      (L.pairOfNormalized o p).2.point (L.loopAt o) L.nonidentityPerm)
    (huniq : ∀ r : FiberPoints.PairFiber (L.loopAt o) L.nonidentityPerm
        (L.pairOfNormalized o p).1 (L.pairOfNormalized o p).2,
      (r.val.1.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).1.point (L.loopAt o) L.nonidentityPerm ∧
        r.val.2.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).2.point (L.loopAt o) L.nonidentityPerm) ∨
      (r.val.1.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).2.point (L.loopAt o) L.nonidentityPerm ∧
        r.val.2.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).1.point (L.loopAt o) L.nonidentityPerm)) :
    NormalizationFibers.AffineFiber L.perm
      (Normalization.parameterMap L.perm p.toParameters) ≃
        L.DiscreteFiber (K := K) o × NormalizationFibers.Gauges (R := K) :=
  (NormalizationFibers.fiberEquiv L.identity o L.perm L.normalized
    (Normalization.parameterMap L.perm p.toParameters) (fun b => by
      rw [L.normalized_coordinate_identity o]
      exact (p.z b).isUnit)).trans
    (Equiv.prodCongr (L.normalizedFiberCharacterEquiv o p hu hv hne huniq) (Equiv.refl _))

/-- The displayed diagonal scaling, stated directly on the original
coordinate index set. -/
def coordinatesOfDiagonal (d : Ω → Kˣ) (z : L.NonidentityColor × Ω → K)
    (ab : ι × Ω) : K :=
  if ha : ab.1 = L.identity then d ab.2 else
    (d (L.perm ab.1 ab.2) : K) * z (⟨ab.1, ha⟩, ab.2)

theorem coordinatesOfDiagonal_normalized
    (p : NormalizationFibers.Normalized (R := K) L.identity o) :
    L.coordinatesOfDiagonal p.z
      ((L.pairOfNormalized o p).1.point (L.loopAt o) L.nonidentityPerm +
        (L.pairOfNormalized o p).2.point (L.loopAt o) L.nonidentityPerm) =
      Normalization.parameterMap L.perm p.toParameters := by
  funext ⟨a, b⟩
  by_cases ha : a = L.identity
  · subst a
    simp [coordinatesOfDiagonal, L.normalized_coordinate_identity o]
  · simpa only [coordinatesOfDiagonal, dif_neg ha, Pi.add_apply, nonidentityPerm] using
      (L.normalized_coordinate_nonidentity o p ⟨a, ha⟩ b).symm

/-- The full affine fiber calculation on one nonempty dense principal
open of the secant factor, with arbitrary nonzero diagonal coordinates. -/
theorem general_normalized_fiber_open_chart [IsAlgClosed K] (hm : 5 ≤ Fintype.card Ω) :
    ∃ P : MvPolynomial (L.NonidentityColor × Ω) K,
      MvPolynomial.aeval (genericCoordinates (k := K) o L.nonidentityPerm) P ≠ 0 ∧
      (principalOpen (k := K) o L.nonidentityPerm P).Nonempty ∧
      PolynomialClosureProduct.closure (principalOpen (k := K) o L.nonidentityPerm P) =
        secantClosure (k := K) o L.nonidentityPerm ∧
      ∀ z ∈ principalOpen (k := K) o L.nonidentityPerm P, ∀ d : Ω → Kˣ,
        Nonempty (NormalizationFibers.NormalizedFiber L.identity o L.perm
          (L.coordinatesOfDiagonal d z) ≃ L.DiscreteFiber (K := K) o) := by
  obtain ⟨P, hP, hnonempty, hdense, hdecomp⟩ :=
    L.generic_unique_torus_decomposition (k := K) o hm
  refine ⟨P, hP, hnonempty, hdense, ?_⟩
  intro z hz d
  obtain ⟨U, V, h, g, hb, gb, hU, hV, hs, hne, huniq⟩ := hdecomp z hz
  let p : NormalizationFibers.Normalized (R := K) L.identity o :=
    ⟨d, h, g, U, V, hb, gb⟩
  have hne' : (L.pairOfNormalized o p).1.point (L.loopAt o) L.nonidentityPerm ≠
      (L.pairOfNormalized o p).2.point (L.loopAt o) L.nonidentityPerm := hne
  have hu : ∀ a, p.u a ≠ 0 := hU
  have hv : ∀ a, p.v a ≠ 0 := hV
  have huniq' : ∀ r : FiberPoints.PairFiber (L.loopAt o) L.nonidentityPerm
        (L.pairOfNormalized o p).1 (L.pairOfNormalized o p).2,
      (r.val.1.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).1.point (L.loopAt o) L.nonidentityPerm ∧
        r.val.2.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).2.point (L.loopAt o) L.nonidentityPerm) ∨
      (r.val.1.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).2.point (L.loopAt o) L.nonidentityPerm ∧
        r.val.2.point (L.loopAt o) L.nonidentityPerm =
          (L.pairOfNormalized o p).1.point (L.loopAt o) L.nonidentityPerm) := by
    intro r
    have hx : r.val.1.point (L.loopAt o) L.nonidentityPerm ∈
        toricClosure (k := K) o L.nonidentityPerm :=
      parameterImage_subset_toricClosure o L.nonidentityPerm
        ⟨r.val.1.coefficient, r.val.1.torus, r.val.1.base, rfl⟩
    have hy : r.val.2.point (L.loopAt o) L.nonidentityPerm ∈
        toricClosure (k := K) o L.nonidentityPerm :=
      parameterImage_subset_toricClosure o L.nonidentityPerm
        ⟨r.val.2.coefficient, r.val.2.torus, r.val.2.base, rfl⟩
    have hr := huniq _ hx _ hy (r.property.trans hs)
    rcases hr with hr | hr
    · exact Or.inl ⟨hr.1.symm, hr.2.symm⟩
    · exact Or.inr ⟨hr.2.symm, hr.1.symm⟩
  have hQ : L.coordinatesOfDiagonal d z = Normalization.parameterMap L.perm p.toParameters := by
    calc
      L.coordinatesOfDiagonal d z =
          L.coordinatesOfDiagonal d (toricPoint L.nonidentityPerm U h +
            toricPoint L.nonidentityPerm V g) := congrArg (L.coordinatesOfDiagonal d) hs.symm
      _ = Normalization.parameterMap L.perm p.toParameters :=
        L.coordinatesOfDiagonal_normalized o p
  rw [hQ]
  exact ⟨L.normalizedFiberCharacterEquiv o p hu hv hne' huniq'⟩

end Sunlet.NormalizedLatinSystem
end
end Stage_GenericFiberConclusions

#check "SUNLET_GenericFiberConclusions_READY"

section Stage_PolynomialEquiv



/-!
# Polynomial isomorphisms of affine algebraic sets

Both directions are supplied by actual polynomials in ambient affine
coordinates.  This retains the algebraic structure beyond a bijection of
closed points.  A polynomial retraction gives a closed image, described
by its explicit equations.
-/

noncomputable section

namespace Sunlet.AlgebraicSets

variable {k I J : Type*} [Field k]

def polynomialMap (F : J → MvPolynomial I k) (x : I → k) : J → k :=
  fun j => MvPolynomial.aeval x (F j)

theorem evaluate_substitution (F : J → MvPolynomial I k) (x : I → k)
    (P : MvPolynomial J k) :
    MvPolynomial.aeval x (MvPolynomial.aeval F P) =
      MvPolynomial.aeval (polynomialMap F x) P := by
  exact MvPolynomial.comp_aeval_apply F (MvPolynomial.aeval x) P

structure PolynomialEquiv (V : Set (I → k)) (W : Set (J → k)) where
  forward : J → MvPolynomial I k
  inverse : I → MvPolynomial J k
  forward_mem : ∀ x ∈ V, polynomialMap forward x ∈ W
  inverse_mem : ∀ y ∈ W, polynomialMap inverse y ∈ V
  left_inverse : ∀ x ∈ V, polynomialMap inverse (polynomialMap forward x) = x
  right_inverse : ∀ y ∈ W, polynomialMap forward (polynomialMap inverse y) = y

def PolynomialEquiv.toEquiv {V : Set (I → k)} {W : Set (J → k)}
    (e : PolynomialEquiv V W) : V ≃ W where
  toFun x := ⟨polynomialMap e.forward x.val, e.forward_mem x.val x.property⟩
  invFun y := ⟨polynomialMap e.inverse y.val, e.inverse_mem y.val y.property⟩
  left_inv x := Subtype.ext (e.left_inverse x.val x.property)
  right_inv y := Subtype.ext (e.right_inverse y.val y.property)

def retractionSet (F : J → MvPolynomial I k) (B : I → MvPolynomial J k)
    (W : Set (J → k)) : Set (I → k) :=
  {x | polynomialMap F x ∈ W ∧ polynomialMap B (polynomialMap F x) = x}

def retractionEquiv (F : J → MvPolynomial I k) (B : I → MvPolynomial J k)
    (W : Set (J → k))
    (h : ∀ y ∈ W, polynomialMap F (polynomialMap B y) = y) :
    PolynomialEquiv (retractionSet F B W) W where
  forward := F
  inverse := B
  forward_mem x hx := hx.1
  inverse_mem y hy := ⟨by rw [h y hy]; exact hy, by rw [h y hy]⟩
  left_inverse x hx := hx.2
  right_inverse := h

theorem mem_retractionSet_iff (F : J → MvPolynomial I k) (B : I → MvPolynomial J k)
    (W : Set (J → k))
    (h : ∀ y ∈ W, polynomialMap F (polynomialMap B y) = y) (x : I → k) :
    x ∈ retractionSet F B W ↔ ∃ y ∈ W, polynomialMap B y = x := by
  constructor
  · intro hx
    exact ⟨polynomialMap F x, hx.1, hx.2⟩
  · rintro ⟨y, hy, rfl⟩
    exact (retractionEquiv F B W h).inverse_mem y hy

/-- Explicit equations of the retraction image. The first family pulls
back the target equations; the second imposes `B(F(x))=x`. -/
def retractionIdeal (F : J → MvPolynomial I k) (B : I → MvPolynomial J k)
    (A : Ideal (MvPolynomial J k)) : Ideal (MvPolynomial I k) :=
  Ideal.span
    ((MvPolynomial.aeval F '' (A : Set (MvPolynomial J k))) ∪
      Set.range (fun i => MvPolynomial.aeval F (B i) - MvPolynomial.X i))

theorem retractionSet_eq_zeroLocus (F : J → MvPolynomial I k)
    (B : I → MvPolynomial J k) (A : Ideal (MvPolynomial J k)) :
    retractionSet F B (MvPolynomial.zeroLocus k A) =
      MvPolynomial.zeroLocus k (retractionIdeal F B A) := by
  rw [retractionIdeal, MvPolynomial.zeroLocus_span]
  ext x
  constructor
  · intro hx P hP
    rcases hP with hP | hP
    · obtain ⟨Q, hQ, rfl⟩ := hP
      rw [evaluate_substitution]
      exact hx.1 Q hQ
    · obtain ⟨i, rfl⟩ := hP
      rw [map_sub, evaluate_substitution, MvPolynomial.aeval_X]
      exact sub_eq_zero.mpr (congrFun hx.2 i)
  · intro hx
    refine ⟨?_, ?_⟩
    · intro P hP
      have h := hx (MvPolynomial.aeval F P) (Or.inl ⟨P, hP, rfl⟩)
      rwa [evaluate_substitution] at h
    · funext i
      have h := hx (MvPolynomial.aeval F (B i) - MvPolynomial.X i) (Or.inr ⟨i, rfl⟩)
      rw [map_sub, evaluate_substitution, MvPolynomial.aeval_X] at h
      exact sub_eq_zero.mp h

end Sunlet.AlgebraicSets
end
end Stage_PolynomialEquiv

#check "SUNLET_PolynomialEquiv_READY"

section Stage_PolynomialEquivCoordinateRings



/-!
# Coordinate rings of the polynomial fiber isomorphisms

The coordinate ring of an algebraic set is the polynomial ring modulo
its full vanishing ideal. A polynomial equivalence induces an algebra
equivalence of these coordinate rings, contravariantly and with the
stated substitution on every coordinate. This makes the algebraic content
of the fiber statements explicit without asserting reducedness of an
arbitrary chosen set of defining equations.
-/

noncomputable section

namespace Sunlet.AlgebraicSets

variable {k I J : Type*} [Field k]

abbrev CoordinateRing (V : Set (I → k)) :=
  MvPolynomial I k ⧸ MvPolynomial.vanishingIdeal k V

/-- For a finite affine space over an algebraically closed field, this
is precisely the quotient by the radical of the given defining ideal. -/
def coordinateRingZeroLocusEquivRadical [IsAlgClosed k] [Finite I]
    (A : Ideal (MvPolynomial I k)) :
    CoordinateRing (MvPolynomial.zeroLocus k A) ≃ₐ[k] MvPolynomial I k ⧸ A.radical :=
  Ideal.quotientEquivAlgOfEq k (MvPolynomial.vanishingIdeal_zeroLocus_eq_radical A)

/-- Pullback of regular functions by the displayed polynomial map. -/
def polynomialPullback {V : Set (I → k)} {W : Set (J → k)}
    (F : J → MvPolynomial I k)
    (hF : ∀ x ∈ V, polynomialMap F x ∈ W) :
    CoordinateRing W →ₐ[k] CoordinateRing V :=
  Ideal.quotientMapₐ (MvPolynomial.vanishingIdeal k V) (MvPolynomial.aeval F) (by
    intro P hP
    change MvPolynomial.aeval F P ∈ MvPolynomial.vanishingIdeal k V
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hP ⊢
    intro x hx
    rw [evaluate_substitution]
    exact hP _ (hF x hx))

@[simp] theorem polynomialPullback_mk {V : Set (I → k)} {W : Set (J → k)}
    (F : J → MvPolynomial I k)
    (hF : ∀ x ∈ V, polynomialMap F x ∈ W) (P : MvPolynomial J k) :
    polynomialPullback F hF (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal k W) P) =
      Ideal.Quotient.mk (MvPolynomial.vanishingIdeal k V) (MvPolynomial.aeval F P) := rfl

/-- Both inverse polynomial maps descend to mutually inverse maps of
the actual reduced coordinate rings, with no function-field replacement. -/
def PolynomialEquiv.coordinateRingEquiv {V : Set (I → k)} {W : Set (J → k)}
    (e : PolynomialEquiv V W) : CoordinateRing W ≃ₐ[k] CoordinateRing V :=
  { polynomialPullback e.forward e.forward_mem with
    invFun := polynomialPullback e.inverse e.inverse_mem
    left_inv := by
      intro x
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
      change polynomialPullback e.inverse e.inverse_mem
        (polynomialPullback e.forward e.forward_mem
          (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal k W) P)) = _
      rw [polynomialPullback_mk, polynomialPullback_mk]
      apply Ideal.Quotient.eq.mpr
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro y hy
      rw [map_sub, evaluate_substitution, evaluate_substitution,
        e.right_inverse y hy, sub_self]
    right_inv := by
      intro x
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
      change polynomialPullback e.forward e.forward_mem
        (polynomialPullback e.inverse e.inverse_mem
          (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal k V) P)) = _
      rw [polynomialPullback_mk, polynomialPullback_mk]
      apply Ideal.Quotient.eq.mpr
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro y hy
      rw [map_sub, evaluate_substitution, evaluate_substitution,
        e.left_inverse y hy, sub_self] }

/-- The algebra equivalence acts by the original forward polynomials. -/
@[simp] theorem PolynomialEquiv.coordinateRingEquiv_coordinate
    {V : Set (I → k)} {W : Set (J → k)} (e : PolynomialEquiv V W) (j : J) :
    e.coordinateRingEquiv
      (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal k W) (MvPolynomial.X j)) =
        Ideal.Quotient.mk (MvPolynomial.vanishingIdeal k V) (e.forward j) := by
  change polynomialPullback e.forward e.forward_mem
    (Ideal.Quotient.mk (MvPolynomial.vanishingIdeal k W) (MvPolynomial.X j)) = _
  rw [polynomialPullback_mk, MvPolynomial.aeval_X]

end Sunlet.AlgebraicSets
end
end Stage_PolynomialEquivCoordinateRings

#check "SUNLET_PolynomialEquivCoordinateRings_READY"

section Stage_FiberAlgebraic



/-!
# Polynomial isomorphisms of the fiber components

The gauge space is embedded in affine seven-space by three independent
equations `x*y=1`, with the seventh coordinate free.  Both the gauge
parameterization of each component and its inverse are given by literal
polynomials.  Each component is closed, components for different
normalized points are disjoint, and their union is the entire fiber.
-/

noncomputable section

namespace Sunlet.FiberAlgebraic

open AlgebraicSets NormalizationFibers

variable {K ι Ω : Type*} [Field K] [DecidableEq ι]
  (e : ι) (o : Ω)

def gaugeSpace : Set (Fin 7 → K) :=
  {x | x 0 * x 1 = 1 ∧ x 2 * x 3 = 1 ∧ x 4 * x 5 = 1}

theorem gaugeSpace_nonempty : (gaugeSpace (K := K)).Nonempty :=
  ⟨fun _ => 1, by simp [gaugeSpace]⟩

def gaugeIdeal : Ideal (MvPolynomial (Fin 7) K) :=
  Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - 1,
    MvPolynomial.X 2 * MvPolynomial.X 3 - 1,
    MvPolynomial.X 4 * MvPolynomial.X 5 - 1}

theorem gaugeSpace_eq_zeroLocus : gaugeSpace (K := K) = MvPolynomial.zeroLocus K (gaugeIdeal (K := K)) := by
  rw [gaugeIdeal, MvPolynomial.zeroLocus_span]
  ext x
  simp [gaugeSpace, map_sub, map_mul, MvPolynomial.aeval_X, sub_eq_zero]

def gaugeCoordinates (g : Gauges (R := K)) : Fin 7 → K
  | 0 => g.S.val
  | 1 => (g.S⁻¹).val
  | 2 => g.H.val
  | 3 => (g.H⁻¹).val
  | 4 => g.Gamma.val
  | 5 => (g.Gamma⁻¹).val
  | _ => g.T

theorem gaugeCoordinates_mem (g : Gauges (R := K)) : gaugeCoordinates g ∈ gaugeSpace := by
  exact ⟨Units.mul_inv _, Units.mul_inv _, Units.mul_inv _⟩

def gaugesOfCoordinates (x : Fin 7 → K) (hx : x ∈ gaugeSpace) : Gauges (R := K) where
  S := ⟨x 0, x 1, hx.1, by rw [mul_comm, hx.1]⟩
  H := ⟨x 2, x 3, hx.2.1, by rw [mul_comm, hx.2.1]⟩
  Gamma := ⟨x 4, x 5, hx.2.2, by rw [mul_comm, hx.2.2]⟩
  T := x 6

@[simp] theorem gaugeCoordinates_gaugesOfCoordinates (x : Fin 7 → K) (hx : x ∈ gaugeSpace) :
    gaugeCoordinates (gaugesOfCoordinates x hx) = x := by
  funext i
  fin_cases i <;> rfl

def gaugeCoordinatesEquiv : Gauges (R := K) ≃ gaugeSpace (K := K) where
  toFun g := ⟨gaugeCoordinates g, gaugeCoordinates_mem g⟩
  invFun x := gaugesOfCoordinates x.val x.property
  left_inv g := by
    apply Gauges.ext
    · apply Units.ext; rfl
    · apply Units.ext; rfl
    · apply Units.ext; rfl
    · rfl
  right_inv x := Subtype.ext (gaugeCoordinates_gaugesOfCoordinates x.val x.property)

def expansionPolynomials (p : Normalized (R := K) e o) : ParamVar ι Ω → MvPolynomial (Fin 7) K
  | .s b => MvPolynomial.X 0 * MvPolynomial.C (p.k b : K)
  | .t b => MvPolynomial.C ((p.z b : K) / (p.l b : K)) *
      MvPolynomial.X 5 * MvPolynomial.X 1 * MvPolynomial.X 3
  | .h b => MvPolynomial.X 2 * MvPolynomial.C ((p.l b : K) / (p.k b : K))
  | .u a => if ha : a = e then MvPolynomial.X 6 else
      MvPolynomial.X 4 * MvPolynomial.C (p.u ⟨a, ha⟩)
  | .v a => if ha : a = e then MvPolynomial.X 4 - MvPolynomial.X 6 else
      MvPolynomial.X 4 * MvPolynomial.C (p.v ⟨a, ha⟩)

def gaugePolynomials (p : Normalized (R := K) e o) : Fin 7 → MvPolynomial (ParamVar ι Ω) K
  | 0 => MvPolynomial.X (.s o)
  | 1 => MvPolynomial.C ((p.z o : K)⁻¹) *
      (MvPolynomial.X (.u e) + MvPolynomial.X (.v e)) * MvPolynomial.X (.t o) *
        MvPolynomial.X (.h o)
  | 2 => MvPolynomial.X (.h o)
  | 3 => MvPolynomial.C ((p.z o : K)⁻¹) *
      (MvPolynomial.X (.u e) + MvPolynomial.X (.v e)) * MvPolynomial.X (.s o) *
        MvPolynomial.X (.t o)
  | 4 => MvPolynomial.X (.u e) + MvPolynomial.X (.v e)
  | 5 => MvPolynomial.C ((p.z o : K)⁻¹) *
      MvPolynomial.X (.s o) * MvPolynomial.X (.t o) * MvPolynomial.X (.h o)
  | _ => MvPolynomial.X (.u e)

theorem expansionPolynomials_evaluate (p : Normalized (R := K) e o) (g : Gauges (R := K)) :
    polynomialMap (expansionPolynomials e o p) (gaugeCoordinates g) =
      (expand e o p g).toParameters.toCoordinates := by
  funext i
  cases i with
  | s b => simp [polynomialMap, expansionPolynomials, gaugeCoordinates, expand,
      Original.toParameters, Parameters.toCoordinates]
  | t b => simp [polynomialMap, expansionPolynomials, gaugeCoordinates, expand,
      Original.toParameters, Parameters.toCoordinates, div_eq_mul_inv,
      Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc, mul_left_comm, mul_comm]
  | h b => simp [polynomialMap, expansionPolynomials, gaugeCoordinates, expand,
      Original.toParameters, Parameters.toCoordinates, div_eq_mul_inv,
      Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc]
  | u a =>
      by_cases ha : a = e <;>
        simp [polynomialMap, expansionPolynomials, gaugeCoordinates, expand,
          Original.toParameters, Parameters.toCoordinates, ha]
  | v a =>
      by_cases ha : a = e <;>
        simp [polynomialMap, expansionPolynomials, gaugeCoordinates, expand,
          Original.toParameters, Parameters.toCoordinates, ha]

theorem gaugePolynomials_evaluate_expansion (p : Normalized (R := K) e o)
    (g : Gauges (R := K)) :
    polynomialMap (gaugePolynomials e o p)
      (polynomialMap (expansionPolynomials e o p) (gaugeCoordinates g)) = gaugeCoordinates g := by
  rw [expansionPolynomials_evaluate]
  funext i
  fin_cases i <;>
    simp [polynomialMap, gaugePolynomials, gaugeCoordinates, expand,
      Original.toParameters, Parameters.toCoordinates, p.k_base, p.l_base,
      Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm]
  all_goals field_simp [Units.ne_zero]

theorem polynomial_section (p : Normalized (R := K) e o) (x : Fin 7 → K)
    (hx : x ∈ gaugeSpace) :
    polynomialMap (gaugePolynomials e o p) (polynomialMap (expansionPolynomials e o p) x) = x := by
  rw [← gaugeCoordinates_gaugesOfCoordinates x hx]
  exact gaugePolynomials_evaluate_expansion e o p _

def component (p : Normalized (R := K) e o) : Set (ParamVar ι Ω → K) :=
  retractionSet (gaugePolynomials e o p) (expansionPolynomials e o p) gaugeSpace

def componentEquiv (p : Normalized (R := K) e o) :
    PolynomialEquiv (component e o p) (gaugeSpace (K := K)) :=
  retractionEquiv _ _ _ (polynomial_section e o p)

theorem component_isAlgebraic (p : Normalized (R := K) e o) :
    ∃ A : Ideal (MvPolynomial (ParamVar ι Ω) K), component e o p = MvPolynomial.zeroLocus K A := by
  refine ⟨retractionIdeal (gaugePolynomials e o p) (expansionPolynomials e o p) gaugeIdeal, ?_⟩
  unfold component
  rw [gaugeSpace_eq_zeroLocus, retractionSet_eq_zeroLocus]

theorem mem_component_iff (p : Normalized (R := K) e o) (x : ParamVar ι Ω → K) :
    x ∈ component e o p ↔ ∃ g : Gauges (R := K),
      (expand e o p g).toParameters.toCoordinates = x := by
  rw [component, mem_retractionSet_iff _ _ _ (polynomial_section e o p)]
  constructor
  · rintro ⟨y, hy, he⟩
    refine ⟨gaugesOfCoordinates y hy, ?_⟩
    rw [← expansionPolynomials_evaluate, gaugeCoordinates_gaugesOfCoordinates]
    exact he
  · rintro ⟨g, rfl⟩
    exact ⟨gaugeCoordinates g, gaugeCoordinates_mem g, expansionPolynomials_evaluate e o p g⟩

theorem component_nonempty (p : Normalized (R := K) e o) : (component e o p).Nonempty := by
  let g : Gauges (R := K) := ⟨1, 1, 1, 0⟩
  exact ⟨(expand e o p g).toParameters.toCoordinates,
    (mem_component_iff e o p _).mpr ⟨g, rfl⟩⟩

theorem components_disjoint (p r : Normalized (R := K) e o) (hpr : p ≠ r) :
    Disjoint (component e o p) (component e o r) := by
  rw [Set.disjoint_left]
  intro x hx hr
  obtain ⟨g, hg⟩ := (mem_component_iff e o p x).mp hx
  obtain ⟨h, hh⟩ := (mem_component_iff e o r x).mp hr
  have he : expand e o p g = expand e o r h :=
    Original.toParameters_injective e (Parameters.coordinatesEquiv.injective (hg.trans hh.symm))
  have hn := congrArg (normalize e o) he
  rw [normalize_expand, normalize_expand] at hn
  exact hpr hn

def affineFiberSet (π : ι → Equiv.Perm Ω) (q : ι × Ω → K) : Set (ParamVar ι Ω → K) :=
  {x | Sunlet.parameterMap π (Parameters.ofCoordinates x) = q}

def affineFiberIdeal (π : ι → Equiv.Perm Ω) (q : ι × Ω → K) :
    Ideal (MvPolynomial (ParamVar ι Ω) K) :=
  Ideal.span (Set.range (fun ab => Sunlet.coordinatePolynomial (K := K) π ab - MvPolynomial.C (q ab)))

theorem affineFiberSet_eq_zeroLocus (π : ι → Equiv.Perm Ω) (q : ι × Ω → K) :
    affineFiberSet π q = MvPolynomial.zeroLocus K (affineFiberIdeal π q) := by
  rw [affineFiberIdeal, MvPolynomial.zeroLocus_span]
  ext x
  constructor
  · intro h P hP
    obtain ⟨ab, rfl⟩ := hP
    simpa only [map_sub, Sunlet.aeval_coordinatePolynomial_ofCoordinates,
      MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] using
      congrFun h ab
  · intro h
    funext ab
    have hh := h _ ⟨ab, rfl⟩
    simpa only [map_sub, Sunlet.aeval_coordinatePolynomial_ofCoordinates,
      MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] using hh

theorem components_cover (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω)
    (q : ι × Ω → K) (hq : ∀ b, IsUnit (q (e, b))) :
    (⋃ p : NormalizedFiber e o π q, component e o p.val) = affineFiberSet π q := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨p, hx⟩
    obtain ⟨g, rfl⟩ := (mem_component_iff e o p.val x).mp hx
    change Sunlet.parameterMap π (Parameters.ofCoordinates _) = q
    rw [Parameters.ofCoordinates_toCoordinates, expand_parameterMap e o π he]
    exact p.property
  · intro hx
    let a : AffineFiber π q := ⟨Parameters.ofCoordinates x, hx⟩
    let b := fiberEquiv e o π he q hq a
    refine ⟨b.1, (mem_component_iff e o b.1.val x).mpr ⟨b.2, ?_⟩⟩
    have h := (fiberEquiv e o π he q hq).symm_apply_apply a
    have hc := congrArg (fun a : AffineFiber π q => a.val.toCoordinates) h
    change (expand e o b.1.val b.2).toParameters.toCoordinates = a.val.toCoordinates at hc
    simpa only [a, Parameters.toCoordinates_ofCoordinates] using hc

end Sunlet.FiberAlgebraic
end
end Stage_FiberAlgebraic

#check "SUNLET_FiberAlgebraic_READY"

section Stage_SixFamilyFibers



/-!
# Restoring the sixth edge family on the whole affine fiber

The first factor of `Parameters` is the independent edge family absorbed
into the two mixture coefficients by `GroupCoordinates.collapse`.  It is
an arbitrary affine family, not a family assumed to consist of units.

A unit output in every color forces every member of this family to be a
unit.  Over that output open, absorption has exactly one independent unit
factor per color.  The proof works over every commutative ring, so the
fiber equivalence does not discard points over rings with nilpotents.
-/

noncomputable section

namespace Sunlet.SixFamilyFibers

abbrev ParamVar (ι Ω : Type*) := ι ⊕ Sunlet.ParamVar ι Ω

/-- Six arbitrary affine families: the extra family and the five unabsorbed
families.  The last two entries of the latter record are the original
mixture-edge families, before multiplication by the extra family. -/
abbrev Parameters (R ι Ω : Type*) := (ι → R) × Sunlet.Parameters R ι Ω

namespace Parameters

variable {R ι Ω : Type*}

def toCoordinates (p : Parameters R ι Ω) : ParamVar ι Ω → R :=
  Sum.elim p.1 p.2.toCoordinates

def ofCoordinates (x : ParamVar ι Ω → R) : Parameters R ι Ω :=
  (fun a => x (.inl a), Sunlet.Parameters.ofCoordinates (fun i => x (.inr i)))

@[simp] theorem ofCoordinates_toCoordinates (p : Parameters R ι Ω) :
    ofCoordinates (toCoordinates p) = p := by
  rcases p with ⟨w, p⟩
  simp [ofCoordinates, toCoordinates]

@[simp] theorem toCoordinates_ofCoordinates (x : ParamVar ι Ω → R) :
    toCoordinates (ofCoordinates x) = x := by
  funext i
  cases i with
  | inl a => rfl
  | inr i =>
    simp [ofCoordinates, toCoordinates, Sunlet.Parameters.toCoordinates_ofCoordinates]

def coordinatesEquiv : Parameters R ι Ω ≃ (ParamVar ι Ω → R) where
  toFun := toCoordinates
  invFun := ofCoordinates
  left_inv := ofCoordinates_toCoordinates
  right_inv := toCoordinates_ofCoordinates

end Parameters

section Rings

variable {R ι Ω : Type*} [CommRing R]

/-- The literal six-family map, with no nonvanishing restriction. -/
def parameterMap (π : ι → Equiv.Perm Ω) (p : Parameters R ι Ω) (ab : ι × Ω) : R :=
  p.1 ab.1 * Sunlet.parameterMap π p.2 ab

def collapse (p : Parameters R ι Ω) : Sunlet.Parameters R ι Ω where
  s := p.2.s
  t := p.2.t
  h := p.2.h
  u a := p.1 a * p.2.u a
  v a := p.1 a * p.2.v a

theorem parameterMap_eq_collapse (π : ι → Equiv.Perm Ω) (p : Parameters R ι Ω) :
    parameterMap π p = Sunlet.parameterMap π (collapse p) := by
  funext ab
  simp only [parameterMap, collapse, Sunlet.parameterMap, Sunlet.coordinate]
  ring

/-- Restore the absorbed family, dividing both coefficients by its units. -/
def expand (p : Sunlet.Parameters R ι Ω) (w : ι → Rˣ) : Parameters R ι Ω :=
  (fun a => (w a : R),
    { s := p.s
      t := p.t
      h := p.h
      u := fun a => ((w a)⁻¹ : Rˣ).val * p.u a
      v := fun a => ((w a)⁻¹ : Rˣ).val * p.v a })

@[simp] theorem collapse_expand (p : Sunlet.Parameters R ι Ω) (w : ι → Rˣ) :
    collapse (expand p w) = p := by
  cases p
  simp [collapse, expand, ← mul_assoc]

theorem expand_collapse (p : Parameters R ι Ω) (w : ι → Rˣ)
    (hw : ∀ a, (w a : R) = p.1 a) : expand (collapse p) w = p := by
  apply Prod.ext
  · exact funext hw
  · rcases p with ⟨r, p⟩
    cases p
    dsimp only at hw
    simp only [expand, collapse]
    congr 1
    · funext a
      rw [← hw a, ← mul_assoc]
      simp
    · funext a
      rw [← hw a, ← mul_assoc]
      simp

theorem expand_parameterMap (π : ι → Equiv.Perm Ω)
    (p : Sunlet.Parameters R ι Ω) (w : ι → Rˣ) :
    parameterMap π (expand p w) = Sunlet.parameterMap π p := by
  rw [parameterMap_eq_collapse, collapse_expand]

theorem expand_unabsorbed_parameterMap (π : ι → Equiv.Perm Ω)
    (p : Sunlet.Parameters R ι Ω) (w : ι → Rˣ) (ab : ι × Ω) :
    Sunlet.parameterMap π (expand p w).2 ab =
      ((w ab.1)⁻¹ : Rˣ).val * Sunlet.parameterMap π p ab := by
  simp only [Sunlet.parameterMap, Sunlet.coordinate, expand]
  ring

theorem range_eq_fiveFamily (π : ι → Equiv.Perm Ω) :
    Set.range (parameterMap (R := R) π) = Set.range (Sunlet.parameterMap (K := R) π) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨collapse p, (parameterMap_eq_collapse π p).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨expand p (fun _ => 1), expand_parameterMap π p _⟩

/-- A single unit coordinate in color `a` forces the absorbed edge
parameter of that color to be a unit. -/
theorem extra_isUnit (π : ι → Equiv.Perm Ω) (p : Parameters R ι Ω)
    (a : ι) (h : ∃ b, IsUnit (parameterMap π p (a, b))) : IsUnit (p.1 a) := by
  obtain ⟨b, hb⟩ := h
  exact (IsUnit.mul_iff.mp hb).1

abbrev AffineFiber (π : ι → Equiv.Perm Ω) (q : ι × Ω → R) :=
  {p : Parameters R ι Ω // parameterMap π p = q}

def fiberUnits (π : ι → Equiv.Perm Ω) (q : ι × Ω → R)
    (hq : ∀ a, ∃ b, IsUnit (q (a, b))) (p : AffineFiber π q) : ι → Rˣ :=
  fun a => (extra_isUnit π p.val a (by simpa only [p.property] using hq a)).unit

@[simp] theorem fiberUnits_val (π : ι → Equiv.Perm Ω) (q : ι × Ω → R)
    (hq : ∀ a, ∃ b, IsUnit (q (a, b))) (p : AffineFiber π q) (a : ι) :
    (fiberUnits π q hq p a : R) = p.val.1 a :=
  IsUnit.unit_spec _

/-- The entire six-family affine fiber is the entire five-family affine
fiber times one copy of the multiplicative group per color. -/
def fiberEquiv (π : ι → Equiv.Perm Ω) (q : ι × Ω → R)
    (hq : ∀ a, ∃ b, IsUnit (q (a, b))) :
    AffineFiber π q ≃ NormalizationFibers.AffineFiber π q × (ι → Rˣ) where
  toFun p :=
    (⟨collapse p.val, (parameterMap_eq_collapse π p.val).symm.trans p.property⟩,
      fiberUnits π q hq p)
  invFun p := ⟨expand p.1.val p.2, (expand_parameterMap π p.1.val p.2).trans p.1.property⟩
  left_inv p := by
    apply Subtype.ext
    exact expand_collapse p.val _ (fiberUnits_val π q hq p)
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact collapse_expand p.1.val p.2
    · funext a
      apply Units.ext
      exact fiberUnits_val π q hq _ a

/-- Combining the two explicit normalizations yields all gauge factors
for the original six edge families. -/
def normalizedFiberEquiv [DecidableEq ι] (e : ι) (o : Ω)
    (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω) (q : ι × Ω → R)
    (hd : ∀ b, IsUnit (q (e, b))) (hr : ∀ a, ∃ b, IsUnit (q (a, b))) :
    AffineFiber π q ≃
      (NormalizationFibers.NormalizedFiber e o π q × NormalizationFibers.Gauges (R := R)) ×
        (ι → Rˣ) :=
  (fiberEquiv π q hr).trans
    (Equiv.prodCongr (NormalizationFibers.fiberEquiv e o π he q hd) (Equiv.refl _))

end Rings

section Naturality

variable {R S ι Ω : Type*} [CommRing R] [CommRing S]

def mapFive (f : R →+* S) (p : Sunlet.Parameters R ι Ω) : Sunlet.Parameters S ι Ω where
  s b := f (p.s b)
  t b := f (p.t b)
  h b := f (p.h b)
  u a := f (p.u a)
  v a := f (p.v a)

def map (f : R →+* S) (p : Parameters R ι Ω) : Parameters S ι Ω :=
  (fun a => f (p.1 a), mapFive f p.2)

theorem collapse_map (f : R →+* S) (p : Parameters R ι Ω) :
    collapse (map f p) = mapFive f (collapse p) := by
  simp [collapse, map, mapFive, map_mul]

theorem expand_map (f : R →+* S) (p : Sunlet.Parameters R ι Ω) (w : ι → Rˣ) :
    map f (expand p w) =
      expand (mapFive f p) (fun a => Units.map f.toMonoidHom (w a)) := by
  simp [map, mapFive, expand, map_mul]

theorem mapFive_parameterMap (f : R →+* S) (π : ι → Equiv.Perm Ω)
    (p : Sunlet.Parameters R ι Ω) :
    Sunlet.parameterMap π (mapFive f p) = f ∘ Sunlet.parameterMap π p := by
  funext ab
  simp [Sunlet.parameterMap, Sunlet.coordinate, mapFive, map_mul, map_add]

theorem map_parameterMap (f : R →+* S) (π : ι → Equiv.Perm Ω) (p : Parameters R ι Ω) :
    parameterMap π (map f p) = f ∘ parameterMap π p := by
  funext ab
  simp [parameterMap, map, mapFive_parameterMap, map_mul]

def mapFiber (f : R →+* S) (π : ι → Equiv.Perm Ω) (q : ι × Ω → R)
    (p : AffineFiber π q) : AffineFiber π (f ∘ q) :=
  ⟨map f p.val, by rw [map_parameterMap, p.property]⟩

def mapFiveFiber (f : R →+* S) (π : ι → Equiv.Perm Ω) (q : ι × Ω → R)
    (p : NormalizationFibers.AffineFiber π q) : NormalizationFibers.AffineFiber π (f ∘ q) :=
  ⟨mapFive f p.val, by rw [mapFive_parameterMap, p.property]⟩

theorem unitWitness_map (f : R →+* S) (q : ι × Ω → R)
    (hq : ∀ a, ∃ b, IsUnit (q (a, b))) : ∀ a, ∃ b, IsUnit ((f ∘ q) (a, b)) := by
  intro a
  obtain ⟨b, hb⟩ := hq a
  exact ⟨b, hb.map f⟩

/-- The affine fiber equivalence commutes with every homomorphism of
commutative rings, not only with extensions of fields. -/
theorem fiberEquiv_natural (f : R →+* S) (π : ι → Equiv.Perm Ω) (q : ι × Ω → R)
    (hq : ∀ a, ∃ b, IsUnit (q (a, b))) (p : AffineFiber π q) :
    fiberEquiv π (f ∘ q) (unitWitness_map f q hq) (mapFiber f π q p) =
      (mapFiveFiber f π q (fiberEquiv π q hq p).1,
        fun a => Units.map f.toMonoidHom ((fiberEquiv π q hq p).2 a)) := by
  apply Prod.ext
  · apply Subtype.ext
    exact collapse_map f p.val
  · funext a
    apply Units.ext
    change (fiberUnits π (f ∘ q) (unitWitness_map f q hq) (mapFiber f π q p) a : S) =
      f (fiberUnits π q hq p a : R)
    rw [fiberUnits_val, fiberUnits_val]
    rfl

end Naturality

section LiteralGroupMap

variable {K G : Type*} [Field K] [AddCommGroup G]

/-- The only coordinate reindexing is negation in the third leaf family. -/
def groupParametersEquiv : GroupCoordinates.Parameters (K := K) (G := G) ≃ Parameters K G G where
  toFun w :=
    (w 0, { s := w 1, t := fun b => w 2 (-b), h := w 3, u := w 4, v := w 5 })
  invFun p := ![p.1, p.2.s, fun b => p.2.t (-b), p.2.h, p.2.u, p.2.v]
  left_inv w := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    rcases p with ⟨w, p⟩
    cases p
    simp

theorem group_parameterMap (w : GroupCoordinates.Parameters (K := K) (G := G)) :
    parameterMap addTranslationPerm (groupParametersEquiv w) = GroupCoordinates.parameterMap w := by
  funext ab
  simp only [parameterMap, groupParametersEquiv, GroupCoordinates.parameterMap,
    GroupCoordinates.coordinate, Sunlet.parameterMap, Sunlet.coordinate,
    addTranslationPerm_apply, Equiv.coe_fn_mk]
  ring

def literalFiberEquiv (q : G × G → K) :
    {w : GroupCoordinates.Parameters (K := K) (G := G) // GroupCoordinates.parameterMap w = q} ≃
      AffineFiber addTranslationPerm q where
  toFun w := ⟨groupParametersEquiv w.val, (group_parameterMap w.val).trans w.property⟩
  invFun p := ⟨groupParametersEquiv.symm p.val, by
    rw [← group_parameterMap, Equiv.apply_symm_apply]
    exact p.property⟩
  left_inv w := Subtype.ext (groupParametersEquiv.symm_apply_apply w.val)
  right_inv p := Subtype.ext (groupParametersEquiv.apply_symm_apply p.val)

/-- Faithful fiber statement for the manuscript's six families themselves,
including all affine parameter points. -/
def literalNormalizedFiberEquiv [DecidableEq G] (q : G × G → K)
    (hd : ∀ b, IsUnit (q (0, b))) (hr : ∀ a, ∃ b, IsUnit (q (a, b))) :
    {w : GroupCoordinates.Parameters (K := K) (G := G) // GroupCoordinates.parameterMap w = q} ≃
      (NormalizationFibers.NormalizedFiber (0 : G) (0 : G) addTranslationPerm q ×
        NormalizationFibers.Gauges (R := K)) × (G → Kˣ) :=
  (literalFiberEquiv q).trans
    (normalizedFiberEquiv 0 0 addTranslationPerm (by ext b; exact zero_add b) q hd hr)

end LiteralGroupMap

end Sunlet.SixFamilyFibers
end
end Stage_SixFamilyFibers

#check "SUNLET_SixFamilyFibers_READY"

section Stage_SixFamilyAlgebraic



/-!
# Algebraic components of the original six-family fibers

The extra absorbed edge parameters are restored as independent units.
Their inverses are polynomial on a fiber: divide the unabsorbed output
coordinate by its fixed nonzero value.  Thus each component is a closed
algebraic set polynomially isomorphic to the three original gauge tori,
one additional torus per color, and one affine line.
-/

noncomputable section

namespace Sunlet.SixFamilyAlgebraic

open AlgebraicSets NormalizationFibers

variable {K ι Ω : Type*} [Field K] [DecidableEq ι]
  (e : ι) (o : Ω)

abbrev GaugeVar (ι : Type*) := Fin 7 ⊕ (ι × Bool)

def gaugeSpace : Set (GaugeVar ι → K) :=
  {x | FiberAlgebraic.gaugeSpace (fun i => x (.inl i)) ∧
    ∀ a, x (.inr (a, false)) * x (.inr (a, true)) = 1}

def gaugeIdeal : Ideal (MvPolynomial (GaugeVar ι) K) :=
  Ideal.span
    ({MvPolynomial.X (.inl 0) * MvPolynomial.X (.inl 1) - 1,
      MvPolynomial.X (.inl 2) * MvPolynomial.X (.inl 3) - 1,
      MvPolynomial.X (.inl 4) * MvPolynomial.X (.inl 5) - 1} ∪
      Set.range (fun a : ι =>
        MvPolynomial.X (.inr (a, false)) * MvPolynomial.X (.inr (a, true)) - 1))

theorem gaugeSpace_eq_zeroLocus :
    gaugeSpace (K := K) (ι := ι) = MvPolynomial.zeroLocus K (gaugeIdeal (K := K) (ι := ι)) := by
  rw [gaugeIdeal, MvPolynomial.zeroLocus_span]
  ext x
  change ((x (.inl 0) * x (.inl 1) = 1 ∧ x (.inl 2) * x (.inl 3) = 1 ∧
    x (.inl 4) * x (.inl 5) = 1) ∧
    ∀ a, x (.inr (a, false)) * x (.inr (a, true)) = 1) ↔ _
  simp only [Set.mem_setOf_eq]
  rw [Set.forall_mem_union]
  simp [map_sub, map_mul, sub_eq_zero]

def gaugeCoordinates (g : Gauges (R := K)) (w : ι → Kˣ) : GaugeVar ι → K
  | .inl i => FiberAlgebraic.gaugeCoordinates g i
  | .inr (a, false) => (w a : K)
  | .inr (a, true) => ((w a)⁻¹ : Kˣ).val

theorem gaugeCoordinates_mem (g : Gauges (R := K)) (w : ι → Kˣ) :
    gaugeCoordinates g w ∈ gaugeSpace :=
  ⟨FiberAlgebraic.gaugeCoordinates_mem g, fun a => Units.mul_inv (w a)⟩

def gaugesOfCoordinates (x : GaugeVar ι → K) (hx : x ∈ gaugeSpace) :
    Gauges (R := K) × (ι → Kˣ) :=
  (FiberAlgebraic.gaugesOfCoordinates (fun i => x (.inl i)) hx.1,
    fun a => ⟨x (.inr (a, false)), x (.inr (a, true)), hx.2 a,
      by rw [mul_comm, hx.2 a]⟩)

@[simp] theorem gaugeCoordinates_gaugesOfCoordinates (x : GaugeVar ι → K)
    (hx : x ∈ gaugeSpace) :
    gaugeCoordinates (gaugesOfCoordinates x hx).1 (gaugesOfCoordinates x hx).2 = x := by
  funext i
  cases i with
  | inl i =>
    exact congrFun (FiberAlgebraic.gaugeCoordinates_gaugesOfCoordinates
      (fun i => x (.inl i)) hx.1) i
  | inr ab =>
    rcases ab with ⟨a, b⟩
    cases b <;> rfl

def gaugeCoordinatesEquiv :
    Gauges (R := K) × (ι → Kˣ) ≃ gaugeSpace (K := K) (ι := ι) where
  toFun g := ⟨gaugeCoordinates g.1 g.2, gaugeCoordinates_mem g.1 g.2⟩
  invFun x := gaugesOfCoordinates x.val x.property
  left_inv g := by
    apply Prod.ext
    · exact FiberAlgebraic.gaugeCoordinatesEquiv.left_inv g.1
    · funext a
      apply Units.ext
      rfl
  right_inv x := Subtype.ext (gaugeCoordinates_gaugesOfCoordinates x.val x.property)

def collapsePolynomials : Sunlet.ParamVar ι Ω → MvPolynomial (SixFamilyFibers.ParamVar ι Ω) K
  | .s b => MvPolynomial.X (.inr (.s b))
  | .t b => MvPolynomial.X (.inr (.t b))
  | .h b => MvPolynomial.X (.inr (.h b))
  | .u a => MvPolynomial.X (.inl a) * MvPolynomial.X (.inr (.u a))
  | .v a => MvPolynomial.X (.inl a) * MvPolynomial.X (.inr (.v a))

theorem collapsePolynomials_evaluate (p : SixFamilyFibers.Parameters K ι Ω) :
    polynomialMap collapsePolynomials (SixFamilyFibers.Parameters.toCoordinates p) =
      (SixFamilyFibers.collapse p).toCoordinates := by
  funext i
  cases i <;> simp [polynomialMap, collapsePolynomials, SixFamilyFibers.collapse,
    SixFamilyFibers.Parameters.toCoordinates, Sunlet.Parameters.toCoordinates]

def expansionPolynomials (p : Normalized (R := K) e o) :
    SixFamilyFibers.ParamVar ι Ω → MvPolynomial (GaugeVar ι) K
  | .inl a => MvPolynomial.X (.inr (a, false))
  | .inr (.s b) => MvPolynomial.rename Sum.inl (FiberAlgebraic.expansionPolynomials e o p (.s b))
  | .inr (.t b) => MvPolynomial.rename Sum.inl (FiberAlgebraic.expansionPolynomials e o p (.t b))
  | .inr (.h b) => MvPolynomial.rename Sum.inl (FiberAlgebraic.expansionPolynomials e o p (.h b))
  | .inr (.u a) => MvPolynomial.X (.inr (a, true)) *
      MvPolynomial.rename Sum.inl (FiberAlgebraic.expansionPolynomials e o p (.u a))
  | .inr (.v a) => MvPolynomial.X (.inr (a, true)) *
      MvPolynomial.rename Sum.inl (FiberAlgebraic.expansionPolynomials e o p (.v a))

/-- The inverse of the extra unit in color `a` is the unabsorbed
coordinate divided by its fixed nonzero output value. -/
def gaugePolynomials (π : ι → Equiv.Perm Ω) (q : ι × Ω → K) (b : ι → Ω)
    (p : Normalized (R := K) e o) :
    GaugeVar ι → MvPolynomial (SixFamilyFibers.ParamVar ι Ω) K
  | .inl i => MvPolynomial.aeval collapsePolynomials (FiberAlgebraic.gaugePolynomials e o p i)
  | .inr (a, false) => MvPolynomial.X (.inl a)
  | .inr (a, true) => MvPolynomial.C ((q (a, b a))⁻¹) *
      MvPolynomial.rename Sum.inr (Sunlet.coordinatePolynomial π (a, b a))

theorem aeval_rename_gauge (g : Gauges (R := K)) (w : ι → Kˣ)
    (P : MvPolynomial (Fin 7) K) :
    MvPolynomial.aeval (gaugeCoordinates g w) (MvPolynomial.rename Sum.inl P) =
      MvPolynomial.aeval (FiberAlgebraic.gaugeCoordinates g) P := by
  rw [MvPolynomial.aeval_rename]
  rfl

theorem expansionPolynomials_evaluate (p : Normalized (R := K) e o)
    (g : Gauges (R := K)) (w : ι → Kˣ) :
    polynomialMap (expansionPolynomials e o p) (gaugeCoordinates g w) =
      SixFamilyFibers.Parameters.toCoordinates
        (SixFamilyFibers.expand (NormalizationFibers.expand e o p g).toParameters w) := by
  have hh (i : Sunlet.ParamVar ι Ω) :=
    congrFun (FiberAlgebraic.expansionPolynomials_evaluate e o p g) i
  funext i
  cases i with
  | inl a =>
    simp [polynomialMap, expansionPolynomials, gaugeCoordinates,
      SixFamilyFibers.Parameters.toCoordinates, SixFamilyFibers.expand]
  | inr i =>
    cases i with
    | s b =>
      simpa only [polynomialMap, expansionPolynomials, aeval_rename_gauge,
        SixFamilyFibers.Parameters.toCoordinates, SixFamilyFibers.expand,
        Sunlet.Parameters.toCoordinates, Sum.elim_inr] using hh (.s b)
    | t b =>
      simpa only [polynomialMap, expansionPolynomials, aeval_rename_gauge,
        SixFamilyFibers.Parameters.toCoordinates, SixFamilyFibers.expand,
        Sunlet.Parameters.toCoordinates, Sum.elim_inr] using hh (.t b)
    | h b =>
      simpa only [polynomialMap, expansionPolynomials, aeval_rename_gauge,
        SixFamilyFibers.Parameters.toCoordinates, SixFamilyFibers.expand,
        Sunlet.Parameters.toCoordinates, Sum.elim_inr] using hh (.h b)
    | u a =>
      simpa only [polynomialMap, expansionPolynomials, map_mul, MvPolynomial.aeval_X,
        aeval_rename_gauge, gaugeCoordinates,
        SixFamilyFibers.Parameters.toCoordinates, SixFamilyFibers.expand,
        Sunlet.Parameters.toCoordinates, Sum.elim_inr] using
        congrArg (fun z : K => ((w a)⁻¹ : Kˣ).val * z) (hh (.u a))
    | v a =>
      simpa only [polynomialMap, expansionPolynomials, map_mul, MvPolynomial.aeval_X,
        aeval_rename_gauge, gaugeCoordinates,
        SixFamilyFibers.Parameters.toCoordinates, SixFamilyFibers.expand,
        Sunlet.Parameters.toCoordinates, Sum.elim_inr] using
        congrArg (fun z : K => ((w a)⁻¹ : Kˣ).val * z) (hh (.v a))

theorem gaugePolynomials_evaluate_expansion (π : ι → Equiv.Perm Ω)
    (he : π e = Equiv.refl Ω) (q : ι × Ω → K) (b : ι → Ω)
    (hb : ∀ a, q (a, b a) ≠ 0) (p : NormalizedFiber e o π q)
    (g : Gauges (R := K)) (w : ι → Kˣ) :
    polynomialMap (gaugePolynomials e o π q b p.val)
      (polynomialMap (expansionPolynomials e o p.val) (gaugeCoordinates g w)) =
        gaugeCoordinates g w := by
  rw [expansionPolynomials_evaluate]
  have hp : Sunlet.parameterMap π (NormalizationFibers.expand e o p.val g).toParameters = q :=
    (NormalizationFibers.expand_parameterMap e o π he p.val g).trans p.property
  funext i
  cases i with
  | inl i =>
    change MvPolynomial.aeval _ (MvPolynomial.aeval collapsePolynomials _) = _
    rw [evaluate_substitution, collapsePolynomials_evaluate, SixFamilyFibers.collapse_expand]
    have h := FiberAlgebraic.gaugePolynomials_evaluate_expansion e o p.val g
    rw [FiberAlgebraic.expansionPolynomials_evaluate] at h
    exact congrFun h i
  | inr ab =>
    rcases ab with ⟨a, c⟩
    cases c with
    | false =>
      simp [polynomialMap, gaugePolynomials, gaugeCoordinates,
        SixFamilyFibers.Parameters.toCoordinates, SixFamilyFibers.expand]
    | true =>
      change MvPolynomial.aeval _ (MvPolynomial.C ((q (a, b a))⁻¹) *
        MvPolynomial.rename Sum.inr (Sunlet.coordinatePolynomial π (a, b a))) = _
      rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_rename]
      change (q (a, b a))⁻¹ *
        MvPolynomial.aeval (SixFamilyFibers.expand
          (NormalizationFibers.expand e o p.val g).toParameters w).2.toCoordinates
            (Sunlet.coordinatePolynomial π (a, b a)) = ((w a)⁻¹ : Kˣ).val
      rw [Sunlet.aeval_coordinatePolynomial, SixFamilyFibers.expand_unabsorbed_parameterMap, hp]
      rw [mul_left_comm, inv_mul_cancel₀ (hb a), mul_one]

theorem polynomial_section (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω)
    (q : ι × Ω → K) (b : ι → Ω) (hb : ∀ a, q (a, b a) ≠ 0)
    (p : NormalizedFiber e o π q) (x : GaugeVar ι → K) (hx : x ∈ gaugeSpace) :
    polynomialMap (gaugePolynomials e o π q b p.val)
      (polynomialMap (expansionPolynomials e o p.val) x) = x := by
  rw [← gaugeCoordinates_gaugesOfCoordinates x hx]
  exact gaugePolynomials_evaluate_expansion e o π he q b hb p _ _

def component (π : ι → Equiv.Perm Ω) (q : ι × Ω → K) (b : ι → Ω)
    (p : NormalizedFiber e o π q) : Set (SixFamilyFibers.ParamVar ι Ω → K) :=
  retractionSet (gaugePolynomials e o π q b p.val) (expansionPolynomials e o p.val) gaugeSpace

def componentEquiv (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω)
    (q : ι × Ω → K) (b : ι → Ω) (hb : ∀ a, q (a, b a) ≠ 0)
    (p : NormalizedFiber e o π q) :
    PolynomialEquiv (component e o π q b p) (gaugeSpace (K := K) (ι := ι)) :=
  retractionEquiv _ _ _ (polynomial_section e o π he q b hb p)

theorem component_isAlgebraic (π : ι → Equiv.Perm Ω) (q : ι × Ω → K)
    (b : ι → Ω) (p : NormalizedFiber e o π q) :
    ∃ A : Ideal (MvPolynomial (SixFamilyFibers.ParamVar ι Ω) K),
      component e o π q b p = MvPolynomial.zeroLocus K A := by
  refine ⟨retractionIdeal (gaugePolynomials e o π q b p.val)
    (expansionPolynomials e o p.val) gaugeIdeal, ?_⟩
  unfold component
  rw [gaugeSpace_eq_zeroLocus, retractionSet_eq_zeroLocus]

theorem mem_component_iff (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω)
    (q : ι × Ω → K) (b : ι → Ω) (hb : ∀ a, q (a, b a) ≠ 0)
    (p : NormalizedFiber e o π q) (x : SixFamilyFibers.ParamVar ι Ω → K) :
    x ∈ component e o π q b p ↔ ∃ (g : Gauges (R := K)) (w : ι → Kˣ),
      SixFamilyFibers.Parameters.toCoordinates
        (SixFamilyFibers.expand (NormalizationFibers.expand e o p.val g).toParameters w) = x := by
  rw [component, mem_retractionSet_iff _ _ _ (polynomial_section e o π he q b hb p)]
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨(gaugesOfCoordinates y hy).1, (gaugesOfCoordinates y hy).2, ?_⟩
    rw [← expansionPolynomials_evaluate, gaugeCoordinates_gaugesOfCoordinates]
    exact hyx
  · rintro ⟨g, w, rfl⟩
    exact ⟨gaugeCoordinates g w, gaugeCoordinates_mem g w,
      expansionPolynomials_evaluate e o p.val g w⟩

theorem components_disjoint (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω)
    (q : ι × Ω → K) (b : ι → Ω) (hb : ∀ a, q (a, b a) ≠ 0)
    (p r : NormalizedFiber e o π q) (hpr : p ≠ r) :
    Disjoint (component e o π q b p) (component e o π q b r) := by
  rw [Set.disjoint_left]
  intro x hx hr
  obtain ⟨g, w, hg⟩ := (mem_component_iff e o π he q b hb p x).mp hx
  obtain ⟨h, v, hh⟩ := (mem_component_iff e o π he q b hb r x).mp hr
  have h6 := SixFamilyFibers.Parameters.coordinatesEquiv.injective (hg.trans hh.symm)
  have h5 := congrArg SixFamilyFibers.collapse h6
  simp only [SixFamilyFibers.collapse_expand] at h5
  have ho := Original.toParameters_injective e h5
  have hn := congrArg (NormalizationFibers.normalize e o) ho
  simp only [normalize_expand] at hn
  exact hpr (Subtype.ext hn)

def affineFiberSet (π : ι → Equiv.Perm Ω) (q : ι × Ω → K) :
    Set (SixFamilyFibers.ParamVar ι Ω → K) :=
  {x | SixFamilyFibers.parameterMap π (SixFamilyFibers.Parameters.ofCoordinates x) = q}

def coordinatePolynomial (π : ι → Equiv.Perm Ω) (ab : ι × Ω) :
    MvPolynomial (SixFamilyFibers.ParamVar ι Ω) K :=
  MvPolynomial.X (.inl ab.1) *
    MvPolynomial.rename Sum.inr (Sunlet.coordinatePolynomial π ab)

theorem aeval_coordinatePolynomial (π : ι → Equiv.Perm Ω)
    (x : SixFamilyFibers.ParamVar ι Ω → K) (ab : ι × Ω) :
    MvPolynomial.aeval x (coordinatePolynomial (K := K) π ab) =
      SixFamilyFibers.parameterMap π (SixFamilyFibers.Parameters.ofCoordinates x) ab := by
  rw [coordinatePolynomial, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_rename]
  change x (.inl ab.1) * MvPolynomial.aeval (x ∘ Sum.inr)
      (Sunlet.coordinatePolynomial (K := K) π ab) =
    x (.inl ab.1) * Sunlet.parameterMap π (Sunlet.Parameters.ofCoordinates (x ∘ Sum.inr)) ab
  rw [Sunlet.aeval_coordinatePolynomial_ofCoordinates]

def affineFiberIdeal (π : ι → Equiv.Perm Ω) (q : ι × Ω → K) :
    Ideal (MvPolynomial (SixFamilyFibers.ParamVar ι Ω) K) :=
  Ideal.span (Set.range (fun ab => coordinatePolynomial (K := K) π ab - MvPolynomial.C (q ab)))

theorem affineFiberSet_eq_zeroLocus (π : ι → Equiv.Perm Ω) (q : ι × Ω → K) :
    affineFiberSet π q = MvPolynomial.zeroLocus K (affineFiberIdeal π q) := by
  rw [affineFiberIdeal, MvPolynomial.zeroLocus_span]
  ext x
  constructor
  · intro hx P hP
    obtain ⟨ab, rfl⟩ := hP
    simpa only [map_sub, aeval_coordinatePolynomial, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] using congrFun hx ab
  · intro hx
    funext ab
    have h := hx _ ⟨ab, rfl⟩
    simpa only [map_sub, aeval_coordinatePolynomial, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] using h

theorem components_cover (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω)
    (q : ι × Ω → K) (b : ι → Ω) (hb : ∀ a, q (a, b a) ≠ 0)
    (hd : ∀ c, IsUnit (q (e, c))) :
    (⋃ p : NormalizedFiber e o π q, component e o π q b p) = affineFiberSet π q := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨p, hx⟩
    obtain ⟨g, w, rfl⟩ := (mem_component_iff e o π he q b hb p x).mp hx
    change SixFamilyFibers.parameterMap π (SixFamilyFibers.Parameters.ofCoordinates _) = q
    rw [SixFamilyFibers.Parameters.ofCoordinates_toCoordinates,
      SixFamilyFibers.expand_parameterMap, NormalizationFibers.expand_parameterMap e o π he]
    exact p.property
  · intro hx
    let a : SixFamilyFibers.AffineFiber π q :=
      ⟨SixFamilyFibers.Parameters.ofCoordinates x, hx⟩
    let f := SixFamilyFibers.normalizedFiberEquiv e o π he q hd
      (fun a => ⟨b a, isUnit_iff_ne_zero.mpr (hb a)⟩)
    let y := f a
    refine ⟨y.1.1, (mem_component_iff e o π he q b hb y.1.1 x).mpr
      ⟨y.1.2, y.2, ?_⟩⟩
    have h := f.symm_apply_apply a
    have hc := congrArg (fun a : SixFamilyFibers.AffineFiber π q =>
      SixFamilyFibers.Parameters.toCoordinates a.val) h
    change (SixFamilyFibers.expand
      (NormalizationFibers.expand e o y.1.1.val y.1.2).toParameters y.2).toCoordinates =
      a.val.toCoordinates at hc
    simpa only [a, SixFamilyFibers.Parameters.toCoordinates_ofCoordinates] using hc

end Sunlet.SixFamilyAlgebraic
end
end Stage_SixFamilyAlgebraic

#check "SUNLET_SixFamilyAlgebraic_READY"

#check @Sunlet.NormalizedLatinSystem.general_normalized_fiber_open_chart
#print axioms Sunlet.NormalizedLatinSystem.general_normalized_fiber_open_chart
#check @Sunlet.FiberAlgebraic.componentEquiv
#print axioms Sunlet.FiberAlgebraic.componentEquiv
#check @Sunlet.FiberAlgebraic.components_cover
#print axioms Sunlet.FiberAlgebraic.components_cover
#check @Sunlet.SixFamilyFibers.fiberEquiv
#print axioms Sunlet.SixFamilyFibers.fiberEquiv
#check @Sunlet.SixFamilyAlgebraic.componentEquiv
#print axioms Sunlet.SixFamilyAlgebraic.componentEquiv
#check @Sunlet.AlgebraicSets.PolynomialEquiv.coordinateRingEquiv
#print axioms Sunlet.AlgebraicSets.PolynomialEquiv.coordinateRingEquiv
