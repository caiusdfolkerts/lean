module

public import sunlet.generic_pair_geometry

/-!
# Characters of the actual nonidentity-color parameter fibers

This bridge keeps the coefficient parameters affine, and only regards them
as units after proving their nonvanishing. It identifies the conventions
used by the generic ratio map with the checked universal-loop character
calculation, including an arbitrary explicit relabelling of the colors.
-/

@[expose] public section
noncomputable section

namespace Sunlet.LoopData

open ToricPairAlgebra

variable {Ω ι K : Type*} [DecidableEq Ω] [Field K]
  (L : LoopData Ω) (e : ι ≃ {x : Ω // x ≠ L.identity})
  (π : ι → Equiv.Perm Ω) (hπ : ∀ a, π a = L.left (e a))

def toricParametersOfNonzero (U : ι → K) (h : Ω → Kˣ)
    (hU : ∀ a, U a ≠ 0) (hbase : h L.identity = 1) : L.ToricParameters (M := Kˣ) where
  coefficient x := if hx : x = L.identity then 1 else
    Units.mk0 (U (e.symm ⟨x, hx⟩)) (hU _)
  torus := h
  coefficient_identity := by simp
  torus_identity := hbase

@[simp] theorem toricParametersOfNonzero_torus (U : ι → K) (h : Ω → Kˣ)
    (hU : ∀ a, U a ≠ 0) (hbase : h L.identity = 1) (x : Ω) :
    (L.toricParametersOfNonzero e U h hU hbase).torus x = h x := rfl

@[simp] theorem toricParametersOfNonzero_coefficient (U : ι → K) (h : Ω → Kˣ)
    (hU : ∀ a, U a ≠ 0) (hbase : h L.identity = 1) (a : ι) :
    ((L.toricParametersOfNonzero e U h hU hbase).coefficient (e a)).val = U a := by
  simp [toricParametersOfNonzero, (e a).property]

include hπ in
theorem toricParametersOfNonzero_coordinate (U : ι → K) (h : Ω → Kˣ)
    (hU : ∀ a, U a ≠ 0) (hbase : h L.identity = 1) (a : ι) (x : Ω) :
    ((L.toricParametersOfNonzero e U h hU hbase).coordinate (e a) x).val =
      toricPoint π U h (a, x) := by
  simp [ToricParameters.coordinate, toricPoint, ToricDifferential.coordinate,
    ToricDifferential.ratio, toricParametersOfNonzero, (e a).property, hπ, LoopData.mul,
    div_eq_mul_inv, mul_assoc]

include hπ in
theorem nonzero_parameters_same_coordinates
    (U V : ι → K) (h g : Ω → Kˣ) (hU : ∀ a, U a ≠ 0) (hV : ∀ a, V a ≠ 0)
    (hbase : h L.identity = 1) (hgbase : g L.identity = 1)
    (heq : toricPoint π U h = toricPoint π V g) :
    ∀ a x, (L.toricParametersOfNonzero e U h hU hbase).coordinate a x =
      (L.toricParametersOfNonzero e V g hV hgbase).coordinate a x := by
  intro a x
  by_cases ha : a = L.identity
  · subst a
    simp [ToricParameters.coordinate, ToricParameters.coefficient_identity]
  · obtain ⟨c, hc⟩ := e.surjective ⟨a, ha⟩
    have hva : (e c).val = a := congrArg Subtype.val hc
    rw [← hva]
    apply Units.ext
    rw [toricParametersOfNonzero_coordinate L e π hπ,
      toricParametersOfNonzero_coordinate L e π hπ]
    exact congrFun heq (c, x)

def characterOfPointEquality
    (U V : ι → K) (h g : Ω → Kˣ) (hU : ∀ a, U a ≠ 0) (hV : ∀ a, V a ≠ 0)
    (hbase : h L.identity = 1) (hgbase : g L.identity = 1)
    (heq : toricPoint π U h = toricPoint π V g) : L.characterSubgroup (M := Kˣ) :=
  (L.toricParametersOfNonzero e U h hU hbase).quotientCharacter
    (L.toricParametersOfNonzero e V g hV hgbase)
    (L.nonzero_parameters_same_coordinates e π hπ U V h g hU hV hbase hgbase heq)

@[simp] theorem characterOfPointEquality_apply
    (U V : ι → K) (h g : Ω → Kˣ) (hU : ∀ a, U a ≠ 0) (hV : ∀ a, V a ≠ 0)
    (hbase : h L.identity = 1) (hgbase : g L.identity = 1)
    (heq : toricPoint π U h = toricPoint π V g) (x : Ω) :
    (L.characterOfPointEquality e π hπ U V h g hU hV hbase hgbase heq).val x =
      g x / h x := rfl

theorem coefficient_of_point_equality
    (U V : ι → K) (h g : Ω → Kˣ) (hU : ∀ a, U a ≠ 0) (hV : ∀ a, V a ≠ 0)
    (hbase : h L.identity = 1) (hgbase : g L.identity = 1)
    (heq : toricPoint π U h = toricPoint π V g) (a : ι) :
    V a = U a *
      ((L.characterOfPointEquality e π hπ U V h g hU hV hbase hgbase heq).val (e a)).val := by
  have hc := ToricParameters.coefficient_of_same_coordinates
    (L.toricParametersOfNonzero e U h hU hbase)
    (L.toricParametersOfNonzero e V g hV hgbase)
    (L.nonzero_parameters_same_coordinates e π hπ U V h g hU hV hbase hgbase heq) (e a)
  have hv := congrArg Units.val hc
  simpa only [Units.val_mul, toricParametersOfNonzero_coefficient,
    toricParametersOfNonzero_torus, characterOfPointEquality_apply] using hv

theorem torus_of_point_equality
    (U V : ι → K) (h g : Ω → Kˣ) (hU : ∀ a, U a ≠ 0) (hV : ∀ a, V a ≠ 0)
    (hbase : h L.identity = 1) (hgbase : g L.identity = 1)
    (heq : toricPoint π U h = toricPoint π V g) (x : Ω) :
    g x = h x *
      (L.characterOfPointEquality e π hπ U V h g hU hV hbase hgbase heq).val x := by
  rw [characterOfPointEquality_apply]
  simp [mul_comm]

include hπ in
/-- Characters preserve the literal ratio coordinates, including affine
coefficient values that happen to vanish. -/
theorem character_action_point (U : ι → K) (h : Ω → Kˣ)
    (χ : L.characterSubgroup (M := Kˣ)) :
    toricPoint π (fun a => U a * (χ.val (e a)).val)
      (fun x => h x * χ.val x) = toricPoint π U h := by
  funext ax
  rcases ax with ⟨a, x⟩
  have hχ : χ.val (π a x) = χ.val (e a) * χ.val x := by
    rw [hπ]
    exact χ.property.2 (e a) x
  simp only [toricPoint, ToricDifferential.coordinate, ToricDifferential.ratio,
    Units.val_mul, hχ]
  field_simp
  <;> ring

end Sunlet.LoopData
