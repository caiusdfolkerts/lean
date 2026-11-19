module

public import Recovery.Unimodular.WeakFano.WeightedPolytope
public import Recovery.Unimodular.WeakFano.IntegerGenericHeights

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace Unimodular.WeightedPolytopes

variable {n : ℕ}

/-- The actual excess at a candidate vertex, as an integral linear form in heights. -/
def wall (U : Finset (Lattice n)) (b : RayBasis U) (u : {u // u ∈ U}) :
    ({u // u ∈ U} → ℤ) →ₗ[ℤ] ℤ where
  toFun h := (∑ i, b.val.repr u.val i * h ⟨b.val i, b.property i⟩) - h u
  map_add' h k := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' a h := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem wall_ne_zero (U : Finset (Lattice n)) (b : RayBasis U)
    (u : {u // u ∈ U}) (hu : ∀ i, b.val i ≠ u.val) : wall U b u ≠ 0 := by
  classical
  have hne (i : Fin n) : (⟨b.val i, b.property i⟩ : {u // u ∈ U}) ≠ u := by
    intro he
    exact hu i (congrArg Subtype.val he)
  have hval : wall U b u (Pi.single u 1) = -1 := by
    simp [wall, Pi.single_apply, hne, fun i => (hne i).symm]
  intro he
  rw [he] at hval
  norm_num at hval

theorem wall_eq_corner_excess (U : Finset (Lattice n)) (b : RayBasis U)
    (u : {u // u ∈ U}) (h : Lattice n → ℤ) :
    (wall U b u (fun v => h v.val) : ℝ) =
      pairing (embed (latticeCorner b.val h)) u.val - h u.val := by
  rw [embed_latticeCorner, pairing_dualCorner]
  simp [wall, Int.cast_sum, mul_comm]

/-- An assignment chosen without assuming a fan or a simple polytope. -/
structure RegularHeight (U : Finset (Lattice n)) (h : Lattice n → ℤ) : Prop where
  positive : ∀ u ∈ U, 0 < h u
  active_exact : ∀ b : RayBasis U, ∀ u ∈ U,
    pairing (embed (latticeCorner b.val h)) u = h u → ∃ i, b.val i = u
  unit_feasible : ∀ b : RayBasis U,
    embed (latticeCorner b.val h) ∈ carrier U (fun u => (h u : ℝ)) →
      dualCorner b.val (fun _ => 1) ∈ carrier U (fun _ => 1)

/-- Generic integer heights produce a simple polytope and preserve every
feasible basis corner of the original unit polytope. No genericity, smallness,
projectivity, or smoothness condition is assumed. -/
theorem exists_regular_height (U : Finset (Lattice n)) :
    ∃ h : Lattice n → ℤ, RegularHeight U h := by
  classical
  let E := {u // u ∈ U}
  let K := {bu : RayBasis U × E // ∀ i, bu.1.val i ≠ bu.2.val}
  letI : Fintype (RayBasis U) := Fintype.ofFinite _
  letI : Fintype K := Fintype.ofFinite _
  let L : K → (E → ℤ) →ₗ[ℤ] ℤ := fun k => wall U k.val.1 k.val.2
  obtain ⟨h', hpos, havoid, hsign⟩ := IntegerGenericHeights.exists_positive_regular_height L
    (fun k => wall_ne_zero U k.val.1 k.val.2 k.property)
  let h : Lattice n → ℤ := fun u => if hu : u ∈ U then h' ⟨u, hu⟩ else 0
  have hext (u : E) : h u.val = h' u := by simp [h, u.property]
  have hext' : (fun u : E => h u.val) = h' := funext hext
  refine ⟨h, ⟨?_, ?_, ?_⟩⟩
  · intro u hu
    simpa only [hext ⟨u, hu⟩] using hpos ⟨u, hu⟩
  · intro b u hu ha
    by_contra! hn
    let k : K := ⟨(b, ⟨u, hu⟩), hn⟩
    have hc : (L k h' : ℝ) = 0 := by
      change (wall U b ⟨u, hu⟩ h' : ℝ) = 0
      rw [← hext', wall_eq_corner_excess, ha, sub_self]
    exact havoid k (by exact_mod_cast hc)
  · intro b hb u hu
    by_cases hx : ∃ i, b.val i = u
    · obtain ⟨i, rfl⟩ := hx
      rw [pairing_dualCorner_basis]
    · have hn : ∀ i, b.val i ≠ u := by simpa using hx
      let k : K := ⟨(b, ⟨u, hu⟩), hn⟩
      by_contra hh
      have hunit : 0 < L k (fun _ => 1) := by
        have hh' : 1 < pairing (dualCorner b.val (fun _ => 1)) u := lt_of_not_ge hh
        have hc := wall_eq_corner_excess U b ⟨u, hu⟩ (fun _ => 1)
        simp only [embed_latticeCorner, Int.cast_one] at hc
        change (L k (fun _ => 1) : ℝ) = _ at hc
        have hreal : (0 : ℝ) < (L k (fun _ => 1) : ℝ) := by linarith
        exact_mod_cast hreal
      have hnew := hsign k hunit
      have hc := wall_eq_corner_excess U b ⟨u, hu⟩ h
      rw [hext'] at hc
      change (L k h' : ℝ) = _ at hc
      have hreal : (0 : ℝ) < (L k h' : ℝ) := by exact_mod_cast hnew
      have hp := hb u hu
      linarith

end Unimodular.WeightedPolytopes

#print axioms Unimodular.WeightedPolytopes.wall_ne_zero
#print axioms Unimodular.WeightedPolytopes.exists_regular_height
#check Unimodular.WeightedPolytopes.exists_regular_height
