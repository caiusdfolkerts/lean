module

public import Unimodular.Extensions

@[expose] public section

noncomputable section

namespace Unimodular.TriangleExtension

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The old lattice is the coordinate hyperplane whose new first coordinate is zero. -/
def lift (v : Lattice n) : Lattice (n + 1) := Fin.cons 0 v

/-- The upper and lower added rays, in the first-coordinate convention. -/
def newRay (u : Lattice n) (upper : Bool) : Lattice (n + 1) :=
  if upper then Fin.cons 1 u else Fin.cons (-1) 0

/-- Coordinates in an old basis followed by the upper shear or lower reflection. -/
def coordinates (b : Module.Basis (Fin n) ℤ (Lattice n)) (u : Lattice n) :
    Bool → (Lattice (n + 1) ≃ₗ[ℤ] Lattice (n + 1))
  | true =>
    { toFun := fun x => Fin.cons (x 0) (b.equivFun (Fin.tail x - (x 0) • u))
      invFun := fun c => Fin.cons (c 0) (b.equivFun.symm (Fin.tail c) + (c 0) • u)
      left_inv := by
        intro x
        simp only [Fin.cons_zero, Fin.tail_cons, b.equivFun.symm_apply_apply, sub_add_cancel]
        exact Fin.cons_self_tail x
      right_inv := by
        intro c
        simp only [Fin.cons_zero, Fin.tail_cons, add_sub_cancel_right, b.equivFun.apply_symm_apply]
        exact Fin.cons_self_tail c
      map_add' := by
        intro x y
        have he : Fin.tail (x + y) - ((x + y) 0) • u =
            (Fin.tail x - (x 0) • u) + (Fin.tail y - (y 0) • u) := by
          ext j
          simp only [Fin.tail, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · change b.equivFun (Fin.tail (x + y) - ((x + y) 0) • u) j =
            b.equivFun (Fin.tail x - (x 0) • u) j +
              b.equivFun (Fin.tail y - (y 0) • u) j
          rw [he, map_add, Pi.add_apply]
      map_smul' := by
        intro a x
        have he : Fin.tail (a • x) - ((a • x) 0) • u =
            a • (Fin.tail x - (x 0) • u) := by
          ext j
          simp only [Fin.tail, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          ring
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · change b.equivFun (Fin.tail (a • x) - ((a • x) 0) • u) j =
            a • b.equivFun (Fin.tail x - (x 0) • u) j
          rw [he, map_smul, Pi.smul_apply] }
  | false =>
    { toFun := fun x => Fin.cons (-x 0) (b.equivFun (Fin.tail x))
      invFun := fun c => Fin.cons (-c 0) (b.equivFun.symm (Fin.tail c))
      left_inv := by
        intro x
        simp only [Fin.cons_zero, Fin.tail_cons, b.equivFun.symm_apply_apply, neg_neg]
        exact Fin.cons_self_tail x
      right_inv := by
        intro c
        simp only [Fin.cons_zero, Fin.tail_cons, b.equivFun.apply_symm_apply, neg_neg]
        exact Fin.cons_self_tail c
      map_add' := by
        intro x y
        have he : Fin.tail (x + y) = Fin.tail x + Fin.tail y := rfl
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [add_comm]
        · simp only [Fin.cons_succ, Pi.add_apply, he, map_add]
      map_smul' := by
        intro a x
        have he : Fin.tail (a • x) = a • Fin.tail x := rfl
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Pi.smul_apply, smul_eq_mul]
        · simp only [Fin.cons_succ, Pi.smul_apply, he, map_smul, RingHom.id_apply] }

def basis (b : Module.Basis (Fin n) ℤ (Lattice n)) (u : Lattice n) (upper : Bool) :
    Module.Basis (Fin (n + 1)) ℤ (Lattice (n + 1)) :=
  Module.Basis.ofEquivFun (coordinates b u upper)

@[simp] theorem repr_apply (b : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s : Bool) (x : Lattice (n + 1)) (i : Fin (n + 1)) :
    (basis b u s).repr x i = coordinates b u s x i := rfl

@[simp] theorem basis_zero (b : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s : Bool) : basis b u s 0 = newRay u s := by
  cases s <;> ext i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [basis, Module.Basis.coe_ofEquivFun, coordinates, newRay, Fin.tail, Pi.single_apply]

@[simp] theorem basis_succ (b : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s : Bool) (j : Fin n) : basis b u s j.succ = lift (b j) := by
  cases s <;> ext i <;> refine Fin.cases ?_ (fun k => ?_) i <;>
    simp [basis, Module.Basis.coe_ofEquivFun, coordinates, lift, Fin.tail, Pi.single_apply]

/-- All old rays have their original coordinates and a new zero coordinate. -/
theorem repr_lift (b : Module.Basis (Fin n) ℤ (Lattice n))
    (u v : Lattice n) (s : Bool) :
    (fun i => (basis b u s).repr (lift v) i) = Fin.cons 0 (fun j => b.repr v j) := by
  cases s <;> ext i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [coordinates, lift]

theorem repr_new_same (b : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s : Bool) :
    (fun i => (basis b u s).repr (newRay u s) i) = Fin.cons 1 0 := by
  cases s <;> ext i <;> refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [coordinates, newRay]

/-- The opposite new ray has old coordinates of u and new coordinate -1. -/
theorem repr_new_opposite (b : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s t : Bool) (hst : s ≠ t) :
    (fun i => (basis b u s).repr (newRay u t) i) =
      Fin.cons (-1) (fun j => b.repr u j) := by
  cases s <;> cases t <;> simp_all [coordinates, newRay]

def height (s : Bool) (x : Ambient (n + 1)) : ℝ := if s then x 0 else -x 0

def residual (u : Lattice n) (s : Bool) (x : Ambient (n + 1)) : Ambient n :=
  if s then Fin.tail x - (x 0) • embed u else Fin.tail x

theorem synthesis (b : Module.Basis (Fin n) ℤ (Lattice n)) (u : Lattice n)
    (s : Bool) (c : Fin (n + 1) → ℝ) :
    (∑ i, c i • embed (basis b u s i)) =
      if s then Fin.cons (c 0) ((∑ j, c j.succ • embed (b j)) + (c 0) • embed u)
      else Fin.cons (-c 0) (∑ j, c j.succ • embed (b j)) := by
  cases s <;> ext i <;> refine Fin.cases ?_ (fun k => ?_) i <;>
    simp [Fin.sum_univ_succ, newRay, lift, embed, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, add_comm]

/-- Exact real-coordinate formula, derived from a synthesis identity in the real vector
space. It is valid for arbitrary real points, not just lattice points. -/
theorem realCoordinates_basis (b : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s : Bool) (x : Ambient (n + 1)) :
    realCoordinates (basis b u s) x =
      Fin.cons (height s x) (realCoordinates b (residual u s x)) := by
  let c : Fin (n + 1) → ℝ := Fin.cons (height s x) (realCoordinates b (residual u s x))
  have hs : (∑ i, c i • embed (basis b u s i)) = x := by
    rw [synthesis]
    cases s <;> simp only [Bool.false_eq_true, if_false, if_true, c, Fin.cons_zero,
      Fin.cons_succ, height, residual, sum_basis_realCoordinates, neg_neg, sub_add_cancel]
    · exact Fin.cons_self_tail x
    · exact Fin.cons_self_tail x
  have h := congrArg (realCoordinates (basis b u s)) hs
  rw [realCoordinates_sum_basis] at h
  exact h.symm

theorem mem_cone_iff (b : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s : Bool) (x : Ambient (n + 1)) :
    x ∈ basisCone (basis b u s) ↔
      0 ≤ height s x ∧ residual u s x ∈ basisCone b := by
  rw [mem_basisCone_iff, realCoordinates_basis, mem_basisCone_iff]
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]

theorem mem_basisFace_iff_coordinates (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (x : Ambient n) :
    x ∈ basisFace b I ↔
      (∀ i, 0 ≤ realCoordinates b x i) ∧ (∀ i ∉ I, realCoordinates b x i = 0) := by
  constructor
  · rintro ⟨c, hc, hz, rfl⟩
    simpa only [realCoordinates_sum_basis] using And.intro hc hz
  · rintro ⟨hc, hz⟩
    exact ⟨realCoordinates b x, hc, hz, sum_basis_realCoordinates b x⟩

def indices (I : Finset (Fin n)) (keepNew : Bool) : Finset (Fin (n + 1)) :=
  I.image Fin.succ ∪ if keepNew then {0} else ∅

@[simp] theorem zero_mem_indices (I : Finset (Fin n)) (k : Bool) :
    (0 : Fin (n + 1)) ∈ indices I k ↔ k = true := by
  cases k <;> simp [indices]

@[simp] theorem succ_mem_indices (I : Finset (Fin n)) (k : Bool) (i : Fin n) :
    i.succ ∈ indices I k ↔ i ∈ I := by
  cases k <;> simp [indices]

theorem mem_face_iff (b : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s k : Bool) (I : Finset (Fin n)) (x : Ambient (n + 1)) :
    x ∈ basisFace (basis b u s) (indices I k) ↔
      0 ≤ height s x ∧ (k = false → height s x = 0) ∧
        residual u s x ∈ basisFace b I := by
  rw [mem_basisFace_iff_coordinates, realCoordinates_basis, mem_basisFace_iff_coordinates]
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, zero_mem_indices,
    succ_mem_indices]
  cases k <;> simp <;> tauto

theorem height_eq_neg_of_ne (s t : Bool) (hst : s ≠ t) (x : Ambient (n + 1)) :
    height s x = -height t x := by cases s <;> cases t <;> simp_all [height]

theorem residual_of_height_zero (u : Lattice n) (s : Bool) (x : Ambient (n + 1))
    (hx : height s x = 0) : residual u s x = Fin.tail x := by
  cases s <;> simp_all [height, residual]

/-- Cones on the same side intersect in the corresponding lifted old face, with the new
ray retained. -/
theorem intersection_same (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s : Bool) (I : Finset (Fin n))
    (hI : basisCone b ∩ basisCone c = basisFace b I) :
    basisCone (basis b u s) ∩ basisCone (basis c u s) =
      basisFace (basis b u s) (indices I true) := by
  ext x
  have h := Set.ext_iff.1 hI (residual u s x)
  simp only [Set.mem_inter_iff, mem_cone_iff, mem_face_iff, Bool.true_eq_false,
    false_implies, true_and] at *
  tauto

/-- Opposite-side cones meet exactly in their old intersection on the coordinate
hyperplane; the new ray is absent from this face. -/
theorem intersection_opposite (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (u : Lattice n) (s t : Bool) (hst : s ≠ t) (I : Finset (Fin n))
    (hI : basisCone b ∩ basisCone c = basisFace b I) :
    basisCone (basis b u s) ∩ basisCone (basis c u t) =
      basisFace (basis b u s) (indices I false) := by
  ext x
  rw [Set.mem_inter_iff, mem_cone_iff, mem_cone_iff, mem_face_iff]
  have hneg := height_eq_neg_of_ne s t hst x
  constructor
  · rintro ⟨⟨hs, hbs⟩, ⟨ht, hct⟩⟩
    have hz : height s x = 0 := by linarith
    have hz' : height t x = 0 := by linarith
    have hrs := residual_of_height_zero u s x hz
    have hrt := residual_of_height_zero u t x hz'
    refine ⟨hs, fun _ => hz, ?_⟩
    rw [← hI]
    exact ⟨hbs, hrs.symm ▸ hrt ▸ hct⟩
  · rintro ⟨hs, hz, hf⟩
    have hz := hz rfl
    have hz' : height t x = 0 := by linarith
    have hrs := residual_of_height_zero u s x hz
    have hrt := residual_of_height_zero u t x hz'
    rw [← hI] at hf
    exact ⟨⟨hs, hf.1⟩, ⟨by linarith, hrt.symm ▸ hrs ▸ hf.2⟩⟩

def maximal (fan : SmoothCompleteFan n) (u : Lattice n) :
    Finset (Module.Basis (Fin (n + 1)) ℤ (Lattice (n + 1))) :=
  (fan.maximal ×ˢ (Finset.univ : Finset Bool)).image (fun p => basis p.1 u p.2)

theorem mem_maximal (fan : SmoothCompleteFan n) (u : Lattice n)
    (B : Module.Basis (Fin (n + 1)) ℤ (Lattice (n + 1))) :
    B ∈ maximal fan u ↔ ∃ b ∈ fan.maximal, ∃ s, basis b u s = B := by
  simp only [maximal, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true,
    Prod.exists, exists_and_left]

/-- The elementary triangle extension is an actual complete smooth fan. Its intersection
field proves face-to-face compatibility between every pair of maximal cones. -/
def fan (old : SmoothCompleteFan n) (u : Lattice n) : SmoothCompleteFan (n + 1) where
  maximal := maximal old u
  complete x := by
    by_cases hx : 0 ≤ x 0
    · obtain ⟨b, hb, hbx⟩ := old.complete (residual u true x)
      exact ⟨basis b u true, (mem_maximal old u _).2 ⟨b, hb, true, rfl⟩,
        (mem_cone_iff b u true x).2 ⟨hx, hbx⟩⟩
    · obtain ⟨b, hb, hbx⟩ := old.complete (residual u false x)
      exact ⟨basis b u false, (mem_maximal old u _).2 ⟨b, hb, false, rfl⟩,
        (mem_cone_iff b u false x).2 ⟨by dsimp [height]; linarith, hbx⟩⟩
  intersection := by
    intro B hB C hC
    obtain ⟨b, hb, s, rfl⟩ := (mem_maximal old u _).1 hB
    obtain ⟨c, hc, t, rfl⟩ := (mem_maximal old u _).1 hC
    obtain ⟨I, J, hI, hJ⟩ := old.intersection b hb c hc
    by_cases hst : s = t
    · subst t
      refine ⟨indices I true, indices J true, intersection_same b c u s I hI, ?_⟩
      rw [Set.inter_comm]
      exact intersection_same c b u s J (by rw [Set.inter_comm]; exact hJ)
    · refine ⟨indices I false, indices J false, intersection_opposite b c u s t hst I hI, ?_⟩
      rw [Set.inter_comm]
      exact intersection_opposite c b u t s (Ne.symm hst) J (by rw [Set.inter_comm]; exact hJ)

/-- The ray set is exactly the lifted old ray set together with the two added rays. -/
theorem rays_eq (old : SmoothCompleteFan n) (u : Lattice n) :
    (fan old u).rays = lift '' old.rays ∪ {newRay u true, newRay u false} := by
  ext v
  constructor
  · rintro ⟨B, hB, i, rfl⟩
    obtain ⟨b, hb, s, rfl⟩ := (mem_maximal old u _).1 hB
    refine Fin.cases ?_ (fun j => ?_) i
    · right
      cases s <;> simp
    · left
      exact ⟨b j, ⟨b, hb, j, rfl⟩, (basis_succ b u s j).symm⟩
  · intro hv
    obtain ⟨b, hb, _⟩ := old.complete 0
    rcases hv with ⟨v, hv, rfl⟩ | hv
    · obtain ⟨c, hc, i, rfl⟩ := hv
      exact ⟨basis c u true, (mem_maximal old u _).2 ⟨c, hc, true, rfl⟩,
        i.succ, basis_succ c u true i⟩
    · rcases hv with hv | hv
      · exact ⟨basis b u true, (mem_maximal old u _).2 ⟨b, hb, true, rfl⟩,
          0, (basis_zero b u true).trans hv.symm⟩
      · have hv : v = newRay u false := hv
        exact ⟨basis b u false, (mem_maximal old u _).2 ⟨b, hb, false, rfl⟩,
          0, (basis_zero b u false).trans hv.symm⟩

/-- Proposition 6.7's local operation preserves the exact positive-coordinate criterion
for deep monotonicity, using the selected old ray in the opposite-ray calculation. -/
theorem positiveCriterion_of_bound (old : SmoothCompleteFan n) (u : Lattice n)
    (hu : ∀ b ∈ old.maximal, ∑ i, max (b.repr u i) 0 ≤ 1)
    (hold : old.PositiveCoordinateCriterion) :
    (fan old u).PositiveCoordinateCriterion := by
  intro B hB v hv
  obtain ⟨b, hb, s, rfl⟩ := (mem_maximal old u _).1 hB
  rw [rays_eq] at hv
  rcases hv with ⟨v, hv, rfl⟩ | hv
  · have hcoord := repr_lift b u v s
    have hsum := congrArg (fun f : Fin (n + 1) → ℤ => ∑ i, max (f i) 0) hcoord
    rw [hsum]
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, max_self, zero_add]
      using hold b hb v hv
  · have hnew : ∃ t, v = newRay u t := by
      rcases hv with hv | hv
      · exact ⟨true, hv⟩
      · exact ⟨false, hv⟩
    obtain ⟨t, rfl⟩ := hnew
    by_cases hst : s = t
    · subst t
      have hcoord := repr_new_same b u s
      have hsum := congrArg (fun f : Fin (n + 1) → ℤ => ∑ i, max (f i) 0) hcoord
      rw [hsum]
      simp [Fin.sum_univ_succ]
    · have hcoord := repr_new_opposite b u s t hst
      have hsum := congrArg (fun f : Fin (n + 1) → ℤ => ∑ i, max (f i) 0) hcoord
      rw [hsum]
      simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, max_eq_right (by omega :
        (-1 : ℤ) ≤ 0), zero_add] using hu b hb

/-- The paper's selected-ray version of the criterion-preservation theorem. -/
theorem positiveCriterion (old : SmoothCompleteFan n) (u : Lattice n)
    (hu : u ∈ old.rays) (hold : old.PositiveCoordinateCriterion) :
    (fan old u).PositiveCoordinateCriterion :=
  positiveCriterion_of_bound old u (fun b hb => hold b hb u hu) hold

/-- The added vectors form the literal triangle relation over the original lattice. -/
theorem triangle_relation (u : Lattice n) :
    newRay u true + newRay u false = lift u := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [newRay, lift]

theorem lift_injective : Function.Injective (lift : Lattice n → Lattice (n + 1)) := by
  intro x y h
  simpa [lift] using congrArg Fin.tail h

theorem basis_pair_injective (u : Lattice n) :
    Function.Injective (fun p : (Module.Basis (Fin n) ℤ (Lattice n)) × Bool =>
      basis p.1 u p.2) := by
  rintro ⟨b, s⟩ ⟨c, t⟩ he
  have hz := congrArg (fun B : Module.Basis (Fin (n + 1)) ℤ (Lattice (n + 1)) => B 0 0) he
  simp only [basis_zero] at hz
  have hst : s = t := by
    cases s <;> cases t
    · rfl
    · norm_num [newRay] at hz
    · norm_num [newRay] at hz
    · rfl
  subst t
  have hbc : b = c := by
    apply DFunLike.ext
    intro i
    have h := congrArg (fun B : Module.Basis (Fin (n + 1)) ℤ (Lattice (n + 1)) =>
      B i.succ) he
    rw [basis_succ, basis_succ] at h
    exact lift_injective h
  cases hbc
  rfl

/-- Every old maximal cone gives exactly two new maximal bases; none collapse. -/
theorem maximal_card (old : SmoothCompleteFan n) (u : Lattice n) :
    (fan old u).maximal.card = 2 * old.maximal.card := by
  change (maximal old u).card = _
  rw [maximal, Finset.card_image_of_injective _ (basis_pair_injective u)]
  simp [Finset.card_product, Nat.mul_comm]

theorem rays_finite (old : SmoothCompleteFan n) : old.rays.Finite := by
  refine (Set.finite_range (fun p : old.maximal × Fin n => p.1.val p.2)).subset ?_
  rintro x ⟨b, hb, i, he⟩
  exact ⟨(⟨b, hb⟩, i), he⟩

theorem newRay_not_mem_lift (u : Lattice n) (s : Bool) (S : Set (Lattice n)) :
    newRay u s ∉ lift '' S := by
  rintro ⟨v, hv, he⟩
  have h := congrFun he 0
  cases s <;> norm_num [lift, newRay] at h

theorem newRays_ne (u : Lattice n) : newRay u true ≠ newRay u false := by
  intro h
  have h := congrFun h 0
  norm_num [newRay] at h

/-- Exactly two rays are added, in every dimension and for every chosen old vector. -/
theorem rays_ncard (old : SmoothCompleteFan n) (u : Lattice n) :
    (fan old u).rays.ncard = old.rays.ncard + 2 := by
  have hd : Disjoint (lift '' old.rays) {newRay u true, newRay u false} := by
    rw [Set.disjoint_left]
    intro x hx hnew
    rcases hnew with h | h
    · exact newRay_not_mem_lift u true old.rays (h ▸ hx)
    · have h : x = newRay u false := h
      exact newRay_not_mem_lift u false old.rays (h ▸ hx)
  rw [rays_eq, Set.ncard_union_eq hd ((rays_finite old).image lift) (Set.toFinite _),
    Set.ncard_image_of_injective _ lift_injective, Set.ncard_pair (newRays_ne u)]

/-- The unique complete fan in the zero lattice, used only to define the initial P¹ fan. -/
def zeroFan : SmoothCompleteFan 0 where
  maximal := {Pi.basisFun ℤ (Fin 0)}
  complete x := by
    refine ⟨Pi.basisFun ℤ (Fin 0), by simp, fun _ => 0, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · exact Subsingleton.elim _ _
  intersection := by
    intro b hb c hc
    have hcone (b : Module.Basis (Fin 0) ℤ (Lattice 0)) (x : Ambient 0) :
        x ∈ basisCone b := ⟨fun _ => 0, fun i => Fin.elim0 i, Subsingleton.elim _ _⟩
    have hface (b : Module.Basis (Fin 0) ℤ (Lattice 0)) (x : Ambient 0) :
        x ∈ basisFace b ∅ := ⟨fun _ => 0, fun i => Fin.elim0 i,
          fun i => Fin.elim0 i, Subsingleton.elim _ _⟩
    refine ⟨∅, ∅, ?_, ?_⟩ <;> ext x <;>
      exact ⟨fun _ => hface _ x, fun _ => ⟨hcone _ x, hcone _ x⟩⟩

theorem zeroFan_positiveCriterion : zeroFan.PositiveCoordinateCriterion := by
  rintro b hb u ⟨c, hc, i, hi⟩
  exact Fin.elim0 i

/-- The complete one-dimensional fan with the two primitive antipodal rays. -/
def projectiveLineFan : SmoothCompleteFan 1 := fan zeroFan 0

theorem projectiveLineFan_positiveCriterion : projectiveLineFan.PositiveCoordinateCriterion := by
  apply positiveCriterion_of_bound zeroFan 0 _ zeroFan_positiveCriterion
  intro b hb
  simp

theorem projectiveLineFan_maximal_card : projectiveLineFan.maximal.card = 2 := by
  rw [projectiveLineFan, maximal_card]
  simp [zeroFan]

theorem projectiveLineFan_rays_ncard : projectiveLineFan.rays.ncard = 2 := by
  rw [projectiveLineFan, rays_ncard]
  have hz : zeroFan.rays = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    rintro x ⟨b, hb, i, hi⟩
    exact Fin.elim0 i
  simp [hz]

end Unimodular.TriangleExtension

end
