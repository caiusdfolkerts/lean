module

public import Continuation.Runtime.HellerRootLattice
public import Continuation.SeriesParallel.All
public import Unimodular.FanBridge
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Basis.SMul

/-! Exact historically checked Heller proof bodies, collected without changing
any mathematical declaration. This new aggregate still requires its own compiler
receipt under the current pin. See audit/theorem-7-1-composition. -/

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 10000



/- Exact historical source: Unimodular/HellerAffine.lean. -/
section Recovered71_HellerAffine

/-! # The determinant variation behind Heller's bound

These lemmas work in arbitrary finite rank. They measure the entire range of an
integer affine function on a Boolean cube, and apply that range to bordered
minors. The bounds are proved symbolically, not by finite-rank enumeration.
-/

namespace Unimodular.Heller

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The width of an affine function on the vertices of a unit cube is the sum
of the absolute values of its coefficients. -/
theorem cube_width (z : ℤ) (a : I → ℤ) :
    ∃ lo hi : I → ℤ,
      (∀ i, lo i = 0 ∨ lo i = 1) ∧
      (∀ i, hi i = 0 ∨ hi i = 1) ∧
      (z + ∑ i, hi i * a i) - (z + ∑ i, lo i * a i) = ∑ i, |a i| := by
  let lo : I → ℤ := fun i => if 0 ≤ a i then 0 else 1
  let hi : I → ℤ := fun i => if 0 ≤ a i then 1 else 0
  refine ⟨lo, hi, ?_, ?_, ?_⟩
  · intro i
    by_cases h : 0 ≤ a i <;> simp [lo, h]
  · intro i
    by_cases h : 0 ≤ a i <;> simp [hi, h]
  · simp only [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : 0 ≤ a i
    · simp [hi, lo, h, abs_of_nonneg h]
    · simp [hi, lo, h, abs_of_neg (lt_of_not_ge h)]

/-- Integer affine values all lying in [-B,B] force coefficient mass at most 2B. -/
theorem coefficient_mass_le {z B : ℤ} {a : I → ℤ}
    (h : ∀ t : I → ℤ, (∀ i, t i = 0 ∨ t i = 1) →
      |z + ∑ i, t i * a i| ≤ B) :
    (∑ i, |a i|) ≤ 2 * B := by
  obtain ⟨lo, hi, hlo, hhi, he⟩ := cube_width z a
  have hl := abs_le.mp (h lo hlo)
  have hh := abs_le.mp (h hi hhi)
  omega

/-- A coefficient equal to a unit consumes one unit of the determinant's total
width two. This is the step that bounds the number of doubled quotient lines. -/
theorem remaining_mass_le_one {z : ℤ} {a : I → ℤ} (i : I)
    (hi : |a i| = 1)
    (h : ∀ t : I → ℤ, (∀ j, t j = 0 ∨ t j = 1) →
      |z + ∑ j, t j * a j| ≤ 1) :
    (∑ j ∈ Finset.univ.erase i, |a j|) ≤ 1 := by
  have hb := coefficient_mass_le h
  have he := Finset.sum_erase_add (Finset.univ) (fun j => |a j|) (Finset.mem_univ i)
  rw [hi] at he
  omega

/-- The square matrix of one lifted vector and an ordered lifted quotient basis. -/
def bordered (a : ℤ) (h v : I → ℤ) : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ :=
  Matrix.fromBlocks (fun _ _ => a) (fun _ i => h i) (fun i _ => v i) 1

/-- Its determinant is affine in all independently chosen lift heights. -/
theorem det_bordered (a : ℤ) (h v : I → ℤ) :
    (bordered a h v).det = a - ∑ i, h i * v i := by
  change (Matrix.fromBlocks (Matrix.of (fun (_ _ : Unit) => a))
    (Matrix.of (fun (_ : Unit) i => h i)) (Matrix.of (fun i (_ : Unit) => v i))
    (1 : Matrix I I ℤ)).det = _
  rw [Matrix.det_fromBlocks_one₂₂]
  simp [Matrix.det_unique, Matrix.sub_apply, Matrix.mul_apply]

/-- Symbolic determinant variation for an arbitrary selection of doubled basis
columns. The coefficient of the extra lifted vector is one. -/
theorem doubled_coordinate_mass_le_one (J : Finset I) (a : ℤ) (h v : I → ℤ)
    (hb : ∀ (s : I → ℤ) (t : ℤ), (∀ i, s i = 0 ∨ s i = 1) →
      (t = 0 ∨ t = 1) →
      |(bordered (a + t) (fun i => h i + if i ∈ J then s i else 0) v).det| ≤ 1) :
    (∑ i ∈ J, |v i|) ≤ 1 := by
  let lo : I → ℤ := fun i => if 0 ≤ v i then 1 else 0
  let hi : I → ℤ := fun i => if 0 ≤ v i then 0 else 1
  have hlo : ∀ i, lo i = 0 ∨ lo i = 1 := by
    intro i
    by_cases h : 0 ≤ v i <;> simp [lo, h]
  have hhi : ∀ i, hi i = 0 ∨ hi i = 1 := by
    intro i
    by_cases h : 0 ≤ v i <;> simp [hi, h]
  have hl := abs_le.mp (hb lo 0 hlo (Or.inl rfl))
  have hh := abs_le.mp (hb hi 1 hhi (Or.inr rfl))
  rw [det_bordered] at hl hh
  have he : (∑ i, (h i + if i ∈ J then lo i else 0) * v i) -
      (∑ i, (h i + if i ∈ J then hi i else 0) * v i) = ∑ i ∈ J, |v i| := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ i, if i ∈ J then |v i| else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hj : i ∈ J
        · by_cases hv : 0 ≤ v i
          · simp [lo, hi, hj, hv, abs_of_nonneg hv, add_mul]
          · simp [lo, hi, hj, hv, abs_of_neg (lt_of_not_ge hv), add_mul]
        · simp [hj]
      _ = _ := by simp
  omega

end Unimodular.Heller

end Recovered71_HellerAffine

/- Exact historical source: Unimodular/HellerLifts.lean. -/
section Recovered71_HellerLifts

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

variable {n : ℕ}

/-- A vector and a quotient basis may be lifted to arbitrary heights. The
resulting maximal minor is the affine height correction times the quotient minor. -/
theorem det_lifted_basis (b : Module.Basis (Fin n) ℤ (Lattice n))
    (l : Fin n → Lattice (n + 1)) (hl : ∀ i, tail (l i) = b i)
    (x : Lattice (n + 1)) :
    (Pi.basisFun ℤ (Fin (n + 1))).det (Fin.cons x l) =
      (x 0 - ∑ i, l i 0 * b.repr (tail x) i) *
        (Pi.basisFun ℤ (Fin n)).det b := by
  let e : Lattice (n + 1) := Pi.single 0 1
  let a : ℤ := x 0 - ∑ i, l i 0 * b.repr (tail x) i
  let v : Fin n → ℤ := fun i => b.repr (tail x) i
  have hx : x = a • e + ∑ i, v i • l i := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
        e, Pi.single_eq_same, mul_one, a, v]
      simp only [mul_comm (l _ 0)]
      omega
    · have hb := congrFun (b.sum_repr (tail x)) k
      have hli (i : Fin n) : l i k.succ = b i k := congrFun (hl i) k
      simpa only [tail, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
        smul_eq_mul, e, Pi.single_eq_of_ne (Fin.succ_ne_zero k), mul_zero,
        zero_add, hli, v] using hb.symm
  let f : Fin (n + 1) → Lattice (n + 1) := Fin.cons e l
  have hu (y : Lattice (n + 1)) : Fin.cons y l = Function.update f 0 y := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [f]
  conv_lhs =>
    rw [hu, hx, (Pi.basisFun ℤ (Fin (n + 1))).det.map_update_add,
      (Pi.basisFun ℤ (Fin (n + 1))).det.map_update_smul,
      (Pi.basisFun ℤ (Fin (n + 1))).det.map_update_sum]
  have hz (i : Fin n) :
      (Pi.basisFun ℤ (Fin (n + 1))).det (Function.update f 0 (v i • l i)) = 0 := by
    rw [(Pi.basisFun ℤ (Fin (n + 1))).det.map_update_smul]
    have he : l i = f i.succ := by simp [f]
    rw [he, (Pi.basisFun ℤ (Fin (n + 1))).det.map_update_self f
      (Fin.succ_ne_zero i).symm, smul_zero]
  simp only [hz, Finset.sum_const_zero, add_zero, smul_eq_mul]
  have hf : Function.update f 0 e = f := by
    simp [f]
  rw [hf]
  change a * (Pi.basisFun ℤ (Fin (n + 1))).det (Fin.cons (Pi.single 0 1) l) = _
  rw [det_cons_first]
  have he : (fun i => tail (l i)) = b := funext hl
  rw [he]

/-- Uniform maximal-minor bounds become the exact affine height bounds, since
the quotient basis determinant is a unit in the unchanged lattice. -/
theorem lifted_height_abs_le_one (U : Set (Lattice (n + 1)))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1))) (fun x : U => x.val))
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (l : Fin n → Lattice (n + 1)) (hl : ∀ i, tail (l i) = b i)
    (hlU : ∀ i, l i ∈ U) {x : Lattice (n + 1)} (hx : x ∈ U) :
    |x 0 - ∑ i, l i 0 * b.repr (tail x) i| ≤ 1 := by
  let labels : Fin (n + 1) → U := Fin.cons ⟨x, hx⟩ (fun i => ⟨l i, hlU i⟩)
  have hh := hU labels
  have he : (fun z : U => z.val) ∘ labels = Fin.cons x l := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [he, det_lifted_basis b l hl, abs_mul,
    Int.isUnit_iff_abs_eq.mp ((Pi.basisFun ℤ (Fin n)).isUnit_det b), mul_one] at hh
  exact hh

/-- If the selected quotient basis columns and an extra column each have two
adjacent lifts, the extra column has at most one unit of coordinate mass on
those selected basis columns. This is the unrestricted-rank doubled-line lemma. -/
theorem doubled_basis_mass_le_one (U : Set (Lattice (n + 1)))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1))) (fun x : U => x.val))
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (J : Finset (Fin n))
    (l : Fin n → Lattice (n + 1)) (hl : ∀ i, tail (l i) = b i)
    (hlU : ∀ i, l i ∈ U)
    (hlplus : ∀ i ∈ J, l i + Pi.single 0 1 ∈ U)
    {x : Lattice (n + 1)} (hx : x ∈ U) (hxplus : x + Pi.single 0 1 ∈ U) :
    (∑ i ∈ J, |b.repr (tail x) i|) ≤ 1 := by
  apply doubled_coordinate_mass_le_one J (x 0) (fun i => l i 0)
    (fun i => b.repr (tail x) i)
  intro s t hs ht
  let x' := x + t • (Pi.single 0 1 : Lattice (n + 1))
  let l' : Fin n → Lattice (n + 1) :=
    fun i => l i + (if i ∈ J then s i else 0) • Pi.single 0 1
  have hxU : x' ∈ U := by
    rcases ht with ht | ht
    · simpa [x', ht] using hx
    · simpa [x', ht] using hxplus
  have hl'U (i : Fin n) : l' i ∈ U := by
    by_cases hi : i ∈ J
    · rcases hs i with h | h
      · simpa [l', hi, h] using hlU i
      · simpa [l', hi, h] using hlplus i hi
    · simpa [l', hi] using hlU i
  have hlt (i : Fin n) : tail (l' i) = b i := by
    ext j
    change l i j.succ + ((if i ∈ J then s i else 0) •
      (Pi.single 0 1 : Lattice (n + 1))) j.succ = b i j
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero j), smul_zero, add_zero]
    exact congrFun (hl i) j
  have hxt : tail x' = tail x := by
    ext j
    simp [x', tail, Pi.single_apply, Fin.succ_ne_zero]
  have hh := lifted_height_abs_le_one U hU b l' hlt hl'U hxU
  rw [hxt] at hh
  have hx0 : x' 0 = x 0 + t := by
    simp only [x', Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  have hl0 (i : Fin n) : l' i 0 = l i 0 + if i ∈ J then s i else 0 := by
    simp only [l', Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  simpa only [det_bordered, hx0, hl0] using hh

end Unimodular.Heller

end

end Recovered71_HellerLifts

/- Exact historical source: Unimodular/HellerFibers.lean. -/
section Recovered71_HellerFibers

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

variable {n : ℕ}

def fiber (S : Finset (Lattice (n + 1))) (q : Lattice n) : Finset (Lattice (n + 1)) :=
  S.filter (fun x => tail x = q)

def projection (S : Finset (Lattice (n + 1))) : Finset (Lattice n) :=
  (S.image tail).erase 0

def doubles (S : Finset (Lattice (n + 1))) : Finset (Lattice n) :=
  (projection S).filter (fun q => (fiber S q).card = 2)

@[simp] theorem mem_fiber {S : Finset (Lattice (n + 1))} {q : Lattice n}
    {x : Lattice (n + 1)} : x ∈ fiber S q ↔ x ∈ S ∧ tail x = q := by simp [fiber]

@[simp] theorem mem_projection {S : Finset (Lattice (n + 1))} {q : Lattice n} :
    q ∈ projection S ↔ q ≠ 0 ∧ ∃ x ∈ S, tail x = q := by
  simp [projection, Finset.mem_image]

@[simp] theorem mem_doubles {S : Finset (Lattice (n + 1))} {q : Lattice n} :
    q ∈ doubles S ↔ q ∈ projection S ∧ (fiber S q).card = 2 := by simp [doubles]

theorem eq_of_tail_eq_of_height_eq {x y : Lattice (n + 1)}
    (ht : tail x = tail y) (hh : x 0 = y 0) : x = y := by
  ext i
  refine Fin.cases hh (fun j => ?_) i
  exact congrFun ht j

/-- Every nonzero quotient column has at most two distinct lifts. -/
theorem fiber_card_le_two (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ S)
    {q : Lattice n} (hq : q ≠ 0) : (fiber S q).card ≤ 2 := by
  by_cases hc : (fiber S q).card ≤ 1
  · omega
  have hn : (fiber S q).Nontrivial := Finset.one_lt_card.1 (by omega)
  obtain ⟨x, hx, y, hy, hxy⟩ := hn
  have hsub : fiber S q ⊆ {x, y} := by
    intro z hz
    by_cases hzx : z = x
    · simp [hzx]
    by_cases hzy : z = y
    · simp [hzy]
    have hx' := mem_fiber.1 hx
    have hy' := mem_fiber.1 hy
    have hz' := mem_fiber.1 hz
    have hxy' := equal_tail_height_distance (S : Set (Lattice (n + 1))) hS hb hx'.1 hy'.1
      (hx'.2.trans hy'.2.symm) (by rw [hx'.2]; exact hq) hxy
    have hxz' := equal_tail_height_distance (S : Set (Lattice (n + 1))) hS hb hx'.1 hz'.1
      (hx'.2.trans hz'.2.symm) (by rw [hx'.2]; exact hq) (Ne.symm hzx)
    have hyz' := equal_tail_height_distance (S : Set (Lattice (n + 1))) hS hb hy'.1 hz'.1
      (hy'.2.trans hz'.2.symm) (by rw [hy'.2]; exact hq) (Ne.symm hzy)
    have h1 := abs_le.mp hxy'.le
    have h2 := abs_le.mp hxz'.le
    have h3 := abs_le.mp hyz'.le
    have hn1 : x 0 ≠ y 0 := fun h => hxy (eq_of_tail_eq_of_height_eq
      (hx'.2.trans hy'.2.symm) h)
    have hn2 : x 0 ≠ z 0 := fun h => hzx (eq_of_tail_eq_of_height_eq
      (hx'.2.trans hz'.2.symm) h).symm
    have hn3 : y 0 ≠ z 0 := fun h => hzy (eq_of_tail_eq_of_height_eq
      (hy'.2.trans hz'.2.symm) h).symm
    omega
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- The zero projection has at most the two opposite primitive coordinate rays. -/
theorem zero_fiber_card_le_two (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ S) (hzero : 0 ∉ S) :
    (fiber S 0).card ≤ 2 := by
  have hsub : fiber S 0 ⊆ {Pi.single 0 1, -(Pi.single 0 1)} := by
    intro x hx
    obtain ⟨hx, ht⟩ := mem_fiber.1 hx
    have h := coordinate_abs_le_one (Pi.basisFun ℤ (Fin (n + 1)))
      (S : Set (Lattice (n + 1))) hS hb hx 0
    simp only [Pi.basisFun_repr] at h
    have hx0 : x 0 ≠ 0 := by
      intro hx0
      apply hzero
      have he : x = 0 := eq_of_tail_eq_of_height_eq (by simpa using ht) hx0
      simpa [he] using hx
    have hbound := abs_le.mp h
    have hc : x 0 = 1 ∨ x 0 = -1 := by omega
    rcases hc with hc | hc
    · have he : x = Pi.single 0 1 := by
        apply eq_of_tail_eq_of_height_eq
        · ext j
          have htj := congrFun ht j
          simpa [tail, Pi.single_apply, Fin.succ_ne_zero] using htj
        · simpa using hc
      simp [he]
    · have he : x = -(Pi.single 0 1) := by
        apply eq_of_tail_eq_of_height_eq
        · ext j
          have htj := congrFun ht j
          simpa [tail, Pi.single_apply, Fin.succ_ne_zero] using htj
        · simpa using hc
      simp [he]
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- Cardinality splits into a zero fiber, one copy of each nonzero projected
column, and one further copy for each doubled projected column. -/
theorem cardinality_projection_bound (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ S) (hzero : 0 ∉ S) :
    S.card ≤ 2 + (projection S).card + (doubles S).card := by
  have hz : (0 : Lattice n) ∈ S.image tail := by
    refine Finset.mem_image.2 ⟨(Pi.basisFun ℤ (Fin (n + 1))) 0, hb 0, ?_⟩
    ext j
    simp [tail, Pi.basisFun_apply, Pi.single_apply, Fin.succ_ne_zero]
  have hcount := Finset.card_eq_sum_card_image tail S
  have he : S.image tail = insert 0 (projection S) :=
    (Finset.insert_erase hz).symm
  rw [he, Finset.sum_insert] at hcount
  · have hf (q : Lattice n) (hq : q ∈ projection S) :
        (fiber S q).card = 1 + if (fiber S q).card = 2 then 1 else 0 := by
      obtain ⟨hnz, x, hx, htx⟩ := mem_projection.1 hq
      have hpos : 0 < (fiber S q).card := Finset.card_pos.2 ⟨x, mem_fiber.2 ⟨hx, htx⟩⟩
      have hup := fiber_card_le_two S hS hb hnz
      split_ifs <;> omega
    have hsum : (∑ q ∈ projection S, (fiber S q).card) =
        (projection S).card + (doubles S).card := by
      calc
        _ = ∑ q ∈ projection S, (1 + if (fiber S q).card = 2 then 1 else 0) :=
          Finset.sum_congr rfl hf
        _ = _ := by simp [Finset.sum_add_distrib, doubles]
    change S.card = (fiber S 0).card + ∑ q ∈ projection S, (fiber S q).card at hcount
    rw [hsum] at hcount
    have hzeroBound := zero_fiber_card_le_two S hS hb hzero
    omega
  · simp [projection]

end Unimodular.Heller

end

end Recovered71_HellerFibers

/- Exact historical source: Unimodular/HellerDoubles.lean. -/
section Recovered71_HellerDoubles

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

variable {n : ℕ}

/-- A nonzero integral vector of coordinate mass at most one is a signed basis
vector. No primitivity or support assumption is added. -/
theorem signed_basis_of_mass_le_one (b : Module.Basis (Fin n) ℤ (Lattice n))
    {q : Lattice n} (hq : q ≠ 0) (hm : (∑ i, |b.repr q i|) ≤ 1) :
    ∃ i, q = b i ∨ q = -b i := by
  have hne : ∃ i, b.repr q i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hq
    apply b.repr.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hne
  have hpos : 0 < |b.repr q i| := abs_pos.mpr hi
  have hle : |b.repr q i| ≤ 1 :=
    (Finset.single_le_sum (fun j _ => abs_nonneg (b.repr q j)) (Finset.mem_univ i)).trans hm
  have hunit : |b.repr q i| = 1 := by omega
  have hother (j : Fin n) (hj : j ≠ i) : b.repr q j = 0 := by
    have hsum : |b.repr q i| + |b.repr q j| ≤ ∑ k, |b.repr q k| := by
      calc
        _ = ∑ k ∈ ({i, j} : Finset (Fin n)), |b.repr q k| := by simp [Ne.symm hj]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => abs_nonneg _)
    have hz := abs_nonneg (b.repr q j)
    have he : |b.repr q j| = 0 := by omega
    exact abs_eq_zero.mp he
  have hqeq : q = b.repr q i • b i := by
    conv_lhs => rw [← b.sum_repr q]
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      rw [hother j hj, zero_smul]
    · simp
  have hbound := abs_le.mp hle
  have hc : b.repr q i = 1 ∨ b.repr q i = -1 := by omega
  refine ⟨i, ?_⟩
  rcases hc with hc | hc
  · left
    simpa [hc] using hqeq
  · right
    simpa [hc] using hqeq

/-- Choose the lower of the two lifts of a doubled nonzero quotient column. -/
theorem exists_adjacent_lifts (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ S)
    {q : Lattice n} (hq : q ∈ doubles S) :
    ∃ x ∈ S, x + Pi.single 0 1 ∈ S ∧ tail x = q := by
  have hd := mem_doubles.1 hq
  have hqnz := (mem_projection.1 hd.1).1
  have hn : (fiber S q).Nontrivial := Finset.one_lt_card.1 (by rw [hd.2]; omega)
  obtain ⟨x, hx, y, hy, hxy⟩ := hn
  obtain ⟨hxS, hxt⟩ := mem_fiber.1 hx
  obtain ⟨hyS, hyt⟩ := mem_fiber.1 hy
  have hdist := equal_tail_height_distance (S : Set (Lattice (n + 1))) hS hb hxS hyS
    (hxt.trans hyt.symm) (by rw [hxt]; exact hqnz) hxy
  have hneq : x 0 ≠ y 0 := fun h => hxy (eq_of_tail_eq_of_height_eq (hxt.trans hyt.symm) h)
  have hbound := abs_le.mp hdist.le
  have hc : y 0 = x 0 + 1 ∨ x 0 = y 0 + 1 := by omega
  rcases hc with hc | hc
  · refine ⟨x, hxS, ?_, hxt⟩
    have he : x + Pi.single 0 1 = y := by
      apply eq_of_tail_eq_of_height_eq
      · ext j
        have hj := congrFun (hxt.trans hyt.symm) j
        simpa [tail, Pi.single_apply, Fin.succ_ne_zero] using hj
      · simpa using hc.symm
    rwa [he]
  · refine ⟨y, hyS, ?_, hyt⟩
    have he : y + Pi.single 0 1 = x := by
      apply eq_of_tail_eq_of_height_eq
      · ext j
        have hj := congrFun (hyt.trans hxt.symm) j
        simpa [tail, Pi.single_apply, Fin.succ_ne_zero] using hj
      · simpa using hc.symm
    rwa [he]

/-- A normalized system contains the full standard lattice basis and hence
spans the full real vector space. -/
theorem real_span_of_contains_basis (U : Set (Lattice n))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin n)) i ∈ U) :
    Submodule.span ℝ (embed '' U) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℝ (Fin n)).span_eq]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  refine ⟨(Pi.basisFun ℤ (Fin n)) i, hb i, ?_⟩
  ext j
  simp [embed, Pi.basisFun_apply, Pi.single_apply]

/-- The doubled quotient lines are contained in the signed vectors of a single
lattice basis. This is the independent-doubled-lines assertion in Heller's proof,
proved without assuming a circuit classification. -/
theorem doubles_subset_signed_basis (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ S) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      ∀ q ∈ doubles S, ∃ i, q = b i ∨ q = -b i := by
  let Q : Set (Lattice n) := (projection S : Set (Lattice n))
  have heQ : Q = projected (S : Set (Lattice (n + 1))) := by
    ext q
    simp [Q, projected]
  have hQ : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun q : Q => q.val) := by
    rw [heQ]
    apply projected_uniform _ hS
    simpa [Pi.basisFun_apply] using hb 0
  have hbQ : ∀ i, (Pi.basisFun ℤ (Fin n)) i ∈ Q := by
    rw [heQ]
    exact projected_contains_basis _ hb
  have hspanQ := real_span_of_contains_basis Q hbQ
  let D : Set (Lattice n) := (doubles S : Set (Lattice n))
  obtain ⟨f, hf, hspan, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (embed '' D)
  choose u hu he using hf
  have hembed : (fun j => embed (u j)) = f := funext he
  let a := fun j => (⟨u j, (mem_doubles.1 (hu j)).1⟩ : Q)
  have ha : LinearIndependent ℝ (fun j => embed (a j).val) := by
    change LinearIndependent ℝ (fun j => embed (u j))
    rwa [hembed]
  obtain ⟨b, hbmem, hbu⟩ := LatticeHull.exists_lattice_basis_extension Q hQ hspanQ a ha
  let J : Finset (Fin n) := Finset.univ.filter (fun i => b i ∈ doubles S)
  have hJ (i : Fin n) : i ∈ J ↔ b i ∈ doubles S := by simp [J]
  have hlift : ∀ i : Fin n, ∃ l ∈ S, tail l = b i ∧
      (i ∈ J → l + Pi.single 0 1 ∈ S) := by
    intro i
    by_cases hd : b i ∈ doubles S
    · obtain ⟨l, hl, hlplus, hlt⟩ := exists_adjacent_lifts S hS hb hd
      exact ⟨l, hl, hlt, fun _ => hlplus⟩
    · obtain ⟨_, l, hl, hlt⟩ := mem_projection.1 (hbmem i)
      exact ⟨l, hl, hlt, fun hi => False.elim (hd ((hJ i).1 hi))⟩
  choose l hlS hlt hlplus using hlift
  refine ⟨b, ?_⟩
  intro q hq
  obtain ⟨x, hx, hxplus, hxt⟩ := exists_adjacent_lifts S hS hb hq
  have hm := doubled_basis_mass_le_one (S : Set (Lattice (n + 1))) hS b J l hlt hlS
    (fun i hi => hlplus i hi) hx hxplus
  rw [hxt] at hm
  have hout (i : Fin n) (hi : i ∉ J) : b.repr q i = 0 := by
    let c : Ambient n →ₗ[ℝ] ℝ := (LinearMap.proj i).comp (realCoordinates b)
    have hspanle : Submodule.span ℝ (Set.range f) ≤ LinearMap.ker c := by
      apply Submodule.span_le.2
      rintro z ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := hbu j
      have hk' : b k = u j := hk
      have hkJ : k ∈ J := (hJ k).2 (by rw [hk']; exact hu j)
      have hik : i ≠ k := fun he => hi (he ▸ hkJ)
      change c (f j) = 0
      rw [← he j, ← hk']
      simp [c, realCoordinates_basis, Pi.single_apply, Ne.symm hik]
    have hqspan : embed q ∈ Submodule.span ℝ (Set.range f) := by
      rw [hspan]
      exact Submodule.subset_span ⟨q, hq, rfl⟩
    have hz := hspanle hqspan
    change (realCoordinates b (embed q)) i = 0 at hz
    simpa only [realCoordinates_embed, Int.cast_eq_zero] using hz
  have hmass : (∑ i, |b.repr q i|) ≤ 1 := by
    have heq : (∑ i ∈ J, |b.repr q i|) = ∑ i, |b.repr q i| :=
      Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by rw [hout i hi, abs_zero])
    rwa [heq] at hm
  exact signed_basis_of_mass_le_one b (mem_projection.1 (mem_doubles.1 hq).1).1 hmass

/-- There are at most twice the quotient rank many doubled oriented columns. -/
theorem doubles_card_le (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ S) :
    (doubles S).card ≤ 2 * n := by
  obtain ⟨b, h⟩ := doubles_subset_signed_basis S hS hb
  let B := Finset.univ.image b ∪ Finset.univ.image (fun i => -b i)
  have hsub : doubles S ⊆ B := by
    intro q hq
    obtain ⟨i, rfl | rfl⟩ := h q hq <;> simp [B]
  calc
    (doubles S).card ≤ B.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.image b).card + (Finset.univ.image (fun i => -b i)).card :=
      Finset.card_union_le _ _
    _ ≤ n + n := add_le_add (by simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := b))
      (by simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun i => -b i))
    _ = _ := by omega

end Unimodular.Heller

end

end Recovered71_HellerDoubles

/- Exact historical source: Unimodular/HellerBound.lean. -/
section Recovered71_HellerBound

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

/-- Heller's ray bound for a system containing the standard basis. The induction
covers every natural rank, including the zero-dimensional empty system. -/
theorem normalized_card_le : ∀ (n : ℕ) (S : Finset (Lattice n)),
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun x : (S : Set (Lattice n)) => x.val) →
    (∀ i, (Pi.basisFun ℤ (Fin n)) i ∈ S) → 0 ∉ S →
    S.card ≤ n * (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro S _ _ hzero
      have he : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro x hx
        have hx0 : x = 0 := Subsingleton.elim _ _
        exact hzero (hx0 ▸ hx)
      simp [he]
  | succ n ih =>
      intro S hS hb hzero
      have heQ : (projection S : Set (Lattice n)) =
          projected (S : Set (Lattice (n + 1))) := by
        ext q
        simp [projected]
      have hQ : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
          (fun q : (projection S : Set (Lattice n)) => q.val) := by
        rw [heQ]
        apply projected_uniform _ hS
        simpa [Pi.basisFun_apply] using hb 0
      have hbQ : ∀ i, (Pi.basisFun ℤ (Fin n)) i ∈ projection S := by
        change ∀ i, (Pi.basisFun ℤ (Fin n)) i ∈ (projection S : Set (Lattice n))
        rw [heQ]
        exact projected_contains_basis _ hb
      have hzQ : (0 : Lattice n) ∉ projection S := by simp
      have hsmall := ih (projection S) hQ hbQ hzQ
      have hcount := cardinality_projection_bound S hS hb hzero
      have hd := doubles_card_le S hS hb
      nlinarith

/-- The determinant condition is preserved under an actual integral lattice
isomorphism. This permits basis normalization without changing the configuration. -/
theorem uniform_image {n : ℕ} (U : Set (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (φ : Lattice n ≃ₗ[ℤ] Lattice n) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : φ '' U => u.val) := by
  intro a
  choose x hx he using fun i => (a i).property
  let labels : Fin n → U := fun i => ⟨x i, hx i⟩
  have h := hU labels
  rw [BasisCover.basis_determinant_abs (Pi.basisFun ℤ (Fin n))
    ((Pi.basisFun ℤ (Fin n)).map φ)]
  rw [Module.Basis.det_map]
  convert h using 1
  congr 2
  funext i
  change φ.symm (a i).val = x i
  rw [← he i, φ.symm_apply_apply]

/-- Full-rank version of the sharp bound, stated for the original lattice
configuration. Its only hypotheses are finiteness, no zero vector, real spanning,
and uniform unimodularity. Neither positivity nor central symmetry is assumed. -/
theorem ray_card_le {n : ℕ} (S : Finset (Lattice n))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun x : (S : Set (Lattice n)) => x.val))
    (hspan : Submodule.span ℝ (embed '' (S : Set (Lattice n))) = ⊤)
    (hzero : 0 ∉ S) : S.card ≤ n * (n + 1) := by
  let a : Fin 0 → (S : Set (Lattice n)) := Fin.elim0
  obtain ⟨b, hb, _⟩ := LatticeHull.exists_lattice_basis_extension
    (S : Set (Lattice n)) hS hspan a (linearIndependent_empty_type ..)
  let φ : Lattice n ≃ₗ[ℤ] Lattice n :=
    b.equiv (Pi.basisFun ℤ (Fin n)) (Equiv.refl _)
  let T : Finset (Lattice n) := S.image φ
  have hT : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun x : (T : Set (Lattice n)) => x.val) := by
    have he : (T : Set (Lattice n)) = φ '' (S : Set (Lattice n)) := by
      simp [T]
    rw [he]
    exact uniform_image _ hS φ
  have hbT : ∀ i, (Pi.basisFun ℤ (Fin n)) i ∈ T := by
    intro i
    exact Finset.mem_image.2 ⟨b i, hb i, by simp [φ]⟩
  have hzT : (0 : Lattice n) ∉ T := by
    intro h
    obtain ⟨x, hx, hφx⟩ := Finset.mem_image.1 h
    have hx0 : x = 0 := φ.injective (by simpa using hφx)
    exact hzero (hx0 ▸ hx)
  have hcard : T.card = S.card := Finset.card_image_of_injective _ φ.injective
  have h := normalized_card_le n T hT hbT hzT
  rwa [hcard] at h

/-- The same theorem for a finite set, retaining its actual cardinality. -/
theorem finite_ray_ncard_le {n : ℕ} (U : Set (Lattice n)) (hfin : U.Finite)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤) (hzero : 0 ∉ U) :
    U.ncard ≤ n * (n + 1) := by
  have h := ray_card_le hfin.toFinset
    (by rw [hfin.coe_toFinset]; exact hU)
    (by rw [hfin.coe_toFinset]; exact hspan)
    (by simpa only [Set.Finite.mem_toFinset] using hzero)
  simpa only [Set.ncard_eq_toFinset_card U hfin] using h

end Unimodular.Heller

end

end Recovered71_HellerBound

/- Exact historical source: Unimodular/HellerEquality.lean. -/
section Recovered71_HellerEquality

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

/-- Adjoining every negative column preserves uniform unimodularity. The proof
uses multilinearity of the actual determinant, with one independent sign per column. -/
theorem uniform_neg_closure {n : ℕ} (S : Finset (Lattice n))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun x : (S : Set (Lattice n)) => x.val)) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun x : ((S ∪ S.image Neg.neg : Finset (Lattice n)) : Set (Lattice n)) => x.val) := by
  intro a
  have hw (i : Fin n) : ∃ x ∈ S, ∃ ε : ℤ, |ε| = 1 ∧ ε • x = (a i).val := by
    rcases Finset.mem_union.1 (a i).property with h | h
    · exact ⟨(a i).val, h, 1, by norm_num, by simp⟩
    · obtain ⟨x, hx, he⟩ := Finset.mem_image.1 h
      exact ⟨x, hx, -1, by norm_num, by simpa using he⟩
  choose x hx ε hε he using hw
  have hf : (fun z : ((S ∪ S.image Neg.neg : Finset (Lattice n)) : Set (Lattice n)) => z.val) ∘ a =
      (fun i => ε i • x i) := by
    funext i
    exact (he i).symm
  have hp : |∏ i, ε i| = 1 := by
    have hprod : ∀ T : Finset (Fin n), |∏ i ∈ T, ε i| = 1 := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp
      | @insert i T hi ih => simp [Finset.prod_insert, hi, abs_mul, hε i, ih]
    exact hprod Finset.univ
  rw [hf, AlternatingMap.map_smul_univ, smul_eq_mul, abs_mul, hp, one_mul]
  exact hS (fun i => ⟨x i, hx i⟩)

/-- Equality in the ray bound forces both primitive orientations of every line.
This is deduced from the already established unrestricted bound, not added as
an assumption in the classification of extremal systems. -/
theorem extremal_neg_closed {n : ℕ} (S : Finset (Lattice n))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun x : (S : Set (Lattice n)) => x.val))
    (hspan : Submodule.span ℝ (embed '' (S : Set (Lattice n))) = ⊤)
    (hzero : 0 ∉ S) (hcard : S.card = n * (n + 1)) :
    ∀ x ∈ S, -x ∈ S := by
  let T := S ∪ S.image Neg.neg
  have hsub : S ⊆ T := Finset.subset_union_left
  have hTspan : Submodule.span ℝ (embed '' (T : Set (Lattice n))) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono (Set.image_mono hsub)
  have hTzero : (0 : Lattice n) ∉ T := by
    intro h
    rcases Finset.mem_union.1 h with h | h
    · exact hzero h
    · obtain ⟨x, hx, he⟩ := Finset.mem_image.1 h
      have hx0 : x = 0 := neg_eq_zero.mp he
      exact hzero (hx0 ▸ hx)
  have hTcard := ray_card_le T (uniform_neg_closure S hS) hTspan hTzero
  have he : S = T := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro x hx
  rw [he]
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨x, hx, rfl⟩)

/-- Every inequality in the inductive count is an equality for an extremal
normalized system. In particular all 2n doubled quotient vectors occur. -/
theorem extremal_projection_counts {n : ℕ} (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ S)
    (hzero : 0 ∉ S) (hcard : S.card = (n + 1) * (n + 2)) :
    (projection S).card = n * (n + 1) ∧ (doubles S).card = 2 * n := by
  have heQ : (projection S : Set (Lattice n)) =
      projected (S : Set (Lattice (n + 1))) := by
    ext q
    simp [projected]
  have hQ : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun q : (projection S : Set (Lattice n)) => q.val) := by
    rw [heQ]
    apply projected_uniform _ hS
    simpa [Pi.basisFun_apply] using hb 0
  have hbQ : ∀ i, (Pi.basisFun ℤ (Fin n)) i ∈ projection S := by
    change ∀ i, (Pi.basisFun ℤ (Fin n)) i ∈ (projection S : Set (Lattice n))
    rw [heQ]
    exact projected_contains_basis _ hb
  have hsmall := normalized_card_le n (projection S) hQ hbQ (by simp)
  have hcount := cardinality_projection_bound S hS hb hzero
  have hd := doubles_card_le S hS hb
  constructor <;> nlinarith

/-- In the equality case the doubled projected vectors are exactly a full
signed integral basis of the quotient lattice. -/
theorem extremal_doubles_basis {n : ℕ} (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ S)
    (hzero : 0 ∉ S) (hcard : S.card = (n + 1) * (n + 2)) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      doubles S = Finset.univ.image b ∪ Finset.univ.image (fun i => -b i) := by
  obtain ⟨b, hbD⟩ := doubles_subset_signed_basis S hS hb
  refine ⟨b, ?_⟩
  let B := Finset.univ.image b ∪ Finset.univ.image (fun i => -b i)
  have hsub : doubles S ⊆ B := by
    intro q hq
    obtain ⟨i, rfl | rfl⟩ := hbD q hq <;> simp [B]
  have hB : B.card ≤ 2 * n := by
    calc
      B.card ≤ (Finset.univ.image b).card +
          (Finset.univ.image (fun i => -b i)).card := Finset.card_union_le _ _
      _ ≤ n + n := add_le_add
        (by simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := b))
        (by simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := fun i => -b i))
      _ = 2 * n := by omega
  have hd := (extremal_projection_counts S hS hb hzero hcard).2
  change doubles S = B
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hd]; exact hB)

end Unimodular.Heller

end

end Recovered71_HellerEquality

/- Exact historical source: Unimodular/HellerExtremalCoordinates.lean. -/
section Recovered71_HellerExtremalCoordinates

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

/-- Independent choices of adjacent heights in a full quotient basis constrain
every lifted ray to coordinate mass at most two. -/
theorem full_doubled_basis_mass_le_two {n : ℕ} (U : Set (Lattice (n + 1)))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1))) (fun x : U => x.val))
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (l : Fin n → Lattice (n + 1)) (hl : ∀ i, tail (l i) = b i)
    (hlU : ∀ i, l i ∈ U) (hlplus : ∀ i, l i + Pi.single 0 1 ∈ U)
    {x : Lattice (n + 1)} (hx : x ∈ U) :
    (∑ i, |b.repr (tail x) i|) ≤ 2 := by
  let v : Fin n → ℤ := fun i => b.repr (tail x) i
  have ha : ∀ s : Fin n → ℤ, (∀ i, s i = 0 ∨ s i = 1) →
      |(x 0 - ∑ i, l i 0 * v i) + ∑ i, s i * (-v i)| ≤ 1 := by
    intro s hs
    let l' : Fin n → Lattice (n + 1) := fun i => l i + s i • Pi.single 0 1
    have hl'U (i : Fin n) : l' i ∈ U := by
      rcases hs i with h | h
      · simpa [l', h] using hlU i
      · simpa [l', h] using hlplus i
    have hlt (i : Fin n) : tail (l' i) = b i := by
      ext j
      change l i j.succ + (s i • (Pi.single 0 1 : Lattice (n + 1))) j.succ = b i j
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero j), smul_zero, add_zero]
      exact congrFun (hl i) j
    have h := lifted_height_abs_le_one U hU b l' hlt hl'U hx
    have he : (x 0 - ∑ i, l i 0 * v i) + ∑ i, s i * (-v i) =
        x 0 - ∑ i, l' i 0 * v i := by
      have hl0 (i : Fin n) : l' i 0 = l i 0 + s i := by
        simp only [l', Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      simp only [hl0, add_mul, Finset.sum_add_distrib, mul_neg, Finset.sum_neg_distrib]
      ring
    rw [he]
    exact h
  have h := coefficient_mass_le ha
  simpa [v, abs_neg] using h

/-- A nonzero integral coordinate family whose entries are bounded by one and
whose total absolute value is at most two has either one or two nonzero entries.
This is a rank-free statement about actual coordinate support. -/
theorem support_card_le_two {n : ℕ} (v : Fin n → ℤ)
    (hm : (∑ i, |v i|) ≤ 2) :
    (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ 2 := by
  let A := Finset.univ.filter (fun i => v i ≠ 0)
  have hb : (A.card : ℤ) ≤ ∑ i, |v i| := by
    calc
      (A.card : ℤ) = ∑ i ∈ A, (1 : ℤ) := by simp
      _ ≤ ∑ i ∈ A, |v i| := by
        apply Finset.sum_le_sum
        intro i hi
        have hz : v i ≠ 0 := (Finset.mem_filter.1 hi).2
        have hp := abs_pos.mpr hz
        omega
      _ ≤ ∑ i, |v i| := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)
  change A.card ≤ 2
  omega

/-- Support size one gives an actual signed basis ray. -/
theorem signed_basis_of_support_single {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (q : Lattice n) (i : Fin n)
    (hi : b.repr q i = 1 ∨ b.repr q i = -1)
    (hz : ∀ j, j ≠ i → b.repr q j = 0) : q = b i ∨ q = -b i := by
  have he : q = b.repr q i • b i := by
    conv_lhs => rw [← b.sum_repr q]
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      rw [hz j hji, zero_smul]
    · simp
  rcases hi with hi | hi
  · left; simpa [hi] using he
  · right; simpa [hi] using he

/-- A pair of quotient basis coordinates cannot occur in both relative signs:
the corresponding two-by-two minor would have absolute value two. -/
theorem excludes_both_pair_signs {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (U : Set (Lattice n)) (hU : IntegralRigidity.Uniform b (fun u : U => u.val))
    (hb : ∀ i, b i ∈ U) {i j : Fin n} (hij : i ≠ j)
    (hplus : b i + b j ∈ U) : b i - b j ∉ U := by
  intro hminus
  have h := two_coordinate_minor_abs_le_one b U hU hb hplus hminus hij
  have hfalse : (2 : ℤ) ≤ 1 := by
    simpa [map_add, map_sub, Finsupp.add_apply, Finsupp.sub_apply,
      Module.Basis.repr_self, Finsupp.single_apply, hij, Ne.symm hij] using h
  omega

end Unimodular.Heller

end

end Recovered71_HellerExtremalCoordinates

/- Exact historical source: Unimodular/HellerSupports.lean. -/
section Recovered71_HellerSupports

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

variable {n : ℕ}

/-- Coordinate support, retaining actual integral coefficients through `b.repr`. -/
def coordSupport (b : Module.Basis (Fin n) ℤ (Lattice n)) (q : Lattice n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => b.repr q i ≠ 0)

@[simp] theorem mem_coordSupport (b : Module.Basis (Fin n) ℤ (Lattice n))
    (q : Lattice n) (i : Fin n) : i ∈ coordSupport b q ↔ b.repr q i ≠ 0 := by
  simp [coordSupport]

theorem coordSupport_nonempty (b : Module.Basis (Fin n) ℤ (Lattice n))
    {q : Lattice n} (hq : q ≠ 0) : (coordSupport b q).Nonempty := by
  by_contra h
  have hz : coordSupport b q = ∅ := Finset.not_nonempty_iff_eq_empty.1 h
  apply hq
  apply b.repr.injective
  ext i
  have hi : i ∉ coordSupport b q := by simp [hz]
  simpa using hi

/-- Uniform columns with identical support are equal up to an overall sign.
This is the no-mixed-incidences lemma in Heller's original argument. -/
theorem same_support_eq_or_neg (b : Module.Basis (Fin n) ℤ (Lattice n))
    (U : Set (Lattice n)) (hU : IntegralRigidity.Uniform b (fun u : U => u.val))
    (hb : ∀ i, b i ∈ U) {q r : Lattice n} (hq : q ∈ U) (hr : r ∈ U)
    (hqnz : q ≠ 0) (hs : coordSupport b q = coordSupport b r) :
    q = r ∨ q = -r := by
  obtain ⟨i, hi⟩ := coordSupport_nonempty b hqnz
  have hqi : b.repr q i ≠ 0 := (mem_coordSupport b q i).1 hi
  have hri : b.repr r i ≠ 0 := (mem_coordSupport b r i).1 (hs ▸ hi)
  have hqb := abs_le.mp (coordinate_abs_le_one b U hU hb hq i)
  have hrb := abs_le.mp (coordinate_abs_le_one b U hU hb hr i)
  have hqi' : b.repr q i = 1 ∨ b.repr q i = -1 := by omega
  have hri' : b.repr r i = 1 ∨ b.repr r i = -1 := by omega
  have heq (ε : ℤ) (hε : |ε| = 1) (hiε : b.repr q i = ε * b.repr r i) :
      q = ε • r := by
    apply b.repr.injective
    ext j
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hji : j = i
    · simpa [hji] using hiε
    by_cases hqj : b.repr q j = 0
    · have hrj : b.repr r j = 0 := by
        have hm : j ∉ coordSupport b q := by simpa using hqj
        rw [hs] at hm
        simpa using hm
      simp [hqj, hrj]
    have hrj : b.repr r j ≠ 0 := by
      apply (mem_coordSupport b r j).1
      rw [← hs]
      exact (mem_coordSupport b q j).2 hqj
    have hqm := coordinate_abs_le_one b U hU hb hq j
    have hrm := coordinate_abs_le_one b U hU hb hr j
    have hqabs : |b.repr q j| = 1 := by
      have hp := abs_pos.mpr hqj
      omega
    have hrabs : |b.repr r j| = 1 := by
      have hp := abs_pos.mpr hrj
      omega
    have hriabs : |b.repr r i| = 1 := by
      rcases hri' with hi | hi <;> simp [hi]
    have hm := two_coordinate_minor_abs_le_one b U hU hb hq hr (Ne.symm hji)
    have he : b.repr q i * b.repr r j - b.repr q j * b.repr r i =
        b.repr r i * (ε * b.repr r j - b.repr q j) := by rw [hiε]; ring
    rw [he, abs_mul, hriabs, one_mul] at hm
    have hεr : |ε * b.repr r j| = 1 := by rw [abs_mul, hε, hrabs, one_mul]
    have hqbounds := abs_le.mp hqabs.le
    have hεbounds := abs_le.mp hεr.le
    have hdiff := abs_le.mp hm
    have hqn := abs_pos.mp (show 0 < |b.repr q j| by omega)
    have hεn := abs_pos.mp (show 0 < |ε * b.repr r j| by omega)
    omega
  rcases hqi' with hqi' | hqi' <;> rcases hri' with hri' | hri'
  · left; simpa using heq 1 (by norm_num) (by rw [hqi', hri']; ring)
  · right; simpa using heq (-1) (by norm_num) (by rw [hqi', hri']; ring)
  · right; simpa using heq (-1) (by norm_num) (by rw [hqi', hri']; ring)
  · left; simpa using heq 1 (by norm_num) (by rw [hqi', hri']; ring)

/-- At most two distinct vectors of a uniform system can have a fixed support. -/
theorem support_fiber_card_le_two (b : Module.Basis (Fin n) ℤ (Lattice n))
    (Q : Finset (Lattice n))
    (hQ : IntegralRigidity.Uniform b (fun q : (Q : Set (Lattice n)) => q.val))
    (hb : ∀ i, b i ∈ Q) (hzero : 0 ∉ Q) (T : Finset (Fin n)) :
    (Q.filter (fun q => coordSupport b q = T)).card ≤ 2 := by
  let F := Q.filter (fun q => coordSupport b q = T)
  rcases Finset.eq_empty_or_nonempty F with he | ⟨q, hq⟩
  · simp [← show F = Q.filter (fun q => coordSupport b q = T) from rfl, he]
  · have hq' := Finset.mem_filter.1 hq
    have hsub : F ⊆ {q, -q} := by
      intro r hr
      have hr' := Finset.mem_filter.1 hr
      have hrnz : r ≠ 0 := fun he => hzero (he ▸ hr'.1)
      rcases same_support_eq_or_neg b (Q : Set (Lattice n)) hQ hb hr'.1 hq'.1 hrnz
        (hr'.2.trans hq'.2.symm) with he | he <;> simp [he]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- All possible supports of size one or two. -/
def smallSupports (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powersetCard 1 ∪ Finset.univ.powersetCard 2

@[simp] theorem mem_smallSupports {T : Finset (Fin n)} :
    T ∈ smallSupports n ↔ T.card = 1 ∨ T.card = 2 := by
  simp [smallSupports]

theorem twice_card_smallSupports (n : ℕ) :
    2 * (smallSupports n).card = n * (n + 1) := by
  have hd : Disjoint (Finset.univ.powersetCard 1 : Finset (Finset (Fin n)))
      (Finset.univ.powersetCard 2) := by
    apply Finset.disjoint_left.2
    intro T h1 h2
    have h1' := (Finset.mem_powersetCard.1 h1).2
    have h2' := (Finset.mem_powersetCard.1 h2).2
    omega
  rw [smallSupports, Finset.card_union_of_disjoint hd, Finset.card_powersetCard,
    Finset.card_powersetCard]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.choose_one_right]
  clear hd
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith

/-- Equality in the support count forces every support of size one or two to
occur twice. This is a finite-cardinality argument valid in every rank. -/
theorem extremal_support_fibers (b : Module.Basis (Fin n) ℤ (Lattice n))
    (Q : Finset (Lattice n))
    (hQ : IntegralRigidity.Uniform b (fun q : (Q : Set (Lattice n)) => q.val))
    (hb : ∀ i, b i ∈ Q) (hzero : 0 ∉ Q)
    (hmass : ∀ q ∈ Q, (∑ i, |b.repr q i|) ≤ 2)
    (hcard : Q.card = n * (n + 1)) :
    ∀ T ∈ smallSupports n, (Q.filter (fun q => coordSupport b q = T)).card = 2 := by
  have hmaps : ∀ q ∈ Q, coordSupport b q ∈ smallSupports n := by
    intro q hq
    have hnz : q ≠ 0 := fun he => hzero (he ▸ hq)
    have hpos := Finset.card_pos.2 (coordSupport_nonempty b hnz)
    have hle := support_card_le_two (fun i => b.repr q i) (hmass q hq)
    exact mem_smallSupports.2 (by change (coordSupport b q).card ≤ 2 at hle; omega)
  have he := Finset.card_eq_sum_card_fiberwise hmaps
  have hsum : (∑ T ∈ smallSupports n, (Q.filter (fun q => coordSupport b q = T)).card) =
      ∑ _T ∈ smallSupports n, (2 : ℕ) := by
    rw [← he]
    simpa [hcard, Nat.mul_comm] using (twice_card_smallSupports n).symm
  intro T hT
  have hle : ∀ T ∈ smallSupports n,
      (Q.filter (fun q => coordSupport b q = T)).card ≤ 2 :=
    fun T _ => support_fiber_card_le_two b Q hQ hb hzero T
  by_contra hne
  have hlt : (Q.filter (fun q => coordSupport b q = T)).card < 2 :=
    lt_of_le_of_ne (hle T hT) hne
  have hstrict := Finset.sum_lt_sum hle ⟨T, hT, hlt⟩
  omega

end Unimodular.Heller

end

end Recovered71_HellerSupports

/- Exact historical source: Unimodular/HellerSignedPairs.lean. -/
section Recovered71_HellerSignedPairs

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

variable {n : ℕ}

/-- Three-column Cramer's identity in arbitrary ambient rank. -/
theorem det_replace_three (b : Module.Basis (Fin n) ℤ (Lattice n))
    (x y z : Lattice n) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    b.det (Function.update (Function.update (Function.update b i x) j y) k z) =
      b.repr z i * (b.repr x j * b.repr y k - b.repr x k * b.repr y j) -
      b.repr z j * (b.repr x i * b.repr y k - b.repr x k * b.repr y i) +
      b.repr z k * (b.repr x i * b.repr y j - b.repr x j * b.repr y i) := by
  let f := Function.update (Function.update b i x) j y
  have hi : b.det (Function.update f k (b i)) =
      b.repr x j * b.repr y k - b.repr x k * b.repr y j := by
    let g := Function.update (Function.update b j x) k y
    have he : Function.update f k (b i) =
        (g ∘ Equiv.swap i j) ∘ Equiv.swap j k := by
      funext t
      by_cases hti : t = i
      · subst t
        simp [f, g, Function.comp_def, Equiv.swap_apply_def, hij, hik, hjk,
          Ne.symm hij, Ne.symm hik, Ne.symm hjk]
      · by_cases htj : t = j
        · subst t
          simp [f, g, Function.comp_def, Equiv.swap_apply_def, hij, hik, hjk,
            Ne.symm hij, Ne.symm hik, Ne.symm hjk]
        · by_cases htk : t = k
          · subst t
            simp [f, g, Function.comp_def, Equiv.swap_apply_def, hij, hik, hjk,
              Ne.symm hij, Ne.symm hik, Ne.symm hjk]
          · simp [f, g, Function.comp_def, Equiv.swap_apply_def, hti, htj, htk]
    rw [he, b.det.map_swap _ hjk, b.det.map_swap _ hij, neg_neg]
    exact det_replace_two b x y hjk
  have hj : b.det (Function.update f k (b j)) =
      -(b.repr x i * b.repr y k - b.repr x k * b.repr y i) := by
    let g := Function.update (Function.update b i x) k y
    have he : Function.update f k (b j) = g ∘ Equiv.swap j k := by
      funext t
      by_cases htj : t = j
      · subst t
        simp [f, g, Function.comp_def, Equiv.swap_apply_def, hij, hik, hjk,
          Ne.symm hij, Ne.symm hik, Ne.symm hjk]
      · by_cases htk : t = k
        · subst t
          simp [f, g, Function.comp_def, Equiv.swap_apply_def, hij, hik, hjk,
            Ne.symm hij, Ne.symm hik, Ne.symm hjk]
        · simp [f, g, Function.comp_def, Equiv.swap_apply_def, htj, htk]
    rw [he, b.det.map_swap _ hjk, det_replace_two b x y hik]
  have hk : b.det (Function.update f k (b k)) =
      b.repr x i * b.repr y j - b.repr x j * b.repr y i := by
    have he : Function.update f k (b k) = f := by
      funext t
      by_cases htk : t = k
      · subst t
        simp [f, Ne.symm hik, Ne.symm hjk]
      · simp [htk]
    rw [he]
    exact det_replace_two b x y hij
  have ho (t : Fin n) (hti : t ≠ i) (htj : t ≠ j) (htk : t ≠ k) :
      b.det (Function.update f k (b t)) = 0 := by
    apply b.det.map_eq_zero_of_eq _ (i := k) (j := t) _ (Ne.symm htk)
    simp [f, hti, htj, htk]
  change b.det (Function.update f k z) = _
  conv_lhs => rw [← b.sum_repr z]
  rw [b.det.map_update_sum]
  simp only [b.det.map_update_smul, smul_eq_mul]
  calc
    _ = ∑ t, ((if t = i then b.repr z i *
          (b.repr x j * b.repr y k - b.repr x k * b.repr y j) else 0) +
        (if t = j then b.repr z j *
          (-(b.repr x i * b.repr y k - b.repr x k * b.repr y i)) else 0) +
        (if t = k then b.repr z k *
          (b.repr x i * b.repr y j - b.repr x j * b.repr y i) else 0)) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases hti : t = i
      · subst t; simp [hi, hij, hik]
      · by_cases htj : t = j
        · subst t; simp [hj, Ne.symm hij, hjk]
        · by_cases htk : t = k
          · subst t; simp [hk, Ne.symm hik, Ne.symm hjk]
          · simp [hti, htj, htk, ho t hti htj htk]
    _ = _ := by simp [Finset.sum_add_distrib]; ring

/-- Uniformity imposes the balanced sign equation on every triangle of pair
supports. This is a symbolic minor calculation, independent of ambient rank. -/
theorem triangle_sign_equation (b : Module.Basis (Fin n) ℤ (Lattice n))
    (U : Set (Lattice n)) (hU : IntegralRigidity.Uniform b (fun u : U => u.val))
    (hb : ∀ i, b i ∈ U) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (α β γ : ℤ) (hα : |α| = 1) (hβ : |β| = 1) (hγ : |γ| = 1)
    (hx : b i + α • b j ∈ U) (hy : b j + β • b k ∈ U)
    (hz : b i + γ • b k ∈ U) : γ = -α * β := by
  let labels : Fin n → U := fun t => ⟨b t, hb t⟩
  let a := Function.update (Function.update (Function.update labels i
    ⟨b i + α • b j, hx⟩) j ⟨b j + β • b k, hy⟩) k ⟨b i + γ • b k, hz⟩
  have h := hU a
  have he : (fun u : U => u.val) ∘ a =
      Function.update (Function.update (Function.update b i (b i + α • b j))
        j (b j + β • b k)) k (b i + γ • b k) := by
    funext t
    by_cases htk : t = k
    · subst t; simp [a]
    · by_cases htj : t = j
      · subst t; simp [a, htk]
      · by_cases hti : t = i
        · subst t; simp [a, labels, hij, hik]
        · simp [a, labels, htk, htj, hti]
  rw [he, det_replace_three b _ _ _ hij hik hjk] at h
  have hm : |γ + α * β| ≤ 1 := by
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self, Finsupp.single_apply] at h
    simpa [smul_eq_mul, hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk,
      mul_comm, add_comm] using h
  have hp : |α * β| = 1 := by rw [abs_mul, hα, hβ, one_mul]
  have hc := abs_le.mp hγ.le
  have hpc := abs_le.mp hp.le
  have hmc := abs_le.mp hm
  have hgn : γ ≠ 0 := by intro he; simp [he] at hγ
  have hpn : α * β ≠ 0 := by intro he; simp [he] at hp
  have heq : γ = -(α * β) := by omega
  simpa [neg_mul] using heq

/-- The two possible pair types exhaust every two-coordinate support once the
extremal support count is attained. -/
theorem pair_sum_or_difference (b : Module.Basis (Fin n) ℤ (Lattice n))
    (Q : Finset (Lattice n))
    (hQ : IntegralRigidity.Uniform b (fun q : (Q : Set (Lattice n)) => q.val))
    (hb : ∀ i, b i ∈ Q) (hzero : 0 ∉ Q) (hneg : ∀ q ∈ Q, -q ∈ Q)
    (hmass : ∀ q ∈ Q, (∑ i, |b.repr q i|) ≤ 2)
    (hcard : Q.card = n * (n + 1)) {i j : Fin n} (hij : i ≠ j) :
    b i + b j ∈ Q ∨ b i - b j ∈ Q := by
  have ht : ({i,j} : Finset (Fin n)) ∈ smallSupports n := by simp [hij]
  have hc := extremal_support_fibers b Q hQ hb hzero hmass hcard {i,j} ht
  obtain ⟨q, hq⟩ := Finset.card_pos.1 (show 0 < (Q.filter
    (fun q => coordSupport b q = {i,j})).card by omega)
  obtain ⟨hq, hs⟩ := Finset.mem_filter.1 hq
  have hqi : b.repr q i ≠ 0 := by
    apply (mem_coordSupport b q i).1
    simp [hs]
  have hqj : b.repr q j ≠ 0 := by
    apply (mem_coordSupport b q j).1
    simp [hs]
  have hbi := abs_le.mp (coordinate_abs_le_one b (Q : Set (Lattice n)) hQ hb hq i)
  have hbj := abs_le.mp (coordinate_abs_le_one b (Q : Set (Lattice n)) hQ hb hq j)
  have hi : b.repr q i = 1 ∨ b.repr q i = -1 := by omega
  have hj : b.repr q j = 1 ∨ b.repr q j = -1 := by omega
  have he : q = b.repr q i • b i + b.repr q j • b j := by
    apply b.repr.injective
    ext k
    by_cases hki : k = i
    · subst k
      simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_apply]
      simp [smul_eq_mul, hij, Ne.symm hij]
    · by_cases hkj : k = j
      · subst k
        simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
          Module.Basis.repr_self, Finsupp.single_apply]
        simp [smul_eq_mul, hij, Ne.symm hij]
      · have hz : b.repr q k = 0 := by
          have hm : k ∉ coordSupport b q := by simp [hs, hki, hkj]
          simpa using hm
        simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
          Module.Basis.repr_self, Finsupp.single_apply]
        simp [hz, smul_eq_mul, hki, hkj, Ne.symm hki, Ne.symm hkj]
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · left
    rw [he] at hq
    simpa [hi, hj] using hq
  · right
    rw [he] at hq
    simpa [hi, hj, sub_eq_add_neg] using hq
  · right
    have hn := hneg q hq
    rw [he] at hn
    simpa [hi, hj, sub_eq_add_neg, neg_add, add_comm] using hn
  · left
    have hn := hneg q hq
    rw [he] at hn
    simpa [hi, hj, neg_add, add_comm] using hn

end Unimodular.Heller

end

end Recovered71_HellerSignedPairs

/- Exact historical source: Unimodular/HellerPairNormalForm.lean. -/
section Recovered71_HellerPairNormalForm

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

variable {n : ℕ}

/-- A centrally symmetric configuration is closed under multiplication by an
integral unit; this is used only after symmetry has been proved from extremality. -/
theorem unit_smul_mem (Q : Finset (Lattice n)) (hneg : ∀ q ∈ Q, -q ∈ Q)
    {q : Lattice n} (hq : q ∈ Q) {a : ℤ} (ha : |a| = 1) : a • q ∈ Q := by
  have hb := abs_le.mp ha.le
  have hn : a ≠ 0 := by intro he; simp [he] at ha
  have hc : a = 1 ∨ a = -1 := by omega
  rcases hc with rfl | rfl
  · simpa using hq
  · simpa using hneg q hq

/-- A complete signed pair system can be reoriented in one integral basis so
that all pair columns are differences. The signs are forced by three-column
minors; an orientation uniqueness theorem is not assumed. -/
theorem exists_signed_pair_basis (b : Module.Basis (Fin n) ℤ (Lattice n))
    (Q : Finset (Lattice n))
    (hQ : IntegralRigidity.Uniform b (fun q : (Q : Set (Lattice n)) => q.val))
    (hb : ∀ i, b i ∈ Q) (hneg : ∀ q ∈ Q, -q ∈ Q)
    (hpair : ∀ i j, i ≠ j → b i + b j ∈ Q ∨ b i - b j ∈ Q) :
    ∃ c : Module.Basis (Fin n) ℤ (Lattice n),
      (∀ i, c i = b i ∨ c i = -b i) ∧ (∀ i, c i ∈ Q) ∧
      ∀ i j, i ≠ j → c i - c j ∈ Q := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨b, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    intro i
    exact Fin.elim0 i
  let a : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let ε : Fin n → Fin n → ℤ := fun i j => if b i + b j ∈ Q then 1 else -1
  have hε (i j : Fin n) : |ε i j| = 1 := by
    dsimp [ε]
    split_ifs <;> norm_num
  have hedge (i j : Fin n) (hij : i ≠ j) : b i + ε i j • b j ∈ Q := by
    dsimp [ε]
    split_ifs with h
    · simpa using h
    · simpa [sub_eq_add_neg] using (hpair i j hij).resolve_left h
  let σ : Fin n → ℤ := fun i => if i = a then 1 else -ε a i
  have hσ (i : Fin n) : |σ i| = 1 := by
    dsimp [σ]
    split_ifs <;> simp [hε]
  let c := b.isUnitSMul (fun i => Int.isUnit_iff_abs_eq.2 (hσ i))
  have hc (i : Fin n) : c i = σ i • b i := Module.Basis.isUnitSMul_apply _ i
  have hcmem (i : Fin n) : c i ∈ Q := by
    rw [hc]
    exact unit_smul_mem Q hneg (hb i) (hσ i)
  have hsign (i : Fin n) : c i = b i ∨ c i = -b i := by
    have hs := abs_le.mp (hσ i).le
    have hnσ : σ i ≠ 0 := by intro he; simpa [he] using hσ i
    have hcases : σ i = 1 ∨ σ i = -1 := by omega
    rcases hcases with h | h
    · left; simp [hc, h]
    · right; simp [hc, h]
  have hanchor (j : Fin n) (hja : j ≠ a) : c a - c j ∈ Q := by
    have he : c a - c j = b a + ε a j • b j := by
      rw [hc, hc]
      simp [σ, hja, sub_eq_add_neg]
    rw [he]
    exact hedge a j (Ne.symm hja)
  refine ⟨c, hsign, hcmem, ?_⟩
  intro i j hij
  by_cases hia : i = a
  · subst i
    exact hanchor j (Ne.symm hij)
  by_cases hja : j = a
  · subst j
    have h := hneg _ (hanchor i hia)
    simpa [neg_sub] using h
  have htri := triangle_sign_equation b (Q : Set (Lattice n)) hQ hb
    (Ne.symm hia) (Ne.symm hja) hij (ε a i) (ε i j) (ε a j)
    (hε a i) (hε i j) (hε a j) (hedge a i (Ne.symm hia))
    (hedge i j hij) (hedge a j (Ne.symm hja))
  have he : c i - c j = (-ε a i) • (b i + ε i j • b j) := by
    rw [hc, hc]
    simp only [σ, if_neg hia, if_neg hja]
    rw [htri]
    module
  rw [he]
  exact unit_smul_mem Q hneg (hedge i j hij) (by simpa using hε a i)

/-- The full signed type-A root set in an arbitrary lattice basis. -/
def rootSet (b : Module.Basis (Fin n) ℤ (Lattice n)) : Set (Lattice n) :=
  {q | (∃ i, q = b i ∨ q = -b i) ∨ ∃ i j, i ≠ j ∧ q = b i - b j}

theorem rootSet_eq_vertex_differences (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    rootSet b = {u | ∃ p q : Option (Fin n), p ≠ q ∧
      u = Graphic.vertex b p - Graphic.vertex b q} := by
  ext u
  constructor
  · rintro (⟨i, h | h⟩ | ⟨i,j,hij,h⟩)
    · exact ⟨some i,none,by simp,by simpa [Graphic.vertex] using h⟩
    · exact ⟨none,some i,by simp,by simpa [Graphic.vertex] using h⟩
    · exact ⟨some i,some j,fun he => hij (Option.some.inj he),h⟩
  · rintro ⟨p,q,hpq,h⟩
    cases p with
    | none => cases q with
      | none => exact (hpq rfl).elim
      | some j => exact Or.inl ⟨j, Or.inr (by simpa [Graphic.vertex] using h)⟩
    | some i => cases q with
      | none => exact Or.inl ⟨i, Or.inl (by simpa [Graphic.vertex] using h)⟩
      | some j => exact Or.inr ⟨i,j,fun he => hpq (congrArg some he),h⟩

/-- Under the support bound derived from doubled lifts, extremal cardinality
forces the complete root system in an actual integral basis. -/
theorem pair_support_normal_form (b : Module.Basis (Fin n) ℤ (Lattice n))
    (Q : Finset (Lattice n))
    (hQ : IntegralRigidity.Uniform b (fun q : (Q : Set (Lattice n)) => q.val))
    (hb : ∀ i, b i ∈ Q) (hzero : 0 ∉ Q) (hneg : ∀ q ∈ Q, -q ∈ Q)
    (hmass : ∀ q ∈ Q, (∑ i, |b.repr q i|) ≤ 2)
    (hcard : Q.card = n * (n + 1)) :
    ∃ c : Module.Basis (Fin n) ℤ (Lattice n),
      (∀ i, c i = b i ∨ c i = -b i) ∧ (Q : Set (Lattice n)) = rootSet c := by
  have hpair : ∀ (i j : Fin n), i ≠ j → b i + b j ∈ Q ∨ b i - b j ∈ Q :=
    fun _ _ hij => pair_sum_or_difference b Q hQ hb hzero hneg hmass hcard hij
  obtain ⟨c, hsign, hcmem, hdiff⟩ := exists_signed_pair_basis b Q hQ hb hneg hpair
  have hcs (i : Fin n) : coordSupport b (c i) = {i} := by
    ext k
    rcases hsign i with hc | hc <;>
      simp [coordSupport, hc, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  have hds (i j : Fin n) (hij : i ≠ j) : coordSupport b (c i - c j) = {i,j} := by
    ext k
    rcases hsign i with hci | hci <;> rcases hsign j with hcj | hcj <;>
      simp only [coordSupport, hci, hcj, map_sub, map_neg,
        Finsupp.sub_apply, Finsupp.neg_apply, Module.Basis.repr_self, Finsupp.single_apply,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    all_goals
      by_cases hki : k = i
      · subst k; simp [hij, Ne.symm hij]
      · by_cases hkj : k = j
        · subst k; simp [hij, Ne.symm hij]
        · simp [hki, hkj, Ne.symm hki, Ne.symm hkj]
  refine ⟨c, hsign, ?_⟩
  ext q
  constructor
  · intro hq
    have hqnz : q ≠ 0 := fun he => hzero (he ▸ hq)
    have hp := Finset.card_pos.2 (coordSupport_nonempty b hqnz)
    have hm := support_card_le_two (fun i => b.repr q i) (hmass q hq)
    change (coordSupport b q).card ≤ 2 at hm
    have hcases : (coordSupport b q).card = 1 ∨ (coordSupport b q).card = 2 := by omega
    rcases hcases with hc | hc
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hc
      exact Or.inl ⟨i, same_support_eq_or_neg b (Q : Set (Lattice n)) hQ hb hq (hcmem i)
        hqnz (hi.trans (hcs i).symm)⟩
    · obtain ⟨i,j,hij,hijq⟩ := Finset.card_eq_two.1 hc
      rcases same_support_eq_or_neg b (Q : Set (Lattice n)) hQ hb hq (hdiff i j hij)
        hqnz (hijq.trans (hds i j hij).symm) with he | he
      · exact Or.inr ⟨i,j,hij,he⟩
      · exact Or.inr ⟨j,i,Ne.symm hij,by simpa [neg_sub] using he⟩
  · rintro (⟨i, h | h⟩ | ⟨i,j,hij,h⟩)
    · simpa [h] using hcmem i
    · simpa [h] using hneg _ (hcmem i)
    · simpa [h] using hdiff i j hij

/-- The preceding equivalent presentation maps to the exact zero-sum lattice
and the exact eᵢ-eⱼ roots displayed in Theorem7.1. -/
theorem rootSet_lattice_identification (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    TypeA.basisEquiv b '' rootSet b = TypeA.roots n := by
  rw [rootSet_eq_vertex_differences]
  exact TypeA.basisEquiv_image_roots b

end Unimodular.Heller

end

end Recovered71_HellerPairNormalForm

/- Exact historical source: Unimodular/HellerRootLifting.lean. -/
section Recovered71_HellerRootLifting

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

variable {n : ℕ}

/-- A vector above the zero quotient column is one of the two primitive
coordinate rays; the zero vector remains explicitly excluded. -/
theorem zero_projection_signed (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ S) (hzero : 0 ∉ S)
    {x : Lattice (n + 1)} (hx : x ∈ S) (ht : tail x = 0) :
    x = Pi.single 0 1 ∨ x = -(Pi.single 0 1) := by
  have h := coordinate_abs_le_one (Pi.basisFun ℤ (Fin (n + 1)))
    (S : Set (Lattice (n + 1))) hS hb hx 0
  simp only [Pi.basisFun_repr] at h
  have hx0 : x 0 ≠ 0 := by
    intro hz
    have he : x = 0 := eq_of_tail_eq_of_height_eq (by simpa using ht) hz
    exact hzero (he ▸ hx)
  have hbd := abs_le.mp h
  have hc : x 0 = 1 ∨ x 0 = -1 := by omega
  rcases hc with hc | hc
  · left
    apply eq_of_tail_eq_of_height_eq
    · ext j
      have htj := congrFun ht j
      simpa [tail, Pi.single_apply, Fin.succ_ne_zero] using htj
    · simpa using hc
  · right
    apply eq_of_tail_eq_of_height_eq
    · ext j
      have htj := congrFun ht j
      simpa [tail, Pi.single_apply, Fin.succ_ne_zero] using htj
    · simpa using hc

/-- Once two adjacent lifts are known, they exhaust that entire quotient fiber. -/
theorem lift_eq_of_adjacent_pair (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ S)
    {q : Lattice n} (hq : q ≠ 0) {l : Lattice (n + 1)}
    (hl : l ∈ S) (hlplus : l + Pi.single 0 1 ∈ S) (hlt : tail l = q)
    {x : Lattice (n + 1)} (hx : x ∈ S) (hxt : tail x = q) :
    x = l ∨ x = l + Pi.single 0 1 := by
  have htplus : tail (l + Pi.single 0 1) = q := by
    ext i
    simpa [tail, Pi.single_apply, Fin.succ_ne_zero] using congrFun hlt i
  have hn : l ≠ l + Pi.single 0 1 := by
    intro he
    have h := congrFun he 0
    simp only [Pi.add_apply, Pi.single_eq_same] at h
    omega
  have hsub : {l, l + Pi.single 0 1} ⊆ fiber S q := by
    intro y hy
    rcases Finset.mem_insert.1 hy with hy | hy
    · subst y; exact mem_fiber.2 ⟨hl,hlt⟩
    · have hy' := Finset.mem_singleton.1 hy
      subst y; exact mem_fiber.2 ⟨hlplus,htplus⟩
  have he : {l, l + Pi.single 0 1} = fiber S q :=
    Finset.eq_of_subset_of_card_le hsub (by simpa [hn] using fiber_card_le_two S hS hb hq)
  have hm := mem_fiber.2 ⟨hx,hxt⟩
  rw [← he] at hm
  simpa using hm

/-- A quotient difference has one forced lift height. Independently moving
one of the two basis lifts gives both inequalities and hence equality. -/
theorem difference_lift_eq (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (c : Module.Basis (Fin n) ℤ (Lattice n))
    (l : Fin n → Lattice (n + 1)) (hlt : ∀ i, tail (l i) = c i)
    (hl : ∀ i, l i ∈ S) (hlplus : ∀ i, l i + Pi.single 0 1 ∈ S)
    {x : Lattice (n + 1)} (hx : x ∈ S) {i j : Fin n} (hij : i ≠ j)
    (hxt : tail x = c i - c j) : x = l i - l j := by
  have hbound (t : Fin n) :
      |x 0 - ∑ k, (Function.update l t (l t + Pi.single 0 1)) k 0 *
        c.repr (tail x) k| ≤ 1 := by
    apply lifted_height_abs_le_one (S : Set (Lattice (n + 1))) hS c _ _ _ hx
    · intro k
      by_cases hkt : k = t
      · subst k
        ext a
        simpa [tail, Pi.single_apply, Fin.succ_ne_zero] using congrFun (hlt t) a
      · simpa [hkt] using hlt k
    · intro k
      by_cases hkt : k = t
      · subst k; simpa using hlplus t
      · simpa [hkt] using hl k
  have hi := hbound i
  have hj := hbound j
  simp [hxt, map_sub, Finsupp.sub_apply, Module.Basis.repr_self,
    Finsupp.single_apply, mul_sub, Finset.sum_sub_distrib, hij, Ne.symm hij] at hi hj
  have hi' := abs_le.mp hi
  have hj' := abs_le.mp hj
  apply eq_of_tail_eq_of_height_eq
  · change tail x = tail (l i) - tail (l j)
    rw [hxt, hlt i, hlt j]
  · change x 0 = l i 0 - l j 0
    omega

/-- The root set is closed under negation, with differences reversed. -/
theorem neg_mem_rootSet (b : Module.Basis (Fin n) ℤ (Lattice n))
    {x : Lattice n} (hx : x ∈ rootSet b) : -x ∈ rootSet b := by
  rcases hx with ⟨i, hi | hi⟩ | ⟨i,j,hij,h⟩
  · exact Or.inl ⟨i,Or.inr (by simp [hi])⟩
  · exact Or.inl ⟨i,Or.inl (by simp [hi])⟩
  · exact Or.inr ⟨j,i,Ne.symm hij,by simp [h]⟩

/-- Lift the complete quotient root system through its full doubled basis.
The resulting basis consists of actual original rays, and equality holds for
the entire original set, not merely for a chosen subconfiguration. -/
theorem lift_complete_root_system (S : Finset (Lattice (n + 1)))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1)))
      (fun x : (S : Set (Lattice (n + 1))) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ S) (hzero : 0 ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S)
    (c : Module.Basis (Fin n) ℤ (Lattice n))
    (hQ : (projection S : Set (Lattice n)) = rootSet c)
    (l : Fin n → Lattice (n + 1)) (hlt : ∀ i, tail (l i) = c i)
    (hl : ∀ i, l i ∈ S) (hlplus : ∀ i, l i + Pi.single 0 1 ∈ S) :
    ∃ H : Module.Basis (Fin (n + 1)) ℤ (Lattice (n + 1)),
      (S : Set (Lattice (n + 1))) = rootSet H := by
  let e : Lattice (n + 1) := Pi.single 0 1
  let v : Fin (n + 1) → Lattice (n + 1) := Fin.cons e (fun i => l i + e)
  have htl : (fun i => tail (l i + e)) = c := by
    funext i
    ext j
    simpa [e, tail, Pi.single_apply, Fin.succ_ne_zero] using congrFun (hlt i) j
  have hunit : IsUnit ((Pi.basisFun ℤ (Fin (n + 1))).det v) := by
    change IsUnit ((Pi.basisFun ℤ (Fin (n + 1))).det
      (Fin.cons (Pi.single 0 1) (fun i => l i + e)))
    rw [det_cons_first, htl]
    exact (Pi.basisFun ℤ (Fin n)).isUnit_det c
  obtain ⟨hli, hsp⟩ := (Pi.basisFun ℤ (Fin (n + 1))).is_basis_iff_det.mpr hunit
  let H := Module.Basis.mk hli hsp.ge
  have hv (i : Fin (n + 1)) : H i = v i := Module.Basis.mk_apply _ _ i
  have hH0 : H 0 = e := by simp [hv, v]
  have hHsucc (i : Fin n) : H i.succ = l i + e := by simp [hv, v]
  have heS : e ∈ S := by simpa [e, Pi.basisFun_apply] using hb 0
  have hHm (i : Fin (n + 1)) : H i ∈ S := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [hH0] using heS
    · simpa [hHsucc, e] using hlplus j
  have hdiff : ∀ i j : Fin (n + 1), i ≠ j → H i - H j ∈ S := by
    intro i
    refine Fin.cases ?_ (fun a => ?_) i
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact (hij rfl).elim
      · intro _
        convert hneg _ (hl b) using 1
        rw [hH0,hHsucc]
        abel
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro _
        convert hl a using 1
        rw [hHsucc,hH0]
        abel
      · intro hij
        have hab : a ≠ b := fun h => hij (congrArg Fin.succ h)
        have hq : c a - c b ∈ projection S := by
          change c a - c b ∈ (projection S : Set (Lattice n))
          rw [hQ]
          exact Or.inr ⟨a,b,hab,rfl⟩
        obtain ⟨_,y,hy,hyt⟩ := mem_projection.1 hq
        have he := difference_lift_eq S hS c l hlt hl hlplus hy hab hyt
        convert hy using 1
        rw [he,hHsucc,hHsucc]
        abel
  have hpos (x : Lattice (n + 1)) (hx : x ∈ S) (i : Fin n)
      (hxt : tail x = c i) : x ∈ rootSet H := by
    rcases lift_eq_of_adjacent_pair S hS hb (c.ne_zero i) (hl i) (hlplus i) (hlt i) hx hxt
      with he | he
    · exact Or.inr ⟨i.succ,0,Fin.succ_ne_zero i,by rw [he,hHsucc,hH0]; simp⟩
    · exact Or.inl ⟨i.succ,Or.inl (by simpa [e] using he.trans (hHsucc i).symm)⟩
  refine ⟨H, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxt : tail x = 0
    · rcases zero_projection_signed S hS hb hzero hx hxt with he | he
      · exact Or.inl ⟨0,Or.inl (by simpa [e,hH0] using he)⟩
      · exact Or.inl ⟨0,Or.inr (by simpa [e,hH0] using he)⟩
    have hxQ : tail x ∈ rootSet c := by
      rw [← hQ]
      exact mem_projection.2 ⟨hxt,x,hx,rfl⟩
    rcases hxQ with ⟨i,hi | hi⟩ | ⟨i,j,hij,hijx⟩
    · exact hpos x hx i hi
    · have hn : tail (-x) = c i := by rw [tail_neg,hi,neg_neg]
      have hm := hpos (-x) (hneg x hx) i hn
      simpa using neg_mem_rootSet H hm
    · have he := difference_lift_eq S hS c l hlt hl hlplus hx hij hijx
      exact Or.inr ⟨i.succ,j.succ,fun h => hij (Fin.succ_inj.1 h),by
        rw [he,hHsucc,hHsucc]; abel⟩
  · rintro (⟨i,hi | hi⟩ | ⟨i,j,hij,hx⟩)
    · simpa [hi] using hHm i
    · simpa [hi] using hneg _ (hHm i)
    · simpa [hx] using hdiff i j hij

end Unimodular.Heller

end

end Recovered71_HellerRootLifting

/- Exact historical source: Unimodular/HellerTheorem.lean. -/
section Recovered71_HellerTheorem

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

/-- The complete equality case after basis normalization. No central symmetry,
small-support restriction, or graphicness is assumed: each is derived from the
extremal cardinality and uniform unimodularity. -/
theorem normalized_extremal_root_basis {n : ℕ} (S : Finset (Lattice n))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun x : (S : Set (Lattice n)) => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin n)) i ∈ S) (hzero : 0 ∉ S)
    (hcard : S.card = n * (n + 1)) :
    ∃ H : Module.Basis (Fin n) ℤ (Lattice n), (S : Set (Lattice n)) = rootSet H := by
  classical
  cases n with
  | zero =>
      have he : S = ∅ := Finset.card_eq_zero.1 (by simpa using hcard)
      refine ⟨Pi.basisFun ℤ (Fin 0), ?_⟩
      ext x
      simp [he, rootSet]
  | succ n =>
      have hneg := extremal_neg_closed S hS
        (real_span_of_contains_basis (S : Set (Lattice (n + 1))) hb) hzero hcard
      obtain ⟨b,hDb⟩ := extremal_doubles_basis S hS hb hzero hcard
      have hbD (i : Fin n) : b i ∈ doubles S := by rw [hDb]; simp
      have hbQ (i : Fin n) : b i ∈ projection S := (mem_doubles.1 (hbD i)).1
      have hQeq : (projection S : Set (Lattice n)) =
          projected (S : Set (Lattice (n + 1))) := by
        ext q
        simp [projected]
      have hQ : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
          (fun q : (projection S : Set (Lattice n)) => q.val) := by
        rw [hQeq]
        apply projected_uniform _ hS
        simpa [Pi.basisFun_apply] using hb 0
      have hQb : IntegralRigidity.Uniform b
          (fun q : (projection S : Set (Lattice n)) => q.val) := by
        intro a
        rw [BasisCover.basis_determinant_abs b (Pi.basisFun ℤ (Fin n))]
        exact hQ a
      have hQneg : ∀ q ∈ projection S, -q ∈ projection S := by
        intro q hq
        obtain ⟨hnz,x,hx,hxt⟩ := mem_projection.1 hq
        exact mem_projection.2 ⟨neg_ne_zero.2 hnz,-x,hneg x hx,by rw [tail_neg,hxt]⟩
      have hQcard := (extremal_projection_counts S hS hb hzero hcard).1
      choose l hl hlplus hlt using fun i => exists_adjacent_lifts S hS hb (hbD i)
      have hmass : ∀ q ∈ projection S, (∑ i, |b.repr q i|) ≤ 2 := by
        intro q hq
        obtain ⟨_,x,hx,hxt⟩ := mem_projection.1 hq
        have h := full_doubled_basis_mass_le_two (S : Set (Lattice (n + 1))) hS b l
          hlt hl hlplus hx
        rwa [hxt] at h
      obtain ⟨c,hcsign,hQc⟩ := pair_support_normal_form b (projection S) hQb hbQ
        (by simp) hQneg hmass hQcard
      have hcD (i : Fin n) : c i ∈ doubles S := by
        rcases hcsign i with h | h <;> rw [h,hDb] <;> simp
      choose l' hl' hlplus' hlt' using fun i => exists_adjacent_lifts S hS hb (hcD i)
      exact lift_complete_root_system S hS hb hzero hneg c hQc l' hlt' hl' hlplus'

/-- Root configurations commute with integral changes of lattice coordinates. -/
theorem rootSet_map {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (φ : Lattice n ≃ₗ[ℤ] Lattice n) : rootSet (b.map φ) = φ '' rootSet b := by
  rw [rootSet_eq_vertex_differences, rootSet_eq_vertex_differences]
  have hv (p : Option (Fin n)) : Graphic.vertex (b.map φ) p = φ (Graphic.vertex b p) := by
    cases p <;> simp [Graphic.vertex]
  ext x
  constructor
  · rintro ⟨p,q,hpq,hx⟩
    refine ⟨Graphic.vertex b p - Graphic.vertex b q,⟨p,q,hpq,rfl⟩,?_⟩
    rw [map_sub, ← hv, ← hv]
    exact hx.symm
  · rintro ⟨y,⟨p,q,hpq,rfl⟩,rfl⟩
    exact ⟨p,q,hpq,by rw [map_sub,hv,hv]⟩

/-- Heller's full equality classification in the original, unnormalized lattice. -/
theorem extremal_root_basis {n : ℕ} (S : Finset (Lattice n))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun x : (S : Set (Lattice n)) => x.val))
    (hspan : Submodule.span ℝ (embed '' (S : Set (Lattice n))) = ⊤)
    (hzero : 0 ∉ S) (hcard : S.card = n * (n + 1)) :
    ∃ H : Module.Basis (Fin n) ℤ (Lattice n), (S : Set (Lattice n)) = rootSet H := by
  let a : Fin 0 → (S : Set (Lattice n)) := Fin.elim0
  obtain ⟨b,hb,_⟩ := LatticeHull.exists_lattice_basis_extension
    (S : Set (Lattice n)) hS hspan a (linearIndependent_empty_type ..)
  let φ : Lattice n ≃ₗ[ℤ] Lattice n :=
    b.equiv (Pi.basisFun ℤ (Fin n)) (Equiv.refl _)
  let T : Finset (Lattice n) := S.image φ
  have hTco : (T : Set (Lattice n)) = φ '' (S : Set (Lattice n)) := by simp [T]
  have hT : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun x : (T : Set (Lattice n)) => x.val) := by
    rw [hTco]
    exact uniform_image _ hS φ
  have hbT : ∀ i, (Pi.basisFun ℤ (Fin n)) i ∈ T := by
    intro i
    exact Finset.mem_image.2 ⟨b i,hb i,by simp [φ]⟩
  have hzT : (0 : Lattice n) ∉ T := by
    intro h
    obtain ⟨x,hx,hφx⟩ := Finset.mem_image.1 h
    have hx0 : x = 0 := φ.injective (by simpa using hφx)
    exact hzero (hx0 ▸ hx)
  have hcardT : T.card = n * (n + 1) := by
    rw [show T.card = S.card from Finset.card_image_of_injective _ φ.injective,hcard]
  obtain ⟨H,hH⟩ := normalized_extremal_root_basis T hT hbT hzT hcardT
  refine ⟨H.map φ.symm, ?_⟩
  rw [rootSet_map, ← hH, hTco, Set.image_image]
  simp

/-- Exactly the ray-bound and equality assertion of Theorem7.1. The target is
literally the zero-sum lattice in ℤ^(n+1), and the target set is literally all
roots eᵢ-eⱼ with i≠j. The fan subdivision assertions of that theorem are separate. -/
theorem extremal_iff_typeA {n : ℕ} (S : Finset (Lattice n))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun x : (S : Set (Lattice n)) => x.val))
    (hspan : Submodule.span ℝ (embed '' (S : Set (Lattice n))) = ⊤)
    (hzero : 0 ∉ S) :
    S.card = n * (n + 1) ↔
      ∃ φ : Lattice n ≃ₗ[ℤ] TypeA.RootLattice n,
        φ '' (S : Set (Lattice n)) = TypeA.roots n := by
  constructor
  · intro hcard
    obtain ⟨H,hH⟩ := extremal_root_basis S hS hspan hzero hcard
    exact ⟨TypeA.basisEquiv H, by rw [hH]; exact rootSet_lattice_identification H⟩
  · rintro ⟨φ,hφ⟩
    have h := Set.ncard_image_of_injective (S : Set (Lattice n)) φ.injective
    rw [hφ, TypeA.roots_ncard, Set.ncard_coe_finset] at h
    exact h.symm

end Unimodular.Heller

end

end Recovered71_HellerTheorem

/- Exact historical source: Unimodular/HellerFan.lean. -/
section Recovered71_HellerFan

noncomputable section

namespace Unimodular.Heller

open TauCeti.Toric

/-- Completeness of an actual finite rational fan forces its exact prescribed
ray configuration to span the real ambient space. This deduction uses the
proved generation of every fan cone by its extreme rays. -/
theorem complete_ray_span {n : ℕ} (S : Finset (Lattice n))
    (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
      (fun u : (S : Set (Lattice n)) => u.val) Φ) (hzero : 0 ∉ S) :
    Submodule.span ℝ (embed '' (S : Set (Lattice n))) = ⊤ := by
  classical
  have hnz (u : (S : Set (Lattice n))) : FanBridge.standardEmbedding n u.val ≠ 0 := by
    intro hu
    have hz : u.val = 0 := by
      ext i
      have hi := congrFun hu i
      change (u.val i : ℝ) = 0 at hi
      exact_mod_cast hi
    exact hzero (hz ▸ u.property)
  apply top_unique
  intro x _
  obtain ⟨C, hC, hx⟩ := Φ.isComplete_iff.1 hcomplete x
  obtain ⟨_, hgen⟩ := AllowedBlocks.fan_cone_allowed
    (FanBridge.standardEmbedding n) (fun u : (S : Set (Lattice n)) => u.val) hnz hrays hC
  rw [← hgen] at hx
  have hle : AllowedBlocks.blockCone (FanBridge.standardEmbedding n)
      (fun u : (S : Set (Lattice n)) => u.val)
      (AllowedBlocks.blockOfCone (FanBridge.standardEmbedding n)
        (fun u : (S : Set (Lattice n)) => u.val) C) ≤
      PointedCone.ofSubmodule (Submodule.span ℝ (embed '' (S : Set (Lattice n)))) := by
    apply Submodule.span_le.mpr
    rintro y ⟨u, hu, rfl⟩
    exact Submodule.subset_span ⟨u.val, u.property, rfl⟩
  exact hle hx

/-- The bound and complete equality case of Theorem 7.1 for genuine complete
fans, including nonsimplicial and nonprojective fans. The equality target is the
literal zero-sum lattice and the entire set of nonzero type-A roots. -/
theorem theorem_7_1_bound_and_equality {n : ℕ} (S : Finset (Lattice n))
    (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
      (fun u : (S : Set (Lattice n)) => u.val) Φ)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (S : Set (Lattice n)) => u.val)) (hzero : 0 ∉ S) :
    S.card ≤ n * (n + 1) ∧
      (S.card = n * (n + 1) ↔
        ∃ φ : Lattice n ≃ₗ[ℤ] TypeA.RootLattice n,
          φ '' (S : Set (Lattice n)) = TypeA.roots n) := by
  have hspan := complete_ray_span S Φ hcomplete hrays hzero
  exact ⟨ray_card_le S hU hspan hzero, extremal_iff_typeA S hU hspan hzero⟩

/-- The ray-span deduction is coordinate-free: the ambient real vector space
is exactly the scalar extension of the original integral lattice. -/
theorem complete_ray_span_general {N V : Type*} [AddCommGroup N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (S : Finset N) (Φ : Fan ι) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays ι (fun u : (S : Set N) => u.val) Φ)
    (hzero : 0 ∉ S) : Submodule.span ℝ (ι '' (S : Set N)) = ⊤ := by
  classical
  have hnz (u : (S : Set N)) : ι u.val ≠ 0 := by
    intro hu
    have hz : u.val = 0 := Φ.lattice.injective (by simpa using hu)
    exact hzero (hz ▸ u.property)
  apply top_unique
  intro x _
  obtain ⟨C, hC, hx⟩ := Φ.isComplete_iff.1 hcomplete x
  obtain ⟨_, hgen⟩ := AllowedBlocks.fan_cone_allowed ι
    (fun u : (S : Set N) => u.val) hnz hrays hC
  rw [← hgen] at hx
  have hle : AllowedBlocks.blockCone ι (fun u : (S : Set N) => u.val)
      (AllowedBlocks.blockOfCone ι (fun u : (S : Set N) => u.val) C) ≤
      PointedCone.ofSubmodule (Submodule.span ℝ (ι '' (S : Set N))) := by
    apply Submodule.span_le.mpr
    rintro y ⟨u, hu, rfl⟩
    exact Submodule.subset_span ⟨u.val, u.property, rfl⟩
  exact hle hx

/-- The bound and its exact integral equality classification on an arbitrary
rank-n lattice. The chosen basis only expresses the determinant hypothesis;
no property of its relation to the ray set is assumed. -/
theorem theorem_7_1_bound_and_equality_general {n : ℕ} {N V : Type*}
    [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : N →+ V}
    (b : Module.Basis (Fin n) ℤ N) (S : Finset N)
    (Φ : Fan ι) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays ι (fun u : (S : Set N) => u.val) Φ)
    (hU : IntegralRigidity.Uniform b (fun u : (S : Set N) => u.val))
    (hzero : 0 ∉ S) :
    S.card ≤ n * (n + 1) ∧
      (S.card = n * (n + 1) ↔
        ∃ ψ : N ≃ₗ[ℤ] TypeA.RootLattice n,
          ψ '' (S : Set N) = TypeA.roots n) := by
  classical
  let φ : N ≃ₗ[ℤ] Lattice n := b.equivFun
  let T := S.image φ
  have hTco : (T : Set (Lattice n)) = φ '' (S : Set N) := by simp [T]
  have hbmap : b.map φ = Pi.basisFun ℤ (Fin n) := by
    ext i j
    simp [φ, Module.Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  have hTU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (T : Set (Lattice n)) => u.val) := by
    intro a
    have hm (i : Fin n) : (a i).val ∈ φ '' (S : Set N) := by
      rw [← hTco]
      exact (a i).property
    choose x hx he using hm
    have h := hU (fun i => ⟨x i, hx i⟩)
    have heq : φ.symm ∘ (fun i => (a i).val) = x := by
      funext i
      change φ.symm (a i).val = x i
      rw [← he i, φ.symm_apply_apply]
    change |(Pi.basisFun ℤ (Fin n)).det (fun i => (a i).val)| ≤ 1
    rw [← hbmap, Module.Basis.det_map, heq]
    exact h
  have hzT : (0 : Lattice n) ∉ T := by
    rintro hz
    obtain ⟨x,hx,hφx⟩ := Finset.mem_image.1 hz
    have hx0 : x = 0 := φ.injective (by simpa using hφx)
    exact hzero (hx0 ▸ hx)
  have hcardT : T.card = S.card := Finset.card_image_of_injective S φ.injective
  let c := CoordinateQuotients.realBasis ι Φ.lattice b
  have hspan := complete_ray_span_general S Φ hcomplete hrays hzero
  have himage : c.equivFun.toLinearMap '' (ι '' (S : Set N)) =
      embed '' (T : Set (Lattice n)) := by
    simp only [hTco, Set.image_image]
    congr 1
    funext u
    ext i
    exact CoordinateQuotients.realBasis_repr ι Φ.lattice b u i
  have hspanT : Submodule.span ℝ (embed '' (T : Set (Lattice n))) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y,rfl⟩ := c.equivFun.surjective x
    have hy : y ∈ Submodule.span ℝ (ι '' (S : Set N)) := by rw [hspan]; trivial
    have hm := Submodule.image_span_subset_span c.equivFun.toLinearMap
      (ι '' (S : Set N)) ⟨y,hy,rfl⟩
    rw [himage] at hm
    exact hm
  refine ⟨by simpa only [hcardT] using ray_card_le T hTU hspanT hzT, ?_⟩
  constructor
  · intro hcard
    obtain ⟨ψ,hψ⟩ := (extremal_iff_typeA T hTU hspanT hzT).1 (hcardT.trans hcard)
    refine ⟨φ.trans ψ,?_⟩
    change (ψ ∘ φ) '' (S : Set N) = TypeA.roots n
    simpa only [hTco, Set.image_image, Function.comp_def] using hψ
  · rintro ⟨ψ,hψ⟩
    have h := Set.ncard_image_of_injective (S : Set N) ψ.injective
    rw [hψ, TypeA.roots_ncard, Set.ncard_coe_finset] at h
    exact h.symm

#print axioms Unimodular.Heller.theorem_7_1_bound_and_equality_general

#print axioms Unimodular.Heller.theorem_7_1_bound_and_equality

end Unimodular.Heller

end

end Recovered71_HellerFan

