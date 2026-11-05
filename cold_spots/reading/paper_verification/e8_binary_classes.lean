module

public import PaperVerification.E8IntegralBasis
public import PaperVerification.BWCode
public import PaperVerification.LatticeTranslationClasses
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.Abel


@[expose] public section
/-! # The exact binary quadratic quotient of E8

The finite quadratic form is obtained by reducing the proved integral E8 basis
form.  Its 135 nonzero isotropic vectors are connected to actual half-lattice
points and actual lattice translation equivalence.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def e8BinaryQ (c : BinaryWord8) : Binary :=
  (∑ i, c i ^ 2) - c 0*c 2 - c 2*c 3 - c 1*c 3 - c 3*c 4 - c 4*c 5 - c 5*c 6 - c 6*c 7

def e8BinaryPolar (c d : BinaryWord8) : Binary := e8BinaryQ (c + d) - e8BinaryQ c - e8BinaryQ d

def e8BinaryRoot : BinaryWord8 := fun i => (e8HalfCoordinates i : Binary)

abbrev E8HoleIndex := {c : BinaryWord8 // e8BinaryQ c = 0 ∧ c ≠ 0}

/- The eight coordinates are split before counting.  The four trailing coordinates
have three disjoint solution branches, of sizes 4, 2, and either 4 or 0.  Only the
remaining four-coordinate sum is evaluated by the kernel's decision procedure. -/

private abbrev E8Head := Fin 4 → Binary
private abbrev E8Tail := Binary × Binary × Binary × Binary

private def e8HeadQ (a : E8Head) : Binary :=
  a 0 + a 1 + a 2 + a 3 + a 0 * a 2 + a 2 * a 3 + a 1 * a 3

private def e8TailQ (q r : Binary) (t : E8Tail) : Binary :=
  q + t.1 + t.2.1 + t.2.2.1 + t.2.2.2 + r * t.1 + t.1 * t.2.1 +
    t.2.1 * t.2.2.1 + t.2.2.1 * t.2.2.2

private theorem e8_binary_sq (x : Binary) : x ^ 2 = x := by
  rcases binary_eq_zero_or_one x with h | h <;> simp only [h, pow_two, zero_mul, one_mul]

private def e8BinaryCoordinates : BinaryWord8 ≃ E8Head × E8Tail where
  toFun c := (![c 0, c 1, c 2, c 3], c 4, c 5, c 6, c 7)
  invFun p := ![p.1 0, p.1 1, p.1 2, p.1 3,
    p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]
  left_inv c := by
    funext i
    fin_cases i <;> rfl
  right_inv := by
    rintro ⟨a, b, c, d, e⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl

private theorem e8BinaryQ_expanded (c : BinaryWord8) :
    e8BinaryQ c = c 0 + c 1 + c 2 + c 3 + c 4 + c 5 + c 6 + c 7 +
      c 0 * c 2 + c 2 * c 3 + c 1 * c 3 + c 3 * c 4 + c 4 * c 5 +
      c 5 * c 6 + c 6 * c 7 := by
  simp [e8BinaryQ, Fin.sum_univ_succ, e8_binary_sq, CharTwo.sub_eq_add] <;> abel

private theorem e8BinaryQ_coordinates (c : BinaryWord8) :
    e8BinaryQ c = e8TailQ (e8HeadQ (e8BinaryCoordinates c).1)
      ((e8BinaryCoordinates c).1 3) (e8BinaryCoordinates c).2 := by
  rw [e8BinaryQ_expanded]
  simp [e8BinaryCoordinates, e8HeadQ, e8TailQ] <;> abel

private theorem e8TailQ_zero (q r b c e : Binary) :
    e8TailQ q r (b, c, 0, e) = (q + b + c + r * b + b * c) + e := by
  dsimp [e8TailQ]
  simp only [add_zero, mul_zero, zero_mul]
  abel

private theorem e8TailQ_one_one (q r c e : Binary) :
    e8TailQ q r (1, c, 1, e) = q + r + c := by
  dsimp [e8TailQ]
  simp only [mul_one, one_mul]
  calc
    q + 1 + c + 1 + e + r + c + c + e =
        (q + r + c) + (1 + 1) + (c + c) + (e + e) := by abel
    _ = q + r + c := by simp only [CharTwo.add_self_eq_zero, add_zero]

private theorem e8TailQ_one_zero (q r c e : Binary) :
    e8TailQ q r (0, c, 1, e) = q + 1 := by
  dsimp [e8TailQ]
  simp only [add_zero, mul_zero, zero_mul, mul_one, one_mul]
  calc
    q + c + 1 + e + c + e = (q + 1) + (c + c) + (e + e) := by abel
    _ = q + 1 := by simp only [CharTwo.add_self_eq_zero, add_zero]

private def e8TailFiberEquiv (q r : Binary) :
    {t : E8Tail // e8TailQ q r t = 0} ≃
      (Binary × Binary) ⊕ (Binary ⊕ {t : Binary × Binary // q = 1}) where
  toFun x := by
    rcases x with ⟨⟨b, c, d, e⟩, hx⟩
    by_cases hd : d = 0
    · exact Sum.inl (b, c)
    · have hd1 : d = 1 := (binary_eq_zero_or_one d).resolve_left hd
      by_cases hb : b = 1
      · exact Sum.inr (Sum.inl e)
      · have hb0 : b = 0 := (binary_eq_zero_or_one b).resolve_right hb
        have hq : q = 1 := CharTwo.add_eq_zero.mp (by
          simpa only [hd1, hb0, e8TailQ_one_zero] using hx)
        exact Sum.inr (Sum.inr ⟨(c, e), hq⟩)
  invFun
    | Sum.inl (b, c) => ⟨(b, c, 0, q + b + c + r * b + b * c), by
        rw [e8TailQ_zero]
        exact CharTwo.add_self_eq_zero _⟩
    | Sum.inr (Sum.inl e) => ⟨(1, q + r, 1, e), by
        rw [e8TailQ_one_one]
        exact CharTwo.add_self_eq_zero _⟩
    | Sum.inr (Sum.inr ⟨(c, e), hq⟩) => ⟨(0, c, 1, e), by
        rw [e8TailQ_one_zero, hq]
        exact CharTwo.add_self_eq_zero _⟩
  left_inv := by
    rintro ⟨⟨b, c, d, e⟩, hx⟩
    apply Subtype.ext
    by_cases hd : d = 0
    · subst d
      have he : e = q + b + c + r * b + b * c :=
        (CharTwo.add_eq_zero.mp (by simpa only [e8TailQ_zero] using hx)).symm
      simp only [dite_true]
      exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl he.symm))
    · have hd1 : d = 1 := (binary_eq_zero_or_one d).resolve_left hd
      subst d
      by_cases hb : b = 1
      · subst b
        have hc : c = q + r :=
          (CharTwo.add_eq_zero.mp (by simpa only [e8TailQ_one_one] using hx)).symm
        simp only [one_ne_zero, dite_false, dite_true]
        exact Prod.ext rfl (Prod.ext hc.symm (Prod.ext rfl rfl))
      · have hb0 : b = 0 := (binary_eq_zero_or_one b).resolve_right hb
        subst b
        simp only [one_ne_zero, zero_ne_one, dite_false]
  right_inv := by
    rintro (⟨b, c⟩ | (e | ⟨⟨c, e⟩, hq⟩))
    · simp only [dite_true]
    · simp only [one_ne_zero, dite_false, dite_true]
    · simp only [one_ne_zero, zero_ne_one, dite_false]

private theorem e8Tail_fiber_card (q r : Binary) :
    Fintype.card {t : E8Tail // e8TailQ q r t = 0} =
      6 + if q = 1 then 4 else 0 := by
  have h := Fintype.card_congr (e8TailFiberEquiv q r)
  by_cases hq : q = 1 <;> simpa [hq, ZMod.card] using h

private theorem card_e8Isotropic :
    Fintype.card {c : BinaryWord8 // e8BinaryQ c = 0} = 136 := by
  let e : {c : BinaryWord8 // e8BinaryQ c = 0} ≃
      (Σ a : E8Head, {t : E8Tail // e8TailQ (e8HeadQ a) (a 3) t = 0}) :=
    (e8BinaryCoordinates.subtypeEquiv
      (p := fun c : BinaryWord8 => e8BinaryQ c = 0)
      (q := fun p : E8Head × E8Tail => e8TailQ (e8HeadQ p.1) (p.1 3) p.2 = 0)
      (fun c => by rw [e8BinaryQ_coordinates])).trans
        (Equiv.subtypeProdEquivSigmaSubtype (α := E8Head) (β := E8Tail)
          (fun (a : E8Head) (t : E8Tail) => e8TailQ (e8HeadQ a) (a 3) t = 0))
  calc
    Fintype.card {c : BinaryWord8 // e8BinaryQ c = 0} =
        ∑ a : E8Head, Fintype.card {t : E8Tail // e8TailQ (e8HeadQ a) (a 3) t = 0} := by
      rw [Fintype.card_congr e, Fintype.card_sigma]
    _ = ∑ a : E8Head, (6 + if e8HeadQ a = 1 then 4 else 0) :=
      Finset.sum_congr rfl (fun a _ => e8Tail_fiber_card _ _)
    _ = 136 := by decide

theorem card_e8HoleIndex : Fintype.card E8HoleIndex = 135 := by
  let Z := {c : BinaryWord8 // e8BinaryQ c = 0}
  let z : Z := ⟨0, by simp [e8BinaryQ]⟩
  let e : E8HoleIndex ≃ {c : Z // c ≠ z} :=
    { toFun := fun c => ⟨⟨c.val, c.property.1⟩, by
        intro h
        exact c.property.2 (congrArg Subtype.val h)⟩
      invFun := fun c => ⟨c.val.val, c.val.property, by
        intro h
        apply c.property
        exact Subtype.ext h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype_compl (fun c : Z => c = z),
    Fintype.card_subtype_eq, card_e8Isotropic]

theorem e8BinaryRoot_q : e8BinaryQ e8BinaryRoot = 1 := by decide

private theorem e8BinaryPolar_root (c : BinaryWord8) :
    e8BinaryPolar c e8BinaryRoot = c 0 + c 1 := by
  have h0 : e8BinaryRoot 0 = 1 := by decide
  have h1 : e8BinaryRoot 1 = 1 := by decide
  have h2 : e8BinaryRoot 2 = 1 := by decide
  have h3 : e8BinaryRoot 3 = 1 := by decide
  have h4 : e8BinaryRoot 4 = 0 := by decide
  have h5 : e8BinaryRoot 5 = 1 := by decide
  have h6 : e8BinaryRoot 6 = 0 := by decide
  have h7 : e8BinaryRoot 7 = 1 := by decide
  calc
    e8BinaryPolar c e8BinaryRoot = c 0 + c 1 +
        2 * (e8BinaryQ c + 9 + c 2 + c 3 + c 4 + c 6) := by
      simp only [e8BinaryPolar, e8BinaryQ_expanded, Pi.add_apply,
        h0, h1, h2, h3, h4, h5, h6, h7, CharTwo.sub_eq_add]
      ring
    _ = c 0 + c 1 := by rw [binary_two_eq_zero, zero_mul, add_zero]

private def e8HalfSliceCoordinateEquiv :
    {c : E8HoleIndex // e8BinaryPolar c.val e8BinaryRoot = 1} ≃
      {c : BinaryWord8 // e8BinaryQ c = 0 ∧ c 0 + c 1 = 1} where
  toFun c := ⟨c.val.val, c.val.property.1, by
    simpa only [e8BinaryPolar_root] using c.property⟩
  invFun c := ⟨⟨c.val, c.property.1, by
    intro hzero
    have h := c.property.2
    rw [hzero] at h
    simpa only [Pi.zero_apply, add_zero, zero_ne_one] using h⟩, by
      rw [e8BinaryPolar_root]
      exact c.property.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem card_e8HalfSliceIndex : Fintype.card
    {c : E8HoleIndex // e8BinaryPolar c.val e8BinaryRoot = 1} = 72 := by
  let e : {c : BinaryWord8 // e8BinaryQ c = 0 ∧ c 0 + c 1 = 1} ≃
      (Σ a : E8Head,
        {t : E8Tail // e8TailQ (e8HeadQ a) (a 3) t = 0 ∧ a 0 + a 1 = 1}) :=
    (e8BinaryCoordinates.subtypeEquiv
      (p := fun c : BinaryWord8 => e8BinaryQ c = 0 ∧ c 0 + c 1 = 1)
      (q := fun p : E8Head × E8Tail =>
        e8TailQ (e8HeadQ p.1) (p.1 3) p.2 = 0 ∧ p.1 0 + p.1 1 = 1)
      (fun c => by
        rw [e8BinaryQ_coordinates]
        rfl)).trans
        (Equiv.subtypeProdEquivSigmaSubtype (α := E8Head) (β := E8Tail)
          (fun (a : E8Head) (t : E8Tail) =>
            e8TailQ (e8HeadQ a) (a 3) t = 0 ∧ a 0 + a 1 = 1))
  have hc (a : E8Head) :
      Fintype.card {t : E8Tail // e8TailQ (e8HeadQ a) (a 3) t = 0 ∧ a 0 + a 1 = 1} =
        if a 0 + a 1 = 1 then (6 + if e8HeadQ a = 1 then 4 else 0) else 0 := by
    by_cases ha : a 0 + a 1 = 1
    · simpa only [ha, and_true, if_true] using e8Tail_fiber_card (e8HeadQ a) (a 3)
    · simp [ha]
  calc
    Fintype.card {c : E8HoleIndex // e8BinaryPolar c.val e8BinaryRoot = 1} =
        ∑ a : E8Head, Fintype.card
          {t : E8Tail // e8TailQ (e8HeadQ a) (a 3) t = 0 ∧ a 0 + a 1 = 1} := by
      rw [Fintype.card_congr (e8HalfSliceCoordinateEquiv.trans e), Fintype.card_sigma]
    _ = ∑ a : E8Head,
        (if a 0 + a 1 = 1 then (6 + if e8HeadQ a = 1 then 4 else 0) else 0) :=
      Finset.sum_congr rfl (fun a _ => hc a)
    _ = 72 := by decide

theorem e8IntegralQ_cast (t : Fin 8 → ℤ) :
    (e8IntegralQ t : Binary) = e8BinaryQ (fun i => (t i : Binary)) := by
  simp only [e8IntegralQ, e8BinaryQ, Int.cast_sub, Int.cast_sum, Int.cast_pow, Int.cast_mul]

def e8HalfRootSum (t : Fin 8 → ℤ) : Fin 8 → ℝ :=
  e8RootSum (fun i => (t i : ℝ) / 2)

theorem e8HalfRootSum_zero : e8HalfRootSum 0 = 0 := by
  simp [e8HalfRootSum, e8RootSum]

theorem e8HalfRootSum_sub (t u : Fin 8 → ℤ) :
    e8HalfRootSum (t - u) = e8HalfRootSum t - e8HalfRootSum u := by
  unfold e8HalfRootSum
  rw [← e8RootSum_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply, Int.cast_sub]
  ring

theorem e8HalfRootSum_two (t : Fin 8 → ℤ) :
    e8HalfRootSum (fun i => 2 * t i) = e8RootSum (fun i => (t i : ℝ)) := by
  unfold e8HalfRootSum
  congr 1
  funext i
  push_cast
  ring

theorem e8HalfRootSum_norm (t : Fin 8 → ℤ) :
    sqDist (e8HalfRootSum t) 0 = (e8IntegralQ t : ℝ) / 2 := by
  simp [sqDist, e8HalfRootSum, e8RootSum, e8SimpleRoot, e8IntegralQ, Fin.sum_univ_succ]
  ring

theorem e8HalfRootSum_double (t : Fin 8 → ℤ) :
    (fun i => 2 * e8HalfRootSum t i) = e8RootSum (fun i => (t i : ℝ)) := by
  change (2 : ℝ) • e8RootSum (fun i => (t i : ℝ) / 2) = _
  rw [← e8RootSum_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem e8HalfRootSum_mem_iff (t : Fin 8 → ℤ) :
    e8HalfRootSum t ∈ dPlusSet 8 ↔ ∀ i, Even (t i) := by
  rw [e8_mem_iff_integer_root_coordinates]
  constructor
  · rintro ⟨k, hk⟩ i
    have h := congrFun (e8RootSum_injective hk) i
    have hi : t i = k i + k i := by exact_mod_cast (show (t i : ℝ) = (k i : ℝ) + k i by linarith)
    exact ⟨k i, hi⟩
  · intro h
    choose k hk using h
    refine ⟨k, ?_⟩
    unfold e8HalfRootSum
    congr 1
    funext i
    rw [hk i]
    push_cast
    ring

theorem e8HalfRootSum_sub_mem_iff (t u : Fin 8 → ℤ) :
    e8HalfRootSum t - e8HalfRootSum u ∈ dPlusSet 8 ↔
      (fun i => (t i : Binary)) = fun i => (u i : Binary) := by
  rw [← e8HalfRootSum_sub, e8HalfRootSum_mem_iff]
  constructor
  · intro h
    funext i
    have hi := ZMod.intCast_eq_zero_iff_even.mpr (h i)
    simpa only [Pi.sub_apply, Int.cast_sub, sub_eq_zero] using hi
  · intro h i
    apply ZMod.intCast_eq_zero_iff_even.mp
    simp only [Pi.sub_apply, Int.cast_sub]
    rw [congrFun h i, sub_self]

def e8ClassPoint (c : BinaryWord8) : Fin 8 → ℝ :=
  e8HalfRootSum (fun i => ((c i).val : ℤ))

theorem e8ClassPoint_sub_mem_iff (c d : BinaryWord8) :
    e8ClassPoint c - e8ClassPoint d ∈ dPlusSet 8 ↔ c = d := by
  rw [e8ClassPoint, e8ClassPoint, e8HalfRootSum_sub_mem_iff]
  simp only [binary_val_cast]

theorem e8HalfRootSum_class (t : Fin 8 → ℤ) :
    e8HalfRootSum t - e8ClassPoint (fun i => (t i : Binary)) ∈ dPlusSet 8 := by
  rw [e8ClassPoint, e8HalfRootSum_sub_mem_iff]
  simp only [binary_val_cast]

theorem sqDist_eq_zero_iff {n : ℕ} (x y : Fin n → ℝ) : sqDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j - y j))).mp h i
      (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · rintro rfl
    simp [sqDist]

theorem sqDist_sub_zero {n : ℕ} (x y : Fin n → ℝ) : sqDist (x - y) 0 = sqDist x y := by
  simp only [sqDist, Pi.sub_apply, Pi.zero_apply, sub_zero]

/-- Isotropy gives integral positive squared distances from every E8 point. -/
theorem e8HalfRootSum_distance_lower {t : Fin 8 → ℤ}
    (hq : e8BinaryQ (fun i => (t i : Binary)) = 0)
    (hne : (fun i => (t i : Binary)) ≠ 0) {y : Fin 8 → ℝ} (hy : y ∈ dPlusSet 8) :
    1 ≤ sqDist (e8HalfRootSum t) y := by
  obtain ⟨k, rfl⟩ := (e8_mem_iff_integer_root_coordinates y).mp hy
  let u : Fin 8 → ℤ := t - fun i => 2 * k i
  have hu : (fun i => (u i : Binary)) = fun i => (t i : Binary) := by
    funext i
    simp [u]
  have hQ : Even (e8IntegralQ u) := by
    apply ZMod.intCast_eq_zero_iff_even.mp
    rw [e8IntegralQ_cast, hu, hq]
  obtain ⟨m, hm⟩ := hQ
  have hd : sqDist (e8HalfRootSum t) (e8RootSum (fun i => (k i : ℝ))) = (m : ℝ) := by
    rw [← e8HalfRootSum_two k, ← sqDist_sub_zero, ← e8HalfRootSum_sub,
      e8HalfRootSum_norm]
    change (e8IntegralQ u : ℝ) / 2 = (m : ℝ)
    rw [hm]
    push_cast
    ring
  have hm0 : 0 ≤ m := by
    exact_mod_cast (hd ▸ sqDist_nonneg (e8HalfRootSum t) (e8RootSum (fun i => (k i : ℝ))))
  have hmne : m ≠ 0 := by
    intro hmz
    have hzero : sqDist (e8HalfRootSum t) (e8RootSum (fun i => (k i : ℝ))) = 0 := by simpa [hmz] using hd
    have he := (sqDist_eq_zero_iff _ _).mp hzero
    have hmem := he.symm ▸ e8RootSum_int_mem k
    have heven := (e8HalfRootSum_mem_iff t).mp hmem
    apply hne
    funext i
    exact ZMod.intCast_eq_zero_iff_even.mpr (heven i)
  have hm1 : 1 ≤ m := by omega
  rw [hd]
  exact_mod_cast hm1

theorem e8ClassPoint_deep (c : E8HoleIndex) : IsDeepHole (dPlusSet 8) (e8ClassPoint c.val) := by
  apply (isDeepHole_E8_iff _).mpr
  apply (squaredDepth_E8_eq_one_iff _).mp
  apply le_antisymm (by simpa using squaredDepth_dPlus_le (by decide : 8 ≤ 8) (e8ClassPoint c.val))
  apply le_csInf ((dPlusSet_nonempty 8).image (fun y => sqDist (e8ClassPoint c.val) y))
  rintro r ⟨y, hy, rfl⟩
  exact e8HalfRootSum_distance_lower (by simpa only [binary_val_cast] using c.property.1)
    (by simpa only [binary_val_cast] using c.property.2) hy

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.card_e8HoleIndex
#print axioms PaperVerification.ColdSpots.e8ClassPoint_deep
