module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.Tactic.Abel
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import paper_verification.lattice003
public import paper_verification.lattice004
public import paper_verification.lattice005
public import paper_verification.lattice006

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.E8BinaryClasses
section Source_E8BinaryClasses

-- original header: module

-- original header: public import PaperVerification.E8IntegralBasis
-- original header: public import PaperVerification.BWCode
-- original header: public import PaperVerification.LatticeTranslationClasses
-- original header: public import Mathlib.Algebra.CharP.Two
-- original header: public import Mathlib.Data.Fintype.BigOperators
-- original header: public import Mathlib.Logic.Equiv.Prod
-- original header: public import Mathlib.Tactic.Abel


-- original header: @[expose] public section
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
end
end Source_E8BinaryClasses
-- END ORIGINAL PaperVerification.E8BinaryClasses


-- BEGIN ORIGINAL PaperVerification.E8TranslationClasses
section Source_E8TranslationClasses

-- original header: module

-- original header: public import PaperVerification.E8BinaryClasses
-- original header: public import PaperVerification.BWEligibility


-- original header: @[expose] public section
/-! # The 135 actual E8 deep-hole classes

Every real deep hole doubles to an E8 point.  Its coordinates in the explicit
integral root basis determine a nonzero isotropic binary vector.  Conversely
every such vector is a deepest half-lattice point.  This identifies the actual
translation quotient, rather than just counting a finite surrogate.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem e8_deep_double_mem {x : Fin 8 → ℝ} (hx : IsDeepHole (dPlusSet 8) x) :
    (fun i => 2 * x i) ∈ dPlusSet 8 := by
  rcases (isDeepHole_E8_iff x).mp hx with ⟨hr, hp⟩ | ⟨hr, hp⟩ | hb | ⟨hr, hp, hq⟩
  · refine ⟨fun i => 2 * roundedInt x i, ?_, Or.inl ?_⟩
    · rw [← Finset.mul_sum]
      exact even_two.mul_right _
    · funext i
      have hi : x i = (roundedInt x i : ℝ) := sub_eq_zero.mp (abs_eq_zero.mp (hr i))
      simp [intVec, hi]
  · refine ⟨fun i => 2 * halfRoundedInt x i + 1, ?_, Or.inl ?_⟩
    · have he : Even (2 * (∑ i, halfRoundedInt x i) + 8) :=
        (even_two.mul_right _).add (by decide)
      simpa [Finset.sum_add_distrib, ← Finset.mul_sum] using he
    · funext i
      have hi := abs_sub_halfRoundedInt x i
      rw [hr i, sub_self] at hi
      have he : x i = (halfRoundedInt x i : ℝ) + 1 / 2 := sub_eq_zero.mp (abs_eq_zero.mp hi)
      simp [intVec, he]
      ring
  · have hgrid := (balancedHalfGrid_iff_paperHalfGrid (by decide : Even 8) x).mp hb
    obtain ⟨m, c, rfl⟩ := halfGrid_integer_halfWord hgrid.1
    have hc4 : binaryWeight c = 4 := by
      have hcount := hgrid.2
      norm_num [nonintegerCount_integer_halfWord] at hcount
      exact hcount
    refine ⟨fun i => 2 * m i + (c i).val, ?_, Or.inl ?_⟩
    · have he : Even (2 * (∑ i, m i) + 4) := (even_two.mul_right _).add (by decide)
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum,
        sum_binary_val, hc4, Nat.cast_ofNat] using he
    · funext i
      simp only [Pi.add_apply, intVec, halfWord, Int.cast_add, Int.cast_mul,
        Int.cast_ofNat, Int.cast_natCast]
      ring
  · refine ⟨roundedInt x + halfRoundedInt x, ?_, Or.inr ?_⟩
    · simpa only [Pi.add_apply, Finset.sum_add_distrib] using
        (Int.not_even_iff_odd.mp hp).add_odd (Int.not_even_iff_odd.mp hq)
    · funext i
      have hri := hr i
      unfold foldedRadius at hri
      by_cases hs : 0 ≤ x i - (roundedInt x i : ℝ)
      · rw [abs_of_nonneg hs] at hri
        simp only [Pi.add_apply, halfRoundedInt, if_pos hs, add_zero, Int.cast_add]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hs)] at hri
        simp only [Pi.add_apply, halfRoundedInt, if_neg hs, Int.cast_add,
          Int.cast_neg, Int.cast_one]
        linarith

theorem e8_halfRoot_coordinates_of_deep {x : Fin 8 → ℝ} (hx : IsDeepHole (dPlusSet 8) x) :
    ∃ t : Fin 8 → ℤ, x = e8HalfRootSum t := by
  obtain ⟨t, ht⟩ := (e8_mem_iff_integer_root_coordinates _).mp (e8_deep_double_mem hx)
  refine ⟨t, ?_⟩
  have he := e8HalfRootSum_double t
  funext i
  have h₁ := congrFun ht i
  have h₂ := congrFun he i
  linarith

theorem e8_deep_halfRoot_binary {t : Fin 8 → ℤ} (hx : IsDeepHole (dPlusSet 8) (e8HalfRootSum t)) :
    e8BinaryQ (fun i => (t i : Binary)) = 0 ∧ (fun i => (t i : Binary)) ≠ 0 := by
  have hdepth : squaredDepth (dPlusSet 8) (e8HalfRootSum t) = 1 :=
    (squaredDepth_E8_eq_one_iff _).mpr ((isDeepHole_E8_iff _).mp hx)
  constructor
  · obtain ⟨y, hy, hdist⟩ := exists_nearest_dPlus (by decide : 0 < 8) (e8HalfRootSum t)
    obtain ⟨k, rfl⟩ := (e8_mem_iff_integer_root_coordinates y).mp hy
    let u : Fin 8 → ℤ := t - fun i => 2 * k i
    have hd : sqDist (e8HalfRootSum t) (e8RootSum (fun i => (k i : ℝ))) =
        (e8IntegralQ u : ℝ) / 2 := by
      rw [← e8HalfRootSum_two k, ← sqDist_sub_zero, ← e8HalfRootSum_sub, e8HalfRootSum_norm]
    have hQ : e8IntegralQ u = 2 := by
      rw [hd, hdepth] at hdist
      exact_mod_cast (show (e8IntegralQ u : ℝ) = 2 by linarith)
    have hu : (fun i => (u i : Binary)) = fun i => (t i : Binary) := by
      funext i
      simp [u]
    have hcast := congrArg (fun z : ℤ => (z : Binary)) hQ
    rw [e8IntegralQ_cast, hu] at hcast
    simpa using hcast
  · intro hzero
    have hmem : e8HalfRootSum t ∈ dPlusSet 8 := by
      apply (e8HalfRootSum_mem_iff t).mpr
      intro i
      apply ZMod.intCast_eq_zero_iff_even.mp
      exact congrFun hzero i
    have hz := squaredDepth_zero_of_mem hmem
    linarith

def e8DeepClassMap (c : E8HoleIndex) : DeepTranslationClasses (dPlusAddSubgroup 8 (by decide)) :=
  ⟨(e8ClassPoint c.val : (Fin 8 → ℝ) ⧸ dPlusAddSubgroup 8 (by decide)),
    e8ClassPoint c.val, e8ClassPoint_deep c, rfl⟩

theorem e8DeepClassMap_bijective : Function.Bijective e8DeepClassMap := by
  constructor
  · intro c d h
    apply Subtype.ext
    apply (e8ClassPoint_sub_mem_iff c.val d.val).mp
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C, x, hx, hC⟩
    obtain ⟨t, rfl⟩ := e8_halfRoot_coordinates_of_deep hx
    let c : E8HoleIndex := ⟨fun i => (t i : Binary), e8_deep_halfRoot_binary hx⟩
    refine ⟨c, Subtype.ext ?_⟩
    exact (QuotientAddGroup.eq_iff_sub_mem.mpr (e8HalfRootSum_class t)).symm.trans hC

def e8DeepClassEquiv : E8HoleIndex ≃ DeepTranslationClasses (dPlusAddSubgroup 8 (by decide)) :=
  Equiv.ofBijective e8DeepClassMap e8DeepClassMap_bijective

theorem e8_deep_translation_class_count :
    Nat.card (DeepTranslationClasses (dPlusAddSubgroup 8 (by decide))) = 135 := by
  rw [← Nat.card_congr e8DeepClassEquiv, Nat.card_eq_fintype_card, card_e8HoleIndex]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.e8_deep_translation_class_count
end
end Source_E8TranslationClasses
-- END ORIGINAL PaperVerification.E8TranslationClasses


-- BEGIN ORIGINAL PaperVerification.E7TranslationGeometry
section Source_E7TranslationGeometry

-- original header: module

-- original header: public import PaperVerification.E8TranslationClasses
-- original header: public import PaperVerification.E7Transfer


-- original header: @[expose] public section
/-! # Actual projection classes in E7*

The only extra identification of half-E8 classes under orthogonal projection is
addition of the binary class of the projection root.  This is proved using the
integral E8 basis and the exact kernel of the coordinate projection.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem project8_zero : project8 0 = 0 := by
  apply Subtype.ext
  funext i
  simp [project8]

theorem project8_add (x y : Fin 8 → ℝ) : project8 (x + y) = project8 x + project8 y := by
  apply Subtype.ext
  funext i
  change (project8 (x + y)).val i = (project8 x).val i + (project8 y).val i
  simp only [project8_apply, Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem project8_sub (x y : Fin 8 → ℝ) : project8 (x - y) = project8 x - project8 y := by
  apply Subtype.ext
  funext i
  change (project8 (x - y)).val i = (project8 x).val i - (project8 y).val i
  simp only [project8_apply, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

theorem project8_eq_zero_iff_constant (x : Fin 8 → ℝ) :
    project8 x = 0 ↔ ∃ a : ℝ, x = fun _ => a := by
  constructor
  · intro h
    refine ⟨(∑ i, x i) / 8, ?_⟩
    funext i
    have hi := congrArg (fun y : zeroSumSpace => y i) h
    change x i - (∑ j, x j) / 8 = 0 at hi
    linarith
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    funext i
    norm_num [project8_apply]

def project8AddHom : (Fin 8 → ℝ) →+ zeroSumSpace where
  toFun := project8
  map_zero' := project8_zero
  map_add' := project8_add

def e7ProjectedAddSubgroup : AddSubgroup zeroSumSpace :=
  (dPlusAddSubgroup 8 (by decide)).map project8AddHom

theorem e7ProjectedAddSubgroup_coe : (e7ProjectedAddSubgroup : Set zeroSumSpace) = e7ProjectedSet := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact project8_mem_e7Projected hx
  · rintro ⟨z, hz, rfl⟩
    exact ⟨intVec z, ⟨z, hz, Or.inl rfl⟩, rfl⟩

theorem e7SquaredDepth_add {g : zeroSumSpace} (hg : g ∈ e7ProjectedSet) (x : zeroSumSpace) :
    e7SquaredDepth (x + g) = e7SquaredDepth x := by
  have hgin : g ∈ e7ProjectedAddSubgroup := by
    change g ∈ (e7ProjectedAddSubgroup : Set zeroSumSpace)
    rwa [e7ProjectedAddSubgroup_coe]
  unfold e7SquaredDepth
  congr 1
  ext r
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hmem : y - g ∈ e7ProjectedSet := by
      rw [← e7ProjectedAddSubgroup_coe] at hy ⊢
      exact e7ProjectedAddSubgroup.sub_mem hy hgin
    refine ⟨y - g, hmem, ?_⟩
    exact (sqDist_add_left x.val y.val g.val).symm
  · rintro ⟨y, hy, rfl⟩
    have hmem : y + g ∈ e7ProjectedSet := by
      rw [← e7ProjectedAddSubgroup_coe] at hy ⊢
      exact e7ProjectedAddSubgroup.add_mem hy hgin
    refine ⟨y + g, hmem, ?_⟩
    exact sqDist_add_add x.val y.val g.val

theorem isE7DeepHole_add_iff {g : zeroSumSpace} (hg : g ∈ e7ProjectedSet) (x : zeroSumSpace) :
    IsE7DeepHole (x + g) ↔ IsE7DeepHole x := by
  rw [isE7DeepHole_iff_depth, isE7DeepHole_iff_depth, e7SquaredDepth_add hg]

theorem e8RootSum_halfCoordinates :
    e8RootSum (fun i => (e8HalfCoordinates i : ℝ)) = fun _ => 1 / 2 := by
  ext i
  fin_cases i <;> norm_num [e8RootSum, e8SimpleRoot, e8HalfCoordinates, Fin.sum_univ_succ]

theorem e8HalfRootSum_halfCoordinates : e8HalfRootSum e8HalfCoordinates = fun _ => 1 / 4 := by
  ext i
  fin_cases i <;> norm_num [e8HalfRootSum, e8RootSum, e8SimpleRoot, e8HalfCoordinates, Fin.sum_univ_succ]

theorem e8_constant_half_integer {a : ℝ} (ha : (fun _ : Fin 8 => a) ∈ dPlusSet 8) :
    ∃ m : ℤ, a = (m : ℝ) / 2 := by
  rcases ha with ⟨z, hz, he | he⟩
  · have h := congrFun he 0
    refine ⟨2 * z 0, ?_⟩
    change a = (z 0 : ℝ) at h
    push_cast
    linarith
  · have h := congrFun he 0
    refine ⟨2 * z 0 + 1, ?_⟩
    push_cast
    linarith

theorem e7Projected_halfRoot_difference_iff (t u : Fin 8 → ℤ) :
    project8 (e8HalfRootSum t) - project8 (e8HalfRootSum u) ∈ e7ProjectedSet ↔
      (fun i => (t i : Binary)) = (fun i => (u i : Binary)) ∨
        (fun i => (t i : Binary)) = (fun i => (u i : Binary)) + e8BinaryRoot := by
  constructor
  · rintro ⟨z, hz, hproj⟩
    obtain ⟨k, hk⟩ := (e8_mem_iff_integer_root_coordinates (intVec z)).mp
      (show intVec z ∈ dPlusSet 8 from ⟨z, hz, Or.inl rfl⟩)
    let w : Fin 8 → ℤ := t - u - fun i => 2 * k i
    have hhalf : e8HalfRootSum w = e8HalfRootSum t - e8HalfRootSum u - intVec z := by
      rw [e8HalfRootSum_sub, e8HalfRootSum_sub, e8HalfRootSum_two, ← hk]
    have hzero : project8 (e8HalfRootSum w) = 0 := by
      rw [hhalf, project8_sub, project8_sub, hproj, sub_self]
    obtain ⟨a, ha⟩ := (project8_eq_zero_iff_constant _).mp hzero
    have hroot : e8RootSum (fun i => (w i : ℝ)) = fun _ => 2 * a := by
      rw [← e8HalfRootSum_double, ha]
    have hmem : (fun _ : Fin 8 => 2 * a) ∈ dPlusSet 8 := hroot ▸ e8RootSum_int_mem w
    obtain ⟨m, hm⟩ := e8_constant_half_integer hmem
    have hmr : e8RootSum (fun i => ((m * e8HalfCoordinates i : ℤ) : ℝ)) = fun _ => (m : ℝ) / 2 := by
      have he : (fun i => ((m * e8HalfCoordinates i : ℤ) : ℝ)) =
          (m : ℝ) • (fun i => (e8HalfCoordinates i : ℝ)) := by funext i; simp
      rw [he, e8RootSum_smul, e8RootSum_halfCoordinates]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hw : ∀ i, w i = m * e8HalfCoordinates i := by
      have he := e8RootSum_injective (hroot.trans (by rw [hm]; exact hmr.symm))
      intro i
      exact_mod_cast congrFun he i
    have hcast (i : Fin 8) : (t i : Binary) - (u i : Binary) = (m : Binary) * e8BinaryRoot i := by
      have h := congrArg (fun v : ℤ => (v : Binary)) (hw i)
      simpa [w, e8BinaryRoot] using h
    rcases binary_eq_zero_or_one (m : Binary) with hm0 | hm1
    · left
      funext i
      have h := hcast i
      simpa only [hm0, zero_mul, sub_eq_zero] using h
    · right
      funext i
      have h := hcast i
      rw [hm1, one_mul] at h
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  · rintro (h | h)
    · rw [← project8_sub]
      exact project8_mem_e7Projected ((e8HalfRootSum_sub_mem_iff t u).mpr h)
    · let w : Fin 8 → ℤ := t - u - e8HalfCoordinates
      have hw : e8HalfRootSum w ∈ dPlusSet 8 := by
        apply (e8HalfRootSum_mem_iff w).mpr
        intro i
        apply ZMod.intCast_eq_zero_iff_even.mp
        have hi := congrFun h i
        change (t i : Binary) = (u i : Binary) + e8BinaryRoot i at hi
        simp only [w, Pi.sub_apply, Int.cast_sub, hi, e8BinaryRoot]
        ring
      have hp := project8_mem_e7Projected hw
      have he : project8 (e8HalfRootSum w) = project8 (e8HalfRootSum t) - project8 (e8HalfRootSum u) := by
        rw [e8HalfRootSum_sub, e8HalfRootSum_sub, e8HalfRootSum_halfCoordinates,
          project8_sub, project8_sub]
        have hz : project8 (fun _ : Fin 8 => (1 / 4 : ℝ)) = 0 :=
          (project8_eq_zero_iff_constant _).mpr ⟨1 / 4, rfl⟩
        rw [hz, sub_zero]
      rwa [he] at hp

def e8HalfSumInt (t : Fin 8 → ℤ) : ℤ :=
  e8IntegralQ (t + e8HalfCoordinates) - e8IntegralQ t - e8IntegralQ e8HalfCoordinates

theorem e8HalfRootSum_sum (t : Fin 8 → ℤ) :
    (∑ i, e8HalfRootSum t i) = (e8HalfSumInt t : ℝ) := by
  simp [e8HalfSumInt, e8HalfRootSum, e8IntegralQ, e8RootSum, e8SimpleRoot,
    e8HalfCoordinates, Fin.sum_univ_succ]
  ring

theorem e8HalfSumInt_cast (t : Fin 8 → ℤ) :
    (e8HalfSumInt t : Binary) = e8BinaryPolar (fun i => (t i : Binary)) e8BinaryRoot := by
  simp only [e8HalfSumInt, Int.cast_sub, e8IntegralQ_cast, e8BinaryPolar, e8BinaryRoot,
    Pi.add_apply, Int.cast_add]
  rfl

theorem e7Slice_project8_of_sum_one {x : Fin 8 → ℝ} (hx : (∑ i, x i) = 1) :
    e7Slice (project8 x) = x := by
  funext i
  simp only [e7Slice, project8_apply, hx]
  ring

theorem e7_project_deep_of_odd_sum {x : Fin 8 → ℝ} (hx : IsDeepHole (dPlusSet 8) x)
    {s : ℤ} (hs : (∑ i, x i) = (s : ℝ)) (hodd : Odd s) : IsE7DeepHole (project8 x) := by
  obtain ⟨k, hk⟩ := hodd
  let z : Fin 8 → ℤ := fun i => if i = 0 then 2 * k else 0
  have hzsum : (∑ i, z i) = 2 * k := by simp [z]
  have hz : intVec z ∈ dPlusSet 8 := ⟨z, by rw [hzsum]; exact even_two.mul_right k, Or.inl rfl⟩
  let y := x - intVec z
  have hysum : (∑ i, y i) = 1 := by
    simp only [y, Pi.sub_apply, Finset.sum_sub_distrib, intVec, ← Int.cast_sum, hzsum, hs, hk]
    push_cast
    ring
  have hy : IsDeepHole (dPlusSet 8) y := by
    rw [isDeepHole_dPlus_iff_depth (by decide : 8 ≤ 8) (by decide : Even 8)]
    change squaredDepth (dPlusSet 8) (x - intVec z) = _
    have htrans := squaredDepth_sub_of_subgroup (dPlusAddSubgroup 8 (by decide)) x (intVec z) hz
    change squaredDepth (dPlusSet 8) (x - intVec z) = squaredDepth (dPlusSet 8) x at htrans
    rw [htrans]
    exact (isDeepHole_dPlus_iff_depth (by decide : 8 ≤ 8) (by decide : Even 8) x).mp hx
  have hproj : IsE7DeepHole (project8 y) := by
    apply (isDeepHole_slice_iff _).mp
    rw [e7Slice_project8_of_sum_one hysum]
    exact hy
  have h := (isE7DeepHole_add_iff (project8_mem_e7Projected hz) (project8 y)).mpr hproj
  have he : project8 y + project8 (intVec z) = project8 x := by
    rw [← project8_add]
    congr 1
    dsimp [y]
    abel
  rwa [he] at h

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.e7Projected_halfRoot_difference_iff
end
end Source_E7TranslationGeometry
-- END ORIGINAL PaperVerification.E7TranslationGeometry


-- BEGIN ORIGINAL PaperVerification.E7TranslationClasses
section Source_E7TranslationClasses

-- original header: module

-- original header: public import PaperVerification.E7TranslationGeometry


-- original header: @[expose] public section
/-! # The 36 translation classes of E7* deep holes

Among the 135 nonzero isotropic E8 classes, exactly 72 meet the affine slice.
Orthogonal projection pairs each such class with its translate by the projection
root.  The resulting 36 classes are identified with the actual quotient of all
real E7* deep holes.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

abbrev E7SliceIndex := {c : E8HoleIndex // e8BinaryPolar c.val e8BinaryRoot = 1}
abbrev E7HoleIndex := {c : E8HoleIndex // e8BinaryPolar c.val e8BinaryRoot = 1 ∧ c.val 0 = 0}

theorem e7Slice_binary_representatives : ∀ c : E7SliceIndex,
    ∃! d : E7HoleIndex, c.val.val = d.val.val ∨ c.val.val = d.val.val + e8BinaryRoot := by
  intro c
  have hroot0 : e8BinaryRoot 0 = 1 := by decide
  have hdouble (a : Binary) : a + a = 0 := by
    rw [← two_mul, binary_two_eq_zero, zero_mul]
  have h11 : (1 : Binary) + 1 = 0 := hdouble 1
  have hrr : e8BinaryRoot + e8BinaryRoot = 0 := by
    funext i
    exact hdouble (e8BinaryRoot i)
  have hshift : (c.val.val + e8BinaryRoot) + e8BinaryRoot = c.val.val := by
    rw [add_assoc, hrr, add_zero]
  rcases binary_eq_zero_or_one (c.val.val 0) with h0 | h1
  · let d : E7HoleIndex := ⟨c.val, c.property, h0⟩
    refine ⟨d, Or.inl rfl, ?_⟩
    intro e he
    rcases he with he | he
    · exact Subtype.ext (Subtype.ext he.symm)
    · have hi := congrFun he 0
      simp only [Pi.add_apply, h0, e.property.2, hroot0, zero_add] at hi
      exact (zero_ne_one hi).elim
  · have hq : e8BinaryQ (c.val.val + e8BinaryRoot) = 0 := by
      have hp := c.property
      change e8BinaryQ (c.val.val + e8BinaryRoot) -
        e8BinaryQ c.val.val - e8BinaryQ e8BinaryRoot = 1 at hp
      rw [c.val.property.1, e8BinaryRoot_q, sub_zero] at hp
      have ha := congrArg (fun a : Binary => a + 1) hp
      simpa only [sub_add_cancel, h11] using ha
    have hp : e8BinaryPolar (c.val.val + e8BinaryRoot) e8BinaryRoot = 1 := by
      unfold e8BinaryPolar
      rw [hshift, hq, c.val.property.1, e8BinaryRoot_q, sub_zero]
      exact sub_eq_iff_eq_add.mpr h11.symm
    have hne : c.val.val + e8BinaryRoot ≠ 0 := by
      intro hz
      have hc : c.val.val = e8BinaryRoot := by
        calc
          c.val.val = (c.val.val + e8BinaryRoot) + e8BinaryRoot := hshift.symm
          _ = e8BinaryRoot := by rw [hz, zero_add]
      have hqc := c.val.property.1
      rw [hc, e8BinaryRoot_q] at hqc
      exact one_ne_zero hqc
    have hz0 : (c.val.val + e8BinaryRoot) 0 = 0 := by
      change c.val.val 0 + e8BinaryRoot 0 = 0
      rw [h1, hroot0]
      exact h11
    let d : E7HoleIndex := ⟨⟨c.val.val + e8BinaryRoot, hq, hne⟩, hp, hz0⟩
    have hd : c.val.val = d.val.val + e8BinaryRoot := hshift.symm
    refine ⟨d, Or.inr hd, ?_⟩
    intro e he
    rcases he with he | he
    · have hi := congrFun he 0
      rw [h1, e.property.2] at hi
      exact (one_ne_zero hi).elim
    · exact Subtype.ext (Subtype.ext (add_right_cancel (he.symm.trans hd)))

theorem e8BinaryRoot_zero : e8BinaryRoot 0 = 1 := by decide


/-- Translation by the projection root preserves the actual isotropic affine slice. -/
def e7Slice_addRoot (c : E7SliceIndex) : E7SliceIndex := by
  have hdouble (a : Binary) : a + a = 0 := by
    rw [← two_mul, binary_two_eq_zero, zero_mul]
  have h11 : (1 : Binary) + 1 = 0 := hdouble 1
  have hrr : e8BinaryRoot + e8BinaryRoot = 0 := by
    funext i
    exact hdouble (e8BinaryRoot i)
  have hshift : (c.val.val + e8BinaryRoot) + e8BinaryRoot = c.val.val := by
    rw [add_assoc, hrr, add_zero]
  have hq : e8BinaryQ (c.val.val + e8BinaryRoot) = 0 := by
    have hp := c.property
    change e8BinaryQ (c.val.val + e8BinaryRoot) -
      e8BinaryQ c.val.val - e8BinaryQ e8BinaryRoot = 1 at hp
    rw [c.val.property.1, e8BinaryRoot_q, sub_zero] at hp
    have ha := congrArg (fun a : Binary => a + 1) hp
    simpa only [sub_add_cancel, h11] using ha
  have hp : e8BinaryPolar (c.val.val + e8BinaryRoot) e8BinaryRoot = 1 := by
    unfold e8BinaryPolar
    rw [hshift, hq, c.val.property.1, e8BinaryRoot_q, sub_zero]
    exact sub_eq_iff_eq_add.mpr h11.symm
  have hne : c.val.val + e8BinaryRoot ≠ 0 := by
    intro hz
    have hc : c.val.val = e8BinaryRoot := by
      calc
        c.val.val = (c.val.val + e8BinaryRoot) + e8BinaryRoot := hshift.symm
        _ = e8BinaryRoot := by rw [hz, zero_add]
    have hqc := c.val.property.1
    rw [hc, e8BinaryRoot_q] at hqc
    exact one_ne_zero hqc
  exact ⟨⟨c.val.val + e8BinaryRoot, hq, hne⟩, hp⟩

@[simp] theorem e7Slice_addRoot_val (c : E7SliceIndex) :
    (e7Slice_addRoot c).val.val = c.val.val + e8BinaryRoot := rfl

/-- The second coordinate records which of the two slice points is chosen. -/
def e7SliceJoin (p : E7HoleIndex × Binary) : E7SliceIndex :=
  if p.2 = 0 then ⟨p.1.val, p.1.property.1⟩
  else e7Slice_addRoot ⟨p.1.val, p.1.property.1⟩

theorem e7SliceJoin_relation (p : E7HoleIndex × Binary) :
    (e7SliceJoin p).val.val = p.1.val.val ∨
      (e7SliceJoin p).val.val = p.1.val.val + e8BinaryRoot := by
  unfold e7SliceJoin
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem e7SliceJoin_bit (p : E7HoleIndex × Binary) :
    (e7SliceJoin p).val.val 0 = p.2 := by
  rcases binary_eq_zero_or_one p.2 with h0 | h1
  · rw [e7SliceJoin, if_pos h0]
    exact p.1.property.2.trans h0.symm
  · have hn : p.2 ≠ 0 := by rw [h1]; exact one_ne_zero
    rw [e7SliceJoin, if_neg hn]
    change (p.1.val.val + e8BinaryRoot) 0 = p.2
    simp only [Pi.add_apply, p.1.property.2, e8BinaryRoot_zero, zero_add]
    exact h1.symm

theorem e7SliceJoin_zero (d : E7HoleIndex) :
    (e7SliceJoin (d, 0)).val.val = d.val.val := by
  rw [e7SliceJoin, if_pos rfl]

theorem e7SliceJoin_one (d : E7HoleIndex) :
    (e7SliceJoin (d, 1)).val.val = d.val.val + e8BinaryRoot := by
  rw [e7SliceJoin, if_neg one_ne_zero, e7Slice_addRoot_val]

theorem e7SliceJoin_bijective : Function.Bijective e7SliceJoin := by
  constructor
  · intro p q hpq
    have hbit : p.2 = q.2 :=
      (e7SliceJoin_bit p).symm.trans
        ((congrArg (fun c : E7SliceIndex => c.val.val 0) hpq).trans (e7SliceJoin_bit q))
    have hp := e7SliceJoin_relation p
    have hq : (e7SliceJoin p).val.val = q.1.val.val ∨
        (e7SliceJoin p).val.val = q.1.val.val + e8BinaryRoot := by
      rw [hpq]
      exact e7SliceJoin_relation q
    obtain ⟨d, hd, huniq⟩ := e7Slice_binary_representatives (e7SliceJoin p)
    exact Prod.ext ((huniq p.1 hp).trans (huniq q.1 hq).symm) hbit
  · intro c
    obtain ⟨d, hd, _⟩ := e7Slice_binary_representatives c
    rcases hd with hd | hd
    · refine ⟨(d, 0), Subtype.ext (Subtype.ext ?_)⟩
      rw [e7SliceJoin_zero]
      exact hd.symm
    · refine ⟨(d, 1), Subtype.ext (Subtype.ext ?_)⟩
      rw [e7SliceJoin_one]
      exact hd.symm

/-- Exact two-point fibers, with the actual root translate distinguished by bit zero. -/
def e7SliceProductEquiv : E7SliceIndex ≃ E7HoleIndex × Binary :=
  (Equiv.ofBijective e7SliceJoin e7SliceJoin_bijective).symm

theorem card_e7HoleIndex : Fintype.card E7HoleIndex = 36 := by
  have h := Fintype.card_congr e7SliceProductEquiv
  rw [card_e8HalfSliceIndex, Fintype.card_prod] at h
  have hbinary : Fintype.card Binary = 2 := by decide
  rw [hbinary] at h
  omega

def e7ClassPoint (c : E7HoleIndex) : zeroSumSpace := project8 (e8ClassPoint c.val.val)

theorem e7ClassPoint_deep (c : E7HoleIndex) : IsE7DeepHole (e7ClassPoint c) := by
  let t : Fin 8 → ℤ := fun i => ((c.val.val i).val : ℤ)
  have hodd : Odd (e8HalfSumInt t) := by
    apply ZMod.intCast_eq_one_iff_odd.mp
    rw [e8HalfSumInt_cast]
    simpa only [t, binary_val_cast] using c.property.1
  exact e7_project_deep_of_odd_sum (e8ClassPoint_deep c.val) (e8HalfRootSum_sum t) hodd

theorem e7ClassPoint_distinct (c d : E7HoleIndex) :
    e7ClassPoint c - e7ClassPoint d ∈ e7ProjectedSet ↔ c = d := by
  rw [e7ClassPoint, e7ClassPoint, e8ClassPoint, e8ClassPoint, e7Projected_halfRoot_difference_iff]
  simp only [binary_val_cast]
  constructor
  · rintro (h | h)
    · exact Subtype.ext (Subtype.ext h)
    · have hi := congrFun h 0
      simp only [Pi.add_apply, c.property.2, d.property.2, e8BinaryRoot_zero, zero_add] at hi
      exact (zero_ne_one hi).elim
  · rintro rfl
    exact Or.inl rfl

theorem project8_e7Slice (x : zeroSumSpace) : project8 (e7Slice x) = x := by
  change project8 (fun i ↦ x.val i + 1 / 8) = x
  rw [project8_add_constant, project8_coe]

theorem e7DeepHole_coset_coverage {x : zeroSumSpace} (hx : IsE7DeepHole x) :
    ∃ c : E7HoleIndex, x - e7ClassPoint c ∈ e7ProjectedSet := by
  have hslice := (isDeepHole_slice_iff x).mpr hx
  obtain ⟨t, ht⟩ := e8_halfRoot_coordinates_of_deep hslice
  have htdeep : IsDeepHole (dPlusSet 8) (e8HalfRootSum t) := ht ▸ hslice
  have hs : (∑ i, e8HalfRootSum t i) = 1 := by
    rw [← ht]
    simp [e7Slice, Finset.sum_add_distrib, zeroSumSpace_sum]
  have hint : e8HalfSumInt t = 1 := by
    rw [e8HalfRootSum_sum] at hs
    exact_mod_cast hs
  have hpolar : e8BinaryPolar (fun i => (t i : Binary)) e8BinaryRoot = 1 := by
    rw [← e8HalfSumInt_cast, hint]
    norm_num
  let a : E7SliceIndex := ⟨⟨fun i => (t i : Binary), e8_deep_halfRoot_binary htdeep⟩, hpolar⟩
  obtain ⟨c, hc, _⟩ := e7Slice_binary_representatives a
  refine ⟨c, ?_⟩
  have hproj : x = project8 (e8HalfRootSum t) := by rw [← ht, project8_e7Slice]
  rw [hproj, e7ClassPoint, e8ClassPoint, e7Projected_halfRoot_difference_iff]
  simpa only [a, binary_val_cast] using hc

def E7DeepTranslationClasses :=
  {C : zeroSumSpace ⧸ e7ProjectedAddSubgroup // ∃ x : zeroSumSpace, IsE7DeepHole x ∧
    (x : zeroSumSpace ⧸ e7ProjectedAddSubgroup) = C}

def e7DeepClassMap (c : E7HoleIndex) : E7DeepTranslationClasses :=
  ⟨(e7ClassPoint c : zeroSumSpace ⧸ e7ProjectedAddSubgroup), e7ClassPoint c, e7ClassPoint_deep c, rfl⟩

theorem e7DeepClassMap_bijective : Function.Bijective e7DeepClassMap := by
  constructor
  · intro c d h
    apply (e7ClassPoint_distinct c d).mp
    rw [← e7ProjectedAddSubgroup_coe]
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C, x, hx, hC⟩
    obtain ⟨c, hc⟩ := e7DeepHole_coset_coverage hx
    refine ⟨c, Subtype.ext ?_⟩
    rw [← e7ProjectedAddSubgroup_coe] at hc
    exact (QuotientAddGroup.eq_iff_sub_mem.mpr hc).symm.trans hC

def e7DeepClassEquiv : E7HoleIndex ≃ E7DeepTranslationClasses :=
  Equiv.ofBijective e7DeepClassMap e7DeepClassMap_bijective

/-- Exactly 36 classes in the quotient by the actual E7* lattice. -/
theorem e7_dual_deep_translation_class_count : Nat.card E7DeepTranslationClasses = 36 := by
  rw [← Nat.card_congr e7DeepClassEquiv, Nat.card_eq_fintype_card, card_e7HoleIndex]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.e7_dual_deep_translation_class_count
end
end Source_E7TranslationClasses
-- END ORIGINAL PaperVerification.E7TranslationClasses


-- BEGIN ORIGINAL PaperVerification.E7PaperRepresentatives
section Source_E7PaperRepresentatives

-- original header: module

-- original header: public import PaperVerification.E7TranslationClasses
-- original header: public import Mathlib.Data.Finset.Powerset
-- original header: public import Mathlib.Data.Fintype.Option
-- original header: public import Mathlib.Data.Fintype.EquivFin

-- original header: @[expose] public section

/-!
# The literal E₇* representatives in equation (26)

The arbitrary-real classification and the genuine translation quotient
are already proved. This module identifies those classes with the
displayed vectors x₀ and x₀+y_S, |S|=4. The actual E8 coordinate cosets
detect the only repetitions, and canonical subsets account for all 36 classes.
The completeness statement quantifies over the entire real hyperplane.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

abbrev E7FourSubset := {S : Finset (Fin 8) // S.card=4}
abbrev E7PaperIndex := Option E7FourSubset

def e7PaperAmbient : E7PaperIndex→Fin 8→ℝ
  | none => e8Axis
  | some S => e8Axis+(fun i=>if i∈S.val then 1/2 else 0)

def e7PaperDouble : E7PaperIndex→Fin 8→ℤ
  | none => fun i=>if i=0 then 2 else 0
  | some S => fun i=>(if i=0 then 2 else 0)+(if i∈S.val then 1 else 0)

def e7PaperHalfSum : E7PaperIndex→ℤ
  | none => 1
  | some _ => 3

def e7PaperCoordinates (p : E7PaperIndex) : Fin 8→ℤ :=
  e8IntCoordinates (e7PaperDouble p) (e7PaperHalfSum p)

def e7PaperBinary (p : E7PaperIndex) : BinaryWord8 :=
  fun i=>(e7PaperCoordinates p i : Binary)

def e7PaperPoint (p : E7PaperIndex) : zeroSumSpace := project8 (e7PaperAmbient p)

/-- This is the actual vector (1/2)1_S-(1/4)1 in the real hyperplane. -/
def e7PaperShift (S : E7FourSubset) : zeroSumSpace :=
  project8 (fun i=>if i∈S.val then 1/2 else 0)

theorem e7PaperShift_apply (S : E7FourSubset) (i : Fin 8) :
    e7PaperShift S i=(if i∈S.val then (1/2:ℝ) else 0)-1/4 := by
  have hs : (∑ j : Fin 8,if j∈S.val then (1/2:ℝ) else 0)=2 := by
    norm_num [S.property]
  simp only [e7PaperShift,project8_apply,hs]
  ring

@[simp] theorem e7PaperPoint_none : e7PaperPoint none=e7Witness := rfl

@[simp] theorem e7PaperPoint_some (S : E7FourSubset) :
    e7PaperPoint (some S)=e7Witness+e7PaperShift S :=
  project8_add _ _

theorem e7Witness_apply (i : Fin 8) :
    e7Witness i=(if i=0 then (1:ℝ) else 0)-1/8 := by
  simp only [e7Witness,project8_apply,e8Axis_sum,e8Axis,intVec]
  split_ifs <;> norm_num

theorem e7PaperDouble_sum (p : E7PaperIndex) :
    (∑ i,e7PaperDouble p i)=e7PaperHalfSum p+e7PaperHalfSum p := by
  cases p with
  | none => norm_num [e7PaperDouble,e7PaperHalfSum]
  | some S => simp [e7PaperDouble,e7PaperHalfSum,Finset.sum_add_distrib,S.property]

theorem e7PaperAmbient_double (p : E7PaperIndex) :
    (fun i=>2*e7PaperAmbient p i)=intVec (e7PaperDouble p) := by
  funext i
  cases p with
  | none => simp [e7PaperAmbient,e7PaperDouble,e8Axis,intVec]
  | some S =>
    by_cases h0 : i=0 <;> by_cases hS : i∈S.val <;>
      norm_num [e7PaperAmbient,e7PaperDouble,e8Axis,intVec,h0,hS] <;>
        split_ifs <;> norm_num

theorem e7PaperAmbient_halfRoot (p : E7PaperIndex) :
    e7PaperAmbient p=e8HalfRootSum (e7PaperCoordinates p) := by
  have hroot := e8RootSum_coordinates (intVec (e7PaperDouble p))
  rw [e8RootCoordinates_int _ _ (e7PaperDouble_sum p)] at hroot
  have hhalf := e8HalfRootSum_double (e7PaperCoordinates p)
  have hdouble := e7PaperAmbient_double p
  funext i
  have h1 := congrFun hroot i
  have h2 := congrFun hhalf i
  have h3 := congrFun hdouble i
  change e8RootSum (fun j=>(e7PaperCoordinates p j:ℝ)) i=
    intVec (e7PaperDouble p) i at h1
  change 2*e8HalfRootSum (e7PaperCoordinates p) i=
    e8RootSum (fun j=>(e7PaperCoordinates p j:ℝ)) i at h2
  linarith

/-- Every displayed binary vector already satisfies the canonical first-bit condition. -/
private theorem e7PaperBinary_zero (p : E7PaperIndex) : e7PaperBinary p 0 = 0 := by
  simp only [e7PaperBinary, e7PaperCoordinates, e8IntCoordinates,
    Matrix.cons_val_zero, Int.cast_mul, Int.cast_ofNat, binary_two_eq_zero, zero_mul]

private theorem e7PaperAmbient_sum (p : E7PaperIndex) :
    (∑ i, e7PaperAmbient p i) = (e7PaperHalfSum p : ℝ) := by
  cases p with
  | none => simpa only [e7PaperAmbient, e7PaperHalfSum, Int.cast_one] using e8Axis_sum
  | some S =>
    have hs : (∑ i : Fin 8, if i ∈ S.val then (1/2 : ℝ) else 0) = 2 := by
      norm_num [S.property]
    change (∑ i : Fin 8, (e8Axis i + (if i ∈ S.val then (1/2 : ℝ) else 0))) = 3
    rw [Finset.sum_add_distrib, e8Axis_sum, hs]
    norm_num

/-- This uses the independently established E8 geometry, before any paper-representative
coverage or projected deepness theorem. -/
private theorem e7PaperAmbient_deep (p : E7PaperIndex) :
    IsDeepHole (dPlusSet 8) (e7PaperAmbient p) := by
  cases p with
  | none => exact (isDeepHole_E8_iff _).mpr e8Axis_folded_hole
  | some S =>
    let z : Fin 8 → ℤ := fun i => if i = 0 then 1 else 0
    have hx (i : Fin 8) : e7PaperAmbient (some S) i =
        (z i : ℝ) + (if i ∈ S.val then 1/2 else 0) := by
      simp only [e7PaperAmbient, Pi.add_apply, e8Axis, intVec, z]
    have hr (i : Fin 8) : foldedRadius (e7PaperAmbient (some S)) i =
        if i ∈ S.val then 1/2 else 0 := by
      by_cases hi : i ∈ S.val
      · rw [if_pos hi]
        exact (foldedRadius_eq_half_iff _ i).mpr
          ⟨z i, by simpa only [if_pos hi] using hx i⟩
      · rw [if_neg hi]
        exact (foldedRadius_eq_zero_iff _ i).mpr
          ⟨z i, by simpa only [if_neg hi, add_zero] using hx i⟩
    apply (isDeepHole_E8_iff _).mpr
    refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
    · intro i
      by_cases hi : i ∈ S.val
      · right
        simpa only [if_pos hi] using hr i
      · left
        simpa only [if_neg hi] using hr i
    · simp only [hr]
      norm_num [S.property]

private def e7PaperClass (p : E7PaperIndex) : E7HoleIndex := by
  have hdeep := e7PaperAmbient_deep p
  rw [e7PaperAmbient_halfRoot] at hdeep
  have hbinary := e8_deep_halfRoot_binary hdeep
  have hsum := e7PaperAmbient_sum p
  rw [e7PaperAmbient_halfRoot, e8HalfRootSum_sum] at hsum
  have hint : e8HalfSumInt (e7PaperCoordinates p) = e7PaperHalfSum p := by
    exact_mod_cast hsum
  have hodd : Odd (e7PaperHalfSum p) := by
    cases p with
    | none =>
      change Odd (1 : ℤ)
      exact ⟨0, by norm_num⟩
    | some S =>
      change Odd (3 : ℤ)
      exact ⟨1, by norm_num⟩
  have hpolar : e8BinaryPolar (e7PaperBinary p) e8BinaryRoot = 1 := by
    change e8BinaryPolar (fun i => (e7PaperCoordinates p i : Binary)) e8BinaryRoot = 1
    rw [← e8HalfSumInt_cast, hint]
    exact ZMod.intCast_eq_one_iff_odd.mpr hodd
  exact ⟨⟨e7PaperBinary p, hbinary⟩, hpolar, e7PaperBinary_zero p⟩

/-- Exact identification of every displayed representative with a canonical binary class. -/
theorem e7PaperBinary_to_class : ∀ p : E7PaperIndex, ∃ c : E7HoleIndex,
    e7PaperBinary p=c.val.val ∨ e7PaperBinary p=c.val.val+e8BinaryRoot := by
  intro p
  exact ⟨e7PaperClass p, Or.inl rfl⟩

def E7PaperEquivalent : E7PaperIndex→E7PaperIndex→Prop
  | none,none => True
  | some S,some T => S.val=T.val ∨ S.val=T.valᶜ
  | _,_ => False

instance (p q : E7PaperIndex) : Decidable (E7PaperEquivalent p q) := by
  cases p <;> cases q <;> unfold E7PaperEquivalent <;> infer_instance

private def e7HalfIndicator (S : Finset (Fin 8)) : Fin 8 → ℝ :=
  fun i => if i ∈ S then 1/2 else 0

private def e7PaperSupport : E7PaperIndex → Finset (Fin 8)
  | none => ∅
  | some S => S.val

private theorem e7PaperSupport_even (p : E7PaperIndex) :
    Even (e7PaperSupport p).card := by
  cases p with
  | none => norm_num [e7PaperSupport]
  | some S => change Even S.val.card; rw [S.property]; decide

private theorem e7PaperAmbient_support (p : E7PaperIndex) :
    e7PaperAmbient p = e8Axis + e7HalfIndicator (e7PaperSupport p) := by
  cases p with
  | none =>
    funext i
    change e8Axis i = e8Axis i +
      (if i ∈ (∅ : Finset (Fin 8)) then (1/2 : ℝ) else 0)
    simp
  | some S => rfl

/-- The two actual E8 coordinate cosets detect equality or complementation of supports. -/
private theorem e7HalfIndicator_sub_mem (S T : Finset (Fin 8)) (hT : Even T.card) :
    e7HalfIndicator S - e7HalfIndicator T ∈ dPlusSet 8 ↔ S = T ∨ S = Tᶜ := by
  constructor
  · rintro ⟨z, hz, he | he⟩
    · left
      apply Finset.ext
      intro i
      constructor
      · intro hi
        by_contra hni
        have h := congrFun he i
        simp only [Pi.sub_apply, e7HalfIndicator, if_pos hi, if_neg hni,
          sub_zero, intVec] at h
        exact integer_ne_half_shift (z i) 0 (by simpa only [Int.cast_zero, zero_add] using h.symm)
      · intro hi
        by_contra hni
        have h := congrFun he i
        simp only [Pi.sub_apply, e7HalfIndicator, if_neg hni, if_pos hi,
          zero_sub, intVec] at h
        apply integer_ne_half_shift (z i) (-1)
        norm_num
        linarith
    · right
      apply Finset.ext
      intro i
      rw [Finset.mem_compl]
      constructor
      · intro hi hti
        have h := congrFun he i
        simp only [Pi.sub_apply, e7HalfIndicator, if_pos hi, if_pos hti, sub_self] at h
        exact integer_ne_half_shift 0 (z i) (by simpa only [Int.cast_zero] using h)
      · intro hti
        by_contra hi
        have h := congrFun he i
        simp only [Pi.sub_apply, e7HalfIndicator, if_neg hi, if_neg hti, sub_self] at h
        exact integer_ne_half_shift 0 (z i) (by simpa only [Int.cast_zero] using h)
  · rintro (rfl | rfl)
    · simpa only [sub_self] using zero_mem_dPlusSet 8
    · refine ⟨fun i => if i ∈ T then -1 else 0, ?_, Or.inr ?_⟩
      · have hs : (∑ i : Fin 8, if i ∈ T then (-1 : ℤ) else 0) = -(T.card : ℤ) := by
          simp
        rw [hs]
        rcases hT with ⟨k, hk⟩
        refine ⟨-(k : ℤ), ?_⟩
        rw [hk]
        push_cast
        ring
      · funext i
        by_cases hi : i ∈ T <;>
          norm_num [e7HalfIndicator, Finset.mem_compl, hi]

private theorem e7PaperSupport_relation (p q : E7PaperIndex) :
    (e7PaperSupport p = e7PaperSupport q ∨
      e7PaperSupport p = (e7PaperSupport q)ᶜ) ↔ E7PaperEquivalent p q := by
  cases p with
  | none =>
    cases q with
    | none => simp [e7PaperSupport, E7PaperEquivalent]
    | some T =>
      change ((∅ : Finset (Fin 8)) = T.val ∨ ∅ = T.valᶜ) ↔ False
      constructor
      · rintro (h | h) <;>
          have hc := congrArg Finset.card h <;>
          norm_num [Finset.card_compl, T.property] at hc
      · exact False.elim
  | some S =>
    cases q with
    | none =>
      change (S.val = ∅ ∨ S.val = (∅ : Finset (Fin 8))ᶜ) ↔ False
      constructor
      · rintro (h | h) <;>
          have hc := congrArg Finset.card h <;>
          norm_num [Finset.card_compl, S.property] at hc
      · exact False.elim
    | some T => rfl

private theorem e7PaperBinary_eq_iff (p q : E7PaperIndex) :
    e7PaperBinary p = e7PaperBinary q ↔
      e7PaperAmbient p - e7PaperAmbient q ∈ dPlusSet 8 := by
  unfold e7PaperBinary
  rw [e7PaperAmbient_halfRoot p, e7PaperAmbient_halfRoot q]
  exact (e8HalfRootSum_sub_mem_iff (e7PaperCoordinates p) (e7PaperCoordinates q)).symm

/-- The only repetitions among the 71 displayed vectors are the two
complementary representatives for each four-subset class. -/
theorem e7PaperBinary_equivalence : ∀ p q : E7PaperIndex,
    (e7PaperBinary p=e7PaperBinary q ∨
      e7PaperBinary p=e7PaperBinary q+e8BinaryRoot) ↔ E7PaperEquivalent p q := by
  intro p q
  have hn : e7PaperBinary p ≠ e7PaperBinary q + e8BinaryRoot := by
    intro h
    have hi := congrFun h 0
    simp only [Pi.add_apply, e7PaperBinary_zero, e8BinaryRoot_zero, zero_add] at hi
    exact zero_ne_one hi
  rw [or_iff_left hn, e7PaperBinary_eq_iff, e7PaperAmbient_support p,
    e7PaperAmbient_support q, add_sub_add_left_eq_sub,
    e7HalfIndicator_sub_mem _ _ (e7PaperSupport_even q), e7PaperSupport_relation]

private abbrev E7CanonicalPaperSubset :=
  {S : Finset (Fin 8) // S.card = 4 ∧ (0 : Fin 8) ∉ S}

private abbrev E7CanonicalPaperIndex := Option E7CanonicalPaperSubset

private def e7CanonicalForget : E7CanonicalPaperIndex → E7PaperIndex
  | none => none
  | some S => some ⟨S.val, S.property.1⟩

private def e7CanonicalClass (p : E7CanonicalPaperIndex) : E7HoleIndex :=
  e7PaperClass (e7CanonicalForget p)

private theorem card_e7CanonicalPaperIndex : Fintype.card E7CanonicalPaperIndex = 36 := by
  have hs : Fintype.card E7CanonicalPaperSubset =
      (((Finset.univ : Finset (Fin 8)).erase 0).powersetCard 4).card := by
    apply Fintype.card_of_subtype
    intro S
    rw [Finset.mem_powersetCard, Finset.subset_erase]
    simp only [Finset.subset_univ, true_and]
    exact and_comm
  rw [Fintype.card_option, hs, Finset.card_powersetCard]
  norm_num <;> decide

private theorem e7CanonicalClass_injective : Function.Injective e7CanonicalClass := by
  intro p q h
  have hb := congrArg (fun c : E7HoleIndex => c.val.val) h
  change e7PaperBinary (e7CanonicalForget p) = e7PaperBinary (e7CanonicalForget q) at hb
  have he := (e7PaperBinary_equivalence _ _).mp (Or.inl hb)
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some T => exact False.elim he
  | some S =>
    cases q with
    | none => exact False.elim he
    | some T =>
      change S.val = T.val ∨ S.val = T.valᶜ at he
      rcases he with he | he
      · exact congrArg some (Subtype.ext he)
      · have h0 : (0 : Fin 8) ∈ S.val := by
          rw [he]
          exact Finset.mem_compl.mpr T.property.2
        exact (S.property.2 h0).elim

/-- Canonical four-subsets avoiding zero supply 35 classes, with the first representative
supplying the remaining class. The target cardinal was proved independently from E8. -/
theorem e7_class_to_paperBinary : ∀ c : E7HoleIndex, ∃ p : E7PaperIndex,
    c.val.val=e7PaperBinary p ∨ c.val.val=e7PaperBinary p+e8BinaryRoot := by
  have hbij : Function.Bijective e7CanonicalClass :=
    (Fintype.bijective_iff_injective_and_card e7CanonicalClass).mpr
      ⟨e7CanonicalClass_injective, by rw [card_e7CanonicalPaperIndex, card_e7HoleIndex]⟩
  intro c
  obtain ⟨p, hp⟩ := hbij.2 c
  refine ⟨e7CanonicalForget p, Or.inl ?_⟩
  have hv := congrArg (fun d : E7HoleIndex => d.val.val) hp
  change e7PaperBinary (e7CanonicalForget p) = c.val.val at hv
  exact hv.symm

theorem e7PaperPoint_difference_iff (p q : E7PaperIndex) :
    e7PaperPoint p-e7PaperPoint q∈e7ProjectedSet ↔ E7PaperEquivalent p q := by
  unfold e7PaperPoint
  rw [e7PaperAmbient_halfRoot,e7PaperAmbient_halfRoot,
    e7Projected_halfRoot_difference_iff]
  exact e7PaperBinary_equivalence p q

theorem e7PaperPoint_deep (p : E7PaperIndex) : IsE7DeepHole (e7PaperPoint p) := by
  obtain ⟨c,hc⟩ := e7PaperBinary_to_class p
  have hmem : e7PaperPoint p-e7ClassPoint c∈e7ProjectedSet := by
    unfold e7PaperPoint e7ClassPoint e8ClassPoint
    rw [e7PaperAmbient_halfRoot,e7Projected_halfRoot_difference_iff]
    change e7PaperBinary p = (fun i ↦ (((c.val.val i).val : ℤ) : Binary)) ∨
      e7PaperBinary p = (fun i ↦ (((c.val.val i).val : ℤ) : Binary)) + e8BinaryRoot
    simpa only [binary_val_cast] using hc
  have h := (isE7DeepHole_add_iff hmem (e7ClassPoint c)).mpr (e7ClassPoint_deep c)
  have he : e7ClassPoint c+(e7PaperPoint p-e7ClassPoint c)=e7PaperPoint p := by abel
  rwa [he] at h

/-- Equation (26), with full quantification over the actual real
hyperplane and membership in the actual E₇* lattice. -/
theorem isE7DeepHole_iff_paper (x : zeroSumSpace) :
    IsE7DeepHole x ↔ ∃ p : E7PaperIndex,x-e7PaperPoint p∈e7ProjectedSet := by
  constructor
  · intro hx
    obtain ⟨c,hc⟩ := e7DeepHole_coset_coverage hx
    obtain ⟨p,hp⟩ := e7_class_to_paperBinary c
    refine ⟨p,?_⟩
    have hcp : e7ClassPoint c-e7PaperPoint p∈e7ProjectedSet := by
      unfold e7PaperPoint e7ClassPoint e8ClassPoint
      rw [e7PaperAmbient_halfRoot,e7Projected_halfRoot_difference_iff]
      change (fun i ↦ (((c.val.val i).val : ℤ) : Binary)) = e7PaperBinary p ∨
        (fun i ↦ (((c.val.val i).val : ℤ) : Binary)) = e7PaperBinary p + e8BinaryRoot
      simpa only [binary_val_cast] using hp
    rw [← e7ProjectedAddSubgroup_coe] at hc hcp ⊢
    have he : x - e7PaperPoint p =
        (x - e7ClassPoint c) + (e7ClassPoint c - e7PaperPoint p) := by abel
    rw [he]
    exact e7ProjectedAddSubgroup.add_mem hc hcp
  · rintro ⟨p,hp⟩
    have h := (isE7DeepHole_add_iff hp (e7PaperPoint p)).mpr (e7PaperPoint_deep p)
    have he : e7PaperPoint p+(x-e7PaperPoint p)=x := by abel
    rwa [he] at h

theorem e7_paper_first_distinct (S : E7FourSubset) :
    e7PaperShift S∉e7ProjectedSet := by
  have h := (e7PaperPoint_difference_iff (some S) none).not.mpr (by simp [E7PaperEquivalent])
  simpa only [e7PaperPoint_some,e7PaperPoint_none,add_sub_cancel_left] using h

theorem e7_paper_subsets_same_class_iff (S T : E7FourSubset) :
    e7PaperShift S-e7PaperShift T∈e7ProjectedSet ↔ S.val=T.val ∨ S.val=T.valᶜ := by
  have h := e7PaperPoint_difference_iff (some S) (some T)
  simpa only [e7PaperPoint_some,add_sub_add_left_eq_sub,E7PaperEquivalent] using h

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.isE7DeepHole_iff_paper
#print axioms PaperVerification.ColdSpots.e7_paper_subsets_same_class_iff
end
end Source_E7PaperRepresentatives
-- END ORIGINAL PaperVerification.E7PaperRepresentatives


-- BEGIN ORIGINAL PaperVerification.E7Roots
section Source_E7Roots

-- original header: module

-- original header: public import PaperVerification.E7MetricMeaning
-- original header: public import PaperVerification.LatticeTranslations


-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def e7RootVector : Fin 7 → (Fin 8 → ℝ) :=
  ![![-1/2,-1/2,-1/2,-1/2,1/2,1/2,1/2,1/2],
    ![1,-1,0,0,0,0,0,0],![0,1,-1,0,0,0,0,0],
    ![0,0,1,-1,0,0,0,0],![0,0,0,1,-1,0,0,0],
    ![0,0,0,0,1,-1,0,0],![0,0,0,0,0,1,-1,0]]

lemma e7RootVector_sum (j : Fin 7) : (∑ i,e7RootVector j i)=0 := by
  fin_cases j <;> norm_num [e7RootVector,Fin.sum_univ_succ]

def e7SimpleRoot (j : Fin 7) : zeroSumSpace := ⟨e7RootVector j,e7RootVector_sum j⟩

theorem e7SimpleRoot_mem (j : Fin 7) : e7SimpleRoot j ∈ e7Set := by
  fin_cases j
  · refine ⟨![-1,-1,-1,-1,0,0,0,0],by decide,Or.inr ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector]
  · refine ⟨![1,-1,0,0,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]
  · refine ⟨![0,1,-1,0,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]
  · refine ⟨![0,0,1,-1,0,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]
  · refine ⟨![0,0,0,1,-1,0,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]
  · refine ⟨![0,0,0,0,1,-1,0,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]
  · refine ⟨![0,0,0,0,0,1,-1,0],by norm_num [Fin.sum_univ_succ],Or.inl ?_⟩
    ext i; fin_cases i <;> norm_num [e7SimpleRoot,e7RootVector,intVec]

def e7RootSum (t : Fin 7 → ℝ) : Fin 8 → ℝ := ∑ i,t i•e7RootVector i

def e7RootCoordinates (x : Fin 8 → ℝ) : Fin 7 → ℝ :=
  ![2*x 7,x 0+x 7,x 0+x 1+2*x 7,x 0+x 1+x 2+3*x 7,
    x 0+x 1+x 2+x 3+4*x 7,x 0+x 1+x 2+x 3+x 4+3*x 7,
    x 0+x 1+x 2+x 3+x 4+x 5+2*x 7]

theorem e7RootCoordinates_sum (t : Fin 7 → ℝ) : e7RootCoordinates (e7RootSum t)=t := by
  ext i
  fin_cases i <;> simp [e7RootCoordinates,e7RootSum,e7RootVector,Fin.sum_univ_succ] <;> ring

theorem e7RootSum_injective : Function.Injective e7RootSum :=
  Function.LeftInverse.injective e7RootCoordinates_sum

theorem e7RootSum_coordinates (x : zeroSumSpace) : e7RootSum (e7RootCoordinates x.val)=x.val := by
  have hx := zeroSumSpace_sum x
  rw [Fin.sum_univ_eight] at hx
  ext i
  fin_cases i <;>
    norm_num [e7RootCoordinates,e7RootSum,e7RootVector,Fin.sum_univ_seven] <;> linarith

def e7IntCoordinates (m : Fin 8 → ℤ) : Fin 7 → ℤ :=
  ![2*m 7,m 0+m 7,m 0+m 1+2*m 7,m 0+m 1+m 2+3*m 7,
    m 0+m 1+m 2+m 3+4*m 7,m 0+m 1+m 2+m 3+m 4+3*m 7,
    m 0+m 1+m 2+m 3+m 4+m 5+2*m 7]

def e7HalfCoordinates : Fin 7 → ℤ := ![1,1,2,3,4,4,4]

theorem e7RootCoordinates_int (m : Fin 8 → ℤ) :
    e7RootCoordinates (intVec m)=fun i ↦ (e7IntCoordinates m i:ℝ) := by
  ext i
  fin_cases i <;> simp [e7RootCoordinates,e7IntCoordinates,intVec]

theorem e7RootCoordinates_half (m : Fin 8 → ℤ) :
    e7RootCoordinates (fun i ↦ (m i:ℝ)+1/2)=
      fun i ↦ ((e7IntCoordinates m i+e7HalfCoordinates i:ℤ):ℝ) := by
  ext i
  fin_cases i <;> simp [e7RootCoordinates,e7IntCoordinates,e7HalfCoordinates] <;> ring

/-- The root lattice cut out in E₈ is exactly the integer span of seven
simple roots with the E₇ Cartan Gram graph. -/
theorem e7Set_simpleRoot_span (x : zeroSumSpace) : x ∈ e7Set ↔
    ∃ t : Fin 7 → ℤ, x.val=e7RootSum (fun i ↦ (t i:ℝ)) := by
  constructor
  · intro hx
    rcases hx with ⟨m,hm,hx|hx⟩
    · refine ⟨e7IntCoordinates m,?_⟩
      rw [← e7RootCoordinates_int,← hx,e7RootSum_coordinates]
    · refine ⟨fun i ↦ e7IntCoordinates m i+e7HalfCoordinates i,?_⟩
      rw [← e7RootCoordinates_half,← hx,e7RootSum_coordinates]
  · rintro ⟨t,ht⟩
    change x.val ∈ dPlusSet 8
    rw [ht]
    let L := dPlusAddSubgroup 8 (by decide)
    have h : (∑ i,t i•e7RootVector i) ∈ L :=
      L.sum_mem (fun i hi ↦ L.zsmul_mem (e7SimpleRoot_mem i) (t i))
    change (∑ i, t i • e7RootVector i) ∈ dPlusSet 8 at h
    simpa only [e7RootSum, Int.cast_smul_eq_zsmul] using h

def e7Cartan (i j : Fin 7) : ℤ :=
  if i = j then 2 else
    if (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
      ((1 : ℕ) ≤ i.val ∧ (1 : ℕ) ≤ j.val ∧
        (i.val + 1 = j.val ∨ j.val + 1 = i.val)) then -1 else 0

theorem e7SimpleRoot_gram (i j : Fin 7) :
    coordinateInner (e7SimpleRoot i).val (e7SimpleRoot j).val=(e7Cartan i j:ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [e7SimpleRoot,e7RootVector,e7Cartan,coordinateInner,Fin.sum_univ_succ]

end PaperVerification.ColdSpots
end
end Source_E7Roots
-- END ORIGINAL PaperVerification.E7Roots


-- BEGIN ORIGINAL PaperVerification.E8PaperTheorems
section Source_E8PaperTheorems

-- original header: module

-- original header: public import PaperVerification.E8Theorems
-- original header: public import PaperVerification.LatticeE8Families

-- original header: @[expose] public section

noncomputable section

namespace PaperVerification.ColdSpots

theorem coldSpot_E8_iff_paper_families {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    IsColdSpot (dPlusSet 8) α x ↔ E8PaperHole x :=
  (coldSpot_E8_iff_deepHole hα x).trans (isDeepHole_E8_iff_paper x)

theorem gaussian_E8_minimum_iff_paper_families {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    setGaussian (dPlusSet 8) α x=(gaussian α 0*gaussian α (1/2))^4 ↔ E8PaperHole x := by
  rw [setGaussian_dPlus_eq (by decide : 0 < 8) hα,
    dPlusGaussian_eight_eq_min_iff hα,e8FoldedHole_iff_paper]

end PaperVerification.ColdSpots
end
end Source_E8PaperTheorems
-- END ORIGINAL PaperVerification.E8PaperTheorems


-- BEGIN ORIGINAL PaperVerification.GaussianMixtures
section Source_GaussianMixtures

-- original header: module

-- original header: public import PaperVerification.DnGaussian
-- original header: public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
-- original header: public import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- original header: public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
-- original header: public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
-- original header: public import Mathlib.MeasureTheory.Measure.Filter

-- original header: @[expose] public section
/-! # Positive Gaussian mixtures, with no σ-finiteness assumption

The nonnegative Tonelli argument is a countable-sum monotone convergence theorem,
so the mixing measure may be arbitrary.  Finiteness at one common minimum is
enough: other points may have infinite energy, as happens for singular potentials.
A real-valued bridge recovers the literal convergent sum of integral potentials.
-/

noncomputable section

namespace PaperVerification.PositiveMixtures

open MeasureTheory Set Filter
open scoped ENNReal

abbrev PositiveParameter := Set.Ioi (0 : ℝ)

variable {ι X : Type*}

def gaussianDistanceSum (d : ι → X → ℝ) (α : PositiveParameter) (x : X) : ℝ :=
  ∑' v : ι, Real.exp (-(α : ℝ) * d v x)

def gaussianMixtureENNReal (ν : Measure PositiveParameter) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ α : PositiveParameter, ENNReal.ofReal (Real.exp (-(α : ℝ) * r)) ∂ν

/-- The literal nonnegative integral potential, whenever finite. -/
def gaussianMixture (ν : Measure PositiveParameter) (r : ℝ) : ℝ :=
  ∫ α : PositiveParameter, Real.exp (-(α : ℝ) * r) ∂ν

def mixtureEnergyENNReal (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X) : ℝ≥0∞ :=
  ∑' v : ι, gaussianMixtureENNReal ν (d v x)

/-- The real series of the actual integral potentials. -/
def mixtureEnergy (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X) : ℝ :=
  ∑' v : ι, gaussianMixture ν (d v x)

theorem measurable_gaussian_term (r : ℝ) :
    Measurable (fun α : PositiveParameter => ENNReal.ofReal (Real.exp (-(α : ℝ) * r))) := by
  exact (Real.continuous_exp.comp ((continuous_subtype_val.neg).mul_const r)).measurable.ennreal_ofReal

theorem gaussianMixture_eq_toReal (ν : Measure PositiveParameter) (r : ℝ) :
    gaussianMixture ν r = (gaussianMixtureENNReal ν r).toReal := by
  apply integral_eq_lintegral_of_nonneg_ae
  · exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)
  · exact (Real.continuous_exp.comp ((continuous_subtype_val.neg).mul_const r)).aestronglyMeasurable

/-- One convergent, everywhere positive Gaussian already forces the index set
of lattice points to be countable. -/
theorem countable_of_gaussian_summable (d : ι → X → ℝ) (α : PositiveParameter) (x : X)
    (h : Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x))) : Countable ι := by
  have hs := h.countable_support
  have he : Function.support (fun v : ι => Real.exp (-(α : ℝ) * d v x)) = univ := by
    ext v
    simp [Function.mem_support, (Real.exp_pos _).ne']
  rw [he] at hs
  exact Set.countable_univ_iff.mp hs

/-- Monotone convergence for a countable sum is the complete Tonelli step here. -/
theorem mixtureEnergy_tonelli [Countable ι] (d : ι → X → ℝ) (ν : Measure PositiveParameter)
    (hs : ∀ α : PositiveParameter, ∀ x, Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x)))
    (x : X) :
    mixtureEnergyENNReal d ν x =
      ∫⁻ α : PositiveParameter, ENNReal.ofReal (gaussianDistanceSum d α x) ∂ν := by
  unfold mixtureEnergyENNReal gaussianMixtureENNReal gaussianDistanceSum
  rw [← lintegral_tsum (fun v => (measurable_gaussian_term (d v x)).aemeasurable)]
  apply lintegral_congr
  intro α
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) (hs α x)).symm

theorem measurable_gaussianDistanceSum [Countable ι] (d : ι → X → ℝ)
    (hs : ∀ α : PositiveParameter, ∀ x, Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x)))
    (x : X) : Measurable (fun α => ENNReal.ofReal (gaussianDistanceSum d α x)) := by
  have he : (fun α : PositiveParameter => ENNReal.ofReal (gaussianDistanceSum d α x)) =
      fun α : PositiveParameter => ∑' v : ι,
        ENNReal.ofReal (Real.exp (-(α : ℝ) * d v x)) := by
    funext α
    exact ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) (hs α x)
  rw [he]
  exact Measurable.ennreal_tsum (fun v => measurable_gaussian_term (d v x))

/-- Strict integration against an arbitrary nonzero positive measure.  Only the
smaller integral must be finite; the larger one may be infinite. -/
theorem lintegral_strict_of_pointwise_strict {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (hν : ν ≠ 0) {f g : A → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∀ a, f a < g a)
    (hfin : (∫⁻ a, f a ∂ν) ≠ ∞) :
    (∫⁻ a, f a ∂ν) < ∫⁻ a, g a ∂ν := by
  let h : A → ℝ≥0∞ := fun a => g a - f a
  have hm : Measurable h := hg.sub hf
  have hp (a : A) : 0 < h a := tsub_pos_iff_lt.mpr (hfg a)
  have hne : (∫⁻ a, h a ∂ν) ≠ 0 := by
    intro hzero
    have hae := (lintegral_eq_zero_iff hm).mp hzero
    letI : (ae ν).NeBot := ae_neBot.mpr hν
    obtain ⟨a, ha⟩ := hae.exists
    exact (hp a).ne' ha
  have he : (fun a => f a + h a) = g := by
    funext a
    exact add_tsub_cancel_of_le (hfg a).le
  rw [← he, lintegral_add_left hf]
  exact ENNReal.lt_add_right hfin hne

/-- Strictness at every positive parameter follows from the exact common
minimum set, not from a separate assumption about the potential. -/
theorem gaussian_strict_off_common_minimum (d : ι → X → ℝ) (H : X → Prop)
    (hmain : ∀ α : PositiveParameter, ∀ x,
      (∀ y, gaussianDistanceSum d α x ≤ gaussianDistanceSum d α y) ↔ H x)
    {c x : X} (hc : H c) (hx : ¬H x) (α : PositiveParameter) :
    gaussianDistanceSum d α c < gaussianDistanceSum d α x := by
  have hmin := (hmain α c).mpr hc
  have hle := hmin x
  apply lt_of_le_of_ne hle
  intro heq
  have hxMin : ∀ y, gaussianDistanceSum d α x ≤ gaussianDistanceSum d α y := by
    intro y
    rw [← heq]
    exact hmin y
  exact hx ((hmain α x).mp hxMin)

/-- Corollary 1.2's complete transfer principle.  Countability is derived from
Gaussian convergence, and no finite or σ-finite measure assumption is imposed.
Finiteness at one common minimum permits singular potentials elsewhere. -/
theorem gaussian_mixture_minimizers (d : ι → X → ℝ) (H : X → Prop)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hs : ∀ α : PositiveParameter, ∀ x, Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x)))
    (hmain : ∀ α : PositiveParameter, ∀ x,
      (∀ y, gaussianDistanceSum d α x ≤ gaussianDistanceSum d α y) ↔ H x)
    (c : X) (hc : H c) (hfin : mixtureEnergyENNReal d ν c ≠ ∞) (x : X) :
    (∀ y, mixtureEnergyENNReal d ν x ≤ mixtureEnergyENNReal d ν y) ↔ H x := by
  letI : Countable ι := countable_of_gaussian_summable d ⟨1, by norm_num⟩ c (hs _ c)
  constructor
  · intro hmin
    by_contra hx
    have hpoint (α : PositiveParameter) : ENNReal.ofReal (gaussianDistanceSum d α c) <
        ENNReal.ofReal (gaussianDistanceSum d α x) := by
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (tsum_nonneg fun _ => (Real.exp_pos _).le)).mpr
      exact gaussian_strict_off_common_minimum d H hmain hc hx α
    have hfin' : (∫⁻ α : PositiveParameter, ENNReal.ofReal (gaussianDistanceSum d α c) ∂ν) ≠ ∞ := by
      rwa [← mixtureEnergy_tonelli d ν hs]
    have hstrict := lintegral_strict_of_pointwise_strict ν hν
      (measurable_gaussianDistanceSum d hs c) (measurable_gaussianDistanceSum d hs x) hpoint hfin'
    rw [← mixtureEnergy_tonelli d ν hs c, ← mixtureEnergy_tonelli d ν hs x] at hstrict
    exact (not_lt_of_ge (hmin c)) hstrict
  · intro hx y
    rw [mixtureEnergy_tonelli d ν hs x, mixtureEnergy_tonelli d ν hs y]
    apply lintegral_mono
    intro α
    exact ENNReal.ofReal_le_ofReal ((hmain α x).mpr hx y)

/-- Convergence at any one ambient point already implies convergence at
every common Gaussian minimum. Thus a singular potential need not be
finite at lattice points or at any prescribed reference point. -/
theorem gaussian_mixture_minimizers_of_exists_finite (d : ι → X → ℝ) (H : X → Prop)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hs : ∀ α : PositiveParameter, ∀ x,
      Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x)))
    (hmain : ∀ α : PositiveParameter, ∀ x,
      (∀ y, gaussianDistanceSum d α x ≤ gaussianDistanceSum d α y) ↔ H x)
    (c : X) (hc : H c) (hfin : ∃ y,mixtureEnergyENNReal d ν y≠∞) (x : X) :
    (∀ y,mixtureEnergyENNReal d ν x≤mixtureEnergyENNReal d ν y) ↔ H x := by
  obtain ⟨y,hy⟩ := hfin
  letI : Countable ι := countable_of_gaussian_summable d ⟨1,by norm_num⟩ c (hs _ c)
  have hle : mixtureEnergyENNReal d ν c≤mixtureEnergyENNReal d ν y := by
    rw [mixtureEnergy_tonelli d ν hs c,mixtureEnergy_tonelli d ν hs y]
    exact lintegral_mono (fun α=>ENNReal.ofReal_le_ofReal ((hmain α c).mpr hc y))
  exact gaussian_mixture_minimizers d H ν hν hs hmain c hc
    (ne_top_of_le_ne_top hy hle) x

theorem mixtureEnergy_eq_toReal (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X)
    (hfin : mixtureEnergyENNReal d ν x ≠ ∞) :
    mixtureEnergy d ν x = (mixtureEnergyENNReal d ν x).toReal := by
  unfold mixtureEnergy mixtureEnergyENNReal at *
  simp_rw [gaussianMixture_eq_toReal]
  exact (ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hfin)).symm

theorem summable_mixtureEnergy (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X)
    (hfin : mixtureEnergyENNReal d ν x ≠ ∞) : Summable (fun v => gaussianMixture ν (d v x)) := by
  simp_rw [gaussianMixture_eq_toReal]
  exact ENNReal.summable_toReal hfin

/-- Finiteness of the nonnegative lattice energy makes every individual
integral potential genuinely integrable.  Thus the real-valued corollary
never relies on the default value of a nonintegrable Bochner integral. -/
theorem integrable_gaussian_term_of_energy_finite (d : ι → X → ℝ)
    (ν : Measure PositiveParameter) (x : X)
    (hfin : mixtureEnergyENNReal d ν x ≠ ∞) (v : ι) :
    Integrable (fun α : PositiveParameter => Real.exp (-(α : ℝ) * d v x)) ν := by
  change (∑' w : ι, gaussianMixtureENNReal ν (d w x)) ≠ ∞ at hfin
  have hv : gaussianMixtureENNReal ν (d v x) ≠ ∞ :=
    ENNReal.ne_top_of_tsum_ne_top hfin v
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    (Real.continuous_exp.comp ((continuous_subtype_val.neg).mul_const (d v x))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mp hv

/-- Literal real-valued convergent lattice sums of the stated integral potential.
Every quantifier over ambient points remains unrestricted. -/
theorem gaussian_mixture_minimizers_real (d : ι → X → ℝ) (H : X → Prop)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hs : ∀ α : PositiveParameter, ∀ x, Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x)))
    (hmain : ∀ α : PositiveParameter, ∀ x,
      (∀ y, gaussianDistanceSum d α x ≤ gaussianDistanceSum d α y) ↔ H x)
    (c : X) (hc : H c) (hfin : ∀ x, mixtureEnergyENNReal d ν x ≠ ∞) (x : X) :
    (∀ y, mixtureEnergy d ν x ≤ mixtureEnergy d ν y) ↔ H x := by
  have h := gaussian_mixture_minimizers d H ν hν hs hmain c hc (hfin c) x
  have he : (∀ y, mixtureEnergy d ν x ≤ mixtureEnergy d ν y) ↔
      ∀ y, mixtureEnergyENNReal d ν x ≤ mixtureEnergyENNReal d ν y := by
    constructor <;> intro hxy y
    · have hy := hxy y
      rw [mixtureEnergy_eq_toReal d ν x (hfin x), mixtureEnergy_eq_toReal d ν y (hfin y)] at hy
      exact (ENNReal.toReal_le_toReal (hfin x) (hfin y)).mp hy
    · rw [mixtureEnergy_eq_toReal d ν x (hfin x), mixtureEnergy_eq_toReal d ν y (hfin y)]
      exact (ENNReal.toReal_le_toReal (hfin x) (hfin y)).mpr (hxy y)
  exact he.trans h

/-- Finiteness of the nonnegative energy is exactly the ordinary convergence
condition for the integral potential and its lattice sum. -/
theorem mixtureEnergyENNReal_ne_top_iff_integrable_summable
    (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X) :
    mixtureEnergyENNReal d ν x ≠ ∞ ↔
      (∀ v : ι, Integrable
        (fun α : PositiveParameter => Real.exp (-(α : ℝ) * d v x)) ν) ∧
      Summable (fun v : ι => gaussianMixture ν (d v x)) := by
  constructor
  · intro hfin
    exact ⟨integrable_gaussian_term_of_energy_finite d ν x hfin,
      summable_mixtureEnergy d ν x hfin⟩
  · rintro ⟨hint, hsum⟩
    have he (v : ι) : gaussianMixtureENNReal ν (d v x) =
        ENNReal.ofReal (gaussianMixture ν (d v x)) := by
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint v)
        (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))).symm
    unfold mixtureEnergyENNReal
    simp_rw [he]
    exact hsum.tsum_ofReal_ne_top

/-- The hypothesis in the real-valued corollary is equivalent to pointwise
integrability of the stated potential and ordinary convergence at every point. -/
theorem mixtureEnergyENNReal_everywhere_finite_iff
    (d : ι → X → ℝ) (ν : Measure PositiveParameter) :
    (∀ x : X, mixtureEnergyENNReal d ν x ≠ ∞) ↔
      (∀ x : X, ∀ v : ι, Integrable
        (fun α : PositiveParameter => Real.exp (-(α : ℝ) * d v x)) ν) ∧
      (∀ x : X, Summable (fun v : ι => gaussianMixture ν (d v x))) := by
  constructor
  · intro h
    exact ⟨fun x => ((mixtureEnergyENNReal_ne_top_iff_integrable_summable d ν x).mp
      (h x)).1, fun x => ((mixtureEnergyENNReal_ne_top_iff_integrable_summable d ν x).mp
      (h x)).2⟩
  · rintro ⟨hint, hsum⟩ x
    exact (mixtureEnergyENNReal_ne_top_iff_integrable_summable d ν x).mpr
      ⟨hint x, hsum x⟩


end PaperVerification.PositiveMixtures

#print axioms PaperVerification.PositiveMixtures.gaussian_mixture_minimizers
#print axioms PaperVerification.PositiveMixtures.gaussian_mixture_minimizers_real
#print axioms PaperVerification.PositiveMixtures.mixtureEnergyENNReal_ne_top_iff_integrable_summable
#print axioms PaperVerification.PositiveMixtures.mixtureEnergyENNReal_everywhere_finite_iff
end
end Source_GaussianMixtures
-- END ORIGINAL PaperVerification.GaussianMixtures


-- BEGIN ORIGINAL PaperVerification.LatticeMixtures
section Source_LatticeMixtures

-- original header: module

-- original header: public import PaperVerification.GaussianMixtures
-- original header: public import PaperVerification.BWNormalized
-- original header: public import PaperVerification.E6Euclidean
-- original header: public import PaperVerification.E7Theorems

-- original header: @[expose] public section

/-! # Corollary 1.2 for every lattice in Theorem 1.1

Each specialization supplies actual Gaussian convergence and the actual theorem
for that lattice.  The only hypotheses on the mixing measure are nonzero
positivity (built into `Measure`) and convergence of the nonnegative energy.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory
open scoped ENNReal
open PaperVerification.PositiveMixtures

variable {n : ℕ}

def setMixtureEnergyENNReal (L : Set (Fin n → ℝ)) (ν : Measure PositiveParameter)
    (x : Fin n → ℝ) : ℝ≥0∞ :=
  mixtureEnergyENNReal (fun v : L => fun y => sqDist v.val y) ν x

def setMixtureEnergy (L : Set (Fin n → ℝ)) (ν : Measure PositiveParameter)
    (x : Fin n → ℝ) : ℝ :=
  mixtureEnergy (fun v : L => fun y => sqDist v.val y) ν x

def IsMixtureColdSpot (L : Set (Fin n → ℝ)) (ν : Measure PositiveParameter)
    (x : Fin n → ℝ) : Prop := ∀ y, setMixtureEnergy L ν x ≤ setMixtureEnergy L ν y

/-- Coordinate-space form of the exact positive-mixture transfer. -/
theorem mixture_coldSpot_iff_of_universal
    (L : Set (Fin n → ℝ))
    (hGauss : ∀ α : ℝ, 0 < α → ∀ x,
      Summable (fun v : L => Real.exp (-α * sqDist v.val x)))
    (hmain : ∀ α : ℝ, 0 < α → ∀ x, IsColdSpot L α x ↔ IsDeepHole L x)
    (c : Fin n → ℝ) (hc : IsDeepHole L c)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, setMixtureEnergyENNReal L ν x ≠ ∞) (x : Fin n → ℝ) :
    IsMixtureColdSpot L ν x ↔ IsDeepHole L x := by
  exact gaussian_mixture_minimizers_real (fun v : L => fun y => sqDist v.val y)
    (IsDeepHole L) ν hν (fun α x => hGauss α α.property x)
    (fun α x => hmain α α.property x) c hc hconv x

/-- Extended-energy form, allowing singular potentials and infinite energy at
some ambient points.  Only one deep hole's energy must be finite. -/
theorem mixture_coldSpot_ennreal_iff_of_universal
    (L : Set (Fin n → ℝ))
    (hGauss : ∀ α : ℝ, 0 < α → ∀ x,
      Summable (fun v : L => Real.exp (-α * sqDist v.val x)))
    (hmain : ∀ α : ℝ, 0 < α → ∀ x, IsColdSpot L α x ↔ IsDeepHole L x)
    (c : Fin n → ℝ) (hc : IsDeepHole L c)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : setMixtureEnergyENNReal L ν c ≠ ∞) (x : Fin n → ℝ) :
    (∀ y, setMixtureEnergyENNReal L ν x ≤ setMixtureEnergyENNReal L ν y) ↔ IsDeepHole L x := by
  exact gaussian_mixture_minimizers (fun v : L => fun y => sqDist v.val y)
    (IsDeepHole L) ν hν (fun α x => hGauss α α.property x)
    (fun α x => hmain α α.property x) c hc hconv x

/-- Corollary 1.2 for every even D_n^+ with n≥8, including E8. -/
theorem mixture_coldSpot_dPlus_iff_deepHole (hn : 8 ≤ n) (heven : Even n)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, setMixtureEnergyENNReal (dPlusSet n) ν x ≠ ∞) (x : Fin n → ℝ) :
    IsMixtureColdSpot (dPlusSet n) ν x ↔ IsDeepHole (dPlusSet n) x := by
  obtain ⟨c, hc⟩ := exists_balancedHalfGrid heven
  have hcdeep : IsDeepHole (dPlusSet n) c :=
    (isDeepHole_dPlus_iff_depth hn heven c).mpr (squaredDepth_dPlus_of_balanced hn hc)
  exact mixture_coldSpot_iff_of_universal (dPlusSet n)
    (fun α hα x => summable_setGaussian_dPlus (by omega) hα x)
    (fun α hα x => coldSpot_dPlus_iff_deepHole hn heven hα x) c hcdeep ν hν hconv x

theorem mixture_coldSpot_E8_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, setMixtureEnergyENNReal (dPlusSet 8) ν x ≠ ∞) (x : Fin 8 → ℝ) :
    IsMixtureColdSpot (dPlusSet 8) ν x ↔ IsDeepHole (dPlusSet 8) x :=
  mixture_coldSpot_dPlus_iff_deepHole (by decide) (by decide) ν hν hconv x

/-- Corollary 1.2 for the usual integral BW16 lattice. -/
theorem mixture_coldSpot_bw16_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, setMixtureEnergyENNReal bw16Set ν x ≠ ∞) (x : Fin 16 → ℝ) :
    IsMixtureColdSpot bw16Set ν x ↔ IsDeepHole bw16Set x := by
  obtain ⟨hupper, c, hc⟩ := bw16_squared_covering_radius
  have hcdeep : IsDeepHole bw16Set c := by intro y; rw [hc]; exact hupper y
  exact mixture_coldSpot_iff_of_universal bw16Set
    (fun α hα x => summable_setGaussian_bw16 hα x)
    (fun α hα x => coldSpot_bw16_iff_deepHole hα x) c hcdeep ν hν hconv x

theorem summable_setGaussian_l6Euclidean {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    Summable (fun v : l6EuclideanSet => Real.exp (-α * sqDist v.val (triTripleFlatten z))) := by
  apply (l6EuclideanIndexEquiv.summable_iff
    (f := fun v : l6EuclideanSet => Real.exp (-α * sqDist v.val (triTripleFlatten z)))).mp
  have hs := summable_l6Gaussian hα z
  convert hs using 1
  funext p
  change Real.exp (-α * sqDist (triTripleFlatten (l6Point p)) (triTripleFlatten z)) = _
  rw [triTripleFlatten_sqDist]

theorem summable_setGaussian_E6 {α : ℝ} (hα : 0 < α) (x : Fin 6 → ℝ) :
    Summable (fun v : e6Set => Real.exp (-α * sqDist v.val x)) := by
  obtain ⟨z, rfl⟩ := e6PhysicalPoint_surjective x
  unfold e6Set e6PhysicalPoint
  rw [summable_scaled_iff _ (by positivity), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact summable_setGaussian_l6Euclidean (by positivity) z

/-- Corollary 1.2 for the root-normalized E6 lattice in ordinary R6. -/
theorem mixture_coldSpot_E6_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, setMixtureEnergyENNReal e6Set ν x ≠ ∞) (x : Fin 6 → ℝ) :
    IsMixtureColdSpot e6Set ν x ↔ IsDeepHole e6Set x := by
  have hcdeep : IsDeepHole e6Set (e6PhysicalPoint e6HoleWitness) := by
    intro y
    rw [e6_covering_radius_attained]
    exact e6_covering_radius_squared y
  exact mixture_coldSpot_iff_of_universal e6Set
    (fun α hα x => summable_setGaussian_E6 hα x)
    (fun α hα x => coldSpot_E6_iff_deepHole hα x)
    (e6PhysicalPoint e6HoleWitness) hcdeep ν hν hconv x

def e7MixtureEnergyENNReal (ν : Measure PositiveParameter) (x : zeroSumSpace) : ℝ≥0∞ :=
  mixtureEnergyENNReal (fun v : e7ProjectedSet => fun y : zeroSumSpace => sqDist v.val.val y.val) ν x

def e7MixtureEnergy (ν : Measure PositiveParameter) (x : zeroSumSpace) : ℝ :=
  mixtureEnergy (fun v : e7ProjectedSet => fun y : zeroSumSpace => sqDist v.val.val y.val) ν x

/-- Corollary 1.2 for E7*, in its actual seven-dimensional Euclidean hyperplane. -/
theorem mixture_coldSpot_E7_dual_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∀ x, e7MixtureEnergyENNReal ν x ≠ ∞) (x : zeroSumSpace) :
    (∀ y, e7MixtureEnergy ν x ≤ e7MixtureEnergy ν y) ↔ IsE7DeepHole x := by
  have hcdeep : IsE7DeepHole e7Witness := (isE7DeepHole_iff_depth _).mpr e7Witness_depth
  exact gaussian_mixture_minimizers_real
    (fun v : e7ProjectedSet => fun y : zeroSumSpace => sqDist v.val.val y.val)
    IsE7DeepHole ν hν (fun α x => summable_e7Gaussian α.property x)
    (fun α x => coldSpot_E7_dual_iff_deepHole α.property x) e7Witness hcdeep hconv x

/-- The same D_n^+ conclusion permits infinite energy away from the minimum
set.  Convergence is required only at a single actual deep hole. -/
theorem mixture_coldSpot_dPlus_ennreal_iff_deepHole (hn : 8 ≤ n) (heven : Even n)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∃ c, IsDeepHole (dPlusSet n) c ∧ setMixtureEnergyENNReal (dPlusSet n) ν c ≠ ∞)
    (x : Fin n → ℝ) :
    (∀ y, setMixtureEnergyENNReal (dPlusSet n) ν x ≤ setMixtureEnergyENNReal (dPlusSet n) ν y) ↔
      IsDeepHole (dPlusSet n) x := by
  obtain ⟨c, hc, hfinite⟩ := hconv
  exact mixture_coldSpot_ennreal_iff_of_universal (dPlusSet n)
    (fun α hα x => summable_setGaussian_dPlus (by omega) hα x)
    (fun α hα x => coldSpot_dPlus_iff_deepHole hn heven hα x) c hc ν hν hfinite x

theorem mixture_coldSpot_E8_ennreal_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∃ c, IsDeepHole (dPlusSet 8) c ∧ setMixtureEnergyENNReal (dPlusSet 8) ν c ≠ ∞)
    (x : Fin 8 → ℝ) :
    (∀ y, setMixtureEnergyENNReal (dPlusSet 8) ν x ≤ setMixtureEnergyENNReal (dPlusSet 8) ν y) ↔
      IsDeepHole (dPlusSet 8) x :=
  mixture_coldSpot_dPlus_ennreal_iff_deepHole (by decide) (by decide) ν hν hconv x

theorem mixture_coldSpot_bw16_ennreal_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∃ c, IsDeepHole bw16Set c ∧ setMixtureEnergyENNReal bw16Set ν c ≠ ∞)
    (x : Fin 16 → ℝ) :
    (∀ y, setMixtureEnergyENNReal bw16Set ν x ≤ setMixtureEnergyENNReal bw16Set ν y) ↔
      IsDeepHole bw16Set x := by
  obtain ⟨c, hc, hfinite⟩ := hconv
  exact mixture_coldSpot_ennreal_iff_of_universal bw16Set
    (fun α hα x => summable_setGaussian_bw16 hα x)
    (fun α hα x => coldSpot_bw16_iff_deepHole hα x) c hc ν hν hfinite x

theorem mixture_coldSpot_E6_ennreal_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∃ c, IsDeepHole e6Set c ∧ setMixtureEnergyENNReal e6Set ν c ≠ ∞)
    (x : Fin 6 → ℝ) :
    (∀ y, setMixtureEnergyENNReal e6Set ν x ≤ setMixtureEnergyENNReal e6Set ν y) ↔
      IsDeepHole e6Set x := by
  obtain ⟨c, hc, hfinite⟩ := hconv
  exact mixture_coldSpot_ennreal_iff_of_universal e6Set
    (fun α hα x => summable_setGaussian_E6 hα x)
    (fun α hα x => coldSpot_E6_iff_deepHole hα x) c hc ν hν hfinite x

theorem mixture_coldSpot_E7_dual_ennreal_iff_deepHole
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hconv : ∃ c, IsE7DeepHole c ∧ e7MixtureEnergyENNReal ν c ≠ ∞) (x : zeroSumSpace) :
    (∀ y, e7MixtureEnergyENNReal ν x ≤ e7MixtureEnergyENNReal ν y) ↔ IsE7DeepHole x := by
  obtain ⟨c, hc, hfinite⟩ := hconv
  exact gaussian_mixture_minimizers
    (fun v : e7ProjectedSet => fun y : zeroSumSpace => sqDist v.val.val y.val)
    IsE7DeepHole ν hν (fun α x => summable_e7Gaussian α.property x)
    (fun α x => coldSpot_E7_dual_iff_deepHole α.property x) c hc hfinite x

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.mixture_coldSpot_dPlus_iff_deepHole
#print axioms PaperVerification.ColdSpots.mixture_coldSpot_bw16_iff_deepHole
#print axioms PaperVerification.ColdSpots.mixture_coldSpot_E6_iff_deepHole
#print axioms PaperVerification.ColdSpots.mixture_coldSpot_E7_dual_iff_deepHole
end
end Source_LatticeMixtures
-- END ORIGINAL PaperVerification.LatticeMixtures


-- BEGIN ORIGINAL PaperVerification.LatticeMixturesExtended
section Source_LatticeMixturesExtended

-- original header: module

-- original header: public import PaperVerification.LatticeMixtures

-- original header: @[expose] public section

/-!
# Corollary 1.2 including singular positive mixtures

Only existence of one finite lattice sum is required. The actual positive
measure may be infinite and need not be sigma finite. The nonnegative
integral-potential sums retain their ordinary extended values at singular
points. Whenever all values are finite, the previously proved real-valued
bridge recovers the literal real series.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory PaperVerification.PositiveMixtures
open scoped ENNReal

theorem mixture_coldSpot_ennreal_iff_of_exists_finite {n : ℕ}
    (L : Set (Fin n→ℝ))
    (hGauss : ∀ α : ℝ,0<α→∀ x,
      Summable (fun v : L=>Real.exp (-α*sqDist v.val x)))
    (hmain : ∀ α : ℝ,0<α→∀ x,IsColdSpot L α x↔IsDeepHole L x)
    (c : Fin n→ℝ) (hc : IsDeepHole L c)
    (ν : Measure PositiveParameter) (hν : ν≠0)
    (hconv : ∃ y,setMixtureEnergyENNReal L ν y≠∞) (x : Fin n→ℝ) :
    (∀ y,setMixtureEnergyENNReal L ν x≤setMixtureEnergyENNReal L ν y) ↔
      IsDeepHole L x :=
  gaussian_mixture_minimizers_of_exists_finite
    (fun v : L=>fun y=>sqDist v.val y) (IsDeepHole L) ν hν
    (fun α y=>hGauss α α.property y) (fun α y=>hmain α α.property y)
    c hc hconv x

theorem mixture_coldSpot_dPlus_iff_exists_finite {n : ℕ}
    (hn : 8≤n) (heven : Even n) (ν : Measure PositiveParameter) (hν : ν≠0)
    (hconv : ∃ y,setMixtureEnergyENNReal (dPlusSet n) ν y≠∞) (x : Fin n→ℝ) :
    (∀ y,setMixtureEnergyENNReal (dPlusSet n) ν x≤setMixtureEnergyENNReal (dPlusSet n) ν y) ↔
      IsDeepHole (dPlusSet n) x := by
  obtain ⟨c,hc⟩ := exists_balancedHalfGrid heven
  have hdeep : IsDeepHole (dPlusSet n) c :=
    (isDeepHole_dPlus_iff_depth hn heven c).mpr (squaredDepth_dPlus_of_balanced hn hc)
  exact mixture_coldSpot_ennreal_iff_of_exists_finite (dPlusSet n)
    (fun α hα y=>summable_setGaussian_dPlus (by omega) hα y)
    (fun α hα y=>coldSpot_dPlus_iff_deepHole hn heven hα y) c hdeep ν hν hconv x

theorem mixture_coldSpot_E6_iff_exists_finite
    (ν : Measure PositiveParameter) (hν : ν≠0)
    (hconv : ∃ y,setMixtureEnergyENNReal e6Set ν y≠∞) (x : Fin 6→ℝ) :
    (∀ y,setMixtureEnergyENNReal e6Set ν x≤setMixtureEnergyENNReal e6Set ν y) ↔
      IsDeepHole e6Set x := by
  have hc : IsDeepHole e6Set (e6PhysicalPoint e6HoleWitness) := by
    intro y
    rw [e6_covering_radius_attained]
    exact e6_covering_radius_squared y
  exact mixture_coldSpot_ennreal_iff_of_exists_finite e6Set
    (fun α hα y=>summable_setGaussian_E6 hα y)
    (fun α hα y=>coldSpot_E6_iff_deepHole hα y)
    (e6PhysicalPoint e6HoleWitness) hc ν hν hconv x

theorem mixture_coldSpot_bw16_iff_exists_finite
    (ν : Measure PositiveParameter) (hν : ν≠0)
    (hconv : ∃ y,setMixtureEnergyENNReal bw16Set ν y≠∞) (x : Fin 16→ℝ) :
    (∀ y,setMixtureEnergyENNReal bw16Set ν x≤setMixtureEnergyENNReal bw16Set ν y) ↔
      IsDeepHole bw16Set x := by
  obtain ⟨hupper,c,hc⟩ := bw16_squared_covering_radius
  have hdeep : IsDeepHole bw16Set c := by
    intro y
    rw [hc]
    exact hupper y
  exact mixture_coldSpot_ennreal_iff_of_exists_finite bw16Set
    (fun α hα y=>summable_setGaussian_bw16 hα y)
    (fun α hα y=>coldSpot_bw16_iff_deepHole hα y) c hdeep ν hν hconv x

theorem mixture_coldSpot_E7_dual_iff_exists_finite
    (ν : Measure PositiveParameter) (hν : ν≠0)
    (hconv : ∃ y,e7MixtureEnergyENNReal ν y≠∞) (x : zeroSumSpace) :
    (∀ y,e7MixtureEnergyENNReal ν x≤e7MixtureEnergyENNReal ν y) ↔ IsE7DeepHole x := by
  have hc : IsE7DeepHole e7Witness := (isE7DeepHole_iff_depth _).mpr e7Witness_depth
  exact gaussian_mixture_minimizers_of_exists_finite
    (fun v : e7ProjectedSet=>fun y : zeroSumSpace=>sqDist v.val.val y.val)
    IsE7DeepHole ν hν (fun α y=>summable_e7Gaussian α.property y)
    (fun α y=>coldSpot_E7_dual_iff_deepHole α.property y) e7Witness hc hconv x

/-- The complete positive-mixture corollary, in an extended-value form
which also covers convergent singular potentials. -/
theorem lattice_corollary_1_2_extended (ν : Measure PositiveParameter) (hν : ν≠0) :
    ((∃ y : Fin 6→ℝ,setMixtureEnergyENNReal e6Set ν y≠∞) →
      ∀ x : Fin 6→ℝ,(∀ y,setMixtureEnergyENNReal e6Set ν x≤setMixtureEnergyENNReal e6Set ν y) ↔
        IsDeepHole e6Set x) ∧
    ((∃ y : Fin 8→ℝ,setMixtureEnergyENNReal (dPlusSet 8) ν y≠∞) →
      ∀ x : Fin 8→ℝ,(∀ y,setMixtureEnergyENNReal (dPlusSet 8) ν x≤
        setMixtureEnergyENNReal (dPlusSet 8) ν y) ↔IsDeepHole (dPlusSet 8) x) ∧
    ((∃ y : zeroSumSpace,e7MixtureEnergyENNReal ν y≠∞) →
      ∀ x : zeroSumSpace,(∀ y,e7MixtureEnergyENNReal ν x≤e7MixtureEnergyENNReal ν y) ↔
        IsE7DeepHole x) ∧
    ((∃ y : Fin 16→ℝ,setMixtureEnergyENNReal bw16Set ν y≠∞) →
      ∀ x : Fin 16→ℝ,(∀ y,setMixtureEnergyENNReal bw16Set ν x≤setMixtureEnergyENNReal bw16Set ν y) ↔
        IsDeepHole bw16Set x) ∧
    (∀ n : ℕ,8≤n→Even n→
      (∃ y : Fin n→ℝ,setMixtureEnergyENNReal (dPlusSet n) ν y≠∞) →
      ∀ x : Fin n→ℝ,(∀ y,setMixtureEnergyENNReal (dPlusSet n) ν x≤
        setMixtureEnergyENNReal (dPlusSet n) ν y) ↔IsDeepHole (dPlusSet n) x) :=
  ⟨fun h x=>mixture_coldSpot_E6_iff_exists_finite ν hν h x,
    fun h x=>mixture_coldSpot_dPlus_iff_exists_finite (by decide) (by decide) ν hν h x,
    fun h x=>mixture_coldSpot_E7_dual_iff_exists_finite ν hν h x,
    fun h x=>mixture_coldSpot_bw16_iff_exists_finite ν hν h x,
    fun _ hn heven h x=>mixture_coldSpot_dPlus_iff_exists_finite hn heven ν hν h x⟩

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.lattice_corollary_1_2_extended
end
end Source_LatticeMixturesExtended
-- END ORIGINAL PaperVerification.LatticeMixturesExtended


-- BEGIN ORIGINAL PaperVerification.LatticePaperTheorems
section Source_LatticePaperTheorems

-- original header: module

-- original header: public import PaperVerification.E6ClassCount
-- original header: public import PaperVerification.E6Normalization
-- original header: public import PaperVerification.E7Roots
-- original header: public import PaperVerification.E7TranslationClasses
-- original header: public import PaperVerification.E8PaperTheorems
-- original header: public import PaperVerification.E8TranslationClasses
-- original header: public import PaperVerification.DnTranslationClasses
-- original header: public import PaperVerification.BWTranslationClasses
-- original header: public import PaperVerification.BWThetaFormula
-- original header: public import PaperVerification.BWNorm
-- original header: public import PaperVerification.LatticeMixtures
-- original header: public import PaperVerification.LatticeMixturesExtended
-- original header: public import PaperVerification.LatticeMetricMeaning
-- original header: public import PaperVerification.E7MetricMeaning
-- original header: public import PaperVerification.E7PaperRepresentatives

-- original header: @[expose] public section

/-! # Explicit endpoints for the cold-spots manuscript

These declarations collect the full statements in one place.  The coordinate
sets and the predicates are those used throughout the proofs; no additional
analytic, geometric, integrality, or finite-support hypothesis is introduced.
The Euclidean metric interpretation is proved in `LatticeMetricMeaning` and
`E7MetricMeaning`, and the lattice normalizations have separate root/code proofs.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory
open PaperVerification.PositiveMixtures
open scoped ENNReal

/-- Theorem 1.1, including every even dimension n≥8 and every α>0. -/
theorem lattice_theorem_1_1 :
    (∀ α : ℝ, 0 < α → ∀ x : Fin 6 → ℝ,
      IsColdSpot e6Set α x ↔ IsDeepHole e6Set x) ∧
    (∀ α : ℝ, 0 < α → ∀ x : Fin 8 → ℝ,
      IsColdSpot (dPlusSet 8) α x ↔ IsDeepHole (dPlusSet 8) x) ∧
    (∀ α : ℝ, 0 < α → ∀ x : zeroSumSpace,
      IsE7ColdSpot α x ↔ IsE7DeepHole x) ∧
    (∀ α : ℝ, 0 < α → ∀ x : Fin 16 → ℝ,
      IsColdSpot bw16Set α x ↔ IsDeepHole bw16Set x) ∧
    (∀ n : ℕ, 8 ≤ n → Even n → ∀ α : ℝ, 0 < α → ∀ x : Fin n → ℝ,
      IsColdSpot (dPlusSet n) α x ↔ IsDeepHole (dPlusSet n) x) :=
  ⟨fun _ hα x ↦ coldSpot_E6_iff_deepHole hα x,
   fun _ hα x ↦ coldSpot_E8_iff_deepHole hα x,
   fun _ hα x ↦ coldSpot_E7_dual_iff_deepHole hα x,
   fun _ hα x ↦ coldSpot_bw16_iff_deepHole hα x,
   fun _ hn heven _ hα x ↦ coldSpot_dPlus_iff_deepHole hn heven hα x⟩

/-- All entries of the radius column are upper bounds with actual attainment. -/
theorem lattice_covering_radius_table :
    ((∀ x : Fin 6 → ℝ, squaredDepth e6Set x ≤ 4/3) ∧
      ∃ x : Fin 6 → ℝ, squaredDepth e6Set x=4/3) ∧
    ((∀ x : Fin 8 → ℝ, squaredDepth (dPlusSet 8) x ≤ 1) ∧
      ∃ x : Fin 8 → ℝ, squaredDepth (dPlusSet 8) x=1) ∧
    ((∀ x : zeroSumSpace, e7SquaredDepth x ≤ 7/8) ∧
      ∃ x : zeroSumSpace, e7SquaredDepth x=7/8) ∧
    ((∀ x : Fin 16 → ℝ, squaredDepth bw16Set x ≤ 3) ∧
      ∃ x : Fin 16 → ℝ, squaredDepth bw16Set x=3) ∧
    (∀ n : ℕ, 8 ≤ n → Even n →
      (∀ x : Fin n → ℝ, squaredDepth (dPlusSet n) x ≤ (n:ℝ)/8) ∧
        ∃ x : Fin n → ℝ, squaredDepth (dPlusSet n) x=(n:ℝ)/8) := by
  refine ⟨⟨e6_covering_radius_squared,e6PhysicalPoint e6HoleWitness,
    e6_covering_radius_attained⟩,?_,e7_covering_radius,bw16_squared_covering_radius,
    fun _ hn heven ↦ dPlus_squared_covering_radius hn heven⟩
  simpa using dPlus_squared_covering_radius (n:=8) (by decide) (by decide)

theorem e6_deep_translation_class_count_uniform :
    Nat.card (DeepTranslationClasses e6AddSubgroup)=2 := by
  simpa only [DeepTranslationClasses,e6AddSubgroup_coe,E6DeepTranslationClasses]
    using e6_deep_translation_class_count

/-- The class column counts actual quotient classes of all real deep holes. -/
theorem lattice_translation_class_table :
    Nat.card (DeepTranslationClasses e6AddSubgroup)=2 ∧
    Nat.card (DeepTranslationClasses (dPlusAddSubgroup 8 (by decide)))=135 ∧
    Nat.card E7DeepTranslationClasses=36 ∧
    Nat.card (DeepTranslationClasses bw16AddSubgroup)=120 ∧
    (∀ n : ℕ, 8 < n → ∀ heven : Even n,
      Nat.card (DeepTranslationClasses (dPlusAddSubgroup n heven))=n.choose (n/2)) :=
  ⟨e6_deep_translation_class_count_uniform,e8_deep_translation_class_count,
   e7_dual_deep_translation_class_count,bw16_deep_translation_class_count,
   fun _ hn heven ↦ dPlus_deep_translation_class_count hn heven⟩

/-- Corollary 1.2 for the literal convergent real sums of integral potentials.
The positive measure is arbitrary. No sigma-finiteness hypothesis is imposed. -/
theorem lattice_corollary_1_2 (ν : Measure PositiveParameter) (hν : ν≠0) :
    ((∀ x : Fin 6 → ℝ, setMixtureEnergyENNReal e6Set ν x≠∞) →
      ∀ x : Fin 6 → ℝ, IsMixtureColdSpot e6Set ν x ↔ IsDeepHole e6Set x) ∧
    ((∀ x : Fin 8 → ℝ, setMixtureEnergyENNReal (dPlusSet 8) ν x≠∞) →
      ∀ x : Fin 8 → ℝ, IsMixtureColdSpot (dPlusSet 8) ν x ↔ IsDeepHole (dPlusSet 8) x) ∧
    ((∀ x : zeroSumSpace, e7MixtureEnergyENNReal ν x≠∞) →
      ∀ x : zeroSumSpace, (∀ y, e7MixtureEnergy ν x ≤ e7MixtureEnergy ν y) ↔ IsE7DeepHole x) ∧
    ((∀ x : Fin 16 → ℝ, setMixtureEnergyENNReal bw16Set ν x≠∞) →
      ∀ x : Fin 16 → ℝ, IsMixtureColdSpot bw16Set ν x ↔ IsDeepHole bw16Set x) ∧
    (∀ n : ℕ, 8 ≤ n → Even n →
      (∀ x : Fin n → ℝ, setMixtureEnergyENNReal (dPlusSet n) ν x≠∞) →
      ∀ x : Fin n → ℝ, IsMixtureColdSpot (dPlusSet n) ν x ↔ IsDeepHole (dPlusSet n) x) :=
  ⟨fun hconv x ↦ mixture_coldSpot_E6_iff_deepHole ν hν hconv x,
   fun hconv x ↦ mixture_coldSpot_E8_iff_deepHole ν hν hconv x,
   fun hconv x ↦ mixture_coldSpot_E7_dual_iff_deepHole ν hν hconv x,
   fun hconv x ↦ mixture_coldSpot_bw16_iff_deepHole ν hν hconv x,
   fun _ hn heven hconv x ↦ mixture_coldSpot_dPlus_iff_deepHole hn heven ν hν hconv x⟩

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.lattice_theorem_1_1
#print axioms PaperVerification.ColdSpots.lattice_covering_radius_table
#print axioms PaperVerification.ColdSpots.lattice_translation_class_table
#print axioms PaperVerification.ColdSpots.lattice_corollary_1_2
end
end Source_LatticePaperTheorems
-- END ORIGINAL PaperVerification.LatticePaperTheorems


-- BEGIN ORIGINAL PaperVerification.E8E7Normalization
section Source_E8E7Normalization

-- original header: module

-- original header: public import PaperVerification.E8IntegralBasis
-- original header: public import PaperVerification.E7Roots


-- original header: @[expose] public section
/-! # Minimal squared norm of the E8 and E7 root lattices

The coordinate lattices used by the principal cold-spot endpoints have exactly
the root normalization printed in the paper.  E7* is already identified with
the ordinary integral dual of this E7 lattice in its Euclidean hyperplane.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem sqDist_zero_pos_of_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < sqDist x 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  unfold sqDist
  simp only [Pi.zero_apply, sub_zero]
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem e8_nonzero_squared_norm_lower {x : Fin 8 → ℝ}
    (hx : x ∈ dPlusSet 8) (hne : x ≠ 0) : 2 ≤ sqDist x 0 := by
  obtain ⟨t, rfl⟩ := (e8_mem_iff_integer_root_coordinates x).mp hx
  have hp := sqDist_zero_pos_of_ne_zero hne
  rw [e8RootSum_norm] at hp ⊢
  have hq : 0 < e8IntegralQ t := by exact_mod_cast (by linarith : (0 : ℝ) < e8IntegralQ t)
  have hq' : (1 : ℝ) ≤ e8IntegralQ t := by exact_mod_cast (by omega : (1 : ℤ) ≤ e8IntegralQ t)
  linarith

theorem e8_minimal_squared_norm :
    (∀ x ∈ dPlusSet 8, x ≠ 0 → 2 ≤ sqDist x 0) ∧
      ∃ x ∈ dPlusSet 8, x ≠ 0 ∧ sqDist x 0 = 2 := by
  refine ⟨fun _ hx hne => e8_nonzero_squared_norm_lower hx hne,
    e8SimpleRoot 1, e8SimpleRoot_mem 1, ?_, ?_⟩
  · intro h
    have he := congrFun h 0
    norm_num [e8SimpleRoot] at he
  · norm_num [sqDist, e8SimpleRoot, Fin.sum_univ_succ]

theorem e7_minimal_squared_norm :
    (∀ x ∈ e7Set, x ≠ 0 → 2 ≤ sqDist x.val 0) ∧
      ∃ x ∈ e7Set, x ≠ 0 ∧ sqDist x.val 0 = 2 := by
  constructor
  · intro x hx hne
    apply e8_nonzero_squared_norm_lower hx
    intro h
    exact hne (Subtype.ext h)
  · refine ⟨e7SimpleRoot 1, e7SimpleRoot_mem 1, ?_, ?_⟩
    · intro h
      have he := congrArg (fun x : zeroSumSpace => x.val 0) h
      norm_num [e7SimpleRoot, e7RootVector] at he
    · norm_num [sqDist, e7SimpleRoot, e7RootVector, Fin.sum_univ_succ]

end PaperVerification.ColdSpots
end
end Source_E8E7Normalization
-- END ORIGINAL PaperVerification.E8E7Normalization


-- BEGIN ORIGINAL PaperVerification.TriangularComplexMeaning
section Source_TriangularComplexMeaning

-- original header: module

-- original header: public import PaperVerification.TriangularMinimum
-- original header: public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- original header: public import Mathlib.Algebra.Ring.Subring.Basic


-- original header: @[expose] public section
/-!
# Literal complex meaning of the cubic theta theorem

The Eisenstein-coordinate theorem is transported by an explicit bijection onto
the whole complex plane.  The Gaussian is the actual sum over Z[ω], the scale
is its ordinary complex norm, and the equality set is exactly E+Zc.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def triComplexInverse (z : ℂ) : TriPoint :=
  (z.re + z.im / Real.sqrt 3, 2 * z.im / Real.sqrt 3)

theorem triComplexInverse_apply (z : TriPoint) : triComplexInverse (triComplex z) = z := by
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  ext <;> simp [triComplexInverse, triComplex] <;> field_simp <;> ring

theorem triComplex_apply_inverse (z : ℂ) : triComplex (triComplexInverse z) = z := by
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  apply Complex.ext <;> simp [triComplexInverse, triComplex] <;> field_simp <;> ring

def triComplexEquiv : TriPoint ≃ ℂ where
  toFun := triComplex
  invFun := triComplexInverse
  left_inv := triComplexInverse_apply
  right_inv := triComplex_apply_inverse

@[simp] theorem triComplexEquiv_apply (z : TriPoint) :
    triComplexEquiv z = triComplex z := rfl

@[simp] theorem triComplex_zero : triComplex 0 = 0 := by simp [triComplex]

theorem triComplex_add (z w : TriPoint) :
    triComplex (z + w) = triComplex z + triComplex w := by
  apply Complex.ext <;> simp [triComplex] <;> ring

theorem triComplex_sub (z w : TriPoint) :
    triComplex (z - w) = triComplex z - triComplex w := by
  apply Complex.ext <;> simp [triComplex] <;> ring

theorem triComplex_smul (r : ℝ) (z : TriPoint) :
    triComplex (r • z) = (r : ℂ) * triComplex z := by
  apply Complex.ext <;> simp [triComplex] <;> ring

theorem eisensteinOmega_eq_exp :
    eisensteinOmega = Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  have he : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, he, Real.cos_pi_sub, Real.cos_pi_div_three]
    simp [eisensteinOmega, triComplex]
  · rw [Complex.exp_ofReal_mul_I_im, he, Real.sin_pi_sub, Real.sin_pi_div_three]
    simp [eisensteinOmega, triComplex]

def eisensteinTheta : ℂ := 1 + 2 * eisensteinOmega

def eisensteinC : ℂ := (1 - eisensteinOmega) / 3

theorem eisensteinTheta_eq : eisensteinTheta = Complex.I * (Real.sqrt 3 : ℂ) := by
  apply Complex.ext <;> simp [eisensteinTheta, eisensteinOmega, triComplex] <;> ring

theorem triComplex_c : triComplex triC = eisensteinC := by
  apply Complex.ext <;> simp [triComplex, triC, eisensteinC, eisensteinOmega] <;> ring

theorem triComplex_theta (z : TriPoint) :
    triComplex (triTheta z) = eisensteinTheta * triComplex z := by
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [eisensteinTheta_eq]
  apply Complex.ext
  · simp only [triComplex, triTheta, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
      zero_add, add_zero, one_mul, sub_zero, zero_sub]
    nlinarith only [congrArg (fun t : ℝ => t * z.2) hs]
  · simp only [triComplex, triTheta, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, zero_add, add_zero, one_mul, sub_zero, zero_sub]
    ring

/-- The literal Eisenstein lattice Z+Zω in the complex plane. -/
def eisensteinSet : Set ℂ :=
  {z | ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * eisensteinOmega}

theorem eisensteinOmega_square : eisensteinOmega ^ 2 = -1 - eisensteinOmega := by
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [eisensteinOmega, triComplex, pow_two]
    nlinarith only [hs]
  · simp [eisensteinOmega, triComplex, pow_two]
    ring

def eisensteinSubring : Subring ℂ where
  carrier := eisensteinSet
  zero_mem' := ⟨0,0,by simp⟩
  one_mem' := ⟨1,0,by simp⟩
  add_mem' := by
    rintro z w ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    exact ⟨a+c,b+d,by push_cast; ring⟩
  neg_mem' := by
    rintro z ⟨a,b,rfl⟩
    exact ⟨-a,-b,by push_cast; ring⟩
  mul_mem' := by
    rintro z w ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    refine ⟨a*c-b*d,a*d+b*c-b*d,?_⟩
    push_cast
    linear_combination (b : ℂ) * (d : ℂ) * eisensteinOmega_square

/-- The concrete two-coordinate lattice is exactly the unital subring
generated by ω, hence literally Z[ω]. -/
theorem eisensteinSet_eq_generated_ring :
    eisensteinSet = (Subring.closure ({eisensteinOmega} : Set ℂ) : Set ℂ) := by
  have hω : eisensteinOmega ∈ eisensteinSubring := ⟨0,1,by simp⟩
  have hleft : Subring.closure ({eisensteinOmega} : Set ℂ) ≤ eisensteinSubring :=
    Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hω)
  apply Set.Subset.antisymm
  · rintro z ⟨a,b,rfl⟩
    exact (Subring.closure ({eisensteinOmega} : Set ℂ)).add_mem
      (intCast_mem (Subring.closure ({eisensteinOmega} : Set ℂ)) a)
      ((Subring.closure _).mul_mem (intCast_mem (Subring.closure ({eisensteinOmega} : Set ℂ)) b)
        (Subring.subset_closure (Set.mem_singleton _)))
  · exact hleft

theorem triComplex_eisEmbed (m : EisInt) :
    triComplex (eisEmbed m) = (m.1 : ℂ) + (m.2 : ℂ) * eisensteinOmega := by
  rw [triComplex_coordinates]
  change (((m.1 : ℝ) : ℂ) + ((m.2 : ℝ) : ℂ) * eisensteinOmega) = _
  simp only [Complex.ofReal_intCast]

def eisensteinComplexIndexEquiv : EisInt ≃ eisensteinSet :=
  Equiv.ofBijective
    (fun m => ⟨triComplex (eisEmbed m), m.1, m.2, triComplex_eisEmbed m⟩)
    ⟨by
      intro m k h
      exact eisEmbed_injective (triComplexEquiv.injective (congrArg Subtype.val h)), by
      rintro ⟨z, a, b, rfl⟩
      exact ⟨(a,b), Subtype.ext (triComplex_eisEmbed (a,b))⟩⟩

def eisensteinGaussian (α : ℝ) (z : ℂ) : ℝ :=
  ∑' m : eisensteinSet, Real.exp (-α * ‖m.val - z‖ ^ 2)

theorem eisensteinGaussian_eq_triangular (α : ℝ) (z : TriPoint) :
    eisensteinGaussian α (triComplex z) = triangularGaussian α z := by
  unfold eisensteinGaussian triangularGaussian
  rw [← eisensteinComplexIndexEquiv.tsum_eq]
  apply tsum_congr
  intro m
  change Real.exp (-α * ‖triComplex (eisEmbed m) - triComplex z‖ ^ 2) = _
  rw [← triComplex_sub, ← triQ_eq_norm_sq]

theorem summable_eisensteinGaussian {α : ℝ} (hα : 0 < α) (z : ℂ) :
    Summable (fun m : eisensteinSet => Real.exp (-α * ‖m.val - z‖ ^ 2)) := by
  obtain ⟨w, rfl⟩ := triComplexEquiv.surjective z
  apply (eisensteinComplexIndexEquiv.summable_iff
    (f := fun m : eisensteinSet => Real.exp (-α * ‖m.val - triComplex w‖ ^ 2))).mp
  convert summable_triangularGaussian hα w using 1
  funext m
  change Real.exp (-α * ‖triComplex (eisEmbed m) - triComplex w‖ ^ 2) = _
  rw [← triComplex_sub, ← triQ_eq_norm_sq]

theorem triPhase_complex_iff (z : TriPoint) : TriPhase z ↔
    ∃ m ∈ eisensteinSet, ∃ k : ℤ, triComplex z = m + (k : ℂ) * eisensteinC := by
  rw [triPhase_iff_integer_multiple]
  constructor
  · rintro ⟨m, k, rfl⟩
    refine ⟨triComplex (eisEmbed m), ⟨m.1,m.2,triComplex_eisEmbed m⟩, k, ?_⟩
    rw [triComplex_add, triComplex_smul, triComplex_c]
    simp only [Complex.ofReal_intCast]
  · rintro ⟨m, ⟨a,b,hm⟩, k, hz⟩
    refine ⟨(a,b), k, ?_⟩
    apply triComplexEquiv.injective
    simp only [triComplexEquiv_apply]
    rw [triComplex_add, triComplex_smul, triComplex_c, triComplex_eisEmbed]
    simpa only [Complex.ofReal_intCast, hm] using hz

/-- Proposition 8.1, equation (30), on the whole complex plane with the
ordinary complex Gaussian and the printed Eisenstein constants. -/
theorem eisenstein_cubic_identity {α : ℝ} (hα : 0 < α) (z : ℂ) :
    eisensteinGaussian α z * eisensteinGaussian α (z + eisensteinC) *
        eisensteinGaussian α (z - eisensteinC) =
      eisensteinGaussian α eisensteinC / 3 *
        (eisensteinGaussian α 0 *
          (eisensteinGaussian α (eisensteinTheta * z + eisensteinC) +
            eisensteinGaussian α (eisensteinTheta * z - eisensteinC)) +
          eisensteinGaussian α eisensteinC * eisensteinGaussian α (eisensteinTheta * z)) := by
  obtain ⟨w, rfl⟩ := triComplexEquiv.surjective z
  simp only [triComplexEquiv_apply]
  rw [← triComplex_c, ← triComplex_zero, ← triComplex_theta,
    ← triComplex_add, ← triComplex_sub, ← triComplex_add, ← triComplex_sub]
  simp only [eisensteinGaussian_eq_triangular]
  exact triangular_cubic_identity hα w

/-- Proposition 8.1's sharp bound, with no restriction on the complex point. -/
theorem eisenstein_product_minimum {α : ℝ} (hα : 0 < α) (z : ℂ) :
    eisensteinGaussian α 0 * eisensteinGaussian α eisensteinC ^ 2 ≤
      eisensteinGaussian α z * eisensteinGaussian α (z + eisensteinC) *
        eisensteinGaussian α (z - eisensteinC) := by
  obtain ⟨w, rfl⟩ := triComplexEquiv.surjective z
  simp only [triComplexEquiv_apply]
  rw [← triComplex_zero, ← triComplex_c, ← triComplex_add, ← triComplex_sub]
  simp only [eisensteinGaussian_eq_triangular]
  exact triangularProduct_minimum hα w

/-- Proposition 8.1's complete equality set E+Zc, including all translates. -/
theorem eisenstein_product_equality_iff {α : ℝ} (hα : 0 < α) (z : ℂ) :
    eisensteinGaussian α z * eisensteinGaussian α (z + eisensteinC) *
        eisensteinGaussian α (z - eisensteinC) =
      eisensteinGaussian α 0 * eisensteinGaussian α eisensteinC ^ 2 ↔
        ∃ m ∈ eisensteinSet, ∃ k : ℤ, z = m + (k : ℂ) * eisensteinC := by
  obtain ⟨w, rfl⟩ := triComplexEquiv.surjective z
  simp only [triComplexEquiv_apply]
  rw [← triPhase_complex_iff w]
  rw [← triComplex_zero, ← triComplex_c, ← triComplex_add, ← triComplex_sub]
  simp only [eisensteinGaussian_eq_triangular]
  exact triangularProduct_equality_iff hα w

end PaperVerification.ColdSpots
end
end Source_TriangularComplexMeaning
-- END ORIGINAL PaperVerification.TriangularComplexMeaning


-- Kernel-environment audit: every mathematical source body precedes this command.
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let kenv := env.checked.get
  let entries := kenv.constants.foldStage2
    (fun rows name ci => rows.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let kind : ConstantInfo → String := fun ci => match ci with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  let mut failures : Array Json := #[]
  for (name, ci) in entries do
    if ci.isUnsafe then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unsafe_declaration", toJson true)])
    let deps := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
    let mut dependencyRows : Array Json := #[]
    for dep in deps do
      match kenv.find? dep with
      | none =>
        failures := failures.push (Json.mkObj [
          ("declaration", toJson name.toString),
          ("missing_dependency", toJson dep.toString)])
      | some info =>
        let origin := match env.getModuleIdxFor? dep with
          | some idx => env.header.moduleNames[idx]!.toString
          | none => env.mainModule.toString
        dependencyRows := dependencyRows.push (Json.mkObj [
          ("name", toJson dep.toString), ("kind", toJson (kind info)),
          ("module", toJson origin)])
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun ax => !allowed.contains ax)
    if !bad.isEmpty then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unapproved_axioms", toJson (bad.map Name.toString))])
    rows := rows.push (Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson (kind ci)),
      ("unsafe", toJson ci.isUnsafe),
      ("type", toJson (toString ci.type)),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("has_body", toJson (ci.value? (allowOpaque := true)).isSome),
      ("dependencies", Json.arr dependencyRows),
      ("axioms", toJson (axioms.map Name.toString))])
  let sourceHash ← IO.getEnv "PAPER_VERIFICATION_SOURCE_SHA256"
  let fingerprint ← IO.getEnv "PAPER_VERIFICATION_FINGERPRINT"
  let document := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("module", toJson env.mainModule.toString),
    ("source_sha256", toJson sourceHash),
    ("fingerprint", toJson fingerprint),
    ("kernel_environment", toJson true),
    ("declarations", Json.arr rows),
    ("failures", Json.arr failures),
    ("passed", toJson failures.isEmpty)]
  let target := (← IO.getEnv "PAPER_VERIFICATION_AUDIT_PATH").getD ".lake/build/paper-audit/PaperVerification_Lattice007.json"
  let path : System.FilePath := target
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (document.compress ++ "\n")
  if !failures.isEmpty then
    throwError "Kernel declaration audit rejected {failures.size} dependency/axiom findings; see {target}"
  logInfo m!"Kernel declaration audit passed for {rows.size} declarations; see {target}"
