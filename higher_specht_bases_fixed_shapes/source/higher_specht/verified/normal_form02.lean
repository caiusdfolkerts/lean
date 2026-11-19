module

public import higher_specht.verified.normal_form01

/- Generated ordinary proof stage. See audit/staged_specht_normal_form/NormalForm02/manifest.json. -/

@[expose] public section

section CanonicalSource10
/- Source: HigherSpecht/LascouxWordStrings.lean -/



/-!
# Actual rank-one crystal strings on finite words

The signature convention pairs an occurrence of `r+1` with a later occurrence
of `r`. The unpaired word is therefore `r^p (r+1)^q`. Lowering changes the
rightmost unpaired `r` to `r+1`; raising is its actual partial inverse.

The tensor construction is the rank-one specialization of Kashiwara's normal
crystal rule (compare the pinned TauCeti Crystal/Tensor module). This file proves
word-level injective weight balancing. Preservation of tableau shape and the
catabolism image condition are separate obligations, not premises hidden in a
claimed higher Specht basis theorem.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

structure StringSystem (A : Type*) where
  raise : A → Option A
  lower : A → Option A
  epsilon : A → ℕ
  phi : A → ℕ
  lower_eq_some_iff {x y : A} : lower x = some y ↔ raise y = some x
  epsilon_zero_iff {x : A} : epsilon x = 0 ↔ raise x = none
  epsilon_raise {x y : A} : raise x = some y → epsilon y + 1 = epsilon x
  phi_zero_iff {x : A} : phi x = 0 ↔ lower x = none
  phi_raise {x y : A} : raise x = some y → phi y = phi x + 1

namespace StringSystem

variable {A B : Type*}

theorem epsilon_lower (c : StringSystem A) {x y : A} (h : c.lower x = some y) :
    c.epsilon y = c.epsilon x + 1 :=
  (c.epsilon_raise (c.lower_eq_some_iff.mp h)).symm

theorem phi_lower (c : StringSystem A) {x y : A} (h : c.lower x = some y) :
    c.phi y + 1 = c.phi x :=
  (c.phi_raise (c.lower_eq_some_iff.mp h)).symm

def tensor (c : StringSystem A) (d : StringSystem B) : StringSystem (A × B) where
  raise x := if d.epsilon x.2 ≤ c.phi x.1 then
    (c.raise x.1).map (fun y => (y, x.2)) else (d.raise x.2).map (fun y => (x.1, y))
  lower x := if d.epsilon x.2 < c.phi x.1 then
    (c.lower x.1).map (fun y => (y, x.2)) else (d.lower x.2).map (fun y => (x.1, y))
  epsilon x := c.epsilon x.1 + (d.epsilon x.2 - c.phi x.1)
  phi x := d.phi x.2 + (c.phi x.1 - d.epsilon x.2)
  lower_eq_some_iff {x y} := by
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    dsimp only
    constructor
    · intro h
      split_ifs at h with hx
      · obtain ⟨z, hz, hzy⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzy
        have := c.phi_lower hz
        rw [if_pos (by omega), c.lower_eq_some_iff.mp hz, Option.map_some]
      · obtain ⟨z, hz, hzy⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzy
        have := d.epsilon_lower hz
        rw [if_neg (by omega), d.lower_eq_some_iff.mp hz, Option.map_some]
    · intro h
      split_ifs at h with hy
      · obtain ⟨z, hz, hzx⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzx
        have := c.phi_raise hz
        rw [if_pos (by omega), c.lower_eq_some_iff.mpr hz, Option.map_some]
      · obtain ⟨z, hz, hzx⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzx
        have := d.epsilon_raise hz
        rw [if_neg (by omega), d.lower_eq_some_iff.mpr hz, Option.map_some]
  epsilon_zero_iff {x} := by
    rcases x with ⟨x₁, x₂⟩
    dsimp only
    split_ifs with h
    · rw [Option.map_eq_none_iff, ← c.epsilon_zero_iff]
      omega
    · rw [Option.map_eq_none_iff, ← d.epsilon_zero_iff]
      omega
  epsilon_raise {x y} h := by
    rcases x with ⟨x₁, x₂⟩
    dsimp only at h ⊢
    split_ifs at h with hx
    · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      have := c.epsilon_raise hz
      have := c.phi_raise hz
      dsimp only
      omega
    · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      have := d.epsilon_raise hz
      dsimp only
      omega
  phi_zero_iff {x} := by
    rcases x with ⟨x₁, x₂⟩
    dsimp only
    split_ifs with h
    · rw [Option.map_eq_none_iff, ← c.phi_zero_iff]
      omega
    · rw [Option.map_eq_none_iff, ← d.phi_zero_iff]
      omega
  phi_raise {x y} h := by
    rcases x with ⟨x₁, x₂⟩
    dsimp only at h ⊢
    split_ifs at h with hx
    · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      have := c.phi_raise hz
      dsimp only
      omega
    · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      have := d.epsilon_raise hz
      have := d.phi_raise hz
      dsimp only
      omega

def transport (c : StringSystem A) (e : A ≃ B) : StringSystem B where
  raise x := (c.raise (e.symm x)).map e
  lower x := (c.lower (e.symm x)).map e
  epsilon x := c.epsilon (e.symm x)
  phi x := c.phi (e.symm x)
  lower_eq_some_iff {x y} := by
    constructor
    · intro h
      obtain ⟨z, hz, hzy⟩ := Option.map_eq_some_iff.mp h
      rw [← hzy, Equiv.symm_apply_apply, c.lower_eq_some_iff.mp hz,
        Option.map_some, Equiv.apply_symm_apply]
    · intro h
      obtain ⟨z, hz, hzx⟩ := Option.map_eq_some_iff.mp h
      rw [← hzx, Equiv.symm_apply_apply, c.lower_eq_some_iff.mpr hz,
        Option.map_some, Equiv.apply_symm_apply]
  epsilon_zero_iff := by intro x; simp only [Option.map_eq_none_iff, c.epsilon_zero_iff]
  epsilon_raise h := by
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa only [Equiv.symm_apply_apply] using c.epsilon_raise hz
  phi_zero_iff := by intro x; simp only [Option.map_eq_none_iff, c.phi_zero_iff]
  phi_raise h := by
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa only [Equiv.symm_apply_apply] using c.phi_raise hz

def lowerValue (c : StringSystem A) (x : {x : A // 0 < c.phi x}) : A :=
  (c.lower x.val).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro h
    exact x.property.ne' (c.phi_zero_iff.mpr h))

theorem lowerValue_spec (c : StringSystem A) (x : {x : A // 0 < c.phi x}) :
    c.lower x.val = some (c.lowerValue x) := (Option.some_get _).symm

/-- A genuine injection along a lowering edge wherever a lowering edge exists. -/
def lowerEmbedding (c : StringSystem A) : {x : A // 0 < c.phi x} ↪ A where
  toFun := c.lowerValue
  inj' x y hxy := by
    have hx := c.lowerValue_spec x
    have hy := c.lowerValue_spec y
    have hx' := c.lower_eq_some_iff.mp hx
    have hy' := c.lower_eq_some_iff.mp hy
    rw [hxy, hy'] at hx'
    exact Subtype.ext (Option.some.inj hx'.symm)

end StringSystem

/-- The one-letter signature crystal at adjacent letters `r` and `r+1`. -/
def letterString (r : ℕ) : StringSystem ℕ where
  raise a := if a = r + 1 then some r else none
  lower a := if a = r then some (r + 1) else none
  epsilon a := if a = r + 1 then 1 else 0
  phi a := if a = r then 1 else 0
  lower_eq_some_iff {x y} := by
    by_cases hx : x = r <;> by_cases hy : y = r + 1 <;> simp_all [eq_comm]
  epsilon_zero_iff := by intros; split_ifs <;> simp_all
  epsilon_raise := by intros; split_ifs at * <;> simp_all <;> omega
  phi_zero_iff := by intros; split_ifs <;> simp_all
  phi_raise := by intros; split_ifs at * <;> simp_all <;> omega

@[simp] theorem letterString_raise (r a : ℕ) :
    (letterString r).raise a = if a = r + 1 then some r else none := rfl

@[simp] theorem letterString_lower (r a : ℕ) :
    (letterString r).lower a = if a = r then some (r + 1) else none := rfl

@[simp] theorem letterString_epsilon (r a : ℕ) :
    (letterString r).epsilon a = if a = r + 1 then 1 else 0 := rfl

@[simp] theorem letterString_phi (r a : ℕ) :
    (letterString r).phi a = if a = r then 1 else 0 := rfl

def emptyWordString : StringSystem (Fin 0 → ℕ) where
  raise _ := none
  lower _ := none
  epsilon _ := 0
  phi _ := 0
  lower_eq_some_iff := by simp
  epsilon_zero_iff := by simp
  epsilon_raise := by simp
  phi_zero_iff := by simp
  phi_raise := by simp

def tailHeadEquiv (n : ℕ) : ((Fin n → ℕ) × ℕ) ≃ (Fin (n + 1) → ℕ) where
  toFun x := Fin.cons x.2 x.1
  invFun u := (Fin.tail u, u 0)
  left_inv x := by cases x; rfl
  right_inv u := Fin.cons_self_tail u

/-- Reversing the tensor-factor order implements the manuscript's pairing
of `r+1` to a subsequent `r`, with no choice of a different signature convention. -/
def wordString (r : ℕ) : (n : ℕ) → StringSystem (Fin n → ℕ)
  | 0 => emptyWordString
  | n + 1 => ((wordString r n).tensor (letterString r)).transport (tailHeadEquiv n)

theorem wordString_balance (r n : ℕ) (u : Fin n → ℕ) :
    ((wordString r n).phi u : ℤ) - (wordString r n).epsilon u =
      ((List.ofFn u).count r : ℤ) - (List.ofFn u).count (r + 1) := by
  induction n with
  | zero => simp [wordString, emptyWordString]
  | succ n ih =>
      have h := ih (Fin.tail u)
      change
        (((letterString r).phi (u 0) +
          ((wordString r n).phi (Fin.tail u) - (letterString r).epsilon (u 0)) : ℕ) : ℤ) -
          ((((wordString r n).epsilon (Fin.tail u) +
            ((letterString r).epsilon (u 0) - (wordString r n).phi (Fin.tail u))) : ℕ) : ℤ) = _
      have hword : List.ofFn u = u 0 :: List.ofFn (Fin.tail u) := List.ofFn_succ
      rw [hword, List.count_cons, List.count_cons]
      by_cases h0 : u 0 = r <;> by_cases h1 : u 0 = r + 1 <;>
        simp [letterString, h0, h1] at * <;> omega

theorem wordString_lower_cons (r n a : ℕ) (u : Fin n → ℕ) :
    (wordString r (n + 1)).lower (Fin.cons a u) =
      if (letterString r).epsilon a < (wordString r n).phi u then
        ((wordString r n).lower u).map (Fin.cons a)
      else ((letterString r).lower a).map (fun b => Fin.cons b u) := by
  simp only [wordString, StringSystem.transport, StringSystem.tensor,
    tailHeadEquiv, Equiv.coe_fn_symm_mk, Fin.tail_cons, Fin.cons_zero, Equiv.coe_fn_mk]
  split_ifs <;> simp only [Option.map_map, Function.comp_def]

theorem wordString_raise_cons (r n a : ℕ) (u : Fin n → ℕ) :
    (wordString r (n + 1)).raise (Fin.cons a u) =
      if (letterString r).epsilon a ≤ (wordString r n).phi u then
        ((wordString r n).raise u).map (Fin.cons a)
      else ((letterString r).raise a).map (fun b => Fin.cons b u) := by
  simp only [wordString, StringSystem.transport, StringSystem.tensor,
    tailHeadEquiv, Equiv.coe_fn_symm_mk, Fin.tail_cons, Fin.cons_zero, Equiv.coe_fn_mk]
  split_ifs <;> simp only [Option.map_map, Function.comp_def]

theorem wordString_lower_changes_one (r n : ℕ) {u v : Fin n → ℕ}
    (h : (wordString r n).lower u = some v) :
    ∃ i : Fin n, u i = r ∧ v = Function.update u i (r + 1) := by
  induction n with
  | zero => simpa only [wordString, emptyWordString, reduceCtorEq] using h
  | succ n ih =>
      have hu : Fin.cons (u 0) (Fin.tail u) = u := Fin.cons_self_tail u
      rw [← hu, wordString_lower_cons] at h
      split_ifs at h with ht
      · obtain ⟨w, hw, hv⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨i, hi, heq⟩ := ih hw
        refine ⟨i.succ, hi, ?_⟩
        rw [← hv, heq, Fin.cons_update, hu]
      · obtain ⟨a, ha, hv⟩ := Option.map_eq_some_iff.mp h
        have hua : u 0 = r ∧ a = r + 1 := by
          dsimp only [letterString] at ha
          split_ifs at ha with hur
          · exact ⟨hur, (Option.some.inj ha).symm⟩
        refine ⟨0, hua.1, ?_⟩
        rw [← hv, hua.2, ← hu, Fin.update_cons_zero, Fin.tail_cons]

def wordLoweringInjection (r n : ℕ) :
    {u : Fin n → ℕ // (List.ofFn u).count (r + 1) < (List.ofFn u).count r} ↪
      (Fin n → ℕ) :=
  { toFun := fun u => (wordString r n).lowerValue ⟨u.val, by
      have h := wordString_balance r n u.val
      have hu := u.property
      omega⟩
    inj' := by
      intro u v h
      apply Subtype.ext
      have h' := (wordString r n).lowerEmbedding.injective h
      exact congrArg (fun z : {w : Fin n → ℕ // 0 < (wordString r n).phi w} => z.val) h' }

theorem wordLoweringInjection_changes_one (r n : ℕ)
    (u : {u : Fin n → ℕ // (List.ofFn u).count (r + 1) < (List.ofFn u).count r}) :
    ∃ i : Fin n, u.val i = r ∧
      wordLoweringInjection r n u = Function.update u.val i (r + 1) := by
  have hp : 0 < (wordString r n).phi u.val := by
    have hb := wordString_balance r n u.val
    have hu := u.property
    omega
  apply wordString_lower_changes_one r n
  change (wordString r n).lower u.val =
    some ((wordString r n).lowerValue ⟨u.val, hp⟩)
  exact (wordString r n).lowerValue_spec ⟨u.val, hp⟩

end HigherSpecht.Lascoux
end
end CanonicalSource10

section CanonicalSource11
/- Source: HigherSpecht/LascouxStringReflections.lean -/



/-!
# Genuine reflections of the constructed crystal strings

The reflection reverses a finite raising/lowering string.  In particular it
fixes every middle vertex, and it is not a Bender--Knuth substitution.  The
construction is instantiated on the literal finite-word signature strings.
Tableau-shape preservation and the catabolism image theorem remain separate.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux.StringSystem

variable {A : Type*}

def reverse (c : StringSystem A) : StringSystem A where
  raise := c.lower
  lower := c.raise
  epsilon := c.phi
  phi := c.epsilon
  lower_eq_some_iff := c.lower_eq_some_iff.symm
  epsilon_zero_iff := c.phi_zero_iff
  epsilon_raise := c.phi_lower
  phi_zero_iff := c.epsilon_zero_iff
  phi_raise := c.epsilon_lower

@[simp] theorem reverse_epsilon (c : StringSystem A) (x : A) :
    c.reverse.epsilon x = c.phi x := rfl

@[simp] theorem reverse_phi (c : StringSystem A) (x : A) :
    c.reverse.phi x = c.epsilon x := rfl

@[simp] theorem reverse_lower (c : StringSystem A) (x : A) :
    c.reverse.lower x = c.raise x := rfl

@[simp] theorem reverse_raise (c : StringSystem A) (x : A) :
    c.reverse.raise x = c.lower x := rfl

@[simp] theorem reverse_reverse (c : StringSystem A) : c.reverse.reverse = c := rfl

def partialIterate (f : A → Option A) : ℕ → A → Option A
  | 0, x => some x
  | k + 1, x => (f x).bind (partialIterate f k)

theorem partialIterate_succ_last (f : A → Option A) (k : ℕ) (x : A) :
    partialIterate f (k + 1) x = (partialIterate f k x).bind f := by
  induction k generalizing x with
  | zero => cases h : f x <;> simp only [partialIterate, h, Option.bind_none, Option.bind_some]
  | succ k ih =>
      change (f x).bind (partialIterate f (k + 1)) =
        ((f x).bind (partialIterate f k)).bind f
      rw [Option.bind_assoc]
      congr 1
      funext y
      exact ih y

def lowerIterate (c : StringSystem A) : ℕ → A → Option A := partialIterate c.lower

theorem lowerIterate_stats (c : StringSystem A) {k : ℕ} {x y : A}
    (h : c.lowerIterate k x = some y) :
    c.epsilon y = c.epsilon x + k ∧ c.phi y + k = c.phi x := by
  induction k generalizing x with
  | zero =>
      have heq : x = y := Option.some.inj h
      subst y
      exact ⟨by omega, by omega⟩
  | succ k ih =>
      obtain ⟨z, hxz, hzy⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨he, hp⟩ := ih hzy
      have he' := c.epsilon_lower hxz
      have hp' := c.phi_lower hxz
      constructor <;> omega

theorem lowerIterate_exists_iff (c : StringSystem A) (k : ℕ) (x : A) :
    (∃ y, c.lowerIterate k x = some y) ↔ k ≤ c.phi x := by
  constructor
  · rintro ⟨y, hy⟩
    have := (c.lowerIterate_stats hy).2
    omega
  · intro hk
    induction k generalizing x with
    | zero => exact ⟨x, rfl⟩
    | succ k ih =>
        have hn : c.lower x ≠ none := by
          intro hzero
          have hz := c.phi_zero_iff.mpr hzero
          omega
        obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp hn
        have hp := c.phi_lower hz
        obtain ⟨y, hy⟩ := ih z (by omega)
        exact ⟨y, Option.bind_eq_some_iff.mpr ⟨z, hz, hy⟩⟩

theorem lowerIterate_reverse_iff (c : StringSystem A) (k : ℕ) (x y : A) :
    c.lowerIterate k x = some y ↔ c.reverse.lowerIterate k y = some x := by
  induction k generalizing x y with
  | zero => simp only [lowerIterate, partialIterate, Option.some.injEq, eq_comm]
  | succ k ih =>
      change (c.lower x).bind (c.lowerIterate k) = some y ↔
        c.reverse.lowerIterate (k + 1) y = some x
      rw [show c.reverse.lowerIterate (k + 1) y =
        (c.reverse.lowerIterate k y).bind c.raise from
          partialIterate_succ_last c.raise k y]
      simp only [Option.bind_eq_some_iff]
      constructor
      · rintro ⟨z, hxz, hzy⟩
        exact ⟨z, (ih z y).mp hzy, c.lower_eq_some_iff.mp hxz⟩
      · rintro ⟨z, hyz, hzx⟩
        exact ⟨z, c.lower_eq_some_iff.mpr hzx, (ih z y).mpr hyz⟩

def lowerAt (c : StringSystem A) (k : ℕ) (x : A) (hk : k ≤ c.phi x) : A :=
  Classical.choose ((c.lowerIterate_exists_iff k x).mpr hk)

theorem lowerAt_spec (c : StringSystem A) (k : ℕ) (x : A) (hk : k ≤ c.phi x) :
    c.lowerIterate k x = some (c.lowerAt k x hk) :=
  Classical.choose_spec ((c.lowerIterate_exists_iff k x).mpr hk)

theorem lowerAt_zero (c : StringSystem A) (x : A) :
    c.lowerAt 0 x (Nat.zero_le _) = x := by
  exact (Option.some.inj (c.lowerAt_spec 0 x (Nat.zero_le _))).symm

theorem lowerAt_stats (c : StringSystem A) (k : ℕ) (x : A) (hk : k ≤ c.phi x) :
    c.epsilon (c.lowerAt k x hk) = c.epsilon x + k ∧
      c.phi (c.lowerAt k x hk) + k = c.phi x :=
  c.lowerIterate_stats (c.lowerAt_spec k x hk)

theorem lowerAt_reverse (c : StringSystem A) (k : ℕ) (x : A) (hk : k ≤ c.phi x)
    (hk' : k ≤ c.epsilon (c.lowerAt k x hk)) :
    c.reverse.lowerAt k (c.lowerAt k x hk) hk' = x := by
  have h := (c.lowerIterate_reverse_iff k x (c.lowerAt k x hk)).mp
    (c.lowerAt_spec k x hk)
  have h' := c.reverse.lowerAt_spec k (c.lowerAt k x hk) hk'
  rw [h] at h'
  exact (Option.some.inj h').symm

def reflection (c : StringSystem A) (x : A) : A :=
  if h : c.epsilon x ≤ c.phi x then
    c.lowerAt (c.phi x - c.epsilon x) x (Nat.sub_le _ _)
  else c.reverse.lowerAt (c.epsilon x - c.phi x) x (Nat.sub_le _ _)

theorem reflection_epsilon (c : StringSystem A) (x : A) :
    c.epsilon (c.reflection x) = c.phi x := by
  unfold reflection
  split_ifs with h
  · have hs := c.lowerAt_stats (c.phi x - c.epsilon x) x (Nat.sub_le _ _)
    omega
  · have hs := c.reverse.lowerAt_stats (c.epsilon x - c.phi x) x (Nat.sub_le _ _)
    simp only [reverse_epsilon, reverse_phi] at hs
    omega

theorem reflection_phi (c : StringSystem A) (x : A) :
    c.phi (c.reflection x) = c.epsilon x := by
  unfold reflection
  split_ifs with h
  · have hs := c.lowerAt_stats (c.phi x - c.epsilon x) x (Nat.sub_le _ _)
    omega
  · have hs := c.reverse.lowerAt_stats (c.epsilon x - c.phi x) x (Nat.sub_le _ _)
    simp only [reverse_epsilon, reverse_phi] at hs
    omega

theorem reflection_eq_self_of_middle (c : StringSystem A) {x : A}
    (hx : c.epsilon x = c.phi x) : c.reflection x = x := by
  rw [reflection, dif_pos hx.le]
  have hsub : c.phi x - c.epsilon x = 0 := by omega
  simpa only [hsub] using c.lowerAt_zero x

theorem reflection_involutive (c : StringSystem A) : Function.Involutive c.reflection := by
  intro x
  rcases lt_trichotomy (c.epsilon x) (c.phi x) with h | h | h
  · have hy : ¬ c.epsilon (c.reflection x) ≤ c.phi (c.reflection x) := by
      rw [c.reflection_epsilon, c.reflection_phi]
      omega
    have he : c.reflection x = c.lowerAt (c.phi x - c.epsilon x) x (Nat.sub_le _ _) :=
      dif_pos h.le
    have hforward : c.lowerIterate (c.phi x - c.epsilon x) x = some (c.reflection x) := by
      rw [he]
      exact c.lowerAt_spec _ _ _
    have hback := (c.lowerIterate_reverse_iff _ x (c.reflection x)).mp hforward
    have hsecond := c.reverse.lowerAt_spec
      (c.epsilon (c.reflection x) - c.phi (c.reflection x)) (c.reflection x) (Nat.sub_le _ _)
    have he' : c.reflection (c.reflection x) = c.reverse.lowerAt
        (c.epsilon (c.reflection x) - c.phi (c.reflection x)) (c.reflection x)
        (Nat.sub_le _ _) := dif_neg hy
    rw [← he'] at hsecond
    simp only [c.reflection_epsilon, c.reflection_phi] at hsecond
    exact Option.some.inj (hsecond.symm.trans hback)
  · rw [c.reflection_eq_self_of_middle h, c.reflection_eq_self_of_middle h]
  · have hy : c.epsilon (c.reflection x) ≤ c.phi (c.reflection x) := by
      rw [c.reflection_epsilon, c.reflection_phi]
      omega
    have he : c.reflection x =
        c.reverse.lowerAt (c.epsilon x - c.phi x) x (Nat.sub_le _ _) :=
      dif_neg (not_le_of_gt h)
    have hforward : c.reverse.lowerIterate (c.epsilon x - c.phi x) x =
        some (c.reflection x) := by
      rw [he]
      exact c.reverse.lowerAt_spec _ _ _
    have hback := (c.reverse.lowerIterate_reverse_iff _ x (c.reflection x)).mp hforward
    have hsecond := c.lowerAt_spec
      (c.phi (c.reflection x) - c.epsilon (c.reflection x)) (c.reflection x) (Nat.sub_le _ _)
    have he' : c.reflection (c.reflection x) = c.lowerAt
        (c.phi (c.reflection x) - c.epsilon (c.reflection x)) (c.reflection x)
        (Nat.sub_le _ _) := dif_pos hy
    rw [← he'] at hsecond
    simp only [c.reflection_epsilon, c.reflection_phi] at hsecond
    exact Option.some.inj (hsecond.symm.trans hback)

def reflectionEquiv (c : StringSystem A) : A ≃ A where
  toFun := c.reflection
  invFun := c.reflection
  left_inv := c.reflection_involutive
  right_inv := c.reflection_involutive

end HigherSpecht.Lascoux.StringSystem

namespace HigherSpecht.Lascoux

theorem word_count_update_balance (n a b : ℕ) (u : Fin n → ℕ) (i : Fin n) :
    (List.ofFn (Function.update u i b)).count a + (if u i = a then 1 else 0) =
      (List.ofFn u).count a + (if b = a then 1 else 0) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [show List.ofFn (Function.update u 0 b) =
            Function.update u 0 b 0 :: List.ofFn (Fin.tail (Function.update u 0 b)) from
              List.ofFn_succ,
          show List.ofFn u = u 0 :: List.ofFn (Fin.tail u) from List.ofFn_succ,
          Fin.tail_update_zero, Function.update_self, List.count_cons, List.count_cons]
        by_cases h1 : u 0 = a <;> by_cases h2 : b = a <;> simp_all <;> omega
      · have ht := ih (Fin.tail u) j
        change (List.ofFn (Function.update (Fin.tail u) j b)).count a +
            (if u j.succ = a then 1 else 0) =
          (List.ofFn (Fin.tail u)).count a + (if b = a then 1 else 0) at ht
        rw [show List.ofFn (Function.update u j.succ b) =
            Function.update u j.succ b 0 :: List.ofFn (Fin.tail (Function.update u j.succ b)) from
              List.ofFn_succ,
          show List.ofFn u = u 0 :: List.ofFn (Fin.tail u) from List.ofFn_succ,
          Fin.tail_update_succ, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)),
          List.count_cons, List.count_cons]
        by_cases huj : u j.succ = a <;> by_cases hb : b = a <;>
          simp only [huj, hb, if_true, if_false] at ht ⊢ <;> omega

theorem word_lower_count (r n a : ℕ) {u v : Fin n → ℕ}
    (h : (wordString r n).lower u = some v) :
    ((List.ofFn v).count a : ℤ) = ((List.ofFn u).count a : ℤ) +
      (if a = r + 1 then 1 else 0) - (if a = r then 1 else 0) := by
  obtain ⟨i, hui, rfl⟩ := wordString_lower_changes_one r n h
  have hc := word_count_update_balance n a (r + 1) u i
  rw [hui] at hc
  have h1 : (if r = a then 1 else 0 : ℕ) = (if a = r then 1 else 0) := by
    split_ifs <;> omega
  have h2 : (if r + 1 = a then 1 else 0 : ℕ) = (if a = r + 1 then 1 else 0) := by
    split_ifs <;> omega
  rw [h1, h2] at hc
  split_ifs at hc ⊢ <;> omega

theorem word_raise_count (r n a : ℕ) {u v : Fin n → ℕ}
    (h : (wordString r n).raise u = some v) :
    ((List.ofFn v).count a : ℤ) = ((List.ofFn u).count a : ℤ) -
      (if a = r + 1 then 1 else 0) + (if a = r then 1 else 0) := by
  have h' := word_lower_count r n a ((wordString r n).lower_eq_some_iff.mpr h)
  omega

theorem word_lowerIterate_count (r n a k : ℕ) {u v : Fin n → ℕ}
    (h : (wordString r n).lowerIterate k u = some v) :
    ((List.ofFn v).count a : ℤ) = ((List.ofFn u).count a : ℤ) + (k : ℤ) *
      ((if a = r + 1 then 1 else 0) - (if a = r then 1 else 0)) := by
  induction k generalizing u with
  | zero =>
      have heq : u = v := Option.some.inj h
      subst v
      simp
  | succ k ih =>
      obtain ⟨w, huw, hwv⟩ := Option.bind_eq_some_iff.mp h
      have h1 := word_lower_count r n a huw
      have h2 := ih hwv
      push_cast
      rw [h2, h1]
      ring

theorem word_raiseIterate_count (r n a k : ℕ) {u v : Fin n → ℕ}
    (h : (wordString r n).reverse.lowerIterate k u = some v) :
    ((List.ofFn v).count a : ℤ) = ((List.ofFn u).count a : ℤ) - (k : ℤ) *
      ((if a = r + 1 then 1 else 0) - (if a = r then 1 else 0)) := by
  have h' := word_lowerIterate_count r n a k
    (((wordString r n).lowerIterate_reverse_iff k v u).mpr h)
  omega

/-- The actual adjacent-letter crystal reflection, obtained from finite word
signatures and their proven partial inverses. -/
def wordReflection (r n : ℕ) : (Fin n → ℕ) ≃ (Fin n → ℕ) :=
  (wordString r n).reflectionEquiv

theorem wordReflection_involutive (r n : ℕ) : Function.Involutive (wordReflection r n) :=
  (wordString r n).reflection_involutive

theorem wordReflection_fixes_equal_counts (r n : ℕ) (u : Fin n → ℕ)
    (hu : (List.ofFn u).count r = (List.ofFn u).count (r + 1)) :
    wordReflection r n u = u := by
  apply (wordString r n).reflection_eq_self_of_middle
  have hb := wordString_balance r n u
  rw [hu] at hb
  omega

/-- Literal content permutation under the constructed reflection. -/
theorem wordReflection_count (r n a : ℕ) (u : Fin n → ℕ) :
    (List.ofFn (wordReflection r n u)).count a =
      if a = r then (List.ofFn u).count (r + 1)
      else if a = r + 1 then (List.ofFn u).count r
      else (List.ofFn u).count a := by
  have hb := wordString_balance r n u
  change (List.ofFn ((wordString r n).reflection u)).count a = _
  unfold StringSystem.reflection
  by_cases h : (wordString r n).epsilon u ≤ (wordString r n).phi u
  · rw [dif_pos h]
    have hc := word_lowerIterate_count r n a
      ((wordString r n).phi u - (wordString r n).epsilon u)
      ((wordString r n).lowerAt_spec _ u (Nat.sub_le _ _))
    by_cases ha : a = r <;> by_cases ha' : a = r + 1 <;>
      simp_all <;> omega
  · rw [dif_neg h]
    have hc := word_raiseIterate_count r n a
      ((wordString r n).epsilon u - (wordString r n).phi u)
      ((wordString r n).reverse.lowerAt_spec _ u (Nat.sub_le _ _))
    simp only [StringSystem.reverse_phi] at hc
    by_cases ha : a = r <;> by_cases ha' : a = r + 1 <;>
      simp_all <;> omega

end HigherSpecht.Lascoux
end
end CanonicalSource11

section CanonicalSource12
/- Source: HigherSpecht/LascouxListStrings.lean -/



/-!
# Literal list signatures and cancellation

This is the same finite-word string construction, transported through the
actual list/tuple equivalence.  The adjacent pair `(r+1),r` is a neutral
string and can be removed without changing either signature coordinate.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

namespace StringSystem

def sigma {I : Type*} {A : I → Type*} (c : (i : I) → StringSystem (A i)) :
    StringSystem (Sigma A) where
  raise x := ((c x.1).raise x.2).map (Sigma.mk x.1)
  lower x := ((c x.1).lower x.2).map (Sigma.mk x.1)
  epsilon x := (c x.1).epsilon x.2
  phi x := (c x.1).phi x.2
  lower_eq_some_iff {x y} := by
    cases x with | mk i x =>
      constructor
      · intro h
        obtain ⟨z, hxz, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [((c i).lower_eq_some_iff.mp hxz), Option.map_some]
      · intro h
        cases y with | mk j y =>
          obtain ⟨z, hyz, heq⟩ := Option.map_eq_some_iff.mp h
          cases heq
          simp only [((c j).lower_eq_some_iff.mpr hyz), Option.map_some]
  epsilon_zero_iff := by intro x; simp only [Option.map_eq_none_iff, (c x.1).epsilon_zero_iff]
  epsilon_raise {x y} h := by
    obtain ⟨z, hxz, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (c x.1).epsilon_raise hxz
  phi_zero_iff := by intro x; simp only [Option.map_eq_none_iff, (c x.1).phi_zero_iff]
  phi_raise {x y} h := by
    obtain ⟨z, hxz, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (c x.1).phi_raise hxz

end StringSystem

def listString (r : ℕ) : StringSystem (List ℕ) :=
  (StringSystem.sigma (wordString r)).transport List.equivSigmaTuple.symm

theorem listString_epsilon_ofFn (r n : ℕ) (u : Fin n → ℕ) :
    (listString r).epsilon (List.ofFn u) = (wordString r n).epsilon u := by
  change (wordString r (List.equivSigmaTuple (List.equivSigmaTuple.symm ⟨n, u⟩)).1).epsilon
    (List.equivSigmaTuple (List.equivSigmaTuple.symm ⟨n, u⟩)).2 = _
  rw [Equiv.apply_symm_apply]

theorem listString_phi_ofFn (r n : ℕ) (u : Fin n → ℕ) :
    (listString r).phi (List.ofFn u) = (wordString r n).phi u := by
  change (wordString r (List.equivSigmaTuple (List.equivSigmaTuple.symm ⟨n, u⟩)).1).phi
    (List.equivSigmaTuple (List.equivSigmaTuple.symm ⟨n, u⟩)).2 = _
  rw [Equiv.apply_symm_apply]

theorem listString_lower_ofFn (r n : ℕ) (u : Fin n → ℕ) :
    (listString r).lower (List.ofFn u) = ((wordString r n).lower u).map List.ofFn := by
  change ((StringSystem.sigma (wordString r)).lower
    (List.equivSigmaTuple (List.equivSigmaTuple.symm ⟨n, u⟩))).map
      List.equivSigmaTuple.symm = _
  rw [Equiv.apply_symm_apply]
  simp only [StringSystem.sigma, Option.map_map, Function.comp_def]
  rfl

theorem listString_raise_ofFn (r n : ℕ) (u : Fin n → ℕ) :
    (listString r).raise (List.ofFn u) = ((wordString r n).raise u).map List.ofFn := by
  change ((StringSystem.sigma (wordString r)).raise
    (List.equivSigmaTuple (List.equivSigmaTuple.symm ⟨n, u⟩))).map
      List.equivSigmaTuple.symm = _
  rw [Equiv.apply_symm_apply]
  simp only [StringSystem.sigma, Option.map_map, Function.comp_def]
  rfl

theorem listString_epsilon_cons (r a : ℕ) (w : List ℕ) :
    (listString r).epsilon (a :: w) = (listString r).epsilon w +
      ((letterString r).epsilon a - (listString r).phi w) := by
  obtain ⟨⟨n, u⟩, rfl⟩ := List.equivSigmaTuple.symm.surjective w
  change (listString r).epsilon (a :: List.ofFn u) =
    (listString r).epsilon (List.ofFn u) +
      ((letterString r).epsilon a - (listString r).phi (List.ofFn u))
  have hcons : List.ofFn (Fin.cons a u) = a :: List.ofFn u := by
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  rw [← hcons, listString_epsilon_ofFn, listString_epsilon_ofFn, listString_phi_ofFn]
  rfl

theorem listString_phi_cons (r a : ℕ) (w : List ℕ) :
    (listString r).phi (a :: w) = (letterString r).phi a +
      ((listString r).phi w - (letterString r).epsilon a) := by
  obtain ⟨⟨n, u⟩, rfl⟩ := List.equivSigmaTuple.symm.surjective w
  change (listString r).phi (a :: List.ofFn u) =
    (letterString r).phi a + ((listString r).phi (List.ofFn u) - (letterString r).epsilon a)
  have hcons : List.ofFn (Fin.cons a u) = a :: List.ofFn u := by
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  rw [← hcons, listString_phi_ofFn, listString_phi_ofFn]
  rfl

theorem listString_lower_cons (r a : ℕ) (w : List ℕ) :
    (listString r).lower (a :: w) =
      if (letterString r).epsilon a < (listString r).phi w then
        ((listString r).lower w).map (List.cons a)
      else ((letterString r).lower a).map (fun b => b :: w) := by
  obtain ⟨⟨n, u⟩, rfl⟩ := List.equivSigmaTuple.symm.surjective w
  change (listString r).lower (a :: List.ofFn u) =
    if (letterString r).epsilon a < (listString r).phi (List.ofFn u) then
      ((listString r).lower (List.ofFn u)).map (List.cons a)
    else ((letterString r).lower a).map (fun b => b :: List.ofFn u)
  have hcons : List.ofFn (Fin.cons a u) = a :: List.ofFn u := by
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  rw [← hcons, listString_lower_ofFn, wordString_lower_cons, listString_phi_ofFn,
    listString_lower_ofFn]
  split_ifs <;> simp only [Option.map_map, Function.comp_def, List.ofFn_succ,
    Fin.cons_zero, Fin.cons_succ]

theorem listString_raise_cons (r a : ℕ) (w : List ℕ) :
    (listString r).raise (a :: w) =
      if (letterString r).epsilon a ≤ (listString r).phi w then
        ((listString r).raise w).map (List.cons a)
      else ((letterString r).raise a).map (fun b => b :: w) := by
  obtain ⟨⟨n, u⟩, rfl⟩ := List.equivSigmaTuple.symm.surjective w
  change (listString r).raise (a :: List.ofFn u) =
    if (letterString r).epsilon a ≤ (listString r).phi (List.ofFn u) then
      ((listString r).raise (List.ofFn u)).map (List.cons a)
    else ((letterString r).raise a).map (fun b => b :: List.ofFn u)
  have hcons : List.ofFn (Fin.cons a u) = a :: List.ofFn u := by
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  rw [← hcons, listString_raise_ofFn, wordString_raise_cons, listString_phi_ofFn,
    listString_raise_ofFn]
  split_ifs <;> simp only [Option.map_map, Function.comp_def, List.ofFn_succ,
    Fin.cons_zero, Fin.cons_succ]

theorem listString_cancel_pair_epsilon (r : ℕ) (w : List ℕ) :
    (listString r).epsilon ((r + 1) :: r :: w) = (listString r).epsilon w := by
  rw [listString_epsilon_cons, listString_epsilon_cons, listString_phi_cons]
  simp only [letterString, if_pos rfl, show r ≠ r + 1 by omega, if_false]
  omega

theorem listString_cancel_pair_phi (r : ℕ) (w : List ℕ) :
    (listString r).phi ((r + 1) :: r :: w) = (listString r).phi w := by
  rw [listString_phi_cons, listString_phi_cons]
  simp only [letterString, if_pos rfl, show r + 1 ≠ r by omega,
    show r ≠ r + 1 by omega, if_false]
  omega

theorem listString_cancel_pair_lower (r : ℕ) (w : List ℕ) :
    (listString r).lower ((r + 1) :: r :: w) =
      ((listString r).lower w).map (fun v => (r + 1) :: r :: v) := by
  rw [listString_lower_cons, listString_lower_cons, listString_phi_cons]
  simp only [letterString, if_pos rfl, show r + 1 ≠ r by omega,
    show r ≠ r + 1 by omega, if_false]
  by_cases hp : 0 < (listString r).phi w
  · rw [if_pos (by omega), if_pos hp]
    simp only [Option.map_map, Function.comp_def]
  · have hz := (listString r).phi_zero_iff.mp (Nat.eq_zero_of_not_pos hp)
    rw [if_neg (by omega), hz]
    rfl

theorem listString_cancel_pair_raise (r : ℕ) (w : List ℕ) :
    (listString r).raise ((r + 1) :: r :: w) =
      ((listString r).raise w).map (fun v => (r + 1) :: r :: v) := by
  rw [listString_raise_cons, listString_raise_cons, listString_phi_cons]
  simp only [letterString, if_pos rfl, show r + 1 ≠ r by omega,
    show r ≠ r + 1 by omega, if_false]
  rw [if_pos (by omega), if_pos (Nat.zero_le _)]
  simp only [Option.map_map, Function.comp_def]

theorem listString_cancel_pair_in_context (r : ℕ) (pre suffix : List ℕ) :
    (listString r).epsilon (pre ++ (r + 1) :: r :: suffix) =
        (listString r).epsilon (pre ++ suffix) ∧
    (listString r).phi (pre ++ (r + 1) :: r :: suffix) =
        (listString r).phi (pre ++ suffix) := by
  induction pre with
  | nil => exact ⟨listString_cancel_pair_epsilon r suffix, listString_cancel_pair_phi r suffix⟩
  | cons a pre ih =>
      simp only [List.cons_append, listString_epsilon_cons, listString_phi_cons,
        ih.1, ih.2, and_self]

theorem listString_neutral_epsilon (r a : ℕ) (w : List ℕ)
    (ha : a ≠ r) (ha' : a ≠ r + 1) :
    (listString r).epsilon (a :: w) = (listString r).epsilon w := by
  rw [listString_epsilon_cons]
  simp [letterString, ha, ha']

theorem listString_neutral_phi (r a : ℕ) (w : List ℕ)
    (ha : a ≠ r) (ha' : a ≠ r + 1) :
    (listString r).phi (a :: w) = (listString r).phi w := by
  rw [listString_phi_cons]
  simp [letterString, ha, ha']

theorem listString_neutral_lower (r a : ℕ) (w : List ℕ)
    (ha : a ≠ r) (ha' : a ≠ r + 1) :
    (listString r).lower (a :: w) = ((listString r).lower w).map (List.cons a) := by
  rw [listString_lower_cons]
  simp only [letterString, ha, ha', if_false]
  by_cases hp : 0 < (listString r).phi w
  · rw [if_pos hp]
  · have hz := (listString r).phi_zero_iff.mp (Nat.eq_zero_of_not_pos hp)
    rw [if_neg hp, hz]
    rfl

theorem listString_neutral_raise (r a : ℕ) (w : List ℕ)
    (ha : a ≠ r) (ha' : a ≠ r + 1) :
    (listString r).raise (a :: w) = ((listString r).raise w).map (List.cons a) := by
  rw [listString_raise_cons]
  simp only [letterString, ha, ha', if_false, Nat.zero_le, if_true]

theorem listString_filter_signature (r : ℕ) (w : List ℕ) :
    (listString r).epsilon (w.filter (fun a => a = r ∨ a = r + 1)) =
        (listString r).epsilon w ∧
    (listString r).phi (w.filter (fun a => a = r ∨ a = r + 1)) =
        (listString r).phi w := by
  induction w with
  | nil => exact ⟨rfl, rfl⟩
  | cons a w ih =>
      by_cases ha : a = r ∨ a = r + 1
      · simp only [List.filter_cons, ha, decide_true, Bool.true_eq, if_true,
          listString_epsilon_cons, listString_phi_cons, ih.1, ih.2, and_self]
      · have har : a ≠ r := fun h => ha (Or.inl h)
        have har' : a ≠ r + 1 := fun h => ha (Or.inr h)
        simp only [List.filter_cons, ha, decide_false, Bool.false_eq_true, if_false,
          listString_neutral_epsilon r a w har har',
          listString_neutral_phi r a w har har', ih.1, ih.2, and_self]

end HigherSpecht.Lascoux
end
end CanonicalSource12

section CanonicalSource13
/- Source: HigherSpecht/LascouxKnuthSignatures.lean -/



/-!
# Signature coordinates on actual Knuth classes

These lemmas concern the literal word signatures already constructed from
rank-one strings.  Concatenation is derived from that construction, and the
two elementary Knuth moves are checked at their three actual letters.
Consequently both string lengths descend to insertion-tableau classes.

Compatibility of the partial operators themselves, and the standardization
image condition, remain separate results.  No cardinality conclusion is
drawn merely from signature invariance.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

@[simp] theorem listString_epsilon_nil (r : ℕ) :
    (listString r).epsilon [] = 0 := rfl

@[simp] theorem listString_phi_nil (r : ℕ) :
    (listString r).phi [] = 0 := rfl

@[simp] theorem listString_lower_nil (r : ℕ) :
    (listString r).lower [] = none := rfl

@[simp] theorem listString_raise_nil (r : ℕ) :
    (listString r).raise [] = none := rfl

/-- The signature of concatenation, in the convention pairing `r+1` with a
later `r`.  Both formulas are consequences of the literal tensor rule. -/
theorem listString_signature_append (r : ℕ) (u v : List ℕ) :
    (listString r).epsilon (u ++ v) =
      (listString r).epsilon v +
        ((listString r).epsilon u - (listString r).phi v) ∧
    (listString r).phi (u ++ v) =
      (listString r).phi u +
        ((listString r).phi v - (listString r).epsilon u) := by
  induction u with
  | nil => simp
  | cons a u ih =>
      simp only [List.cons_append, listString_epsilon_cons, listString_phi_cons,
        ih.1, ih.2]
      constructor <;> omega

theorem listString_signature_knuth_left (r a b c : ℕ)
    (hab : a < b) (hbc : b ≤ c) :
    (listString r).epsilon [b, a, c] = (listString r).epsilon [b, c, a] ∧
    (listString r).phi [b, a, c] = (listString r).phi [b, c, a] := by
  simp only [listString_epsilon_cons, listString_phi_cons,
    listString_epsilon_nil, listString_phi_nil, letterString_epsilon, letterString_phi]
  split_ifs <;> constructor <;> omega

theorem listString_signature_knuth_right (r a b c : ℕ)
    (hab : a ≤ b) (hbc : b < c) :
    (listString r).epsilon [a, c, b] = (listString r).epsilon [c, a, b] ∧
    (listString r).phi [a, c, b] = (listString r).phi [c, a, b] := by
  simp only [listString_epsilon_cons, listString_phi_cons,
    listString_epsilon_nil, listString_phi_nil, letterString_epsilon, letterString_phi]
  split_ifs <;> constructor <;> omega

/-- The actual elementary Knuth relation preserves both signature
coordinates in every context. -/
theorem listString_signature_of_knuth (r : ℕ) {u v : List ℕ}
    (h : KnuthEquivalent u v) :
    (listString r).epsilon u = (listString r).epsilon v ∧
    (listString r).phi u = (listString r).phi v := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | symm h ih => exact ⟨ih.1.symm, ih.2.symm⟩
  | trans h₁ h₂ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1, ih₁.2.trans ih₂.2⟩
  | append l t h ih =>
      simp only [(listString_signature_append r _ _).1,
        (listString_signature_append r _ _).2, ih.1, ih.2, and_self]
  | left hab hbc => exact listString_signature_knuth_left r _ _ _ hab hbc
  | right hab hbc => exact listString_signature_knuth_right r _ _ _ hab hbc

end HigherSpecht.Lascoux
end
end CanonicalSource13

section CanonicalSource14
/- Source: HigherSpecht/LascouxCyclage.lean -/



/-!
# Restricted cyclic rotation and the actual first lowering

The first lowering commutes with moving a nonminimal initial letter to the
end when the lower letter is more frequent.  The restriction is essential:
lowering `000` gives `001`, which is not fixed by cyclic rotation.

This is a word-level ingredient for the restricted-cyclage step in the
Lascoux embedding argument.  It does not identify the image of that embedding
with the catabolizable tableaux, and no counting theorem is inferred here.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem listString_balance (r : ℕ) (w : List ℕ) :
    ((listString r).phi w : ℤ) - (listString r).epsilon w =
      (w.count r : ℤ) - w.count (r + 1) := by
  obtain ⟨⟨n, u⟩, rfl⟩ := List.equivSigmaTuple.symm.surjective w
  change ((listString r).phi (List.ofFn u) : ℤ) -
    (listString r).epsilon (List.ofFn u) =
      ((List.ofFn u).count r : ℤ) - (List.ofFn u).count (r + 1)
  rw [listString_phi_ofFn, listString_epsilon_ofFn]
  exact wordString_balance r n u

theorem listString_append_upper_signature (r : ℕ) (w : List ℕ) :
    (listString r).epsilon (w ++ [r + 1]) = (listString r).epsilon w + 1 ∧
    (listString r).phi (w ++ [r + 1]) = (listString r).phi w := by
  induction w with
  | nil =>
      simp only [List.nil_append, listString_epsilon_cons, listString_phi_cons]
      change (0 + ((if r + 1 = r + 1 then 1 else 0) - 0) = 0 + 1) ∧
        ((if r + 1 = r then 1 else 0) + (0 - (if r + 1 = r + 1 then 1 else 0)) = 0)
      simp [show r + 1 ≠ r by omega]
  | cons a w ih =>
      simp only [List.cons_append, listString_epsilon_cons, listString_phi_cons, ih.1, ih.2]
      exact ⟨by omega, by trivial⟩

theorem listString_lower_append_upper (r : ℕ) (w : List ℕ) :
    (listString r).lower (w ++ [r + 1]) =
      ((listString r).lower w).map (fun v => v ++ [r + 1]) := by
  induction w with
  | nil =>
      rw [List.nil_append, listString_lower_cons]
      change (if (if r + 1 = r + 1 then 1 else 0) < 0 then
        (none : Option (List ℕ)).map (List.cons (r + 1)) else
        (if r + 1 = r then some (r + 1) else none).map (fun b => [b])) = none
      simp [show r + 1 ≠ r by omega]
  | cons a w ih =>
      rw [List.cons_append, listString_lower_cons,
        (listString_append_upper_signature r w).2, ih, listString_lower_cons]
      split_ifs <;> simp only [Option.map_map, Function.comp_def, List.cons_append]

theorem listString_append_neutral_signature (r a : ℕ) (w : List ℕ)
    (ha : a ≠ r) (ha' : a ≠ r + 1) :
    (listString r).epsilon (w ++ [a]) = (listString r).epsilon w ∧
    (listString r).phi (w ++ [a]) = (listString r).phi w := by
  induction w with
  | nil =>
      rw [List.nil_append, listString_neutral_epsilon r a [] ha ha',
        listString_neutral_phi r a [] ha ha']
      exact ⟨rfl, rfl⟩
  | cons b w ih =>
      simp only [List.cons_append, listString_epsilon_cons, listString_phi_cons,
        ih.1, ih.2, and_self]

theorem listString_lower_append_neutral (r a : ℕ) (w : List ℕ)
    (ha : a ≠ r) (ha' : a ≠ r + 1) :
    (listString r).lower (w ++ [a]) =
      ((listString r).lower w).map (fun v => v ++ [a]) := by
  induction w with
  | nil =>
      rw [List.nil_append, listString_neutral_lower r a [] ha ha']
      rfl
  | cons b w ih =>
      rw [List.cons_append, listString_lower_cons,
        (listString_append_neutral_signature r a w ha ha').2, ih, listString_lower_cons]
      split_ifs <;> simp only [Option.map_map, Function.comp_def, List.cons_append]

def rotateHead : List ℕ → List ℕ
  | [] => []
  | a :: w => w ++ [a]

theorem lower_rotateHead_of_count (r a : ℕ) (w : List ℕ) (ha : a ≠ r)
    (hc : (a :: w).count (r + 1) < (a :: w).count r) :
    (listString r).lower (rotateHead (a :: w)) =
      ((listString r).lower (a :: w)).map rotateHead := by
  by_cases hau : a = r + 1
  · subst a
    have hcount : w.count (r + 1) + 1 < w.count r := by
      simpa only [List.count_cons_self, List.count_cons_of_ne ha] using hc
    have hbalance := listString_balance r w
    have hp : 1 < (listString r).phi w := by omega
    rw [rotateHead, listString_lower_append_upper, listString_lower_cons]
    simp [letterString_epsilon, letterString_lower, hp, ha,
      Option.map_map, Function.comp_def, rotateHead]
  · rw [rotateHead, listString_lower_append_neutral r a w ha hau,
      listString_neutral_lower r a w ha hau]
    simp only [Option.map_map, Function.comp_def, rotateHead]

theorem firstLowering_rotateHead (a : ℕ) (w : List ℕ) (ha : a ≠ 0)
    (hc : (a :: w).count 1 < (a :: w).count 0) :
    (listString 0).lower (rotateHead (a :: w)) =
      ((listString 0).lower (a :: w)).map rotateHead :=
  lower_rotateHead_of_count 0 a w ha hc

end HigherSpecht.Lascoux
end
end CanonicalSource14

section CanonicalSource15
/- Source: HigherSpecht/LascouxWordBlocks.lean -/



/-!
# Literal signature blocks and protected matched letters

The tensor rule is proved for arbitrary concatenated words.  A block with zero
raising and lowering signature is then fixed, position by position, by either
partial operator in every surrounding context.  This is the cancellation fact
needed to prove that the selected tableau cut stays strictly inside its column
bounds; it does not assume that column condition as an operator hypothesis.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem listString_epsilon_append (r : ℕ) (u v : List ℕ) :
    (listString r).epsilon (u ++ v) = (listString r).epsilon v +
      ((listString r).epsilon u - (listString r).phi v) :=
  (listString_signature_append r u v).1

theorem listString_phi_append (r : ℕ) (u v : List ℕ) :
    (listString r).phi (u ++ v) = (listString r).phi u +
      ((listString r).phi v - (listString r).epsilon u) :=
  (listString_signature_append r u v).2

theorem listString_lower_append (r : ℕ) (u v : List ℕ) :
    (listString r).lower (u ++ v) =
      if (listString r).epsilon u < (listString r).phi v then
        ((listString r).lower v).map (fun w => u ++ w)
      else ((listString r).lower u).map (fun w => w ++ v) := by
  induction u with
  | nil =>
      simp only [List.nil_append, listString_epsilon_nil, listString_lower_nil]
      by_cases hv : 0 < (listString r).phi v
      · simp [hv]
      · have hz : (listString r).phi v = 0 := by omega
        have hn := (listString r).phi_zero_iff.mp hz
        simp [hv, hn]
  | cons a u ih =>
      have hnoneu : (listString r).phi u = 0 → (listString r).lower u = none :=
        (listString r).phi_zero_iff.mp
      have hnonev : (listString r).phi v = 0 → (listString r).lower v = none :=
        (listString r).phi_zero_iff.mp
      simp only [List.cons_append, listString_lower_cons,
        (listString_signature_append r u v).2, listString_epsilon_cons, ih]
      clear ih
      by_cases ha : a = r <;> by_cases hb : a = r + 1 <;>
        simp only [letterString_epsilon, letterString_phi, letterString_lower,
          ha, hb, if_true, if_false]
      all_goals try omega
      all_goals split_ifs <;>
        first | omega | skip
      all_goals
        simp_all only [Option.map_map, Option.map_none, Option.map_some,
          Function.comp_def, List.cons_append]
      all_goals omega

theorem listString_raise_append (r : ℕ) (u v : List ℕ) :
    (listString r).raise (u ++ v) =
      if (listString r).epsilon u ≤ (listString r).phi v then
        ((listString r).raise v).map (fun w => u ++ w)
      else ((listString r).raise u).map (fun w => w ++ v) := by
  induction u with
  | nil => simp [listString_epsilon_nil, listString_raise_nil]
  | cons a u ih =>
      have hnoneu : (listString r).epsilon u = 0 → (listString r).raise u = none :=
        (listString r).epsilon_zero_iff.mp
      have hnonev : (listString r).epsilon v = 0 → (listString r).raise v = none :=
        (listString r).epsilon_zero_iff.mp
      simp only [List.cons_append, listString_raise_cons,
        (listString_signature_append r u v).2, listString_epsilon_cons, ih]
      clear ih
      by_cases ha : a = r <;> by_cases hb : a = r + 1 <;>
        simp only [letterString_epsilon, letterString_phi, letterString_raise,
          ha, hb, if_true, if_false]
      all_goals try omega
      all_goals split_ifs <;>
        first | omega | skip
      all_goals
        simp_all only [Option.map_map, Option.map_none, Option.map_some,
          Function.comp_def, List.cons_append]
      all_goals omega

theorem listString_lower_length (r : ℕ) {u v : List ℕ}
    (h : (listString r).lower u = some v) : v.length = u.length := by
  induction u generalizing v with
  | nil => simp [listString_lower_nil] at h
  | cons a u ih =>
      rw [listString_lower_cons] at h
      split_ifs at h with ht
      · obtain ⟨w, hw, hweq⟩ := Option.map_eq_some_iff.mp h
        rw [← hweq]
        simpa only [List.length_cons] using congrArg Nat.succ (ih hw)
      · obtain ⟨b, hb, hbeq⟩ := Option.map_eq_some_iff.mp h
        rw [← hbeq]
        rfl

theorem listString_raise_length (r : ℕ) {u v : List ℕ}
    (h : (listString r).raise u = some v) : v.length = u.length := by
  exact (listString_lower_length r ((listString r).lower_eq_some_iff.mpr h)).symm

def NeutralSignature (r : ℕ) (u : List ℕ) : Prop :=
  (listString r).epsilon u = 0 ∧ (listString r).phi u = 0

theorem listString_lower_replicate_signature (r k : ℕ) :
    (listString r).epsilon (List.replicate k r) = 0 ∧
      (listString r).phi (List.replicate k r) = k := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      simp only [List.replicate_succ, listString_epsilon_cons,
        listString_phi_cons, letterString_epsilon, letterString_phi, ih.1, ih.2]
      simp [show r ≠ r + 1 by omega, Nat.add_comm]

theorem listString_upper_replicate_signature (r k : ℕ) :
    (listString r).epsilon (List.replicate k (r + 1)) = k ∧
      (listString r).phi (List.replicate k (r + 1)) = 0 := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      simp only [List.replicate_succ, listString_epsilon_cons,
        listString_phi_cons, letterString_epsilon, letterString_phi, ih.1, ih.2]
      simp [show r + 1 ≠ r by omega]

theorem neutralSignature_of_no_adjacent_letters (r : ℕ) (u : List ℕ)
    (h : ∀ x ∈ u, x ≠ r ∧ x ≠ r + 1) : NeutralSignature r u := by
  induction u with
  | nil => exact ⟨rfl, rfl⟩
  | cons a u ih =>
      have ha := h a (by simp)
      have hu := ih (fun x hx => h x (by simp [hx]))
      simp only [NeutralSignature, listString_epsilon_cons, listString_phi_cons,
        letterString_epsilon, letterString_phi, ha.1, ha.2, if_false, hu.1, hu.2]
      simp

/-- A vertical matched block, with arbitrary irrelevant letters between the
two rows, has zero signature.  This is the block that prevents a lowering
step from violating a tight column inequality. -/
theorem NeutralSignature.matched_sandwich {r : ℕ} {middle : List ℕ}
    (hmiddle : NeutralSignature r middle) (k : ℕ) :
    NeutralSignature r
      (List.replicate k (r + 1) ++ middle ++ List.replicate k r) := by
  have hu := listString_upper_replicate_signature r k
  have hl := listString_lower_replicate_signature r k
  have hmid := listString_signature_append r (List.replicate k (r + 1)) middle
  have hall := listString_signature_append r
    (List.replicate k (r + 1) ++ middle) (List.replicate k r)
  constructor
  · simpa [hmid.1, hmiddle.1, hmiddle.2, hu.1, hl.1, hl.2] using hall.1
  · simpa [hmid.1, hmid.2, hmiddle.1, hmiddle.2, hu.1, hu.2,
      hl.2] using hall.2

theorem NeutralSignature.append {r : ℕ} {u v : List ℕ}
    (hu : NeutralSignature r u) (hv : NeutralSignature r v) :
    NeutralSignature r (u ++ v) := by
  obtain ⟨he, hp⟩ := listString_signature_append r u v
  exact ⟨by simpa [hu.1, hv.1, hv.2] using he,
    by simpa [hu.2, hv.2, hu.1] using hp⟩

theorem lower_prepend_neutral {r : ℕ} {b : List ℕ} (hb : NeutralSignature r b)
    (u : List ℕ) :
    (listString r).lower (b ++ u) =
      ((listString r).lower u).map (fun v => b ++ v) := by
  rw [listString_lower_append, hb.1]
  split_ifs with h
  · rfl
  · have hphi : (listString r).phi u = 0 := by omega
    rw [(listString r).phi_zero_iff.mp hb.2, (listString r).phi_zero_iff.mp hphi]
    rfl

theorem lower_append_neutral {r : ℕ} {b : List ℕ} (hb : NeutralSignature r b)
    (u : List ℕ) :
    (listString r).lower (u ++ b) =
      ((listString r).lower u).map (fun v => v ++ b) := by
  rw [listString_lower_append, hb.2, if_neg (Nat.not_lt_zero _)]

theorem raise_prepend_neutral {r : ℕ} {b : List ℕ} (hb : NeutralSignature r b)
    (u : List ℕ) :
    (listString r).raise (b ++ u) =
      ((listString r).raise u).map (fun v => b ++ v) := by
  rw [listString_raise_append, hb.1, if_pos (Nat.zero_le _)]

theorem raise_append_neutral {r : ℕ} {b : List ℕ} (hb : NeutralSignature r b)
    (u : List ℕ) :
    (listString r).raise (u ++ b) =
      ((listString r).raise u).map (fun v => v ++ b) := by
  rw [listString_raise_append, hb.2]
  split_ifs with h
  · have he : (listString r).epsilon u = 0 := Nat.le_zero.mp h
    rw [(listString r).epsilon_zero_iff.mp hb.1, (listString r).epsilon_zero_iff.mp he]
    rfl
  · rfl

/-- Every letter in a genuinely matched block is left fixed.  The lengths of
the two surrounding words are preserved, so this is positional preservation. -/
theorem lower_preserves_neutral_block {r : ℕ} {b : List ℕ}
    (hb : NeutralSignature r b) (pre suffix : List ℕ) {v : List ℕ}
    (h : (listString r).lower (pre ++ b ++ suffix) = some v) :
    ∃ pre' suffix', v = pre' ++ b ++ suffix' ∧
      pre'.length = pre.length ∧ suffix'.length = suffix.length := by
  rw [listString_lower_append, (listString_signature_append r pre b).1,
    hb.1, hb.2] at h
  simp only [Nat.sub_zero, Nat.zero_add] at h
  split_ifs at h with ht
  · obtain ⟨s, hs, hv⟩ := Option.map_eq_some_iff.mp h
    exact ⟨pre, s, hv.symm, rfl, listString_lower_length r hs⟩
  · rw [lower_append_neutral hb pre] at h
    simp only [Option.map_map, Function.comp_def] at h
    obtain ⟨p, hp, hv⟩ := Option.map_eq_some_iff.mp h
    exact ⟨p, suffix, hv.symm, listString_lower_length r hp, rfl⟩

theorem raise_preserves_neutral_block {r : ℕ} {b : List ℕ}
    (hb : NeutralSignature r b) (pre suffix : List ℕ) {v : List ℕ}
    (h : (listString r).raise (pre ++ b ++ suffix) = some v) :
    ∃ pre' suffix', v = pre' ++ b ++ suffix' ∧
      pre'.length = pre.length ∧ suffix'.length = suffix.length := by
  rw [listString_raise_append, (listString_signature_append r pre b).1,
    hb.1, hb.2] at h
  simp only [Nat.sub_zero, Nat.zero_add] at h
  split_ifs at h with ht
  · obtain ⟨s, hs, hv⟩ := Option.map_eq_some_iff.mp h
    exact ⟨pre, s, hv.symm, rfl, listString_raise_length r hs⟩
  · rw [raise_append_neutral hb pre] at h
    simp only [Option.map_map, Function.comp_def] at h
    obtain ⟨p, hp, hv⟩ := Option.map_eq_some_iff.mp h
    exact ⟨p, suffix, hv.symm, listString_raise_length r hp, rfl⟩

theorem lower_neutral_block_getElem? {r : ℕ} {b : List ℕ}
    (hb : NeutralSignature r b) (pre suffix : List ℕ) {v : List ℕ}
    (h : (listString r).lower (pre ++ b ++ suffix) = some v)
    (i : Fin b.length) : v[pre.length + i.val]? = some b[i] := by
  obtain ⟨p, s, hv, hp, hs⟩ := lower_preserves_neutral_block hb pre suffix h
  rw [hv, List.append_assoc,
    List.getElem?_append_right (by omega)]
  simp only [hp, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left i.isLt]
  exact List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩

theorem raise_neutral_block_getElem? {r : ℕ} {b : List ℕ}
    (hb : NeutralSignature r b) (pre suffix : List ℕ) {v : List ℕ}
    (h : (listString r).raise (pre ++ b ++ suffix) = some v)
    (i : Fin b.length) : v[pre.length + i.val]? = some b[i] := by
  obtain ⟨p, s, hv, hp, hs⟩ := raise_preserves_neutral_block hb pre suffix h
  rw [hv, List.append_assoc,
    List.getElem?_append_right (by omega)]
  simp only [hp, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left i.isLt]
  exact List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩

/-- If the preceding upper-letter block can match the entire lower-letter
block, every one of those lower letters is fixed by actual lowering. -/
theorem lower_matched_lower_block {r U L : ℕ} (hUL : L ≤ U)
    (middle : List ℕ) (hmiddle : NeutralSignature r middle)
    (pre suffix : List ℕ) {v : List ℕ}
    (h : (listString r).lower
      (pre ++ List.replicate U (r + 1) ++ middle ++ List.replicate L r ++ suffix) =
        some v) (i : Fin L) :
    v[pre.length + U + middle.length + i.val]? = some r := by
  let p := pre ++ List.replicate (U - L) (r + 1)
  let b := List.replicate L (r + 1) ++ middle ++ List.replicate L r
  have hb : NeutralSignature r b := hmiddle.matched_sandwich L
  have hword : pre ++ List.replicate U (r + 1) ++ middle ++
      List.replicate L r ++ suffix = p ++ b ++ suffix := by
    have hrep : List.replicate U (r + 1) =
        List.replicate (U - L) (r + 1) ++ List.replicate L (r + 1) := by
      rw [← List.replicate_add, Nat.sub_add_cancel hUL]
    dsimp [p, b]
    rw [hrep]
    simp only [List.append_assoc]
  have hindex : L + middle.length + i.val < b.length := by
    simp only [b, List.length_append, List.length_replicate]
    omega
  have hh := lower_neutral_block_getElem? hb p suffix (hword ▸ h)
    ⟨L + middle.length + i.val, hindex⟩
  have hpos : p.length + (L + middle.length + i.val) =
      pre.length + U + middle.length + i.val := by
    simp only [p, List.length_append, List.length_replicate]
    omega
  rw [hpos] at hh
  have hval : b[L + middle.length + i.val]'hindex = r := by
    dsimp [b]
    rw [List.getElem_append_right (by simp)]
    simp
  simpa only [Fin.getElem_fin, hval] using hh

/-- Dually, a following lower-letter block protects the entire upper-letter
block from actual raising. -/
theorem raise_matched_upper_block {r U L : ℕ} (hUL : U ≤ L)
    (middle : List ℕ) (hmiddle : NeutralSignature r middle)
    (pre suffix : List ℕ) {v : List ℕ}
    (h : (listString r).raise
      (pre ++ List.replicate U (r + 1) ++ middle ++ List.replicate L r ++ suffix) =
        some v) (i : Fin U) :
    v[pre.length + i.val]? = some (r + 1) := by
  let b := List.replicate U (r + 1) ++ middle ++ List.replicate U r
  let s := List.replicate (L - U) r ++ suffix
  have hb : NeutralSignature r b := hmiddle.matched_sandwich U
  have hword : pre ++ List.replicate U (r + 1) ++ middle ++
      List.replicate L r ++ suffix = pre ++ b ++ s := by
    have hrep : List.replicate L r = List.replicate U r ++ List.replicate (L - U) r := by
      rw [← List.replicate_add, Nat.add_sub_of_le hUL]
    dsimp [b, s]
    rw [hrep]
    simp only [List.append_assoc]
  have hindex : i.val < b.length := by
    simp only [b, List.length_append, List.length_replicate]
    omega
  have hh := raise_neutral_block_getElem? hb pre s (hword ▸ h) ⟨i.val, hindex⟩
  have hval : b[i.val]'hindex = r + 1 := by
    dsimp [b]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simpa using i.isLt)]
    simp
  simpa only [Fin.getElem_fin, hval] using hh

/-- In a concatenation of literal row words, actual lowering acts in exactly
one row.  The unchanged contexts are returned, not assumed. -/
theorem lower_flatMap_context {A : Type*} (r : ℕ) (rows : List A) (word : A → List ℕ)
    {output : List ℕ} (h : (listString r).lower (rows.flatMap word) = some output) :
    ∃ before a after row', rows = before ++ a :: after ∧
      (listString r).lower (word a) = some row' ∧
      output = before.flatMap word ++ row' ++ after.flatMap word := by
  induction rows generalizing output with
  | nil => simp [listString_lower_nil] at h
  | cons a rows ih =>
      simp only [List.flatMap_cons] at h
      rw [listString_lower_append] at h
      split_ifs at h with hc
      · obtain ⟨tail, htail, houtput⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨before, b, after, row', hrows, hrow, htail'⟩ := ih htail
        refine ⟨a :: before, b, after, row', ?_, hrow, ?_⟩
        · simpa only [List.cons_append] using congrArg (List.cons a) hrows
        · rw [← houtput, htail']
          simp only [List.flatMap_cons, List.append_assoc]
      · obtain ⟨row', hrow, houtput⟩ := Option.map_eq_some_iff.mp h
        exact ⟨[], a, rows, row', rfl, hrow, by simpa using houtput.symm⟩

theorem raise_flatMap_context {A : Type*} (r : ℕ) (rows : List A) (word : A → List ℕ)
    {output : List ℕ} (h : (listString r).raise (rows.flatMap word) = some output) :
    ∃ before a after row', rows = before ++ a :: after ∧
      (listString r).raise (word a) = some row' ∧
      output = before.flatMap word ++ row' ++ after.flatMap word := by
  induction rows generalizing output with
  | nil => simp [listString_raise_nil] at h
  | cons a rows ih =>
      simp only [List.flatMap_cons] at h
      rw [listString_raise_append] at h
      split_ifs at h with hc
      · obtain ⟨tail, htail, houtput⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨before, b, after, row', hrows, hrow, htail'⟩ := ih htail
        refine ⟨a :: before, b, after, row', ?_, hrow, ?_⟩
        · simpa only [List.cons_append] using congrArg (List.cons a) hrows
        · rw [← houtput, htail']
          simp only [List.flatMap_cons, List.append_assoc]
      · obtain ⟨row', hrow, houtput⟩ := Option.map_eq_some_iff.mp h
        exact ⟨[], a, rows, row', rfl, hrow, by simpa using houtput.symm⟩

end HigherSpecht.Lascoux
end
end CanonicalSource15

section CanonicalSource16
/- Source: HigherSpecht/LascouxCutSelection.lean -/



/-!
# Actual signature selection discharges the tableau column bounds

The two adjacent row blocks are retained as literal word segments.  If the
column bound were tight, their relevant letters would form a fully matched
signature block, and the preceding positional preservation theorem would
forbid the alleged change.  Thus the recut inequalities follow from an actual
partial-operator value and an actual changed position.

The separate row-reading decomposition still has to instantiate these local
statements for every tableau word before the full tableau crystal is exported.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

def rowLowerCount (T : SemistandardYoungTableau mu) (v r : ℕ) : ℕ :=
  T.rowCountLt r (v + 1) - T.rowCountLt r v

def rowUpperCount (T : SemistandardYoungTableau mu) (v r : ℕ) : ℕ :=
  T.rowCountLt r (v + 2) - T.rowCountLt r (v + 1)

theorem lower_cut_bounds_of_changed_block (T : SemistandardYoungTableau mu) (v r : ℕ)
    (pre middle suffix output : List ℕ) (hmiddle : NeutralSignature v middle)
    (hstep : (listString v).lower
      (pre ++ List.replicate (rowUpperCount T v (r + 1)) (v + 1) ++ middle ++
        List.replicate (rowLowerCount T v r) v ++ suffix) = some output)
    (i : Fin (rowLowerCount T v r))
    (hchanged : output[pre.length + rowUpperCount T v (r + 1) +
      middle.length + i.val]? ≠ some v) :
    T.rowCountLt r v < T.rowCountLt r (v + 1) ∧
      T.rowCountLt (r + 1) (v + 2) < T.rowCountLt r (v + 1) := by
  have hi := i.isLt
  have hlow : T.rowCountLt r v < T.rowCountLt r (v + 1) := by
    dsimp only [rowLowerCount] at hi
    omega
  refine ⟨hlow, ?_⟩
  have hcolumn := (T.isCut_rowCountLt v).succ_le_cut r
  by_contra hnot
  have htight : T.rowCountLt (r + 1) (v + 2) = T.rowCountLt r (v + 1) := by omega
  have hneighbor := (T.isCut_rowCountLt v).cut_succ_le r
  have hmatch : rowLowerCount T v r ≤ rowUpperCount T v (r + 1) := by
    dsimp only [rowLowerCount, rowUpperCount]
    omega
  exact hchanged (lower_matched_lower_block hmatch middle hmiddle pre suffix hstep i)

/-- The actual selected position produces an actual same-shape tableau;
neither column inequality is supplied as an extra premise. -/
def lowerTableauOfChangedBlock (T : SemistandardYoungTableau mu) (v r : ℕ)
    (pre middle suffix output : List ℕ) (hmiddle : NeutralSignature v middle)
    (hstep : (listString v).lower
      (pre ++ List.replicate (rowUpperCount T v (r + 1)) (v + 1) ++ middle ++
        List.replicate (rowLowerCount T v r) v ++ suffix) = some output)
    (i : Fin (rowLowerCount T v r))
    (hchanged : output[pre.length + rowUpperCount T v (r + 1) +
      middle.length + i.val]? ≠ some v) : SemistandardYoungTableau mu :=
  lowerTableauAt T v r
    (lower_cut_bounds_of_changed_block T v r pre middle suffix output hmiddle hstep i hchanged).1
    (lower_cut_bounds_of_changed_block T v r pre middle suffix output hmiddle hstep i hchanged).2

theorem raise_column_bound_of_changed_block (T : SemistandardYoungTableau mu) (v r : ℕ)
    (pre middle suffix output : List ℕ) (hmiddle : NeutralSignature v middle)
    (hstep : (listString v).raise
      (pre ++ List.replicate (rowUpperCount T v (r + 1)) (v + 1) ++ middle ++
        List.replicate (rowLowerCount T v r) v ++ suffix) = some output)
    (i : Fin (rowUpperCount T v (r + 1)))
    (hchanged : output[pre.length + i.val]? ≠ some (v + 1)) :
    T.rowCountLt (r + 1) (v + 1) < T.rowCountLt (r + 1) (v + 2) ∧
      T.rowCountLt (r + 1) (v + 1) < T.rowCountLt r v := by
  have hi := i.isLt
  have hhigh : T.rowCountLt (r + 1) (v + 1) < T.rowCountLt (r + 1) (v + 2) := by
    dsimp only [rowUpperCount] at hi
    omega
  refine ⟨hhigh, ?_⟩
  have hcolumn := (T.isCut_rowCountLt v).cut_succ_le r
  by_contra hnot
  have htight : T.rowCountLt (r + 1) (v + 1) = T.rowCountLt r v := by omega
  have hneighbor := (T.isCut_rowCountLt v).succ_le_cut r
  have hmatch : rowUpperCount T v (r + 1) ≤ rowLowerCount T v r := by
    dsimp only [rowLowerCount, rowUpperCount]
    omega
  exact hchanged (raise_matched_upper_block hmatch middle hmiddle pre suffix hstep i)

end HigherSpecht.Lascoux
end
end CanonicalSource16

section CanonicalSource17
/- Source: HigherSpecht/LascouxZeroBlock.lean -/



/-!
# The literal first lowering on a contiguous block of minimal letters

For a semistandard row word the zeros lie in a single block in the lowest
row.  If there are more zeros than ones, the actual signature lowering
changes the last zero in that block.  The surrounding positive letters are
retained in their original positions.  This supplies the word calculation
behind the separately constructed, shape-preserving first tableau lowering.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

theorem listString_signature_of_not_mem (r : ℕ) {w : List ℕ}
    (h : r ∉ w) :
    (listString r).epsilon w = w.count (r + 1) ∧ (listString r).phi w = 0 := by
  induction w with
  | nil => simp
  | cons a w ih =>
      have ha : a ≠ r := fun heq => h (by simp [heq])
      have hw : r ∉ w := fun hm => h (by simp [hm])
      obtain ⟨he, hp⟩ := ih hw
      by_cases hau : a = r + 1
      · subst a
        simp [listString_epsilon_cons, listString_phi_cons, he, hp, letterString,
          show r + 1 ≠ r by omega, List.count_cons, Nat.add_comm]
      · simp [listString_epsilon_cons, listString_phi_cons, he, hp,
          letterString, ha, hau, List.count_cons]

theorem listString_signature_replicate_lower (r m : ℕ) :
    (listString r).epsilon (List.replicate m r) = 0 ∧
      (listString r).phi (List.replicate m r) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp [List.replicate_succ, listString_epsilon_cons, listString_phi_cons,
        ih.1, ih.2, letterString_epsilon, letterString_phi,
        show r ≠ r + 1 by omega, Nat.add_comm]

theorem listString_lower_replicate_lower (r m : ℕ) :
    (listString r).lower (List.replicate (m + 1) r) =
      some (List.replicate m r ++ [r + 1]) := by
  induction m with
  | zero =>
      simp [List.replicate_succ, listString_lower_cons, letterString_lower,
        letterString_epsilon, show r ≠ r + 1 by omega]
  | succ m ih =>
      rw [List.replicate_succ, listString_lower_cons,
        (listString_signature_replicate_lower r (m + 1)).2]
      simp only [letterString_epsilon, if_neg (show r ≠ r + 1 by omega)]
      rw [if_pos (Nat.succ_pos m), ih, Option.map_some]
      rw [List.replicate_succ, List.cons_append]

/-- A suffix without the lower letter cannot change which earlier letter
is lowered.  This follows from the actual one-letter append calculations. -/
theorem listString_lower_append_of_not_mem (r : ℕ) (u v : List ℕ)
    (hv : r ∉ v) :
    (listString r).lower (u ++ v) =
      ((listString r).lower u).map (fun w => w ++ v) := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v a ih =>
      have hv' : r ∉ v := fun hm => hv (by simp [hm])
      have ha : a ≠ r := fun heq => hv (by simp [heq])
      rw [← List.append_assoc]
      by_cases ha' : a = r + 1
      · subst a
        rw [listString_lower_append_upper, ih hv']
        simp only [Option.map_map, Function.comp_def, List.append_assoc]
      · rw [listString_lower_append_neutral r a _ ha ha', ih hv']
        simp only [Option.map_map, Function.comp_def, List.append_assoc]

/-- The exact signature length preceding the zero block, allowing arbitrary
positive letters on either side. -/
theorem listString_phi_zeroBlock (before suffix : List ℕ) (m : ℕ)
    (hp : 0 ∉ before) (hs : 0 ∉ suffix) :
    (listString 0).phi (before ++ List.replicate m 0 ++ suffix) =
      m - before.count 1 := by
  obtain ⟨he, hphi⟩ := listString_signature_of_not_mem 0 hp
  obtain ⟨_, hsphi⟩ := listString_signature_of_not_mem 0 hs
  rw [List.append_assoc, (listString_signature_append 0 _ _).2,
    (listString_signature_append 0 _ _).2, hphi, he, hsphi,
    (listString_signature_replicate_lower 0 m).1,
    (listString_signature_replicate_lower 0 m).2]
  simp

/-- The first lowering changes precisely the rightmost zero when the
minimal-letter block outnumbers the preceding ones.  In a tableau the
stronger global condition `number of ones < number of zeros` supplies this
inequality automatically. -/
theorem listString_lower_zeroBlock (before suffix : List ℕ) (m : ℕ)
    (hp : 0 ∉ before) (hs : 0 ∉ suffix) (hm : before.count 1 < m + 1) :
    (listString 0).lower (before ++ List.replicate (m + 1) 0 ++ suffix) =
      some (before ++ List.replicate m 0 ++ 1 :: suffix) := by
  induction before with
  | nil =>
      rw [List.nil_append, List.nil_append,
        listString_lower_append_of_not_mem 0 _ suffix hs,
        listString_lower_replicate_lower, Option.map_some]
      simp only [Nat.zero_add, List.append_assoc, List.singleton_append]
  | cons a before ih =>
      have ha : a ≠ 0 := fun heq => hp (by simp [heq])
      have hp' : 0 ∉ before := fun hx => hp (by simp [hx])
      have hm' : before.count 1 < m + 1 := by
        simp only [List.count_cons] at hm
        omega
      have hcondition : (letterString 0).epsilon a <
          (listString 0).phi (before ++ List.replicate (m + 1) 0 ++ suffix) := by
        rw [listString_phi_zeroBlock before suffix (m + 1) hp' hs]
        by_cases ha1 : a = 1
        · subst a
          have hcount : before.count 1 + 1 < m + 1 := by
            simpa only [List.count_cons_self] using hm
          change (1 : ℕ) < m + 1 - before.count 1
          omega
        · simp only [letterString_epsilon, Nat.zero_add, if_neg ha1]
          omega
      simp only [List.cons_append, listString_lower_cons, if_pos hcondition,
        ih hp' hm', Option.map_some]

end HigherSpecht.Lascoux
end
end CanonicalSource17

section CanonicalSource18
/- Source: HigherSpecht/LascouxTableauRowWords.lean -/



/-!
# Literal row words of semistandard tableaux

Each row is split at its three actual `rowCountLt` values into irrelevant
letters, a constant lower-letter block, a constant upper-letter block, and
irrelevant letters.  These equalities connect the recut API to the literal
signature words; the block boundaries are counted from the tableau itself.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

variable {mu : YoungDiagram}

def tableauRowSegment (T : SemistandardYoungTableau mu) (r a b : ℕ) : List ℕ :=
  (List.range' a (b - a)).map (T r)

def tableauRowWord (T : SemistandardYoungTableau mu) (r : ℕ) : List ℕ :=
  tableauRowSegment T r 0 (mu.rowLen r)

def tableauRowBefore (T : SemistandardYoungTableau mu) (v r : ℕ) : List ℕ :=
  tableauRowSegment T r 0 (T.rowCountLt r v)

def tableauRowAfter (T : SemistandardYoungTableau mu) (v r : ℕ) : List ℕ :=
  tableauRowSegment T r (T.rowCountLt r (v + 2)) (mu.rowLen r)

@[simp] theorem tableauRowSegment_length (T : SemistandardYoungTableau mu) (r a b : ℕ) :
    (tableauRowSegment T r a b).length = b - a := by
  simp [tableauRowSegment]

theorem tableauRowSegment_append (T : SemistandardYoungTableau mu) (r a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    tableauRowSegment T r a b ++ tableauRowSegment T r b c = tableauRowSegment T r a c := by
  unfold tableauRowSegment
  rw [← List.map_append]
  apply congrArg (List.map (T r))
  calc
    List.range' a (b - a) ++ List.range' b (c - b) =
        List.range' a (b - a) ++ List.range' (a + (b - a)) (c - b) := by
      rw [Nat.add_sub_of_le hab]
    _ = List.range' a ((b - a) + (c - b)) := List.range'_append_1
    _ = List.range' a (c - a) := by congr 1; omega

theorem map_eq_replicate_of_forall {A B : Type*} (xs : List A) (f : A → B) (b : B)
    (h : ∀ x ∈ xs, f x = b) : xs.map f = List.replicate xs.length b := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.length_cons, List.replicate_succ,
        h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem tableauRowSegment_lower_block (T : SemistandardYoungTableau mu) (v r : ℕ) :
    tableauRowSegment T r (T.rowCountLt r v) (T.rowCountLt r (v + 1)) =
      List.replicate (rowLowerCount T v r) v := by
  have hm : ∀ j ∈ List.range' (T.rowCountLt r v)
      (T.rowCountLt r (v + 1) - T.rowCountLt r v), T r j = v := by
    intro j hj
    obtain ⟨k, hk, hj⟩ := List.mem_range'.mp hj
    have hmono := T.rowCountLt_mono r (Nat.le_succ v)
    have hjn : j < T.rowCountLt r (v + 1) := by omega
    have hja : T.rowCountLt r v ≤ j := by omega
    have hjlen := hjn.trans_le (T.rowCountLt_le_rowLen r (v + 1))
    have hlo := T.lt_rowCountLt_iff (x := v) hjlen
    have hhi := T.lt_rowCountLt_iff (x := v + 1) hjlen
    omega
  simpa only [tableauRowSegment, rowLowerCount, List.length_range'] using
    map_eq_replicate_of_forall
      (List.range' (T.rowCountLt r v) (T.rowCountLt r (v + 1) - T.rowCountLt r v))
      (T r) v hm

theorem tableauRowSegment_upper_block (T : SemistandardYoungTableau mu) (v r : ℕ) :
    tableauRowSegment T r (T.rowCountLt r (v + 1)) (T.rowCountLt r (v + 2)) =
      List.replicate (rowUpperCount T v r) (v + 1) := by
  simpa only [rowLowerCount, rowUpperCount, Nat.add_assoc] using
    tableauRowSegment_lower_block T (v + 1) r

theorem tableauRowWord_blocks (T : SemistandardYoungTableau mu) (v r : ℕ) :
    tableauRowWord T r = tableauRowBefore T v r ++
      List.replicate (rowLowerCount T v r) v ++
        List.replicate (rowUpperCount T v r) (v + 1) ++ tableauRowAfter T v r := by
  rw [← tableauRowSegment_lower_block, ← tableauRowSegment_upper_block]
  unfold tableauRowWord tableauRowBefore tableauRowAfter
  rw [tableauRowSegment_append T r 0 (T.rowCountLt r v)
    (T.rowCountLt r (v + 1)) (Nat.zero_le _) (T.rowCountLt_mono r (by omega))]
  rw [tableauRowSegment_append T r 0 (T.rowCountLt r (v + 1))
    (T.rowCountLt r (v + 2)) (Nat.zero_le _) (T.rowCountLt_mono r (by omega))]
  rw [tableauRowSegment_append T r 0 (T.rowCountLt r (v + 2))
    (mu.rowLen r) (Nat.zero_le _) (T.rowCountLt_le_rowLen r (v + 2))]

theorem tableauRowBefore_neutral (T : SemistandardYoungTableau mu) (v r : ℕ) :
    NeutralSignature v (tableauRowBefore T v r) := by
  apply neutralSignature_of_no_adjacent_letters
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  obtain ⟨k, hk, hj⟩ := List.mem_range'.mp hj
  have hjcut : j < T.rowCountLt r v := by omega
  have hjlen := hjcut.trans_le (T.rowCountLt_le_rowLen r v)
  have hlt := (T.lt_rowCountLt_iff (x := v) hjlen).mp hjcut
  exact ⟨by omega, by omega⟩

theorem tableauRowAfter_neutral (T : SemistandardYoungTableau mu) (v r : ℕ) :
    NeutralSignature v (tableauRowAfter T v r) := by
  apply neutralSignature_of_no_adjacent_letters
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  obtain ⟨k, hk, hj⟩ := List.mem_range'.mp hj
  have hbound := T.rowCountLt_le_rowLen r (v + 2)
  have hjcut : T.rowCountLt r (v + 2) ≤ j := by omega
  have hjlen : j < mu.rowLen r := by omega
  have hlt := T.lt_rowCountLt_iff (x := v + 2) hjlen
  exact ⟨by omega, by omega⟩

theorem tableauRowWord_signature (T : SemistandardYoungTableau mu) (v r : ℕ) :
    (listString v).epsilon (tableauRowWord T r) = rowUpperCount T v r ∧
      (listString v).phi (tableauRowWord T r) = rowLowerCount T v r := by
  rw [tableauRowWord_blocks T v r]
  simp only [listString_epsilon_append, listString_phi_append,
    (tableauRowBefore_neutral T v r).1, (tableauRowBefore_neutral T v r).2,
    (tableauRowAfter_neutral T v r).1, (tableauRowAfter_neutral T v r).2,
    (listString_lower_replicate_signature v _).1,
    (listString_lower_replicate_signature v _).2,
    (listString_upper_replicate_signature v _).1,
    (listString_upper_replicate_signature v _).2]
  exact ⟨by omega, by omega⟩

def loweredTableauRowWord (T : SemistandardYoungTableau mu) (v r : ℕ) : List ℕ :=
  tableauRowBefore T v r ++ List.replicate (rowLowerCount T v r - 1) v ++
    List.replicate (rowUpperCount T v r + 1) (v + 1) ++ tableauRowAfter T v r

theorem tableauRow_lower (T : SemistandardYoungTableau mu) (v r : ℕ)
    (hpos : 0 < rowLowerCount T v r) :
    (listString v).lower (tableauRowWord T r) =
      some (tableauRowBefore T v r ++
        List.replicate (rowLowerCount T v r - 1) v ++
          List.replicate (rowUpperCount T v r + 1) (v + 1) ++ tableauRowAfter T v r) := by
  rw [tableauRowWord_blocks T v r, lower_append_neutral (tableauRowAfter_neutral T v r)]
  rw [List.append_assoc, lower_prepend_neutral (tableauRowBefore_neutral T v r)]
  rw [listString_lower_append, (listString_lower_replicate_signature v _).1,
    (listString_upper_replicate_signature v _).2, if_neg (lt_irrefl 0)]
  have hlen : rowLowerCount T v r = (rowLowerCount T v r - 1) + 1 := by omega
  have hlower : (listString v).lower (List.replicate (rowLowerCount T v r) v) =
      some (List.replicate (rowLowerCount T v r - 1) v ++ [v + 1]) := by
    conv_lhs => rw [hlen]
    exact listString_lower_replicate_lower v _
  rw [hlower]
  simp only [Option.map_some, List.append_assoc, List.replicate_succ,
    List.cons_append, List.nil_append]

theorem tableauRow_lower_eq (T : SemistandardYoungTableau mu) (v r : ℕ)
    {output : List ℕ} (h : (listString v).lower (tableauRowWord T r) = some output) :
    0 < rowLowerCount T v r ∧ output = loweredTableauRowWord T v r := by
  have hs := (listString v).phi_lower h
  rw [(tableauRowWord_signature T v r).2] at hs
  have hp : 0 < rowLowerCount T v r := by omega
  refine ⟨hp, ?_⟩
  have heq := tableauRow_lower T v r hp
  rw [h] at heq
  exact Option.some.inj heq

theorem replicate_append_cons_eq {A : Type*} (a : A) (k : ℕ) (tail : List A) :
    List.replicate k a ++ a :: tail = List.replicate (k + 1) a ++ tail := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons a) ih

theorem listString_raise_replicate_upper (v k : ℕ) :
    (listString v).raise (List.replicate (k + 1) (v + 1)) =
      some (v :: List.replicate k (v + 1)) := by
  rw [List.replicate_succ, listString_raise_cons,
    (listString_upper_replicate_signature v k).2]
  simp [letterString, show v + 1 ≠ v by omega]

def raisedTableauRowWord (T : SemistandardYoungTableau mu) (v r : ℕ) : List ℕ :=
  tableauRowBefore T v r ++ List.replicate (rowLowerCount T v r + 1) v ++
    List.replicate (rowUpperCount T v r - 1) (v + 1) ++ tableauRowAfter T v r

theorem tableauRow_raise (T : SemistandardYoungTableau mu) (v r : ℕ)
    (hpos : 0 < rowUpperCount T v r) :
    (listString v).raise (tableauRowWord T r) = some (raisedTableauRowWord T v r) := by
  rw [tableauRowWord_blocks T v r, raise_append_neutral (tableauRowAfter_neutral T v r)]
  rw [List.append_assoc, raise_prepend_neutral (tableauRowBefore_neutral T v r)]
  rw [listString_raise_append, (listString_lower_replicate_signature v _).1,
    (listString_upper_replicate_signature v _).2, if_pos (le_refl 0)]
  have hlen : rowUpperCount T v r = (rowUpperCount T v r - 1) + 1 := by omega
  have hraise : (listString v).raise (List.replicate (rowUpperCount T v r) (v + 1)) =
      some (v :: List.replicate (rowUpperCount T v r - 1) (v + 1)) := by
    conv_lhs => rw [hlen]
    exact listString_raise_replicate_upper v _
  rw [hraise]
  simp only [Option.map_some, raisedTableauRowWord, List.append_assoc,
    replicate_append_cons_eq]

theorem tableauRow_raise_eq (T : SemistandardYoungTableau mu) (v r : ℕ)
    {output : List ℕ} (h : (listString v).raise (tableauRowWord T r) = some output) :
    0 < rowUpperCount T v r ∧ output = raisedTableauRowWord T v r := by
  have hs := (listString v).epsilon_raise h
  rw [(tableauRowWord_signature T v r).1] at hs
  have hp : 0 < rowUpperCount T v r := by omega
  refine ⟨hp, ?_⟩
  have heq := tableauRow_raise T v r hp
  rw [h] at heq
  exact Option.some.inj heq

end HigherSpecht.Lascoux
end
end CanonicalSource18

section CanonicalSource19
/- Source: HigherSpecht/LascouxTableauWords.lean -/



/-!
# Actual tableau row readings and the selected row

Rows are read from highest row index down to zero, and entries in each row
from left to right.  The partial word operator determines a genuine changed
row and returns the unchanged contexts and its actual adjacent-row context.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht.Lascoux

def descendingRows : ℕ → List ℕ
  | 0 => []
  | n + 1 => n :: descendingRows n

theorem descendingRows_eq_reverse_range (n : ℕ) :
    descendingRows n = (List.range n).reverse := by
  induction n with
  | zero => rfl
  | succ n ih => simp [descendingRows, List.range_succ, ih]

@[simp] theorem mem_descendingRows {n r : ℕ} : r ∈ descendingRows n ↔ r < n := by
  induction n with
  | zero => simp [descendingRows]
  | succ n ih => simp only [descendingRows, List.mem_cons, ih]; omega

theorem descendingRows_context {n r : ℕ} {before after : List ℕ}
    (h : descendingRows n = before ++ r :: after) :
    r < n ∧ after = descendingRows r ∧
      (∀ a ∈ before, r < a) ∧
      (r + 1 = n → before = []) ∧
      (r + 1 < n → ∃ before', before = before' ++ [r + 1]) := by
  induction n generalizing r before after with
  | zero =>
      have hl := congrArg List.length h
      simp [descendingRows] at hl
  | succ n ih =>
      cases before with
      | nil =>
          simp only [descendingRows, List.nil_append, List.cons.injEq] at h
          obtain ⟨hr, ha⟩ := h
          subst r
          exact ⟨by omega, ha.symm, by simp, fun _ => rfl, by intro h; omega⟩
      | cons a before =>
          simp only [descendingRows, List.cons_append, List.cons.injEq] at h
          obtain ⟨ha, ht⟩ := h
          subst a
          obtain ⟨hr, hafter, hbefore, htop, hprev⟩ := ih ht
          refine ⟨by omega, hafter, ?_, ?_, ?_⟩
          · intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact hr
            · exact hbefore a ha
          · intro htop'
            omega
          · intro hprev'
            by_cases hlt : r + 1 < n
            · obtain ⟨b, hb⟩ := hprev hlt
              exact ⟨n :: b, by simp only [hb, List.cons_append]⟩
            · have heq : r + 1 = n := by omega
              rw [htop heq]
              exact ⟨[], by simp [heq]⟩

def tableauWord {mu : YoungDiagram} (T : SemistandardYoungTableau mu) : List ℕ :=
  (descendingRows (mu.colLen 0)).flatMap (tableauRowWord T)

structure SelectedLoweringRow {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (v : ℕ) (output : List ℕ) where
  row : ℕ
  row_lt : row < mu.colLen 0
  before : List ℕ
  after : List ℕ
  rows_eq : descendingRows (mu.colLen 0) = before ++ row :: after
  after_eq : after = descendingRows row
  before_gt : ∀ a ∈ before, row < a
  before_top : row + 1 = mu.colLen 0 → before = []
  before_neighbor : row + 1 < mu.colLen 0 → ∃ b, before = b ++ [row + 1]
  lower_pos : 0 < rowLowerCount T v row
  output_eq : output = before.flatMap (tableauRowWord T) ++
    loweredTableauRowWord T v row ++ after.flatMap (tableauRowWord T)

theorem exists_selectedLoweringRow {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (v : ℕ) {output : List ℕ} (h : (listString v).lower (tableauWord T) = some output) :
    Nonempty (SelectedLoweringRow T v output) := by
  obtain ⟨before, row, after, row', hrows, hrow, hout⟩ :=
    lower_flatMap_context v (descendingRows (mu.colLen 0)) (tableauRowWord T) h
  obtain ⟨hr, ha, hb, htop, hneighbor⟩ := descendingRows_context hrows
  obtain ⟨hpos, hrow'⟩ := tableauRow_lower_eq T v row hrow
  refine ⟨⟨row, hr, before, after, hrows, ha, hb, htop, hneighbor, hpos, ?_⟩⟩
  simpa only [hrow'] using hout

theorem SelectedLoweringRow.word_eq {mu : YoungDiagram} {T : SemistandardYoungTableau mu}
    {v : ℕ} {output : List ℕ} (R : SelectedLoweringRow T v output) :
    tableauWord T = R.before.flatMap (tableauRowWord T) ++
      tableauRowWord T R.row ++ R.after.flatMap (tableauRowWord T) := by
  simp only [tableauWord, R.rows_eq, List.flatMap_append, List.flatMap_cons,
    List.append_assoc]

structure SelectedRaisingRow {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (v : ℕ) (output : List ℕ) where
  row : ℕ
  row_lt : row < mu.colLen 0
  before : List ℕ
  after : List ℕ
  rows_eq : descendingRows (mu.colLen 0) = before ++ row :: after
  after_eq : after = descendingRows row
  before_gt : ∀ a ∈ before, row < a
  upper_pos : 0 < rowUpperCount T v row
  output_eq : output = before.flatMap (tableauRowWord T) ++
    raisedTableauRowWord T v row ++ after.flatMap (tableauRowWord T)

theorem exists_selectedRaisingRow {mu : YoungDiagram} (T : SemistandardYoungTableau mu)
    (v : ℕ) {output : List ℕ} (h : (listString v).raise (tableauWord T) = some output) :
    Nonempty (SelectedRaisingRow T v output) := by
  obtain ⟨before, row, after, row', hrows, hrow, hout⟩ :=
    raise_flatMap_context v (descendingRows (mu.colLen 0)) (tableauRowWord T) h
  obtain ⟨hr, ha, hb, htop, hneighbor⟩ := descendingRows_context hrows
  obtain ⟨hpos, hrow'⟩ := tableauRow_raise_eq T v row hrow
  refine ⟨⟨row, hr, before, after, hrows, ha, hb, hpos, ?_⟩⟩
  simpa only [hrow'] using hout

theorem SelectedRaisingRow.word_eq {mu : YoungDiagram} {T : SemistandardYoungTableau mu}
    {v : ℕ} {output : List ℕ} (R : SelectedRaisingRow T v output) :
    tableauWord T = R.before.flatMap (tableauRowWord T) ++
      tableauRowWord T R.row ++ R.after.flatMap (tableauRowWord T) := by
  simp only [tableauWord, R.rows_eq, List.flatMap_append, List.flatMap_cons,
    List.append_assoc]

end HigherSpecht.Lascoux
end
end CanonicalSource19
