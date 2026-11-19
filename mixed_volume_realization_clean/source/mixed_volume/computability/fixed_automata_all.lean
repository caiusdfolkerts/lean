module

public import mixed_volume.computability.uniform_mix
public import matrix_mortality.matrix_semigroup
public import Mathlib.Tactic.FinCases
public import matrix_mortality.neary_encoding
public import matrix_mortality.undecidability.universal_mortality35
public import matrix_mortality.undecidability.problems
public import mixed_volume.computability.rational_primrec
public import Mathlib.Algebra.MvPolynomial.Eval
public import mixed_volume.computability.effective_pfa
public import mixed_volume.computability.rational_code
public import Mathlib.Computability.RE
public import Mathlib.Data.List.Sublists

/-! Standby source partition. Generation is not a proof certificate.
Exact copied proof ranges are recorded in the adjacent manifest. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators





/-! ## FixedPFA -/

namespace MixedVolume.FixedPFA
open SevenState UniformMix FractionalWords MatrixMortality

/-- Rational damping of an arbitrary signed row, without any bound on the
encoded input word length. -/
def normOne (v : State → ℚ) : ℚ := ∑ i, |v i|
def scale (v : State → ℚ) : ℚ := 1 / (1 + normOne v)

theorem normOne_nonneg (v : State → ℚ) : 0 ≤ normOne v :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem abs_le_normOne (v : State → ℚ) (i : State) : |v i| ≤ normOne v := by
  exact Finset.single_le_sum (f := fun j => |v j|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem scale_pos (v : State → ℚ) : 0 < scale v := by
  unfold scale
  have h := normOne_nonneg v
  positivity

theorem scaled_bound (v : State → ℚ) (i : State) : |scale v * v i| < 1 := by
  rw [abs_mul,abs_of_pos (scale_pos v)]
  have hd : 0 < 1 + normOne v := by linarith [normOne_nonneg v]
  rw [scale,one_div,inv_mul_eq_div,div_lt_one hd]
  linarith [abs_le_normOne v i]

def prefixRow (u v : List Bool) : State → ℚ := SevenState.row ᵥ* C u v

theorem sum_vecMul (r : State → ℚ) (M : M7) (hM : ∀ i, ∑ j, M i j = 1) :
    ∑ j, (r ᵥ* M) j = ∑ i, r i := by
  simp only [Matrix.vecMul,dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,hM,mul_one]

theorem prefixRow_sum (u v : List Bool) : ∑ i, prefixRow u v i = 0 := by
  rw [prefixRow,sum_vecMul _ _ (C_row_sum u v),SevenState.row_sum]

def initial (u v : List Bool) : State → ℚ :=
  uniform + (scale (prefixRow u v) / 14) • prefixRow u v

theorem initial_sum (u v : List Bool) : ∑ i, initial u v i = 1 := by
  simp only [initial,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum,prefixRow_sum,mul_zero,add_zero,uniform]
  norm_num

theorem initial_positive (u v : List Bool) (i : State) : 0 < initial u v i := by
  have h := (abs_lt.mp (scaled_bound (prefixRow u v) i)).1
  change 0 < 1/7 + (scale (prefixRow u v)/14)*prefixRow u v i
  nlinarith

variable {α : Type*} [Fintype α]

def matrices (upper lower : α → List Bool) : α → M7 :=
  transition (fun a => C (upper a) (lower a))

theorem matrices_positive (upper lower : α → List Bool) (a : α) (i j : State) :
    0 < matrices upper lower a i j := transition_positive _ _ _ _

theorem matrices_row_sum (upper lower : α → List Bool) (a : α) (i : State) :
    ∑ j, matrices upper lower a i j = 1 :=
  transition_row_sum _ (fun a => C_row_sum _ _) a i

theorem matrices_column_sum (upper lower : α → List Bool) (a : α) (j : State) :
    ∑ i, matrices upper lower a i j = 1 :=
  transition_column_sum _ (fun a => C_column_sum _ _) a j

theorem sum_wordProduct (r : State → ℚ) (M : α → M7)
    (hM : ∀ a i, ∑ j, M a i j = 1) (w : List α) :
    ∑ j, (r ᵥ* wordProduct M w) j = ∑ i, r i := by
  induction w generalizing r with
  | nil => simp
  | cons a w ih =>
    rw [wordProduct_cons,← Matrix.vecMul_vecMul,ih,sum_vecMul r (M a) (hM a)]

theorem uniform_C (u v : List Bool) : uniform ᵥ* C u v = uniform := by
  funext j
  simp only [Matrix.vecMul,dotProduct,uniform,← Finset.mul_sum,C_column_sum,mul_one]

theorem initial_J (u v : List Bool) : initial u v ᵥ* J = uniform := by
  funext j
  simp only [Matrix.vecMul,dotProduct,J,← Finset.sum_mul,initial_sum,one_mul,uniform]

theorem initial_word (upper lower : α → List Bool) (u v : List Bool) (w : List α) :
    initial u v ᵥ* wordProduct (matrices upper lower) w =
      uniform + (scale (prefixRow u v) / 14 *
        mixing (fun a => C (upper a) (lower a)) ^ w.length) •
        (SevenState.row ᵥ* C (u ++ spell upper w) (v ++ spell lower w)) := by
  rw [matrices,wordProduct_transition _ (fun a => C_row_sum _ _) (fun a => C_column_sum _ _),
    Matrix.vecMul_add,Matrix.vecMul_smul,Matrix.vecMul_smul,initial_J]
  rw [initial,Matrix.add_vecMul,Matrix.smul_vecMul,
    uniform_wordProduct _ (fun a => C_column_sum _ _) w,wordProduct_C]
  rw [prefixRow,Matrix.vecMul_vecMul,← C_append]
  module

/-- The fixed suffix is encoded in a fixed, bounded rational accepting column. -/
def suffixDeviation (U V : List Bool) (i : State) : ℚ := C U V i (some 0) - 1/7

def accepting (U V : List Bool) (i : State) : ℚ :=
  1/2 + (scale (suffixDeviation U V)/2) * suffixDeviation U V i

theorem accepting_bounds (U V : List Bool) (i : State) :
    0 < accepting U V i ∧ accepting U V i < 1 := by
  have h := abs_lt.mp (scaled_bound (suffixDeviation U V) i)
  unfold accepting
  constructor <;> nlinarith [h.1,h.2]

theorem acceptance_expand (U V : List Bool) (r : State → ℚ)
    (hr : ∑ i, r i = 1) :
    r ⬝ᵥ accepting U V = 1/2 + (scale (suffixDeviation U V)/2) *
      ((r ᵥ* C U V) (some 0) - 1/7) := by
  simp only [dotProduct,accepting,suffixDeviation,mul_add,mul_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp_rw [mul_left_comm (r _) (scale (suffixDeviation U V)/2)]
  simp only [← Finset.mul_sum,← Finset.sum_mul,hr,one_mul,Matrix.vecMul,dotProduct]

theorem acceptance (upper lower : α → List Bool) (u v U V : List Bool) (w : List α) :
    (initial u v ᵥ* wordProduct (matrices upper lower) w) ⬝ᵥ accepting U V =
      1/2 + (scale (suffixDeviation U V)/2 * (scale (prefixRow u v)/14) *
        mixing (fun a => C (upper a) (lower a)) ^ w.length) *
        score (u ++ spell upper w ++ U) (v ++ spell lower w ++ V) := by
  rw [acceptance_expand U V _ (by
    rw [sum_wordProduct _ _ (matrices_row_sum upper lower),initial_sum])]
  rw [initial_word,Matrix.add_vecMul,Matrix.smul_vecMul,uniform_C,
    Matrix.vecMul_vecMul,← C_append]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,uniform,row_C_first]
  ring

theorem acceptance_gt_cutpoint_iff (upper lower : α → List Bool)
    (u v U V : List Bool) (w : List α) :
    1/2 < (initial u v ᵥ* wordProduct (matrices upper lower) w) ⬝ᵥ accepting U V ↔
      u ++ spell upper w ++ U = v ++ spell lower w ++ V := by
  rw [acceptance,lt_add_iff_pos_right,mul_pos_iff_of_pos_left (by
    apply mul_pos
    · exact mul_pos (div_pos (scale_pos _) (by norm_num)) (div_pos (scale_pos _) (by norm_num))
    · exact pow_pos (mixing_pos _) _),score_pos_iff]

theorem acceptance_ge_cutpoint_iff (upper lower : α → List Bool)
    (u v U V : List Bool) (w : List α) :
    1/2 ≤ (initial u v ᵥ* wordProduct (matrices upper lower) w) ⬝ᵥ accepting U V ↔
      u ++ spell upper w ++ U = v ++ spell lower w ++ V := by
  rw [acceptance,le_add_iff_nonneg_right,mul_nonneg_iff_of_pos_left (by
    apply mul_pos
    · exact mul_pos (div_pos (scale_pos _) (by norm_num)) (div_pos (scale_pos _) (by norm_num))
    · exact pow_pos (mixing_pos _) _),score_nonneg_iff]

end MixedVolume.FixedPFA

/-! ## BinarySelector -/

namespace MixedVolume.BinarySelector
open MatrixMortality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev BlockState (ι : Type*) := Fin 4 × ι

def rotate : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 1).trans ((Equiv.swap 0 2).trans (Equiv.swap 0 3))

def applyMatrix (M : Fin 4 → Matrix ι ι ℚ) : Matrix (BlockState ι) (BlockState ι) ℚ :=
  fun i j => if i.1 = j.1 then M i.1 i.2 j.2 else 0

def rotateMatrix : Matrix (BlockState ι) (BlockState ι) ℚ :=
  fun i j => if j.1 = rotate i.1 ∧ j.2 = i.2 then 1 else 0

def matrices (M : Fin 4 → Matrix ι ι ℚ) : Bool → Matrix (BlockState ι) (BlockState ι) ℚ
  | false => applyMatrix M
  | true => rotateMatrix

def embed (b : Fin 4) (p : ι → ℚ) : BlockState ι → ℚ :=
  fun i => if i.1 = b then p i.2 else 0

def accepting (f : ι → ℚ) : BlockState ι → ℚ := fun i => f i.2

theorem embed_nonneg (b : Fin 4) (p : ι → ℚ) (hp : ∀ i, 0 ≤ p i) (j : BlockState ι) :
    0 ≤ embed b p j := by
  unfold embed
  split_ifs
  · exact hp _
  · exact le_rfl

theorem embed_sum (b : Fin 4) (p : ι → ℚ) : ∑ i, embed b p i = ∑ i, p i := by
  classical
  simp [embed,Fintype.sum_prod_type]

theorem embed_acceptance (b : Fin 4) (p f : ι → ℚ) :
    embed b p ⬝ᵥ accepting f = p ⬝ᵥ f := by
  classical
  simp [embed,accepting,dotProduct,Fintype.sum_prod_type]

theorem matrices_nonneg (M : Fin 4 → Matrix ι ι ℚ) (hM : ∀ a i j, 0 ≤ M a i j)
    (a : Bool) (i j : BlockState ι) : 0 ≤ matrices M a i j := by
  cases a <;> simp only [matrices,applyMatrix,rotateMatrix]
  · split_ifs
    · exact hM _ _ _
    · exact le_rfl
  · split_ifs <;> norm_num

theorem matrices_row_sum (M : Fin 4 → Matrix ι ι ℚ)
    (hM : ∀ a i, ∑ j, M a i j = 1) (a : Bool) (i : BlockState ι) :
    ∑ j, matrices M a i j = 1 := by
  classical
  cases a
  · simp [matrices,applyMatrix,Fintype.sum_prod_type,hM]
  · rw [Finset.sum_eq_single (rotate i.1,i.2)]
    · simp [matrices,rotateMatrix]
    · intro j _ hj
      have hn : ¬ (j.1 = rotate i.1 ∧ j.2 = i.2) := by
        rintro ⟨h₁,h₂⟩
        exact hj (Prod.ext h₁ h₂)
      simp [matrices,rotateMatrix,hn]
    · simp

theorem matrices_column_sum (M : Fin 4 → Matrix ι ι ℚ)
    (hM : ∀ a j, ∑ i, M a i j = 1) (a : Bool) (j : BlockState ι) :
    ∑ i, matrices M a i j = 1 := by
  classical
  cases a
  · simp [matrices,applyMatrix,Fintype.sum_prod_type,hM]
  · simp only [matrices,rotateMatrix,Fintype.sum_prod_type]
    have h : (∑ b : Fin 4, if j.1 = rotate b then (1 : ℚ) else 0) = 1 := by
      have he := Equiv.sum_comp rotate (fun b => if j.1 = b then (1 : ℚ) else 0)
      simpa using he
    convert h using 1
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : j.1 = rotate b <;> simp [hb]

theorem embed_apply (M : Fin 4 → Matrix ι ι ℚ) (b : Fin 4) (p : ι → ℚ) :
    embed b p ᵥ* applyMatrix M = embed b (p ᵥ* M b) := by
  classical
  funext j
  rcases j with ⟨c,j⟩
  by_cases h : b = c
  · subst c
    simp [embed,applyMatrix,Matrix.vecMul,dotProduct,Fintype.sum_prod_type]
  · simp [embed,applyMatrix,Matrix.vecMul,dotProduct,Fintype.sum_prod_type,h,Ne.symm h]

theorem embed_rotate (b : Fin 4) (p : ι → ℚ) :
    embed b p ᵥ* rotateMatrix = embed (rotate b) p := by
  classical
  funext j
  rcases j with ⟨c,j⟩
  simp only [Matrix.vecMul,dotProduct,rotateMatrix]
  rw [Finset.sum_eq_single (rotate.symm c,j)]
  · simp [embed,Equiv.symm_apply_eq]
  · intro i _ hi
    have hn : ¬ (c = rotate i.1 ∧ j = i.2) := by
      rintro ⟨h₁,h₂⟩
      apply hi
      apply Prod.ext
      · simpa only [Equiv.symm_apply_apply] using (congrArg rotate.symm h₁).symm
      · exact h₂.symm
    simp only [if_neg hn,mul_zero]
  · simp

def decode (b : Fin 4) : List Bool → List (Fin 4)
  | [] => []
  | false :: w => b :: decode b w
  | true :: w => decode (rotate b) w

def finalBlock (b : Fin 4) : List Bool → Fin 4
  | [] => b
  | false :: w => finalBlock b w
  | true :: w => finalBlock (rotate b) w

theorem word_simulation (M : Fin 4 → Matrix ι ι ℚ) (b : Fin 4) (p : ι → ℚ)
    (w : List Bool) :
    embed b p ᵥ* wordProduct (matrices M) w =
      embed (finalBlock b w) (p ᵥ* wordProduct M (decode b w)) := by
  induction w generalizing b p with
  | nil => simp [decode,finalBlock]
  | cons a w ih =>
    cases a
    · rw [wordProduct_cons,← Matrix.vecMul_vecMul]
      change (embed b p ᵥ* applyMatrix M) ᵥ* wordProduct (matrices M) w = _
      rw [embed_apply,ih]
      simp only [decode,finalBlock,wordProduct_cons,Matrix.vecMul_vecMul]
    · rw [wordProduct_cons,← Matrix.vecMul_vecMul]
      change (embed b p ᵥ* rotateMatrix) ᵥ* wordProduct (matrices M) w = _
      rw [embed_rotate,ih]
      rfl

/-- The selector returns to block zero after each encoded source letter. -/
def code : Fin 4 → List Bool
  | 0 => [false]
  | 1 => [true,false,true,true,true]
  | 2 => [true,true,false,true,true]
  | 3 => [true,true,true,false,true]

theorem code_decode (a : Fin 4) : decode 0 (code a) = [a] := by
  fin_cases a <;> decide

theorem code_finalBlock (a : Fin 4) : finalBlock 0 (code a) = 0 := by
  fin_cases a <;> decide

theorem code_simulation (M : Fin 4 → Matrix ι ι ℚ) (p : ι → ℚ) (a : Fin 4) :
    embed 0 p ᵥ* wordProduct (matrices M) (code a) = embed 0 (p ᵥ* M a) := by
  rw [word_simulation,code_decode,code_finalBlock]
  simp

def encode (w : List (Fin 4)) : List Bool := w.flatMap code

theorem encode_simulation (M : Fin 4 → Matrix ι ι ℚ) (p : ι → ℚ) (w : List (Fin 4)) :
    embed 0 p ᵥ* wordProduct (matrices M) (encode w) = embed 0 (p ᵥ* wordProduct M w) := by
  induction w generalizing p with
  | nil => simp [encode]
  | cons a w ih =>
    rw [show encode (a::w) = code a ++ encode w from rfl,wordProduct_append,
      ← Matrix.vecMul_vecMul,code_simulation,ih,wordProduct_cons,Matrix.vecMul_vecMul]

theorem universal_cutpoint_iff (M : Fin 4 → Matrix ι ι ℚ) (p f : ι → ℚ) (theta : ℚ) :
    (∀ w : List Bool, (embed 0 p ᵥ* wordProduct (matrices M) w) ⬝ᵥ accepting f ≤ theta) ↔
    ∀ w : List (Fin 4), (p ᵥ* wordProduct M w) ⬝ᵥ f ≤ theta := by
  constructor
  · intro h w
    simpa only [encode_simulation,embed_acceptance] using h (encode w)
  · intro h w
    rw [word_simulation,embed_acceptance]
    exact h (decode 0 w)

end MixedVolume.BinarySelector

/-! ## FixedCorrespondence -/

namespace MixedVolume.FixedCorrespondence

open MatrixMortality

/-- Complete the dangling final bit in the lower word of a tag history. -/
theorem lower_history_completion (β : ℕ) (body : List TagLetter)
    (history : List (Stroke TagLetter β)) :
    spell (nearyLower β body) (tileHistory history) ++ [true] =
      [true] ++ tagEncode β (produced (tagOutput body) history) := by
  cases history with
  | nil => rfl
  | cons first history =>
    rw [spell_nearyLower_tileHistory_append_true]
    simp only [produced_cons,tagOutput,tagEncode_cons,tagCode,List.cons_append]

/-- At a completed pulse, an arbitrary lower word parses into complete strokes.
The empty word represents the empty history. -/
theorem history_of_gap_scan (β : ℕ) (body : List TagLetter) (hβ : 0 < β)
    (word : List NearyTile)
    (hscan : pulseScan β (.gap β) (spell (nearyLower β body) word) = some (.gap β)) :
    ∃ history : List (Stroke TagLetter β), word = tileHistory history := by
  cases word with
  | nil => exact ⟨[],rfl⟩
  | cons tile rest =>
    apply tileHistory_of_pulseScan β body hβ
    change pulseScan β .virgin
      (nearyLower β body tile ++ spell (nearyLower β body) rest) = _
    change pulseScan β (.gap β)
      (nearyLower β body tile ++ spell (nearyLower β body) rest) = _ at hscan
    rw [pulseScan_append] at hscan ⊢
    cases tile with
    | erase letter =>
      rw [pulseScan_nearyLower_erase] at hscan
      simp at hscan
    | rule letter =>
      rw [pulseScan_nearyLower_rule_from_gap β β body hβ] at hscan
      simp only [or_true,if_true,Option.bind_some] at hscan
      rw [pulseScan_nearyLower_rule_from_virgin β body hβ]
      exact hscan

/-- The variable left boundary is the initial queue with its final one removed. -/
def initialBoundary (β : ℕ) (front : List TagLetter) : List Bool :=
  tagEncode β front ++ nearyMarker β

/-- A fixed-morphism correspondence match yields precisely a queue-history equation. -/
theorem history_of_match (β : ℕ) (body front : List TagLetter) (hβ : 0 < β)
    (word : List NearyTile)
    (hmatch : spell (nearyUpper β) word ++ nearyMarker β =
      initialBoundary β front ++ spell (nearyLower β body) word) :
    ∃ history : List (Stroke TagLetter β),
      consumed history ++ [.b] = (front ++ [.b]) ++ produced (tagOutput body) history := by
  have hscan : pulseScan β (.gap β) (spell (nearyLower β body) word) = some (.gap β) := by
    have h := congrArg (pulseScan β .virgin) hmatch
    rw [spell_nearyUpper,pulseScan_encoded_final β hβ] at h
    rw [initialBoundary,pulseScan_append,pulseScan_encoded_final β hβ] at h
    exact h.symm
  obtain ⟨history,rfl⟩ := history_of_gap_scan β body hβ word hscan
  refine ⟨history,tagEncode_injective β hβ ?_⟩
  have h := congrArg (fun bits => bits ++ [true]) hmatch
  rw [spell_nearyUpper_tileHistory] at h
  have hright :
      (initialBoundary β front ++ spell (nearyLower β body) (tileHistory history)) ++ [true] =
        tagEncode β ((front ++ [.b]) ++ produced (tagOutput body) history) := by
    rw [List.append_assoc,lower_history_completion]
    simp [initialBoundary,tagEncode_append,tagEncode_cons,tagCode,nearyMarker,List.append_assoc]
  rw [hright] at h
  simpa only [tagEncode_append,marker_append_true,List.append_assoc] using h

/-- Every terminating computation whose short terminal queue is `[b]` has a
matching word for the fixed four tiles. -/
theorem match_of_halts (β : ℕ) (body front : List TagLetter)
    (hβ : 2 < β) (hbody : β - 1 ∣ body.length)
    (hinvariant : NearyInvariant β (front ++ [.b]))
    (hhalts : TagHaltsFrom β (tagOutput body) (front ++ [.b])) :
    ∃ word : List NearyTile,
      spell (nearyUpper β) word ++ nearyMarker β =
        initialBoundary β front ++ spell (nearyLower β body) word := by
  obtain ⟨history,hhistory⟩ := terminal_history_of_tagHaltsFrom
    (tagOutput body) (NearyInvariant β) [.b] (front ++ [.b])
    (nearyInvariant_step β body (by omega) hbody)
    (nearyInvariant_short_eq_b β hβ) hinvariant hhalts
  refine ⟨tileHistory history,?_⟩
  apply List.append_cancel_right (bs := [true])
  rw [spell_nearyUpper_tileHistory]
  rw [List.append_assoc (initialBoundary β front),lower_history_completion]
  calc
    (tagEncode β (consumed history) ++ nearyMarker β) ++ [true] =
        tagEncode β (consumed history ++ [.b]) := by
          simp only [tagEncode_append,marker_append_true,List.append_assoc]
    _ = tagEncode β ((front ++ [.b]) ++ produced (tagOutput body) history) :=
      congrArg (tagEncode β) hhistory
    _ = initialBoundary β front ++ ([true] ++ tagEncode β (produced (tagOutput body) history)) := by
      simp [initialBoundary,tagEncode_append,tagEncode_cons,tagCode,nearyMarker,List.append_assoc]

/-- Universal equivalence for the arbitrary initial queue, including immediate
termination and arbitrary candidate correspondence words. -/
theorem match_iff_halts (β : ℕ) (body front : List TagLetter)
    (hβ : 2 < β) (hbody : β - 1 ∣ body.length)
    (hinvariant : NearyInvariant β (front ++ [.b])) :
    (∃ word : List NearyTile,
      spell (nearyUpper β) word ++ nearyMarker β =
        initialBoundary β front ++ spell (nearyLower β body) word) ↔
      TagHaltsFrom β (tagOutput body) (front ++ [.b]) := by
  constructor
  · rintro ⟨word,hword⟩
    obtain ⟨history,hhistory⟩ := history_of_match β body front (by omega) word hword
    exact tagHaltsFrom_of_history (tagOutput body) history (front ++ [.b]) [.b]
      (by simp; omega) hhistory
  · exact match_of_halts β body front hβ hbody hinvariant

end MixedVolume.FixedCorrespondence

/-! ## FixedTag -/

namespace MixedVolume.FixedTag

open MatrixMortality MatrixMortality.Undecidability
open MatrixMortality.Undecidability.NearyCompiler

variable {ι : Type*} [Primcodable ι] {accepts : ι → Prop}

def beta (S : TwoTagSource ι accepts) : ℕ := deletionWidth S.period

def fixedBody (S : TwoTagSource ι accepts) : List TagLetter :=
  body S.cyclicSystem [] S.haltPhase S.period_pos

def whole (S : TwoTagSource ι accepts) : List TagLetter :=
  wholeAppendant S.cyclicSystem [] S.haltPhase S.period_pos

def bitsWord (S : TwoTagSource ι accepts) (bits : List Bool) : List TagLetter :=
  spell (bitObject S.cyclicSystem [] S.haltPhase S.period_pos) bits

def padding (S : TwoTagSource ι accepts) (bits : List Bool) : ℕ :=
  beta S + 1 - (bitsWord S bits).length % (beta S - 1)

def tokens (S : TwoTagSource ι accepts) (bits : List Bool) : List DataToken :=
  bits.map .bit ++ List.replicate (padding S bits) (.junk .raw)

def queueBits (S : TwoTagSource ι accepts) (bits : List Bool) : List TagLetter :=
  (bitsWord S bits ++ repeatWord (padding S bits) (whole S)).drop 1

def queue (S : TwoTagSource ι accepts) (index : ι) : List TagLetter :=
  queueBits S (S.cyclicInput index)

theorem beta_large (S : TwoTagSource ι accepts) : 2 < beta S := deletionWidth_large S.period_pos

theorem whole_eq (S : TwoTagSource ι accepts) : whole S = fixedBody S ++ [.b] :=
  wholeAppendant_eq_body_append S.cyclicSystem [] S.haltPhase S.period_pos

theorem fixedBody_divisible (S : TwoTagSource ι accepts) : beta S - 1 ∣ (fixedBody S).length :=
  (arithmeticEnvelope S.cyclicSystem [] S.haltPhase S.period_pos).body_divisible

theorem whole_length_mod (S : TwoTagSource ι accepts) : (whole S).length ≡ 1 [MOD beta S - 1] := by
  rw [whole_eq,List.length_append,List.length_singleton]
  exact (fixedBody_divisible S).modEq_zero_nat.add (Nat.ModEq.refl 1)

theorem whole_long (S : TwoTagSource ι accepts) : beta S ≤ (whole S).length := by
  rw [whole,wholeAppendant_length]
  have ht := trackWidth_pos S.cyclicSystem []
  exact Nat.le_mul_of_pos_right _ ht

theorem padding_ge_three (S : TwoTagSource ι accepts) (bits : List Bool) : 3 ≤ padding S bits := by
  have hb := beta_large S
  have hm := Nat.mod_lt (bitsWord S bits).length (show 0 < beta S-1 by omega)
  dsimp [padding]
  omega

theorem encode_tokens (S : TwoTagSource ι accepts) (bits : List Bool) :
    encodeData S.cyclicSystem [] S.haltPhase S.period_pos (tokens S bits) =
      bitsWord S bits ++ repeatWord (padding S bits) (whole S) := by
  rw [tokens,encodeData_append]
  congr 1
  · simpa [bitsWord,encodeData,Function.comp_def,dataTokenWord] using
      (spell_comp_map (dataTokenWord S.cyclicSystem [] S.haltPhase S.period_pos) DataToken.bit bits).symm
  · induction padding S bits with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ,encodeData_cons,repeatWord_succ_left,ih]
      rfl

theorem dataBits_tokens (S : TwoTagSource ι accepts) (bits : List Bool) :
    dataBits (tokens S bits) = bits := by
  rw [tokens,dataBits_append,dataBits_bits]
  have hz (n : ℕ) : dataBits (List.replicate n (DataToken.junk JunkAtom.raw)) = [] := by
    induction n with
    | zero => rfl
    | succ n ih => simpa [List.replicate_succ,dataBits] using ih
  rw [hz,List.append_nil]

theorem tokens_stable (S : TwoTagSource ι accepts) (bits : List Bool) (hb : bits ≠ []) :
    StableData (tokens S bits) := by
  have hn : 0 < padding S bits := lt_of_lt_of_le (by decide : 0 < 3) (padding_ge_three S bits)
  have hend : EndsInJunk (List.replicate (padding S bits) (DataToken.junk JunkAtom.raw)) := by
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hn,List.replicate_succ']
    exact EndsInJunk.prepend _ (.last .raw)
  refine ⟨EndsInJunk.prepend _ hend,?_⟩
  intro h
  exact False.elim (hb ((dataBits_tokens S bits).symm.trans h))

theorem queueBits_semantic (S : TwoTagSource ι accepts) (bits : List Bool) :
    queueBits S bits =
      (encodeData S.cyclicSystem [] S.haltPhase S.period_pos (tokens S bits)).drop
        (objectEntryPhase (⟨0,S.period_pos⟩ : Fin S.period)).val := by
  rw [objectEntryPhase_zero _ rfl,encode_tokens]
  rfl

theorem queueBits_long (S : TwoTagSource ι accepts) (bits : List Bool) :
    beta S ≤ (queueBits S bits).length := by
  have hw := whole_long S
  have hp := padding_ge_three S bits
  have hb := beta_large S
  rw [queueBits,List.length_drop,List.length_append,repeatWord_length]
  have hh : beta S + beta S ≤ padding S bits * (whole S).length :=
    calc
      beta S + beta S = 2 * beta S := by omega
      _ ≤ padding S bits * (whole S).length := Nat.mul_le_mul (by omega) hw
  omega

theorem queueBits_ends (S : TwoTagSource ι accepts) (bits : List Bool) : EndsInB (queueBits S bits) := by
  have hp := padding_ge_three S bits
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (show padding S bits ≠ 0 by omega)
  rw [queueBits,hn,repeatWord_succ_right,whole_eq]
  let front := bitsWord S bits ++ repeatWord n (fixedBody S ++ [.b]) ++ fixedBody S
  have hf : 1 ≤ front.length := by
    have hb := beta_large S
    have hl := (arithmeticEnvelope S.cyclicSystem [] S.haltPhase S.period_pos).body_long
    change beta S - 1 ≤ (fixedBody S).length at hl
    dsimp [front]
    simp only [List.length_append]
    omega
  refine ⟨front.drop 1,?_⟩
  simpa only [front,List.append_assoc] using
    (List.drop_append_of_le_length hf :
      (front ++ [TagLetter.b]).drop 1 = front.drop 1 ++ [TagLetter.b])

theorem queueBits_invariant (S : TwoTagSource ι accepts) (bits : List Bool) :
    NearyInvariant (beta S) (queueBits S bits) := by
  refine ⟨queueBits_ends S bits,?_⟩
  have hp := padding_ge_three S bits
  have hw := whole_length_mod S
  have hb := beta_large S
  let L := (bitsWord S bits).length
  let r := padding S bits
  have hr : L % (beta S-1) + r = beta S+1 := by
    have hm := Nat.mod_lt (bitsWord S bits).length (show 0 < beta S-1 by omega)
    dsimp [r,padding,L]
    omega
  have hsum : L + r * (whole S).length ≡ 2 [MOD beta S-1] := by
    have hh := (Nat.mod_modEq L (beta S-1)).symm.add (hw.mul_left r)
    have he : L % (beta S-1)+r*1 = beta S+1 := by omega
    rw [he] at hh
    have hb2 : beta S+1 ≡ 2 [MOD beta S-1] := by
      have he : beta S+1 = (beta S-1)+2 := by omega
      rw [he]
      exact Nat.add_modEq_left
    exact hh.trans hb2
  have hge : 1 ≤ L + r * (whole S).length := by
    have hw' := whole_long S
    have : beta S ≤ r * (whole S).length := Nat.le_trans hw' (Nat.le_mul_of_pos_left _ (by dsimp [r]; omega))
    omega
  have hsub := Nat.ModEq.sub hge (by decide : 1 ≤ 2) hsum (Nat.ModEq.refl (n := beta S-1) 1)
  simpa [queueBits,List.length_drop,List.length_append,repeatWord_length,L,r] using hsub

theorem queue_halting_iff (S : TwoTagSource ι accepts) (index : ι) :
    TagHaltsFrom (beta S) (tagOutput (fixedBody S)) (queue S index) ↔ accepts index := by
  rw [queue,queueBits_semantic,beta,fixedBody,
    ← compiledOutput_eq_tagOutput S.cyclicSystem [] S.haltPhase S.period_pos]
  constructor
  · intro hh
    obtain ⟨firing,reach,fires⟩ := semantic_halts_implies_firing S.cyclicSystem [] S.haltPhase
      S.period_pos S.appendant_nonempty_at_zero ⟨0,S.period_pos⟩ (tokens S (S.cyclicInput index))
      (tokens_stable S _ (S.cyclicInput_nonempty index)) hh
    rw [dataBits_tokens] at reach
    exact S.accepts_of_avoidingFiring index firing reach fires
  · intro ha
    obtain ⟨firingTokens,stable,bits,beforePulse⟩ := read_avoidingReaches S.cyclicSystem [] S.haltPhase
      S.period_pos S.appendant_nonempty_at_zero (S.accepts_implies_exactFiring index ha)
      (tokens S (S.cyclicInput index)) (tokens_stable S _ (S.cyclicInput_nonempty index))
      (dataBits_tokens S _)
    obtain ⟨remaining,ends,empty,pulse⟩ := read_next_firing S.cyclicSystem [] S.haltPhase
      S.period_pos S.haltPhase_nonzero firingTokens stable [] bits
    obtain ⟨emitted,_,drains⟩ := drain_junk_before_haltingSeed S.cyclicSystem [] S.haltPhase
      (CyclicTag.shift S.haltPhase 1) S.period_pos remaining ends empty
    apply tagHaltsFrom_of_reaches (beforePulse.trans (pulse.trans drains))
    exact postHaltingSeed_halts S.cyclicSystem [] S.haltPhase (CyclicTag.shift S.haltPhase 1)
      S.period_pos emitted

theorem bitsWord_primrec (S : TwoTagSource ι accepts) : Primrec (bitsWord S) := by
  have h : Primrec (bitObject S.cyclicSystem [] S.haltPhase S.period_pos) := Primrec.dom_finite _
  exact (Primrec.list_flatMap Primrec.id (h.comp₂ Primrec₂.right)).of_eq fun _ => rfl

theorem padding_primrec (S : TwoTagSource ι accepts) : Primrec (padding S) :=
  Primrec.nat_sub.comp (Primrec.const _) (Primrec.nat_mod.comp
    (Primrec.list_length.comp (bitsWord_primrec S)) (Primrec.const _))

theorem queueBits_primrec (S : TwoTagSource ι accepts) : Primrec (queueBits S) := by
  have hr : Primrec (fun bits => repeatWord (padding S bits) (whole S)) :=
    Primrec.list_flatten.comp (MatrixMortality.Primrec.list_replicate.comp (padding_primrec S) (Primrec.const _))
  exact Primrec.list_drop.comp (Primrec.const 1) (Primrec.list_append.comp (bitsWord_primrec S) hr)

theorem queue_primrec (S : TwoTagSource ι accepts) : Primrec (queue S) :=
  (queueBits_primrec S).comp S.cyclicInput_primrec

/-- A fixed binary tag program, with a primitive-recursive input compiler,
recognizes the complete halting predicate. -/
theorem universal_queue_halting_iff (index : Nat.Partrec.Code) :
    TagHaltsFrom (beta UniversalTwoTag.source) (tagOutput (fixedBody UniversalTwoTag.source))
      (queue UniversalTwoTag.source index) ↔ CodeHalts index := queue_halting_iff _ _

end MixedVolume.FixedTag

/-! ## Completeness -/

namespace MixedVolume.Completeness

open MatrixMortality.Undecidability Encodable

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- Every semidecidable predicate many-one reduces to halting at input zero. -/
theorem re_reduces_halting {p : α → Prop} (hp : REPred p) : p ≤₀ CodeHalts := by
  have h : Partrec₂ (fun a : α => fun _ : ℕ =>
      Part.assert (p a) (fun _ => Part.some ())) :=
    ((show Partrec _ from hp).comp Computable.fst).to₂
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp h
  refine ⟨fun a => Nat.Partrec.Code.curry c (encode a),
    (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const c) Primrec.encode).to_comp,?_⟩
  intro a
  change p a ↔ (Nat.Partrec.Code.eval (Nat.Partrec.Code.curry c (encode a)) 0).Dom
  rw [Nat.Partrec.Code.eval_curry,hc]
  simp [Part.assert]

/-- Taking complements preserves the same computable reduction map. -/
theorem complement_reduction {p : α → Prop} {q : β → Prop} (h : p ≤₀ q) :
    (fun a => ¬p a) ≤₀ (fun b => ¬q b) := by
  obtain ⟨f,hf,he⟩ := h
  exact ⟨f,hf,fun a => not_congr (he a)⟩

/-- Co-recursive enumerability and hardness under computable many-one reductions. -/
def CoREComplete (q : β → Prop) : Prop :=
  REPred (fun b => ¬q b) ∧
    ∀ (p : ℕ → Prop), REPred (fun n => ¬p n) → p ≤₀ q

theorem complete_of_nonhalting_reduction {q : β → Prop}
    (upper : REPred (fun b => ¬q b))
    (hard : (fun c => ¬CodeHalts c) ≤₀ q) : CoREComplete q := by
  refine ⟨upper,?_⟩
  intro p hp
  have h := complement_reduction (re_reduces_halting hp)
  have h' : p ≤₀ (fun c => ¬CodeHalts c) := by
    simpa only [not_not] using h
  exact h'.trans hard

/-- Every co-r.e.-hard target in this development is undecidable. -/
theorem not_computable_of_nonhalting_reduction {q : β → Prop}
    (hard : (fun c => ¬CodeHalts c) ≤₀ q) : ¬ComputablePred q := by
  intro hq
  have h := ComputablePred.computable_of_manyOneReducible hard hq
  exact codeHalts_not_computable (h.not.of_eq (fun _ => not_not))

/-- A co-r.e.-hard target cannot itself be recursively enumerable. -/
theorem not_re_of_nonhalting_reduction {q : β → Prop}
    (hard : (fun c => ¬CodeHalts c) ≤₀ q) : ¬REPred q := by
  intro hq
  obtain ⟨f,hf,he⟩ := hard
  have h : REPred (fun c => q (f c)) := (show Partrec _ from hq).comp hf
  exact ComputablePred.halting_problem_not_re 0 (h.of_eq (fun c => (he c).symm))

/-- Undecidability on a promise domain also excludes partial algorithms that
may diverge outside that domain. Every emitted hard instance meets the promise. -/
theorem no_partial_decider_on_promise {q promise : β → Prop}
    (emit : Nat.Partrec.Code → β) (effective : Computable emit)
    (promised : ∀ c, promise (emit c))
    (correct : ∀ c, q (emit c) ↔ ¬ CodeHalts c) :
    ¬ ∃ decision : β →. Bool, Partrec decision ∧
      ∀ b, promise b → ∃ answer : Bool,
        answer ∈ decision b ∧ (answer = true ↔ q b) := by
  classical
  rintro ⟨decision,hd,answers⟩
  choose answer member accurate using (fun c => answers (emit c) (promised c))
  have ha : Computable answer := (hd.comp effective).of_eq_tot member
  have hnon : ComputablePred (fun c => ¬ CodeHalts c) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨answer,ha,?_⟩
    funext c
    exact propext ((accurate c).trans (correct c)).symm
  exact codeHalts_not_computable (hnon.not.of_eq (fun _ => not_not))

/-- Exact finite certificate search yields a recursively enumerable language. -/
theorem certificate_re {q : β → Prop} (verify : β × ℕ → Prop)
    (effective : ComputablePred verify)
    (correct : ∀ b, q b ↔ ∃ n, verify (b,n)) : REPred q := by
  classical
  have hr : Partrec (fun b => Nat.rfind (fun n => Part.some (decide (verify (b,n))))) :=
    Partrec.rfind effective.decide.partrec
  apply hr.dom_re.of_eq
  intro b
  rw [correct]
  simp [Nat.rfind_dom]

/-- A sound and complete effective finite-certificate verifier is impossible. -/
theorem no_finite_certificates {q : β → Prop}
    (hard : (fun c => ¬CodeHalts c) ≤₀ q) :
    ¬ ∃ verify : β × ℕ → Prop, ComputablePred verify ∧
      ∀ b, q b ↔ ∃ n, verify (b,n) := by
  rintro ⟨verify,effective,correct⟩
  exact not_re_of_nonhalting_reduction hard (certificate_re verify effective correct)

end MixedVolume.Completeness

/-! ## RationalPolynomial -/

namespace MixedVolume.RationalPrimrec

variable {α σ : Type*} [Primcodable α]

/-- Evaluating any fixed rational polynomial on effective rational inputs is
primitive recursive, with no bound on input denominators or numerators. -/
theorem polynomial_eval (P : MvPolynomial σ ℚ) {a : α → σ → ℚ}
    (ha : ∀ j, RationalPrimrec (fun x => a x j)) :
    RationalPrimrec (fun x => MvPolynomial.eval (a x) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (RationalPrimrec.const (α := α) c)
  | add P Q hP hQ => simpa using hP.add hQ
  | mul_X P j hP => simpa using hP.mul (ha j)

end MixedVolume.RationalPrimrec

/-! ## FixedUniversal -/

namespace MixedVolume.FixedUniversal

open MatrixMortality MatrixMortality.Undecidability Matrix
open scoped BigOperators

abbrev Source := Nat.Partrec.Code

def width : ℕ := FixedTag.beta UniversalTwoTag.source
def program : List TagLetter := FixedTag.fixedBody UniversalTwoTag.source
def queue (index : Source) : List TagLetter := FixedTag.queue UniversalTwoTag.source index
def front (index : Source) : List TagLetter := (queue index).dropLast
def inputPrefix (index : Source) : List Bool := FixedCorrespondence.initialBoundary width (front index)
def upper (a : Fin 4) : List Bool := nearyUpper width (nearyTileOfFin a)
def lower (a : Fin 4) : List Bool := nearyLower width program (nearyTileOfFin a)
def marker : List Bool := nearyMarker width

theorem front_append_b (index : Source) : front index ++ [.b] = queue index := by
  obtain ⟨q,hq⟩ := FixedTag.queueBits_ends UniversalTwoTag.source
    (UniversalTwoTag.source.cyclicInput index)
  change queue index = q ++ [.b] at hq
  simp [front,hq]

theorem prefix_primrec : Primrec inputPrefix :=
  Primrec.list_append.comp
    ((tagEncode_primrec width).comp
      (MatrixMortality.Primrec.list_dropLast.comp (FixedTag.queue_primrec UniversalTwoTag.source)))
    (Primrec.const marker)

/-- The four source tiles are fixed; the complete source input is in `inputPrefix`. -/
theorem correspondence_iff (index : Source) :
    (∃ w : List (Fin 4), spell upper w ++ marker = inputPrefix index ++ spell lower w) ↔
      CodeHalts index := by
  have relabel := gpcpSolvable_relabel_equiv (nearyUpper width) (nearyLower width program)
    [] marker (inputPrefix index) [] nearyTileEquivFin.symm
  have hu : (nearyUpper width) ∘ nearyTileEquivFin.symm = upper := by
    funext a
    rfl
  have hv : (nearyLower width program) ∘ nearyTileEquivFin.symm = lower := by
    funext a
    rfl
  rw [hu,hv] at relabel
  have hmatch := FixedCorrespondence.match_iff_halts width program (front index)
    (FixedTag.beta_large UniversalTwoTag.source)
    (FixedTag.fixedBody_divisible UniversalTwoTag.source)
    (by rw [front_append_b]; exact FixedTag.queueBits_invariant UniversalTwoTag.source _)
  rw [front_append_b] at hmatch
  have hhalts := FixedTag.universal_queue_halting_iff index
  have hrel : (∃ w : List (Fin 4), spell upper w ++ marker = inputPrefix index ++ spell lower w) ↔
      ∃ w : List NearyTile, spell (nearyUpper width) w ++ marker =
        inputPrefix index ++ spell (nearyLower width program) w := by
    simpa only [IsGPCPSolution,List.nil_append,List.append_nil] using relabel
  exact hrel.trans (hmatch.trans hhalts)

abbrev State := SevenState.State
abbrev BlockState := BinarySelector.BlockState State

def baseMatrices : Fin 4 → Matrix State State ℚ := FixedPFA.matrices upper lower
def baseInitial (index : Source) : State → ℚ := FixedPFA.initial [] (inputPrefix index)
def baseOutput : State → ℚ := FixedPFA.accepting marker []
def matrices : Bool → Matrix BlockState BlockState ℚ := BinarySelector.matrices baseMatrices
def initial (index : Source) : BlockState → ℚ := BinarySelector.embed 0 (baseInitial index)
def output : BlockState → ℚ := BinarySelector.accepting baseOutput

theorem base_initial_positive (index : Source) (j : State) : 0 < baseInitial index j :=
  FixedPFA.initial_positive [] (inputPrefix index) j

theorem initial_nonneg (index : Source) (j : BlockState) : 0 ≤ initial index j :=
  BinarySelector.embed_nonneg 0 _ (fun j => (base_initial_positive index j).le) j

theorem initial_sum (index : Source) : ∑ j, initial index j = 1 := by
  rw [initial,BinarySelector.embed_sum]
  exact FixedPFA.initial_sum [] (inputPrefix index)

theorem matrices_nonneg (a : Bool) (i j : BlockState) : 0 ≤ matrices a i j :=
  BinarySelector.matrices_nonneg baseMatrices
    (fun a i j => (FixedPFA.matrices_positive upper lower a i j).le) a i j

theorem matrices_row_sum (a : Bool) (i : BlockState) : ∑ j, matrices a i j = 1 :=
  BinarySelector.matrices_row_sum baseMatrices
    (FixedPFA.matrices_row_sum upper lower) a i

theorem matrices_column_sum (a : Bool) (j : BlockState) : ∑ i, matrices a i j = 1 :=
  BinarySelector.matrices_column_sum baseMatrices
    (FixedPFA.matrices_column_sum upper lower) a j

theorem output_bounds (j : BlockState) : 0 < output j ∧ output j < 1 :=
  FixedPFA.accepting_bounds marker [] j.2

/-- The universal cutpoint condition on arbitrary binary words is equivalent
to nonhalting of the source program. -/
theorem universal_iff (index : Source) :
    (∀ w : List Bool, (initial index ᵥ* wordProduct matrices w) ⬝ᵥ output ≤ 1/2) ↔
      ¬ CodeHalts index := by
  rw [initial,matrices,output,BinarySelector.universal_cutpoint_iff]
  rw [← correspondence_iff index]
  simp only [not_exists,← not_lt]
  apply forall_congr'
  intro w
  apply not_congr
  simpa only [baseInitial,baseMatrices,baseOutput,List.nil_append,List.append_nil] using
    FixedPFA.acceptance_gt_cutpoint_iff upper lower [] (inputPrefix index) marker [] w

theorem base_initial_effective (j : State) : RationalPrimrec (fun index => baseInitial index j) := by
  have hrow (i : State) : RationalPrimrec (fun index : Source =>
      FixedPFA.prefixRow [] (inputPrefix index) i) :=
    RationalPrimrec.vecMul (fun i => RationalPrimrec.const (SevenState.row i))
      (EffectivePFA.C_effective (Primrec.const []) prefix_primrec) i
  have hscale : RationalPrimrec (fun index : Source =>
      FixedPFA.scale (FixedPFA.prefixRow [] (inputPrefix index))) :=
    (RationalPrimrec.const 1).div
      ((RationalPrimrec.const 1).add (RationalPrimrec.finite_sum (fun i => (hrow i).abs)))
  exact (RationalPrimrec.const (UniformMix.uniform j)).add
    ((hscale.div (RationalPrimrec.const 14)).mul (hrow j))

theorem initial_effective (j : BlockState) : RationalPrimrec (fun index => initial index j) := by
  unfold initial BinarySelector.embed
  split_ifs
  · exact base_initial_effective j.2
  · exact RationalPrimrec.const 0

end MixedVolume.FixedUniversal

end -- noncomputable section
end -- public section

/- BEGIN SOURCE: MixedVolume/Computability/Represented.lean -/
section


/-! Exact computability through explicit surjective data representations.

Rational numbers use the already checked denominator-positive integer codes.
Lists and finite vectors retain their ordinary mathematical meaning: their
representations are simply lists and vectors of the corresponding codes.
The closure lemmas below prove actual Mathlib `Primrec` or `Computable`
programs, rather than identifying executable Lean code with computability.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace MixedVolume.Represented

class Representation (α : Type) where
  Code : Type
  instPrimcodable : Primcodable Code
  decode : Code → α
  onto : Function.Surjective decode

attribute [instance_reducible, instance] Representation.instPrimcodable

abbrev Code (α : Type) [Representation α] := Representation.Code α
abbrev decode {α : Type} [Representation α] : Code α → α := Representation.decode

@[reducible] instance (priority := 10) identityRepresentation (α : Type) [Primcodable α] :
    Representation α where
  Code := α
  instPrimcodable := inferInstance
  decode := id
  onto := Function.surjective_id

@[reducible] instance (priority := 2000) rationalRepresentation : Representation ℚ where
  Code := RationalCode.Code
  instPrimcodable := inferInstance
  decode := RationalCode.eval
  onto := RationalCode.eval_surjective

@[reducible] instance (priority := 1000) pairRepresentation (α β : Type)
    [Representation α] [Representation β] : Representation (α × β) where
  Code := Code α × Code β
  instPrimcodable := inferInstance
  decode x := (decode x.1, decode x.2)
  onto := by
    rintro ⟨a,b⟩
    obtain ⟨c,hc⟩ := Representation.onto a
    obtain ⟨d,hd⟩ := Representation.onto b
    exact ⟨(c,d),by simp [hc,hd]⟩

@[reducible] instance (priority := 1000) listRepresentation (α : Type) [Representation α] :
    Representation (List α) where
  Code := List (Code α)
  instPrimcodable := inferInstance
  decode x := x.map decode
  onto := by
    intro l
    induction l with
    | nil => exact ⟨[],rfl⟩
    | cons a l ih =>
      obtain ⟨c,hc⟩ := Representation.onto a
      obtain ⟨d,hd⟩ := ih
      exact ⟨c::d,by simp [hc,hd]⟩

@[reducible] instance (priority := 1000) functionRepresentation (n : ℕ) (α : Type)
    [Representation α] : Representation (Fin n → α) where
  Code := Fin n → Code α
  instPrimcodable := inferInstance
  decode x i := decode (x i)
  onto := by
    intro f
    classical
    choose c hc using fun i => Representation.onto (f i)
    exact ⟨c,funext hc⟩

def Primitive {α β : Type} [Representation α] [Representation β]
    (f : α → β) : Prop :=
  ∃ F : Code α → Code β, Primrec F ∧ ∀ c, decode (F c) = f (decode c)

def Effective {α β : Type} [Representation α] [Representation β]
    (f : α → β) : Prop :=
  ∃ F : Code α → Code β, Computable F ∧ ∀ c, decode (F c) = f (decode c)

namespace Primitive

variable {α β γ δ : Type} [Representation α] [Representation β]
  [Representation γ] [Representation δ]

theorem effective {f : α → β} (h : Primitive f) : Effective f := by
  obtain ⟨F,hF,he⟩ := h
  exact ⟨F,hF.to_comp,he⟩

theorem of_eq {f g : α → β} (hf : Primitive f) (h : ∀ x, f x = g x) :
    Primitive g := by
  obtain ⟨F,hF,he⟩ := hf
  exact ⟨F,hF,fun c => (he c).trans (h _)⟩

theorem comp {f : β → γ} {g : α → β} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f (g x)) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨F ∘ G,hF.comp hG,fun c => by rw [Function.comp_apply,heF,heG]⟩

theorem id : Primitive (_root_.id : α → α) := ⟨_root_.id,Primrec.id,fun _ => rfl⟩

theorem const (b : β) : Primitive (fun _ : α => b) := by
  obtain ⟨c,hc⟩ := Representation.onto b
  exact ⟨fun _ => c,Primrec.const c,fun _ => hc⟩

theorem fst : Primitive (Prod.fst : α × β → α) :=
  ⟨Prod.fst,Primrec.fst,fun _ => rfl⟩

theorem snd : Primitive (Prod.snd : α × β → β) :=
  ⟨Prod.snd,Primrec.snd,fun _ => rfl⟩

theorem pair {f : α → β} {g : α → γ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => (f x,g x)) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  refine ⟨fun c => (F c,G c),Primrec.pair hF hG,?_⟩
  intro c
  exact Prod.ext (heF c) (heG c)

theorem nat {f : α → ℕ} (hf : Primitive f) :
    Primitive (fun x => (f x : ℚ)) := by
  obtain ⟨F,hF,he⟩ := hf
  exact ⟨fun c => RationalCode.nat (F c),RationalCode.nat_primrec.comp hF,
    fun c => by
      change RationalCode.eval (RationalCode.nat (F c)) = (f (decode c) : ℚ)
      rw [RationalCode.eval_nat]
      exact congrArg (fun n : ℕ => (n : ℚ)) (he c)⟩

theorem add {f g : α → ℚ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x + g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨fun c => RationalCode.add (F c) (G c),RationalCode.add_primrec.comp hF hG,
    fun c => (RationalCode.eval_add _ _).trans (congrArg₂ (·+·) (heF c) (heG c))⟩

theorem mul {f g : α → ℚ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x * g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨fun c => RationalCode.mul (F c) (G c),RationalCode.mul_primrec.comp hF hG,
    fun c => (RationalCode.eval_mul _ _).trans (congrArg₂ (·*·) (heF c) (heG c))⟩

theorem neg {f : α → ℚ} (hf : Primitive f) : Primitive (fun x => -f x) := by
  obtain ⟨F,hF,he⟩ := hf
  exact ⟨fun c => RationalCode.neg (F c),RationalCode.neg_primrec.comp hF,
    fun c => (RationalCode.eval_neg _).trans (congrArg Neg.neg (he c))⟩

theorem inv {f : α → ℚ} (hf : Primitive f) : Primitive (fun x => (f x)⁻¹) := by
  obtain ⟨F,hF,he⟩ := hf
  exact ⟨fun c => RationalCode.inv (F c),RationalCode.inv_primrec.comp hF,
    fun c => (RationalCode.eval_inv _).trans (congrArg Inv.inv (he c))⟩

theorem abs {f : α → ℚ} (hf : Primitive f) : Primitive (fun x => |f x|) := by
  obtain ⟨F,hF,he⟩ := hf
  exact ⟨fun c => RationalCode.abs (F c),RationalCode.abs_primrec.comp hF,
    fun c => (RationalCode.eval_abs _).trans (congrArg (fun q : ℚ => |q|) (he c))⟩

theorem sub {f g : α → ℚ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x - g x) :=
  (hf.add hg.neg).of_eq fun _ => (sub_eq_add_neg _ _).symm

theorem div {f g : α → ℚ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x / g x) :=
  (hf.mul hg.inv).of_eq fun _ => (div_eq_mul_inv _ _).symm

theorem pow {f : α → ℚ} (hf : Primitive f) (n : ℕ) :
    Primitive (fun x => f x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (const (α := α) (1 : ℚ))
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem fin_app {n : ℕ} : Primitive (fun p : (Fin n → β) × Fin n => p.1 p.2) :=
  ⟨fun p => p.1 p.2,Primrec.fin_app,fun _ => rfl⟩

theorem fin_function {n : ℕ} {f : α → Fin n → β}
    (hf : ∀ i, Primitive (fun x => f x i)) : Primitive f := by
  classical
  choose F hF he using hf
  refine ⟨fun c i => F i c,MatrixMortality.Primrec.fin_function hF,?_⟩
  intro c
  exact funext fun i => he i c

theorem list_map {f : α → List β} {g : α × β → γ}
    (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => (f x).map (fun y => g (x,y))) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  refine ⟨fun c => (F c).map (fun d => G (c,d)),
    Primrec.list_map hF (Primrec₂.mk hG),?_⟩
  intro c
  change ((F c).map (fun d => G (c,d))).map decode =
    (f (decode c)).map (fun y => g (decode c,y))
  rw [List.map_map,←heF c]
  change (F c).map _ = ((F c).map decode).map _
  rw [List.map_map]
  congr 1
  funext d
  exact heG (c,d)

end Primitive

end MixedVolume.Represented

end
end -- component scope
/- END SOURCE: MixedVolume/Computability/Represented.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/RepresentedLists.lean -/
section


@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace MixedVolume.Represented

def PrimitivePred {α : Type} [Representation α] (p : α → Prop) : Prop :=
  PrimrecPred (fun c : Code α => p (decode c))

namespace PrimitivePred

variable {α β : Type} [Representation α] [Representation β]

theorem of_eq {p q : α → Prop} (hp : PrimitivePred p) (h : ∀ x, p x ↔ q x) :
    PrimitivePred q := _root_.PrimrecPred.of_eq hp (fun c => h (decode c))

theorem comp {p : β → Prop} {f : α → β} (hp : PrimitivePred p) (hf : Primitive f) :
    PrimitivePred (fun x => p (f x)) := by
  obtain ⟨F,hF,he⟩ := hf
  exact _root_.PrimrecPred.of_eq (_root_.PrimrecPred.comp hp hF) (fun c => by rw [he])

theorem not {p : α → Prop} (hp : PrimitivePred p) : PrimitivePred (fun x => ¬p x) :=
  PrimrecPred.not hp

theorem and {p q : α → Prop} (hp : PrimitivePred p) (hq : PrimitivePred q) :
    PrimitivePred (fun x => p x ∧ q x) := PrimrecPred.and hp hq

theorem or {p q : α → Prop} (hp : PrimitivePred p) (hq : PrimitivePred q) :
    PrimitivePred (fun x => p x ∨ q x) := PrimrecPred.or hp hq

theorem nat_le {f g : α → ℕ} (hf : Primitive f) (hg : Primitive g) :
    PrimitivePred (fun x => f x ≤ g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact (Primrec.nat_le.comp hF hG).of_eq (fun c => by
    change Nat.le (F c) (G c) ↔ f (decode c) ≤ g (decode c)
    rw [←heF c,←heG c] <;> rfl)

theorem nat_lt {f g : α → ℕ} (hf : Primitive f) (hg : Primitive g) :
    PrimitivePred (fun x => f x < g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact (Primrec.nat_lt.comp hF hG).of_eq (fun c => by
    change Nat.lt (F c) (G c) ↔ f (decode c) < g (decode c)
    rw [←heF c,←heG c] <;> rfl)

theorem rat_nonnegative : PrimitivePred (fun q : ℚ => 0 ≤ q) := by
  apply (Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).of_eq
  intro c
  change c.2.1 ≤ c.1 ↔ 0 ≤ RationalCode.eval c
  have hd : 0 < (RationalCode.denominator c : ℚ) := by
    exact_mod_cast RationalCode.denominator_pos c
  rw [RationalCode.eval,le_div_iff₀ hd,zero_mul,sub_nonneg]
  exact_mod_cast (Iff.rfl : c.2.1 ≤ c.1 ↔ c.2.1 ≤ c.1)

theorem le {f g : α → ℚ} (hf : Primitive f) (hg : Primitive g) :
    PrimitivePred (fun x => f x ≤ g x) :=
  (rat_nonnegative.comp (hg.sub hf)).of_eq fun _ => sub_nonneg

theorem lt {f g : α → ℚ} (hf : Primitive f) (hg : Primitive g) :
    PrimitivePred (fun x => f x < g x) :=
  (le hg hf).not.of_eq fun _ => not_le

theorem eq {f g : α → ℚ} (hf : Primitive f) (hg : Primitive g) :
    PrimitivePred (fun x => f x = g x) :=
  ((le hf hg).and (le hg hf)).of_eq fun _ => le_antisymm_iff.symm

theorem forall_mem {p : α × β → Prop} {f : α → List β}
    (hp : PrimitivePred p) (hf : Primitive f) :
    PrimitivePred (fun x => ∀ y ∈ f x, p (x,y)) := by
  obtain ⟨F,hF,heF⟩ := hf
  change PrimrecPred (fun q : Code α × Code β => p (decode q.1,decode q.2)) at hp
  have hs : Primrec (fun q : Code β × Code α => (q.2,q.1)) :=
    Primrec.pair Primrec.snd Primrec.fst
  have hp' : PrimrecPred (fun q : Code β × Code α => p (decode q.2,decode q.1)) :=
    _root_.PrimrecPred.comp
      (p := fun q : Code α × Code β => p (decode q.1,decode q.2))
      (f := fun q : Code β × Code α => (q.2,q.1)) hp hs
  have h := (PrimrecRel.forall_mem_list (R := fun d c => p (decode c,decode d))
    hp').comp
    hF Primrec.id
  apply h.of_eq
  intro c
  change (∀ y, List.Mem y (F c) → p (decode c,decode y)) ↔
    ∀ y ∈ f (decode c), p (decode c,y)
  rw [←heF c]
  change (∀ y, List.Mem y (F c) → p (decode c,decode y)) ↔
    ∀ y ∈ (F c).map decode, p (decode c,y)
  simp <;> rfl

end PrimitivePred

namespace Primitive

variable {α β γ δ : Type} [Representation α] [Representation β]
  [Representation γ] [Representation δ]

theorem ite {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : PrimitivePred p) (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => if p x then f x else g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  refine ⟨fun c => if p (decode c) then F c else G c,Primrec.ite hp hF hG,?_⟩
  intro c
  by_cases h : p (decode c) <;> simp only [h,ite_true,ite_false,heF,heG]

theorem nat_add {f g : α → ℕ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x + g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨fun c => Nat.add (F c) (G c),Primrec.nat_add.comp hF hG,
    fun c => by
      change Nat.add (F c) (G c) = f (decode c) + g (decode c)
      exact congrArg₂ Nat.add (heF c) (heG c)⟩

theorem nat_sub {f g : α → ℕ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x - g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨fun c => Nat.sub (F c) (G c),Primrec.nat_sub.comp hF hG,
    fun c => by
      change Nat.sub (F c) (G c) = f (decode c) - g (decode c)
      exact congrArg₂ Nat.sub (heF c) (heG c)⟩

theorem nat_mul {f g : α → ℕ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x * g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨fun c => Nat.mul (F c) (G c),Primrec.nat_mul.comp hF hG,
    fun c => by
      change Nat.mul (F c) (G c) = f (decode c) * g (decode c)
      exact congrArg₂ Nat.mul (heF c) (heG c)⟩

theorem list_cons {f : α → β} {g : α → List β} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x :: g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨fun c => F c :: G c,Primrec.list_cons.comp hF hG,
    fun c => by
      change decode (F c) :: (G c).map decode = f (decode c) :: g (decode c)
      rw [heF]; exact congrArg _ (heG c)⟩

theorem list_append {f g : α → List β} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x ++ g x) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨fun c => List.append (F c) (G c),Primrec.list_append.comp hF hG,
    fun c => by
      change (List.append (F c) (G c)).map decode =
        f (decode c) ++ g (decode c)
      exact (List.map_append (f := decode) (l₁ := F c) (l₂ := G c)).trans
        (congrArg₂ List.append (heF c) (heG c))⟩

theorem list_length {f : α → List β} (hf : Primitive f) :
    Primitive (fun x => (f x).length) := by
  obtain ⟨F,hF,heF⟩ := hf
  exact ⟨fun c => (F c).length,Primrec.list_length.comp hF,
    fun c => by
      change (F c).length = (f (decode c)).length
      rw [←heF c]; exact (List.length_map _).symm⟩

theorem list_range {f : α → ℕ} (hf : Primitive f) :
    Primitive (fun x => List.range (f x)) := by
  obtain ⟨F,hF,heF⟩ := hf
  exact ⟨fun c => List.range (F c),Primrec.list_range.comp hF,
    fun c => by
      change (List.range (F c)).map _root_.id = List.range (f (decode c))
      have hn : (F c : ℕ) = f (decode c) := heF c
      simpa only [List.map_id] using congrArg List.range hn⟩

theorem list_getD (b : β) {f : α → List β} {g : α → ℕ}
    (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => (f x).getD (g x) b) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  obtain ⟨d,hd⟩ := Representation.onto b
  refine ⟨fun c => (F c).getD (G c) d,(Primrec.list_getD d).comp hF hG,?_⟩
  intro c
  change decode ((F c).getD (G c) d) = (f (decode c)).getD (g (decode c)) b
  rw [←heF c,←heG c,←hd]
  exact (List.getD_map (F c) d decode).symm

theorem list_foldr {f : α → List β} {g : α → γ} {h : α × (β × γ) → γ}
    (hf : Primitive f) (hg : Primitive g) (hh : Primitive h) :
    Primitive (fun x => (f x).foldr (fun b c => h (x,(b,c))) (g x)) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  obtain ⟨H,hH,heH⟩ := hh
  refine ⟨fun c => (F c).foldr (fun b d => H (c,(b,d))) (G c),
    Primrec.list_foldr (h := fun c p => H (c,p)) hF hG (Primrec₂.mk hH),?_⟩
  intro c
  change decode ((F c).foldr (fun b d => H (c,(b,d))) (G c)) =
    (f (decode c)).foldr (fun b d => h (decode c,(b,d))) (g (decode c))
  rw [←heF c,←heG c]
  change decode ((F c).foldr _ (G c)) = ((F c).map decode).foldr _ (decode (G c))
  generalize F c = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldr_cons,List.map_cons,heH]
    exact congrArg (fun z => h (decode c,(decode b,z))) ih

theorem list_flatMap {f : α → List β} {g : α × β → List γ}
    (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => (f x).flatMap (fun y => g (x,y))) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  refine ⟨fun c => (F c).flatMap (fun d => G (c,d)),
    Primrec.list_flatMap hF (Primrec₂.mk hG),?_⟩
  intro c
  change ((F c).flatMap (fun d => G (c,d))).map decode =
    (f (decode c)).flatMap (fun y => g (decode c,y))
  rw [List.map_flatMap,←heF c]
  change (F c).flatMap (fun d => (G (c,d)).map decode) =
    ((F c).map decode).flatMap (fun y => g (decode c,y))
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro d hd
  exact heG (c,d)

theorem list_filter {f : α → List β} {p : α × β → Prop} [DecidablePred p]
    (hf : Primitive f) (hp : PrimitivePred p) :
    Primitive (fun x => (f x).filter (fun y => p (x,y))) := by
  obtain ⟨F,hF,heF⟩ := hf
  change PrimrecPred (fun q : Code α × Code β => p (decode q.1,decode q.2)) at hp
  have hs : Primrec (fun q : Code β × Code α => (q.2,q.1)) :=
    Primrec.pair Primrec.snd Primrec.fst
  have hp' : PrimrecPred (fun q : Code β × Code α => p (decode q.2,decode q.1)) :=
    _root_.PrimrecPred.comp
      (p := fun q : Code α × Code β => p (decode q.1,decode q.2))
      (f := fun q : Code β × Code α => (q.2,q.1)) hp hs
  refine ⟨fun c => (F c).filter (fun d => p (decode c,decode d)),
    (PrimrecRel.listFilter (R := fun d c => p (decode c,decode d))
      hp').comp hF Primrec.id,?_⟩
  intro c
  change ((F c).filter (fun d => p (decode c,decode d))).map decode =
    (f (decode c)).filter (fun y => p (decode c,y))
  rw [←heF c]
  change ((F c).filter _).map decode = ((F c).map decode).filter _
  simp only [List.filter_map] <;> rfl

theorem nat_rec {f : α → ℕ} {g : α → β} {h : α × (ℕ × β) → β}
    (hf : Primitive f) (hg : Primitive g) (hh : Primitive h) :
    Primitive (fun x => Nat.rec (motive := fun _ => β) (g x)
      (fun n z => h (x,(n,z))) (f x)) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  obtain ⟨H,hH,heH⟩ := hh
  refine ⟨fun c => Nat.rec (motive := fun _ => Code β) (G c)
      (fun n z => H (c,(n,z))) (F c),
    Primrec.nat_rec' (h := fun c p => H (c,p)) hF hG (Primrec₂.mk hH),?_⟩
  intro c
  change decode (Nat.rec (motive := fun _ => Code β) (G c)
    (fun n z => H (c,(n,z))) (F c)) =
    Nat.rec (motive := fun _ => β) (g (decode c))
      (fun n z => h (decode c,(n,z))) (f (decode c))
  rw [←heF c]
  change decode (Nat.rec (motive := fun _ => Code β) (G c)
    (fun n z => H (c,(n,z))) (F c)) =
    Nat.rec (motive := fun _ => β) (g (decode c))
      (fun n z => h (decode c,(n,z))) (F c)
  induction F c with
  | zero => exact heG c
  | succ n ih =>
    simp only [Nat.rec_add_one,heH]
    exact congrArg (fun z => h (decode c,(n,z))) ih

theorem list_take {f : α → List β} {g : α → ℕ}
    (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => (f x).take (g x)) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  refine ⟨fun c => (F c).take (G c),Primrec.list_take.comp hG hF,?_⟩
  intro c
  change ((F c).take (G c)).map decode = (f (decode c)).take (g (decode c))
  rw [←heF c,←heG c]
  change ((F c).take (G c)).map decode = ((F c).map decode).take (G c)
  exact List.map_take

theorem list_ofFn {n : ℕ} {f : α → Fin n → β}
    (hf : ∀ i, Primitive (fun x => f x i)) :
    Primitive (fun x => List.ofFn (f x)) := by
  classical
  choose F hF he using hf
  refine ⟨fun c => List.ofFn (fun i => F i c),Primrec.list_ofFn hF,?_⟩
  intro c
  change (List.ofFn (fun i => F i c)).map decode = List.ofFn (f (decode c))
  rw [List.map_ofFn]
  congr 1
  exact funext fun i => he i c

theorem list_sum {f : α → List ℚ} (hf : Primitive f) :
    Primitive (fun x => (f x).sum) := by
  have h := list_foldr hf (const (0 : ℚ))
    ((fst.comp snd).add (snd.comp snd))
  exact h.of_eq fun _ => rfl

theorem list_prod {f : α → List ℚ} (hf : Primitive f) :
    Primitive (fun x => (f x).prod) := by
  have h := list_foldr hf (const (1 : ℚ))
    ((fst.comp snd).mul (snd.comp snd))
  exact h.of_eq fun _ => rfl

/-- The exponent is an ordinary natural-number input, without a fixed bound. -/
theorem pow_nat {f : α → ℚ} {g : α → ℕ} (hf : Primitive f) (hg : Primitive g) :
    Primitive (fun x => f x ^ g x) := by
  have h := nat_rec hg (const (1 : ℚ))
    ((snd.comp snd).mul (hf.comp fst))
  apply h.of_eq
  intro x
  induction g x with
  | zero => simp
  | succ n ih => simpa only [Nat.rec_add_one, pow_succ, ih]

/-- A sum over a data-dependent finite range is primitive recursive. -/
theorem range_sum {f : α × ℕ → ℚ} {n : α → ℕ}
    (hf : Primitive f) (hn : Primitive n) :
    Primitive (fun x => ((List.range (n x)).map (fun i => f (x,i))).sum) :=
  list_sum (list_map (list_range hn) hf)

theorem range_sum_eq_fin_sum (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  have h : (List.range n).map f = List.ofFn (fun i : Fin n => f i) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [h, List.sum_ofFn]

theorem finset_sum {ι : Type} (s : Finset ι) {f : α → ι → ℚ}
    (hf : ∀ i ∈ s, Primitive (fun x => f x i)) :
    Primitive (fun x => ∑ i ∈ s, f x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (α := α) (0 : ℚ))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem finite_sum {ι : Type} [Fintype ι] {f : α → ι → ℚ}
    (hf : ∀ i, Primitive (fun x => f x i)) :
    Primitive (fun x => ∑ i, f x i) :=
  finset_sum Finset.univ (fun i _ => hf i)

theorem list_sublists {f : α → List β} (hf : Primitive f) :
    Primitive (fun x => (f x).sublists) := by
  have hstep : Primitive (fun x : α × (β × List (List β)) =>
      x.2.2.flatMap (fun l => [l,x.2.1 :: l])) := by
    apply list_flatMap (g := fun p : (α × (β × List (List β))) × List β =>
      [p.2,p.1.2.1 :: p.2]) (snd.comp snd)
    exact list_cons snd
      (list_cons (list_cons (fst.comp (snd.comp fst)) snd) (const []))
  have h := list_foldr hf (const ([[]] : List (List β))) hstep
  apply h.of_eq
  intro x
  induction f x with
  | nil => rfl
  | cons b l ih => simp only [List.foldr_cons,List.sublists_cons,ih,List.bind_eq_flatMap]

end Primitive

end MixedVolume.Represented

end
end -- component scope
/- END SOURCE: MixedVolume/Computability/RepresentedLists.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/EffectiveElimination.lean -/
section


/-! Uniform rational list algorithms for Fourier--Motzkin elimination.

The elimination coordinate is an ordinary natural-number input. In particular,
the number of vertices and barycentric variables is not fixed or bounded,
even when the ambient dimension is fixed.
The geometric identification with the typed halfspace algorithm is proved
separately, so these computability proofs need no convex-geometric imports.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace MixedVolume.EffectiveElimination
open Represented Represented.Primitive

abbrev Inequality := List ℚ × ℚ

def coefficient (p : Inequality) (j : ℕ) : ℚ := p.1.getD j 0

def tail (j : ℕ) (p : Inequality) : Inequality := (p.1.take j,p.2)

def combine (j : ℕ) (l u : Inequality) : Inequality :=
  ((List.range j).map (fun i => coefficient u j * coefficient l i -
    coefficient l j * coefficient u i),
    coefficient u j * l.2 - coefficient l j * u.2)

def eliminate (j : ℕ) (S : List Inequality) : List Inequality :=
  ((S.filter fun p => coefficient p j = 0).map (tail j)) ++
    (S.filter fun p => coefficient p j < 0).flatMap (fun l =>
      (S.filter fun p => 0 < coefficient p j).map (combine j l))

def eliminateSuffix (n : ℕ) : ℕ → List Inequality → List Inequality
  | 0,S => S
  | m+1,S => eliminateSuffix n m (eliminate (n+m) S)

def negative (p : Inequality) : Inequality := (p.1.map (fun q => -q),-p.2)

def equality (a : List ℚ) (b : ℚ) : List Inequality := [(a,b),negative (a,b)]

def barycentricSystem (n : ℕ) (L : List (Fin n → ℚ)) : List Inequality :=
  (List.range L.length).map (fun j =>
    ((List.range (n+L.length)).map (fun i => if i=n+j then -1 else 0),0)) ++
  equality ((List.range (n+L.length)).map (fun i => if i<n then 0 else 1)) 1 ++
  (List.ofFn fun i : Fin n =>
    equality ((List.ofFn fun k : Fin n => if k=i then 1 else 0) ++
      L.map (fun v => -v i)) 0).flatten

def hullHalfspaces (n : ℕ) (L : List (Fin n → ℚ)) : List Inequality :=
  eliminateSuffix n L.length (barycentricSystem n L)

theorem coefficient_primitive :
    Primitive (fun p : Inequality × ℕ => coefficient p.1 p.2) :=
  list_getD 0 (fst.comp fst) snd

theorem tail_primitive : Primitive (fun p : ℕ × Inequality => tail p.1 p.2) :=
  (list_take (fst.comp snd) fst).pair (snd.comp snd)

theorem combine_primitive :
    Primitive (fun p : ℕ × (Inequality × Inequality) => combine p.1 p.2.1 p.2.2) := by
  have hj : Primitive (fun p : ℕ × (Inequality × Inequality) => p.1) := fst
  have hl : Primitive (fun p : ℕ × (Inequality × Inequality) => p.2.1) := fst.comp snd
  have hu : Primitive (fun p : ℕ × (Inequality × Inequality) => p.2.2) := snd.comp snd
  have hlj := coefficient_primitive.comp (hl.pair hj)
  have huj := coefficient_primitive.comp (hu.pair hj)
  apply pair
  · apply list_map (g := fun p : (ℕ × (Inequality × Inequality)) × ℕ =>
      coefficient p.1.2.2 p.1.1 * coefficient p.1.2.1 p.2 -
        coefficient p.1.2.1 p.1.1 * coefficient p.1.2.2 p.2) (list_range hj)
    exact ((huj.comp fst).mul
      (coefficient_primitive.comp ((hl.comp fst).pair snd))).sub
      ((hlj.comp fst).mul
        (coefficient_primitive.comp ((hu.comp fst).pair snd)))
  · exact (huj.mul (snd.comp hl)).sub (hlj.mul (snd.comp hu))

theorem eliminate_primitive :
    Primitive (fun p : ℕ × List Inequality => eliminate p.1 p.2) := by
  let H : (ℕ × List Inequality) × Inequality → ℚ :=
    fun p => coefficient p.2 p.1.1
  have hH : Primitive H := coefficient_primitive.comp (snd.pair (fst.comp fst))
  have hz : Primitive (fun p : ℕ × List Inequality =>
      p.2.filter (fun q => coefficient q p.1=0)) :=
    list_filter snd (PrimitivePred.eq hH (const 0))
  have hn : Primitive (fun p : ℕ × List Inequality =>
      p.2.filter (fun q => coefficient q p.1<0)) :=
    list_filter snd (PrimitivePred.lt hH (const 0))
  have hp : Primitive (fun p : ℕ × List Inequality =>
      p.2.filter (fun q => 0<coefficient q p.1)) :=
    list_filter snd (PrimitivePred.lt (const 0) hH)
  apply list_append
  · exact list_map hz (tail_primitive.comp ((fst.comp fst).pair snd))
  · apply list_flatMap (g := fun p : (ℕ × List Inequality) × Inequality =>
      (p.1.2.filter (fun q => 0 < coefficient q p.1.1)).map (combine p.1.1 p.2)) hn
    apply list_map (g := fun p : ((ℕ × List Inequality) × Inequality) × Inequality =>
      combine p.1.1.1 p.1.2 p.2) (hp.comp fst)
    exact combine_primitive.comp
      ((fst.comp (fst.comp fst)).pair ((snd.comp fst).pair snd))

private def eliminationStep (n : ℕ) (p : ℕ × List Inequality) : ℕ × List Inequality :=
  (p.1-1,eliminate (n+(p.1-1)) p.2)

private theorem iterate_eliminationStep (n m : ℕ) (S : List Inequality) :
    (eliminationStep n)^[m] (m,S) = (0,eliminateSuffix n m S) := by
  induction m generalizing S with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    simpa only [eliminationStep,Nat.add_sub_cancel,eliminateSuffix] using
      ih (eliminate (n+m) S)

theorem eliminateSuffix_primitive (n : ℕ) :
    Primitive (fun p : ℕ × List Inequality => eliminateSuffix n p.1 p.2) := by
  have hstep : Primitive (eliminationStep n) :=
    (nat_sub fst (const 1)).pair
      (eliminate_primitive.comp
        ((nat_add (const n) (nat_sub fst (const 1))).pair snd))
  have h := nat_rec (f := fun p : ℕ × List Inequality => p.1) fst id
    (hstep.comp (snd.comp snd))
  have hi : Primitive (fun p : ℕ × List Inequality =>
      (eliminationStep n)^[p.1] p) := h.of_eq fun p => by
    induction p.1 with
    | zero => rfl
    | succ k ih => simpa only [Nat.rec_add_one,Function.iterate_succ_apply',ih]
  exact (snd.comp hi).of_eq fun p => congrArg Prod.snd (iterate_eliminationStep n p.1 p.2)

theorem negative_primitive : Primitive negative :=
  (list_map fst (snd.neg)).pair snd.neg

theorem equality_primitive :
    Primitive (fun p : List ℚ × ℚ => equality p.1 p.2) :=
  list_cons id (list_cons negative_primitive (const []))

theorem barycentricSystem_primitive (n : ℕ) : Primitive (barycentricSystem n) := by
  have hlen : Primitive (fun L : List (Fin n → ℚ) => L.length) := list_length id
  have hfirst : Primitive (fun L : List (Fin n → ℚ) =>
      (List.range L.length).map (fun j =>
        ((List.range (n+L.length)).map (fun i => if i=n+j then (-1 : ℚ) else 0),
          (0 : ℚ)))) := by
    apply list_map (g := fun p : List (Fin n → ℚ) × ℕ =>
      ((List.range (n+p.1.length)).map (fun i => if i=n+p.2 then (-1 : ℚ) else 0),
        (0 : ℚ))) (list_range hlen)
    apply pair
    · apply list_map (g := fun p : (List (Fin n → ℚ) × ℕ) × ℕ =>
        if p.2=n+p.1.2 then (-1 : ℚ) else 0)
        (list_range ((nat_add (const n) hlen).comp fst))
      apply Primitive.ite
      · apply ((PrimitivePred.nat_le snd
            ((nat_add (const n) snd).comp fst)).and
          (PrimitivePred.nat_le ((nat_add (const n) snd).comp fst) snd)).of_eq
        intro x
        exact le_antisymm_iff.symm
      · exact const (-1)
      · exact const 0
    · exact const 0
  have hsum : Primitive (fun L : List (Fin n → ℚ) =>
      equality ((List.range (n+L.length)).map (fun i => if i<n then 0 else 1)) 1) := by
    apply equality_primitive.comp (g := fun L : List (Fin n → ℚ) =>
      ((List.range (n+L.length)).map (fun i => if i<n then 0 else 1),1))
    apply pair
    · apply list_map (g := fun p : List (Fin n → ℚ) × ℕ =>
        if p.2<n then (0 : ℚ) else 1) (list_range (nat_add (const n) hlen))
      exact Primitive.ite (PrimitivePred.nat_lt snd (const n)) (const 0) (const 1)
    · exact const 1
  have hcoords : Primitive (fun L : List (Fin n → ℚ) => List.ofFn fun i : Fin n =>
      equality ((List.ofFn fun k : Fin n => if k=i then 1 else 0) ++
        L.map (fun v => -v i)) 0) := by
    apply list_ofFn
    intro i
    apply equality_primitive.comp (g := fun L : List (Fin n → ℚ) =>
      ((List.ofFn fun k : Fin n => if k=i then 1 else 0) ++
        L.map (fun v => -v i),0))
    apply pair
    · apply list_append (const _)
      exact list_map id ((fin_app.comp (snd.pair (const i))).neg)
    · exact const 0
  have hlast := (list_flatMap hcoords snd).of_eq fun _ => List.flatMap_id
  exact (hfirst.list_append hsum).list_append hlast

theorem hullHalfspaces_primitive (n : ℕ) : Primitive (hullHalfspaces n) :=
  (eliminateSuffix_primitive n).comp ((list_length id).pair (barycentricSystem_primitive n))

end MixedVolume.EffectiveElimination

end
end -- component scope
/- END SOURCE: MixedVolume/Computability/EffectiveElimination.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/EffectiveGrids.lean -/
section


@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace MixedVolume.EffectiveGrids
open Represented Represented.Primitive
open EffectiveElimination

def selections {α : Type} : {n : ℕ} → (Fin n → List α) → List (Fin n → α)
  | 0,_ => [Fin.elim0]
  | n+1,L => (L 0).flatMap (fun a => (selections (Fin.tail L)).map (Fin.cons a))

theorem fin_cons_primitive {α : Type} [Representation α] (n : ℕ) :
    Primitive (fun p : α × (Fin n → α) => Fin.cons p.1 p.2) := by
  apply fin_function
  intro i
  induction i using Fin.cases with
  | zero => exact fst
  | succ j => exact fin_app.comp (snd.pair (const j))

theorem selections_primitive {α : Type} [Representation α] (n : ℕ) :
    Primitive (@selections α n) := by
  induction n with
  | zero => exact const _
  | succ n ih =>
    have ht : Primitive (fun L : Fin (n+1) → List α => Fin.tail L) :=
      fin_function fun i => fin_app.comp (id.pair (const i.succ))
    apply list_flatMap (g := fun p : (Fin (n+1) → List α) × α =>
      (selections (Fin.tail p.1)).map (Fin.cons p.2))
      (fin_app.comp (id.pair (const 0)))
    apply list_map (g := fun p : ((Fin (n+1) → List α) × α) × (Fin n → α) =>
      Fin.cons p.1.2 p.2) ((ih.comp ht).comp fst)
    exact (fin_cons_primitive n).comp ((snd.comp fst).pair snd)

def coordinateGrid (R k : ℕ) : List ℚ :=
  (List.range (2*R*(k+1)+1)).map (fun j : ℕ =>
    ((j : ℚ)-(R : ℚ)*((k : ℚ)+1))/((k : ℚ)+1))

def vertexGrid (d R k : ℕ) : List (Fin d → ℚ) :=
  selections (fun _ : Fin d => coordinateGrid R k)

def candidates (d R k : ℕ) : List (List (Fin d → ℚ)) :=
  (vertexGrid d R k).sublists.filter (fun L => 0 ∈ L)

def candidateTuples (n d R k : ℕ) : List (Fin n → List (Fin d → ℚ)) :=
  selections (fun _ : Fin n => candidates d R k)

def indexList (d R k : ℕ) : List (Fin d → ℕ) :=
  selections (fun _ : Fin d => List.range (2*(R+1)*(k+1)))

def corner (d : ℕ) (outer : Bool) (p : Inequality) (R k : ℕ)
    (v : Fin d → ℕ) : Fin d → ℚ :=
  fun i => (((v i : ℚ)-((R+1)*(k+1) : ℕ)) +
    if (if outer then coefficient p i ≤ 0 else 0 ≤ coefficient p i)
      then 1 else 0) / ((k : ℚ)+1)

def value (d : ℕ) (p : Inequality) (x : Fin d → ℚ) : ℚ :=
  ∑ i : Fin d, coefficient p i * x i

def Test (d : ℕ) (outer : Bool) (S : List Inequality) (R k : ℕ)
    (v : Fin d → ℕ) : Prop :=
  ∀ p ∈ S, value d p (corner d outer p R k v) ≤ p.2

instance (d : ℕ) (outer : Bool) (S : List Inequality) (R k : ℕ) (v : Fin d → ℕ) :
    Decidable (Test d outer S R k v) := inferInstanceAs (Decidable (∀ p ∈ S, _))

def boxVolume (d : ℕ) (outer : Bool) (S : List Inequality) (R k : ℕ) : ℚ :=
  (((indexList d R k).filter (fun v => Test d outer S R k v)).length : ℚ) /
    ((k : ℚ)+1)^d

theorem coordinateGrid_primitive (R : ℕ) : Primitive (coordinateGrid R) := by
  unfold coordinateGrid
  apply list_map (g := fun p : ℕ × ℕ =>
    ((p.2 : ℚ)-(R : ℚ)*((p.1 : ℚ)+1))/((p.1 : ℚ)+1))
    (list_range (nat_add (nat_mul (const (2*R)) (nat_add id (const 1))) (const 1)))
  exact (snd.nat.sub ((const (R : ℚ)).mul ((fst.nat).add (const 1)))).div
    (fst.nat.add (const 1))

theorem vertexGrid_primitive (d R : ℕ) : Primitive (vertexGrid d R) :=
  (selections_primitive d).comp (fin_function (fun _ => coordinateGrid_primitive R))

theorem vector_zero_primitive (d : ℕ) :
    PrimitivePred (fun v : Fin d → ℚ => v=0) := by
  have h : PrimitivePred (fun v : Fin d → ℚ =>
      ∀ q ∈ List.ofFn v, q=0) :=
    PrimitivePred.forall_mem
      (PrimitivePred.eq snd (const 0)) (list_ofFn fun i => fin_app.comp (id.pair (const i)))
  apply h.of_eq
  intro v
  constructor
  · intro hv
    funext i
    exact hv (v i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · rintro rfl q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    rfl

theorem candidates_primitive (d R : ℕ) : Primitive (candidates d R) := by
  apply list_filter (p := fun p : ℕ × List (Fin d → ℚ) => 0 ∈ p.2)
    ((vertexGrid_primitive d R).list_sublists)
  have h : PrimitivePred (fun p : ℕ × List (Fin d → ℚ) =>
      ¬∀ v ∈ p.2, ¬v=0) := (PrimitivePred.forall_mem
    ((vector_zero_primitive d).comp snd).not snd).not
  classical
  exact h.of_eq fun p => by simp

theorem candidateTuples_primitive (n d R : ℕ) : Primitive (candidateTuples n d R) :=
  (selections_primitive n).comp (fin_function fun _ => candidates_primitive d R)

theorem indexList_primitive (d : ℕ) :
    Primitive (fun p : ℕ × ℕ => indexList d p.1 p.2) :=
  (selections_primitive d).comp (fin_function fun _ =>
    list_range (nat_mul (nat_mul (const 2) (nat_add fst (const 1)))
      (nat_add snd (const 1))))

theorem value_primitive (d : ℕ) :
    Primitive (fun p : Inequality × (Fin d → ℚ) => value d p.1 p.2) := by
  unfold value
  apply finite_sum
  intro i
  exact (coefficient_primitive.comp (fst.pair (const i.val))).mul
    (fin_app.comp (snd.pair (const i)))

theorem corner_primitive (d : ℕ) (outer : Bool) :
    Primitive (fun p : Inequality × (ℕ × (ℕ × (Fin d → ℕ))) =>
      corner d outer p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hR : Primitive (fun p : Inequality × (ℕ × (ℕ × (Fin d → ℕ))) => p.2.1) :=
    fst.comp snd
  have hk : Primitive (fun p : Inequality × (ℕ × (ℕ × (Fin d → ℕ))) => p.2.2.1) :=
    fst.comp (snd.comp snd)
  have hv : Primitive (fun p : Inequality × (ℕ × (ℕ × (Fin d → ℕ))) => p.2.2.2) :=
    snd.comp (snd.comp snd)
  apply fin_function
  intro i
  have hc : Primitive (fun p : Inequality × (ℕ × (ℕ × (Fin d → ℕ))) =>
      coefficient p.1 i) := coefficient_primitive.comp (fst.pair (const i.val))
  have hsign : PrimitivePred (fun p : Inequality × (ℕ × (ℕ × (Fin d → ℕ))) =>
      if outer then coefficient p.1 i ≤ 0 else 0 ≤ coefficient p.1 i) := by
    cases outer
    · exact PrimitivePred.le (const 0) hc
    · exact PrimitivePred.le hc (const 0)
  exact (((fin_app.comp (hv.pair (const i))).nat.sub
    ((nat_mul (nat_add hR (const 1)) (nat_add hk (const 1))).nat)).add
      (Primitive.ite hsign (const 1) (const 0))).div (hk.nat.add (const 1))

theorem test_primitive (d : ℕ) (outer : Bool) :
    PrimitivePred (fun p : (List Inequality × (ℕ × ℕ)) × (Fin d → ℕ) =>
      Test d outer p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  apply PrimitivePred.forall_mem
    (p := fun p : ((List Inequality × (ℕ × ℕ)) × (Fin d → ℕ)) × Inequality =>
      value d p.2 (corner d outer p.2 p.1.1.2.1 p.1.1.2.2 p.1.2) ≤ p.2.2)
    (f := fun p => p.1.1)
  · apply PrimitivePred.le _ (snd.comp snd)
    apply (value_primitive d).comp
      (g := fun p : ((List Inequality × (ℕ × ℕ)) × (Fin d → ℕ)) × Inequality =>
        (p.2,corner d outer p.2 p.1.1.2.1 p.1.1.2.2 p.1.2))
    apply pair snd
    apply (corner_primitive d outer).comp
      (g := fun p : ((List Inequality × (ℕ × ℕ)) × (Fin d → ℕ)) × Inequality =>
        (p.2,(p.1.1.2.1,(p.1.1.2.2,p.1.2))))
    exact snd.pair
      ((fst.comp (snd.comp (fst.comp fst))).pair
        ((snd.comp (snd.comp (fst.comp fst))).pair (snd.comp fst)))
  · exact fst.comp fst

theorem boxVolume_primitive (d : ℕ) (outer : Bool) :
    Primitive (fun p : List Inequality × (ℕ × ℕ) => boxVolume d outer p.1 p.2.1 p.2.2) := by
  apply div
  · apply nat
    apply list_length
    apply list_filter
      (p := fun p : (List Inequality × (ℕ × ℕ)) × (Fin d → ℕ) =>
        Test d outer p.1.1 p.1.2.1 p.1.2.2 p.2)
      ((indexList_primitive d).comp snd)
    exact test_primitive d outer
  · exact ((snd.comp snd).nat.add (const 1)).pow d

end MixedVolume.EffectiveGrids

end
end -- component scope
/- END SOURCE: MixedVolume/Computability/EffectiveGrids.lean -/

/- BEGIN SOURCE: MixedVolume/Computability/RepresentedSearch.lean -/
section


/-! Total unbounded search and list traversal for represented computation.
Termination is proved mathematically and converted to the standard partial
recursive search theorem; it is never postulated as an oracle.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace MixedVolume.Represented

theorem computable_list_map {α β γ : Type} [Primcodable α] [Primcodable β]
    [Primcodable γ] {f : α → List β} {g : α → β → γ}
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun x => (f x).map (g x)) := by
  let step (x : α) (p : ℕ × List γ) : List γ :=
    match (f x)[p.1]? with
    | none => p.2
    | some b => p.2 ++ [g x b]
  have hs : Computable₂ step := by
    have hc : Computable (fun p : α × (ℕ × List γ) =>
      Option.casesOn (motive := fun _ => List γ) (f p.1)[p.2.1]? p.2.2
        (fun b => p.2.2 ++ [g p.1 b])) := by
      apply Computable.option_casesOn (g := fun p b => p.2.2 ++ [g p.1 b])
        (Computable.list_getElem?.comp (hf.comp Computable.fst)
          (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd)
      exact (Computable.list_concat.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
        (hg.comp (Computable.fst.comp Computable.fst) Computable.snd)).to₂
    apply Computable₂.mk
    exact hc.of_eq fun p => by
      cases he : (f p.1)[p.2.1]? <;> simp [step,he]
  have hrec := Computable.nat_rec (Computable.list_length.comp hf)
    (Computable.const ([] : List γ)) hs
  have hcorrect (x : α) (k : ℕ) :
      k.rec ([] : List γ) (fun j z => step x (j,z)) = ((f x).take k).map (g x) := by
    induction k with
    | zero => simp
    | succ k ih =>
      change step x (k,Nat.rec ([] : List γ) (fun j z => step x (j,z)) k) = _
      rw [ih,List.take_add_one,List.map_append]
      cases h : (f x)[k]? <;> simp [step,h]
  exact hrec.of_eq fun x => by simpa using hcorrect x (f x).length

theorem computable_list_foldl {α β γ : Type} [Primcodable α] [Primcodable β]
    [Primcodable γ] {f : α → List β} {g : α → γ} {h : α → γ × β → γ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun x => (f x).foldl (fun z b => h x (z,b)) (g x)) := by
  let step (x : α) (p : ℕ × γ) : γ :=
    match (f x)[p.1]? with
    | none => p.2
    | some b => h x (p.2,b)
  have hs : Computable₂ step := by
    have hc : Computable (fun p : α × (ℕ × γ) =>
      Option.casesOn (motive := fun _ => γ) (f p.1)[p.2.1]? p.2.2
        (fun b => h p.1 (p.2.2,b))) := by
      apply Computable.option_casesOn (g := fun p b => h p.1 (p.2.2,b))
        (Computable.list_getElem?.comp (hf.comp Computable.fst)
          (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd)
      exact (hh.comp (Computable.fst.comp Computable.fst)
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
          Computable.snd)).to₂
    apply Computable₂.mk
    exact hc.of_eq fun p => by
      cases he : (f p.1)[p.2.1]? <;> simp [step,he]
  have hrec := Computable.nat_rec (Computable.list_length.comp hf) hg hs
  have hcorrect (x : α) (k : ℕ) :
      k.rec (g x) (fun j z => step x (j,z)) =
        ((f x).take k).foldl (fun z b => h x (z,b)) (g x) := by
    induction k with
    | zero => simp
    | succ k ih =>
      change step x (k,Nat.rec (g x) (fun j z => step x (j,z)) k) = _
      rw [ih,List.take_add_one,List.foldl_append]
      cases hget : (f x)[k]? <;> simp [step,hget]
  exact hrec.of_eq fun x => by simpa using hcorrect x (f x).length

theorem computable_list_foldr {α β γ : Type} [Primcodable α] [Primcodable β]
    [Primcodable γ] {f : α → List β} {g : α → γ} {h : α → β × γ → γ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun x => (f x).foldr (fun b z => h x (b,z)) (g x)) := by
  have hh' : Computable₂ (fun x (p : γ × β) => h x (p.2,p.1)) :=
    (hh.comp Computable.fst
      ((Computable.snd.comp Computable.snd).pair
        (Computable.fst.comp Computable.snd))).to₂
  exact (computable_list_foldl (Computable.list_reverse.comp hf) hg hh').of_eq
    fun x => by simp only [List.foldl_reverse]

def EffectivePred {α : Type} [Representation α] (p : α → Prop) : Prop :=
  ComputablePred (fun c : Code α => p (decode c))

namespace Effective
variable {α β γ : Type} [Representation α] [Representation β] [Representation γ]

theorem of_eq {f g : α → β} (hf : Effective f) (h : ∀ x, f x=g x) : Effective g := by
  obtain ⟨F,hF,he⟩ := hf
  exact ⟨F,hF,fun c => (he c).trans (h _)⟩

theorem comp {f : β → γ} {g : α → β} (hf : Effective f) (hg : Effective g) :
    Effective (fun x => f (g x)) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨F ∘ G,hF.comp hG,fun c => by rw [Function.comp_apply,heF,heG]⟩

theorem id : Effective (_root_.id : α → α) := Primitive.id.effective
theorem const (b : β) : Effective (fun _ : α => b) := (Primitive.const b).effective
theorem fst : Effective (Prod.fst : α × β → α) := Primitive.fst.effective
theorem snd : Effective (Prod.snd : α × β → β) := Primitive.snd.effective

theorem pair {f : α → β} {g : α → γ} (hf : Effective f) (hg : Effective g) :
    Effective (fun x => (f x,g x)) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  exact ⟨fun c => (F c,G c),Computable.pair hF hG,fun c => Prod.ext (heF c) (heG c)⟩

theorem add {f g : α → ℚ} (hf : Effective f) (hg : Effective g) :
    Effective (fun x => f x+g x) :=
  (Primitive.add Primitive.fst Primitive.snd).effective.comp (hf.pair hg)

theorem mul {f g : α → ℚ} (hf : Effective f) (hg : Effective g) :
    Effective (fun x => f x*g x) :=
  (Primitive.mul Primitive.fst Primitive.snd).effective.comp (hf.pair hg)

theorem sub {f g : α → ℚ} (hf : Effective f) (hg : Effective g) :
    Effective (fun x => f x-g x) :=
  (Primitive.sub Primitive.fst Primitive.snd).effective.comp (hf.pair hg)

theorem div {f g : α → ℚ} (hf : Effective f) (hg : Effective g) :
    Effective (fun x => f x/g x) :=
  (Primitive.div Primitive.fst Primitive.snd).effective.comp (hf.pair hg)

theorem nat {f : α → ℕ} (hf : Effective f) : Effective (fun x => (f x : ℚ)) :=
  (Primitive.nat Primitive.id).effective.comp hf

theorem fin_function {n : ℕ} {f : α → Fin n → β}
    (hf : ∀ i, Effective (fun x => f x i)) : Effective f := by
  classical
  choose F hF he using hf
  refine ⟨fun c i => F i c,?_,fun c => funext (fun i => he i c)⟩
  exact (Primrec.vector_get'.to_comp.comp (Computable.vector_ofFn hF)).of_eq
    fun _ => by funext i; simp

theorem list_map {f : α → List β} {g : α × β → γ}
    (hf : Effective f) (hg : Effective g) :
    Effective (fun x => (f x).map (fun y => g (x,y))) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  refine ⟨fun c => (F c).map (fun d => G (c,d)),computable_list_map hF hG.to₂,?_⟩
  intro c
  change ((F c).map (fun d => G (c,d))).map decode =
    (f (decode c)).map (fun y => g (decode c,y))
  rw [List.map_map,←heF c]
  change (F c).map _ = ((F c).map decode).map _
  rw [List.map_map]
  congr 1
  exact funext fun d => heG (c,d)

theorem list_length {f : α → List β} (hf : Effective f) :
    Effective (fun x => (f x).length) :=
  (Primitive.list_length Primitive.id).effective.comp hf

theorem list_range {f : α → ℕ} (hf : Effective f) :
    Effective (fun x => List.range (f x)) :=
  (Primitive.list_range Primitive.id).effective.comp hf

theorem list_getD (b : β) {f : α → List β} {g : α → ℕ}
    (hf : Effective f) (hg : Effective g) :
    Effective (fun x => (f x).getD (g x) b) :=
  (Primitive.list_getD b Primitive.fst Primitive.snd).effective.comp (hf.pair hg)

theorem list_sum {f : α → List ℚ} (hf : Effective f) :
    Effective (fun x => (f x).sum) :=
  (Primitive.list_sum Primitive.id).effective.comp hf

theorem list_prod {f : α → List ℚ} (hf : Effective f) :
    Effective (fun x => (f x).prod) :=
  (Primitive.list_prod Primitive.id).effective.comp hf

theorem pow_nat {f : α → ℚ} {g : α → ℕ} (hf : Effective f) (hg : Effective g) :
    Effective (fun x => f x ^ g x) :=
  (Primitive.pow_nat Primitive.fst Primitive.snd).effective.comp (hf.pair hg)

theorem range_sum {f : α × ℕ → ℚ} {n : α → ℕ}
    (hf : Effective f) (hn : Effective n) :
    Effective (fun x => ((List.range (n x)).map (fun i => f (x,i))).sum) :=
  list_sum (list_map (list_range hn) hf)

theorem list_foldr {f : α → List β} {g : α → γ} {h : α × (β × γ) → γ}
    (hf : Effective f) (hg : Effective g) (hh : Effective h) :
    Effective (fun x => (f x).foldr (fun b c => h (x,(b,c))) (g x)) := by
  obtain ⟨F,hF,heF⟩ := hf
  obtain ⟨G,hG,heG⟩ := hg
  obtain ⟨H,hH,heH⟩ := hh
  refine ⟨fun c => (F c).foldr (fun b d => H (c,(b,d))) (G c),
    computable_list_foldr (h := fun c p => H (c,p)) hF hG hH.to₂,?_⟩
  intro c
  change decode ((F c).foldr (fun b d => H (c,(b,d))) (G c)) =
    (f (decode c)).foldr (fun b d => h (decode c,(b,d))) (g (decode c))
  rw [←heF c,←heG c]
  change decode ((F c).foldr _ (G c)) = ((F c).map decode).foldr _ (decode (G c))
  generalize F c = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldr_cons,List.map_cons,heH]
    exact congrArg (fun z => h (decode c,(decode b,z))) ih

theorem finite_sum {ι : Type} [Fintype ι] {f : α → ι → ℚ}
    (hf : ∀ i, Effective (fun x => f x i)) :
    Effective (fun x => ∑ i, f x i) := by
  classical
  have h (s : Finset ι) : Effective (fun x => ∑ i ∈ s, f x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using (const (α := α) (0 : ℚ))
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using (hf i).add ih
  exact h Finset.univ

end Effective

theorem PrimitivePred.effective {α : Type} [Representation α] {p : α → Prop}
    (hp : PrimitivePred p) : EffectivePred p := hp.computablePred

namespace EffectivePred
variable {α β : Type} [Representation α] [Representation β]

theorem of_eq {p q : α → Prop} (hp : EffectivePred p) (h : ∀ x, p x ↔ q x) :
    EffectivePred q := _root_.ComputablePred.of_eq hp (fun c => h (decode c))

theorem comp {p : β → Prop} {f : α → β} (hp : EffectivePred p) (hf : Effective f) :
    EffectivePred (fun x => p (f x)) := by
  classical
  obtain ⟨F,hF,he⟩ := hf
  exact _root_.ComputablePred.of_eq ((hp.decide.comp hF).computablePred) (fun c => by rw [he])

theorem not {p : α → Prop} (hp : EffectivePred p) : EffectivePred (fun x => ¬p x) :=
  ComputablePred.not hp

theorem and {p q : α → Prop} (hp : EffectivePred p) (hq : EffectivePred q) :
    EffectivePred (fun x => p x ∧ q x) := by
  classical
  exact ((Primrec.and.to_comp.comp hp.decide hq.decide).of_eq
    (fun _ => by simp)).computablePred

theorem or {p q : α → Prop} (hp : EffectivePred p) (hq : EffectivePred q) :
    EffectivePred (fun x => p x ∨ q x) := by
  classical
  exact ((Primrec.or.to_comp.comp hp.decide hq.decide).of_eq
    (fun _ => by simp)).computablePred

theorem le {f g : α → ℚ} (hf : Effective f) (hg : Effective g) :
    EffectivePred (fun x => f x ≤ g x) :=
  (PrimitivePred.le Primitive.fst Primitive.snd).effective.comp (hf.pair hg)

theorem lt {f g : α → ℚ} (hf : Effective f) (hg : Effective g) :
    EffectivePred (fun x => f x < g x) :=
  (PrimitivePred.lt Primitive.fst Primitive.snd).effective.comp (hf.pair hg)

theorem forall_mem {p : α × β → Prop} {f : α → List β}
    (hp : PrimitivePred p) (hf : Effective f) :
    EffectivePred (fun x => ∀ y ∈ f x, p (x,y)) := by
  have h : PrimitivePred (fun x : α × List β => ∀ y ∈ x.2, p (x.1,y)) :=
    PrimitivePred.forall_mem
      (hp.comp ((Primitive.fst.comp Primitive.fst).pair Primitive.snd)) Primitive.snd
  exact h.effective.comp (Effective.id.pair hf)

end EffectivePred

namespace Effective

theorem find {α : Type} [Representation α] {P : α × ℕ → Prop} [DecidablePred P]
    (hp : EffectivePred P) (he : ∀ x, ∃ k, P (x,k)) :
    Effective (fun x => Nat.find (he x)) := by
  change ComputablePred (fun p : Code α × ℕ => P (decode p.1,p.2)) at hp
  refine ⟨fun c => Nat.find (he (decode c)),?_,fun _ => rfl⟩
  exact Computable.find (P := fun c n => P (decode c,n)) hp (fun c => he (decode c))


end Effective

theorem effective_exists_re {α β : Type} [Representation α] [Representation β]
    {P : α × β → Prop} (hp : EffectivePred P) :
    REPred (fun c : Code α => ∃ b : β, P (decode c,b)) := by
  classical
  let test (c : Code α) (n : ℕ) : Bool :=
    match Encodable.decode (α := Code β) n with
    | none => false
    | some d => decide (P (decode c,decode d))
  have ht : Computable₂ test := by
    have hc : Computable (fun p : Code α × ℕ =>
      Option.casesOn (motive := fun _ => Bool) (Encodable.decode (α := Code β) p.2) false
        (fun d => decide (P (decode p.1,decode d)))) := by
      apply Computable.option_casesOn
        (g := fun p d => decide (P (decode p.1,decode d)))
        (Computable.decode.comp Computable.snd) (Computable.const false)
      exact (hp.decide.comp (Computable.pair (Computable.fst.comp Computable.fst)
        Computable.snd)).to₂
    apply Computable₂.mk
    exact hc.of_eq fun p => by
      cases he : Encodable.decode (α := Code β) p.2 <;> simp [test,he]
  have hs : Partrec (fun c => Nat.rfind (fun n => Part.some (test c n))) :=
    Partrec.rfind ht.partrec₂
  apply hs.dom_re.of_eq
  intro c
  simp only [Nat.rfind_dom,Part.mem_some_iff,Part.some_dom,implies_true,forall_const,and_true]
  constructor
  · rintro ⟨n,hn⟩
    cases hd : Encodable.decode (α := Code β) n with
    | none => simp [test,hd] at hn
    | some d => exact ⟨decode d,by simpa [test,hd] using hn⟩
  · rintro ⟨b,hb⟩
    obtain ⟨d,hd⟩ := Representation.onto b
    exact ⟨Encodable.encode d,by simp [test,Encodable.encodek,hd,hb]⟩

end MixedVolume.Represented

end
end -- component scope
/- END SOURCE: MixedVolume/Computability/RepresentedSearch.lean -/

