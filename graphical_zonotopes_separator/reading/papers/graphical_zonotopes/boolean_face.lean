module

public import Papers.GraphicalZonotopes.BooleanFourier
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The three choices in each factor are exactly `1`, `uᵢ`, and `uᵢvᵢ`. -/
def tensorMonomial (a : I → Option Bool) (uv : Cube I × Cube I) : ℝ :=
  ∏ i, match a i with
    | none => 1
    | some false => spin (uv.1 i)
    | some true => spin (uv.1 i)*spin (uv.2 i)

/-- The actual tensor product of the three-dimensional one-part spaces,
realized as a subspace of functions on all independent signs. -/
def tensorSpace : Submodule ℝ ((Cube I × Cube I) → ℝ) :=
  Submodule.span ℝ (Set.range (tensorMonomial (I := I)))

def active (a : I → Option Bool) : Finset I := univ.filter (fun i => (a i).isSome)
def second (a : I → Option Bool) : Finset I := univ.filter (fun i => a i=some true)

theorem second_subset_active (a : I → Option Bool) : second a⊆active a := by
  intro i hi
  simp only [second,mem_filter,mem_univ,true_and] at hi
  simp [active,hi]

theorem tensorMonomial_eq (a : I → Option Bool) (uv : Cube I × Cube I) :
    tensorMonomial a uv=character (active a) uv.1*character (second a) uv.2 := by
  simp only [tensorMonomial,character,← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  cases h : a i with
  | none => simp [active,second,h]
  | some b => cases b <;> simp [active,second,h]

def coordinateChange : (Cube I × Cube I) ≃ (Cube I × Cube I) where
  toFun uv := (uv.1,fun i => Bool.xor (uv.1 i) (uv.2 i))
  invFun uv := (uv.1,fun i => Bool.xor (uv.1 i) (uv.2 i))
  left_inv uv := by
    apply Prod.ext
    · rfl
    · funext i
      change Bool.xor (uv.1 i) (Bool.xor (uv.1 i) (uv.2 i)) = uv.2 i
      cases uv.1 i <;> cases uv.2 i <;> rfl
  right_inv uv := by
    apply Prod.ext
    · rfl
    · funext i
      change Bool.xor (uv.1 i) (Bool.xor (uv.1 i) (uv.2 i)) = uv.2 i
      cases uv.1 i <;> cases uv.2 i <;> rfl

theorem spin_xor (a b : Bool) : spin (Bool.xor a b)=spin a*spin b := by
  cases a <;> cases b <;> norm_num [spin]

/-- This identifies the transformed tensor generators with the paper's
original factors `1,sᵢ₀,sᵢ₁`; the independent-coordinate change is an equivalence. -/
theorem tensorMonomial_coordinateChange (a : I → Option Bool) (s : Cube I × Cube I) :
    tensorMonomial a (coordinateChange s)=
      ∏ i,match a i with
        | none => 1
        | some false => spin (s.1 i)
        | some true => spin (s.2 i) := by
  apply prod_congr rfl
  intro i hi
  cases h : a i with
  | none => rfl
  | some b =>
    cases b
    · rfl
    · change spin (s.1 i)*spin (Bool.xor (s.1 i) (s.2 i))=spin (s.2 i)
      rw [spin_xor,← mul_assoc,spin_mul_self,one_mul]

def HasRestrictedExpansion (p : (Cube I × Cube I) → ℝ) : Prop :=
  ∃ P : Finset I → Cube I → ℝ,(∀ A,DependsOn A (P A)) ∧
    ∀ u v,p (u,v)=∑ A : Finset I,character A u*P A v

theorem tensorMonomial_expansion (a : I → Option Bool) :
    HasRestrictedExpansion (tensorMonomial a) := by
  refine ⟨fun A v => if A=active a then character (second a) v else 0,?_,?_⟩
  · intro A
    by_cases h : A=active a
    · subst A
      simpa using (dependsOn_character (second a)).mono (second_subset_active a)
    · simpa [h] using dependsOn_const A (0 : ℝ)
  · intro u v
    simp [tensorMonomial_eq]

theorem restrictedExpansion_of_mem_tensorSpace {p : (Cube I × Cube I) → ℝ}
    (hp : p∈tensorSpace) : HasRestrictedExpansion p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a,rfl⟩ := hp
    exact tensorMonomial_expansion a
  | zero =>
    refine ⟨fun _ _ => 0,fun A => dependsOn_const A 0,?_⟩
    simp
  | add p q hp hq ihp ihq =>
    obtain ⟨P,hP,hp⟩ := ihp
    obtain ⟨Q,hQ,hq⟩ := ihq
    refine ⟨fun A => P A+Q A,fun A => (hP A).add (hQ A),?_⟩
    intro u v
    simp only [Pi.add_apply,hp,hq,mul_add,sum_add_distrib]
  | smul c p hp ih =>
    obtain ⟨P,hP,hp⟩ := ih
    refine ⟨fun A => c • P A,fun A => (hP A).smul c,?_⟩
    intro u v
    simp only [Pi.smul_apply,smul_eq_mul,hp,mul_sum]
    apply sum_congr rfl
    intro A hA
    ring

theorem constant_mem_tensorSpace (c : ℝ) : (fun _ : Cube I × Cube I => c)∈tensorSpace := by
  have h : tensorMonomial (fun _ : I => none)∈tensorSpace :=
    Submodule.subset_span ⟨_,rfl⟩
  convert (tensorSpace (I := I)).smul_mem c h using 1
  funext uv
  simp [tensorMonomial]

theorem full_character_product_mem (B : Finset I) :
    (fun uv : Cube I × Cube I => character univ uv.1*character B uv.2)∈tensorSpace := by
  let a : I → Option Bool := fun i => if i∈B then some true else some false
  have h := (Submodule.subset_span (R := ℝ)
    (s := Set.range (tensorMonomial (I := I))) (⟨a,rfl⟩ : tensorMonomial a∈Set.range tensorMonomial))
  have ha : active a=univ := by
    ext i
    by_cases hi : i ∈ B <;> simp [active,a,hi]
  have hb : second a=B := by ext i; simp [second,a]
  have he : tensorMonomial a = (fun uv : Cube I × Cube I => character univ uv.1*character B uv.2) := by
    funext uv
    rw [tensorMonomial_eq,ha,hb]
  rw [he] at h
  exact h

def phase (G : Cube I → ℝ) (uv : Cube I × Cube I) : ℝ := character univ uv.1*G uv.2
def faceFunction (G : Cube I → ℝ) (uv : Cube I × Cube I) : ℝ := (1+phase G uv)/2

theorem phase_mem_tensorSpace (G : Cube I → ℝ) : phase G∈tensorSpace := by
  obtain ⟨c,hc⟩ := exists_character_expansion G
  have h : (∑ B : Finset I,c B •
      (fun uv : Cube I × Cube I => character univ uv.1*character B uv.2))∈tensorSpace :=
    (tensorSpace (I := I)).sum_mem fun B _ =>
      (tensorSpace (I := I)).smul_mem (c B) (full_character_product_mem B)
  convert h using 1
  funext uv
  simp only [phase,hc,mul_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply sum_congr rfl
  intro B hB
  ring

theorem faceFunction_mem_tensorSpace (G : Cube I → ℝ) : faceFunction G∈tensorSpace := by
  have h := (tensorSpace (I := I)).smul_mem (1/2 : ℝ)
    ((tensorSpace (I := I)).add_mem (constant_mem_tensorSpace 1) (phase_mem_tensorSpace G))
  convert h using 1
  funext uv
  simp only [faceFunction,Pi.smul_apply,smul_eq_mul,Pi.add_apply]
  ring

/-- Nonfactorization across every nonempty proper partition. The factors are
arbitrary real functions of their respective variables. For a sign-valued
function, any factorization can equivalently be rescaled to sign factors. -/
def Nonseparable (G : Cube I → ℝ) : Prop :=
  ∀ A : Finset I,A.Nonempty → A≠univ →
    ¬∃ H K : Cube I → ℝ,DependsOn A H ∧ DependsOn Aᶜ K ∧ ∀ v,G v=H v*K v

theorem factor_of_complementary_equation {G P Q : Cube I → ℝ} {A : Finset I}
    (hG : ∀ v,G v=1 ∨ G v=-1)
    (hP : DependsOn A P) (hQ : DependsOn Aᶜ Q)
    (heq : ∀ v,P v=G v*Q v) (v₀ : Cube I) (hc : P v₀≠0) :
    ∃ H K : Cube I → ℝ,DependsOn A H ∧ DependsOn Aᶜ K ∧ ∀ v,G v=H v*K v := by
  let c := P v₀
  let K : Cube I → ℝ := fun v => G (mix A v₀ v)
  let H : Cube I → ℝ := fun v => P v/c
  have hGsquare : ∀ v,G v*G v=1 := by
    intro v
    rcases hG v with h | h <;> rw [h] <;> norm_num
  have hKsquare : ∀ v,K v*K v=1 := fun v => hGsquare (mix A v₀ v)
  have hQc : ∀ v,Q v=K v*c := by
    intro v
    have h := heq (mix A v₀ v)
    rw [hP.mix_left,hQ.mix_right] at h
    have hh := congrArg (fun x : ℝ => K v*x) h
    change K v*c=K v*(K v*Q v) at hh
    rw [← mul_assoc,hKsquare,one_mul] at hh
    exact hh.symm
  refine ⟨H,K,?_,?_,?_⟩
  · intro u v huv
    change P u/c=P v/c
    rw [hP u v huv]
  · intro u v huv
    apply congrArg G
    funext i
    by_cases hi : i∈A
    · simp [mix,hi]
    · simp [mix,hi,huv i (by simpa using hi)]
  · intro v
    change G v=(P v/c)*K v
    rw [heq v,hQc v]
    have hc' : c≠0 := hc
    calc
      G v=G v*(K v*K v) := by rw [hKsquare,mul_one]
      _=(G v*(K v*c)/c)*K v := by field_simp [hc']

theorem restricted_components_equation {p : (Cube I × Cube I) → ℝ}
    {G : Cube I → ℝ} {P : Finset I → Cube I → ℝ}
    (hp : ∀ u v,p (u,v)=∑ A : Finset I,character A u*P A v)
    (hgp : ∀ u v,phase G (u,v)*p (u,v)=p (u,v)) :
    ∀ A v,P A v=G v*P Aᶜ v := by
  intro A v
  have hcoeff : ∀ B : Finset I,
      (∑ u : Cube I,character B u*p (u,v))=(2 : ℝ)^Fintype.card I*P B v := by
    intro B
    have hs : ∀ u,p (u,v)=∑ C : Finset I,P C v*character C u := by
      intro u
      rw [hp]
      apply sum_congr rfl
      intro C hC
      ring
    simp_rw [hs]
    exact coefficient_extraction (fun C => P C v) B
  have h := congrArg (fun f : Cube I → ℝ => ∑ u,character A u*f u)
    (funext fun u => hgp u v)
  have hleft : (∑ u : Cube I,character A u*(phase G (u,v)*p (u,v)))=
      G v*(∑ u : Cube I,character Aᶜ u*p (u,v)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro u hu
    rw [← character_compl]
    unfold phase
    ring
  change (∑ u : Cube I,character A u*(phase G (u,v)*p (u,v)))=
    ∑ u : Cube I,character A u*p (u,v) at h
  rw [hleft,hcoeff,hcoeff] at h
  have hn : (2 : ℝ)^Fintype.card I≠0 := pow_ne_zero _ (by norm_num)
  apply (mul_left_cancel₀ hn)
  calc
    (2 : ℝ)^Fintype.card I*P A v=G v*((2 : ℝ)^Fintype.card I*P Aᶜ v) := h.symm
    _=(2 : ℝ)^Fintype.card I*(G v*P Aᶜ v) := by ring

theorem phase_square {G : Cube I → ℝ} (hG : ∀ v,G v=1 ∨ G v=-1)
    (uv : Cube I × Cube I) : phase G uv*phase G uv=1 := by
  have hGv : G uv.2*G uv.2=1 := by
    rcases hG uv.2 with h | h <;> rw [h] <;> norm_num
  have hu := character_square (univ : Finset I) uv.1
  calc
    phase G uv*phase G uv=(character univ uv.1*character univ uv.1)*(G uv.2*G uv.2) := by
      unfold phase
      ring
    _=1 := by rw [hu,hGv]; norm_num

theorem vanishes_iff_phase_fixed {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (p : (Cube I × Cube I) → ℝ) :
    (∀ uv,faceFunction G uv=0 → p uv=0) ↔
      ∀ u v,phase G (u,v)*p (u,v)=p (u,v) := by
  constructor
  · intro hp u v
    have hs := phase_square hG (u,v)
    have hsign : phase G (u,v)=1 ∨ phase G (u,v)=-1 := by
      have h : (phase G (u,v)-1)*(phase G (u,v)+1)=0 := by nlinarith
      rcases mul_eq_zero.mp h with h | h
      · left; linarith
      · right; linarith
    rcases hsign with h | h
    · simp [h]
    · have hz := hp (u,v) (by simp [faceFunction,h])
      simp [hz]
  · intro hp uv hf
    have h := hp uv.1 uv.2
    have hg : phase G uv=-1 := by unfold faceFunction at hf; linarith
    rw [hg] at h
    linarith

/-- Lemma9.9: the complete vanishing subspace is the one-dimensional line
through the Boolean function, for every nonempty finite index set. -/
theorem boolean_face_line [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (hsep : Nonseparable G)
    (p : (Cube I × Cube I) → ℝ) (hp : p∈tensorSpace) :
    (∀ uv,faceFunction G uv=0 → p uv=0) ↔
      ∃ c : ℝ,p=c • faceFunction G := by
  constructor
  · intro hzero
    obtain ⟨P,hP,hp⟩ := restrictedExpansion_of_mem_tensorSpace hp
    have hgp := (vanishes_iff_phase_fixed hG p).mp hzero
    have hcomponents := restricted_components_equation hp hgp
    have hproper : ∀ A : Finset I,A≠∅ → A≠univ → ∀ v,P A v=0 := by
      intro A hA htop v
      by_contra hv
      exact hsep A (nonempty_iff_ne_empty.mpr hA) htop
        (factor_of_complementary_equation hG (hP A) (hP Aᶜ)
          (hcomponents A) v hv)
    obtain ⟨c,hc⟩ := (dependsOn_empty_iff (P ∅)).mp (hP ∅)
    have hfull : ∀ v,P univ v=G v*c := by
      intro v
      simpa only [compl_univ,hc] using hcomponents univ v
    have hne : (∅ : Finset I)≠univ := by
      exact ne_of_lt (empty_ssubset.mpr univ_nonempty)
    refine ⟨2*c,?_⟩
    funext uv
    rw [hp]
    have hs : (∑ A : Finset I,character A uv.1*P A uv.2)=
        character ∅ uv.1*P ∅ uv.2+character univ uv.1*P univ uv.2 := by
      have hh := sum_subset (f := fun A : Finset I => character A uv.1 * P A uv.2) (subset_univ ({∅,univ} : Finset (Finset I)))
        (fun A hAu hnot => by
          have hA : A≠∅ := by intro h; apply hnot; simp [h]
          have htop : A≠univ := by intro h; apply hnot; simp [h]
          rw [hproper A hA htop,mul_zero])
      simpa only [sum_pair hne] using hh.symm
    rw [hs,character_empty,one_mul,hc,hfull]
    simp only [Pi.smul_apply,smul_eq_mul,faceFunction,phase]
    ring
  · rintro ⟨c,rfl⟩ uv huv
    simp [huv]

theorem faceFunction_boolean {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (uv : Cube I × Cube I) :
    faceFunction G uv=0 ∨ faceFunction G uv=1 := by
  have hs := phase_square hG uv
  have hp : faceFunction G uv*(faceFunction G uv-1)=0 := by
    unfold faceFunction
    nlinarith [hs]
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem faceFunction_ne_zero [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) : faceFunction G≠0 := by
  let v₀ : Cube I := fun _ => false
  obtain ⟨i⟩ := ‹Nonempty I›
  have hvalue : ∃ u : Cube I,faceFunction G (u,v₀)=1 := by
    rcases hG v₀ with h | h
    · refine ⟨fun _ => false,?_⟩
      simp [faceFunction,phase,character,spin,h]
    · let u : Cube I := fun j => if j=i then true else false
      have hu : character univ u=-1 := by
        rw [character_univ,prod_eq_single i]
        · simp [u,spin]
        · intro j hj hji
          simp [u,hji,spin]
        · simp
      exact ⟨u,by simp [faceFunction,phase,hu,h]⟩
  obtain ⟨u,hu⟩ := hvalue
  intro hz
  rw [hz] at hu
  norm_num at hu

/-- All tensor polynomials vanishing on the literal zero set of `f`. -/
def faceKernel (G : Cube I → ℝ) : Submodule ℝ ((Cube I × Cube I) → ℝ) where
  carrier := {p | p∈tensorSpace ∧ ∀ uv,faceFunction G uv=0 → p uv=0}
  zero_mem' := ⟨(tensorSpace (I := I)).zero_mem,by simp⟩
  add_mem' hp hq := ⟨(tensorSpace (I := I)).add_mem hp.1 hq.1,by
    intro uv huv
    simp [hp.2 uv huv,hq.2 uv huv]⟩
  smul_mem' c p hp := ⟨(tensorSpace (I := I)).smul_mem c hp.1,by
    intro uv huv
    simp [hp.2 uv huv]⟩

theorem faceKernel_eq_span [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (hsep : Nonseparable G) :
    faceKernel G=Submodule.span ℝ {faceFunction G} := by
  ext p
  constructor
  · intro hp
    obtain ⟨c,hc⟩ := (boolean_face_line hG hsep p hp.1).mp hp.2
    exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩
  · intro hp
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hp
    exact ⟨(tensorSpace (I := I)).smul_mem c (faceFunction_mem_tensorSpace G),
      fun uv huv => by simp [huv]⟩

theorem faceKernel_finrank [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (hsep : Nonseparable G) :
    Module.finrank ℝ (faceKernel G)=1 := by
  rw [faceKernel_eq_span hG hsep]
  exact finrank_span_singleton (faceFunction_ne_zero hG)

theorem Nonseparable.neg {G : Cube I → ℝ} (hG : Nonseparable G) :
    Nonseparable (-G) := by
  intro A hA htop hfactor
  obtain ⟨H,K,hH,hK,h⟩ := hfactor
  apply hG A hA htop
  refine ⟨(-1 : ℝ) • H,K,hH.smul (-1),hK,?_⟩
  intro v
  have hv := h v
  change -G v=H v*K v at hv
  change G v=((-1 : ℝ)*H v)*K v
  linarith

/-- The nonfactorization convention is unchanged if the candidate factors
are required to be sign-valued: every real factorization of a sign function
has such a normalization. -/
theorem normalize_sign_factorization {G H K : Cube I → ℝ} {A : Finset I}
    (hG : ∀ v,G v=1 ∨ G v=-1)
    (hH : DependsOn A H) (hK : DependsOn Aᶜ K)
    (hfactor : ∀ v,G v=H v*K v) :
    ∃ H' K' : Cube I → ℝ,DependsOn A H' ∧ DependsOn Aᶜ K' ∧
      (∀ v,H' v=1 ∨ H' v=-1) ∧ (∀ v,K' v=1 ∨ K' v=-1) ∧
      ∀ v,G v=H' v*K' v := by
  let v₀ : Cube I := fun _ => false
  let H' : Cube I → ℝ := fun v => G (mix A v v₀)*G v₀
  let K' : Cube I → ℝ := fun v => G (mix A v₀ v)
  have hH' : DependsOn A H' := by
    intro u v huv
    change G (mix A u v₀)*G v₀=G (mix A v v₀)*G v₀
    congr 2
    funext i
    by_cases hi : i∈A
    · simp [mix,hi,huv i hi]
    · simp [mix,hi]
  have hK' : DependsOn Aᶜ K' := by
    intro u v huv
    apply congrArg G
    funext i
    by_cases hi : i∈A
    · simp [mix,hi]
    · simp [mix,hi,huv i (by simpa using hi)]
  refine ⟨H',K',hH',hK',?_,fun v => hG (mix A v₀ v),?_⟩
  · intro v
    rcases hG (mix A v v₀) with ha | ha <;>
      rcases hG v₀ with hb | hb <;> simp [H',ha,hb]
  · intro v
    have h₀ : G v₀*G v₀=1 := by
      rcases hG v₀ with h | h <;> rw [h] <;> norm_num
    change G v=(G (mix A v v₀)*G v₀)*G (mix A v₀ v)
    rw [hfactor (mix A v v₀),hfactor (mix A v₀ v),
      hH.mix_left,hH.mix_left,hK.mix_right,hK.mix_right]
    calc
      G v=G v*(G v₀*G v₀) := by rw [h₀,mul_one]
      _=(H v*K v₀*G v₀)*(H v₀*K v) := by rw [hfactor v,hfactor v₀]; ring

end BooleanFourier
end GraphicalZonotopes
