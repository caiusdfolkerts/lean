module

public import Papers.RationalityTenSmallTripleCores
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-!
# From arbitrary small incidence cores to the two finite models

This module performs the combinatorial normalization omitted from a bare
finite catalogue check. Lines are arbitrary subsets of eight labels, each
with at least three points. Distinct lines share at most one point and
every point used by the family lies on at least three lines. No assumption
that lines have size exactly three is made.

The four-point-line branch is reduced to the checked 4+3+3 root. Otherwise
all lines have size three, every used point has degree exactly three, and
the three-line root puts the family into the finite classification.

DRAFT: written while execution was unavailable; not compiled.
-/

namespace Papers.RationalityTen.SmallTripleCores

open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma mem_image_perm (p : Equiv.Perm (Fin 8)) (T : Triple) (x : Fin 8) :
    p x ∈ T.image p ↔ x ∈ T := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨y, hy, hxy⟩
    exact p.injective hxy ▸ hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

lemma image_perm_injective (p : Equiv.Perm (Fin 8)) :
    Function.Injective (fun T : Triple => T.image p) := by
  intro A B h
  change A.image p = B.image p at h
  apply Finset.ext
  intro x
  rw [← mem_image_perm p A x, ← mem_image_perm p B x, h]

lemma image_inter_perm (p : Equiv.Perm (Fin 8)) (A B : Triple) :
    (A ∩ B).image p = A.image p ∩ B.image p := by
  apply Finset.ext
  intro x
  obtain ⟨y, rfl⟩ := p.surjective x
  simp only [mem_image_perm, Finset.mem_inter]

lemma card_image_perm (p : Equiv.Perm (Fin 8)) (T : Triple) :
    (T.image p).card = T.card :=
  Finset.card_image_of_injective T p.injective

lemma inter_card_image_perm (p : Equiv.Perm (Fin 8)) (A B : Triple) :
    (A.image p ∩ B.image p).card = (A ∩ B).card := by
  rw [← image_inter_perm, card_image_perm]

lemma card_relabel (p : Equiv.Perm (Fin 8)) (L : Family) :
    (relabel p L).card = L.card :=
  Finset.card_image_of_injective L (image_perm_injective p)

lemma degree_relabel (p : Equiv.Perm (Fin 8)) (L : Family) (v : Fin 8) :
    degree (relabel p L) (p v) = degree L v := by
  unfold degree relabel
  have hh :
      (L.image fun T => T.image p).filter (fun T => p v ∈ T) =
        (L.filter fun T => v ∈ T).image (fun T => T.image p) := by
    apply Finset.ext
    intro S
    constructor
    · intro hS
      rcases Finset.mem_filter.mp hS with ⟨hS, hv⟩
      rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
      exact Finset.mem_image.mpr
        ⟨T, Finset.mem_filter.mpr ⟨hT, (mem_image_perm p T v).mp hv⟩, rfl⟩
    · intro hS
      rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
      rcases Finset.mem_filter.mp hT with ⟨hT, hv⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨T, hT, rfl⟩, (mem_image_perm p T v).mpr hv⟩
  rw [hh, Finset.card_image_of_injective _ (image_perm_injective p)]

lemma pairSeparated_relabel (p : Equiv.Perm (Fin 8)) {L : Family}
    (hL : pairSeparated L) : pairSeparated (relabel p L) := by
  intro A hA B hB hne
  rcases Finset.mem_image.mp hA with ⟨A, hAL, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨B, hBL, rfl⟩
  rw [inter_card_image_perm]
  exact hL hAL hBL (fun h => hne (congrArg (fun T : Triple => T.image p) h))

lemma inter_card_mono {A B C D : Triple} (hAC : A ⊆ C) (hBD : B ⊆ D) :
    (A ∩ B).card ≤ (C ∩ D).card :=
  Finset.card_le_card (fun _ hx => Finset.mem_inter.mpr
    ⟨hAC (Finset.mem_inter.mp hx).1, hBD (Finset.mem_inter.mp hx).2⟩)

lemma common_point_unique {A B : Triple} {p x : Fin 8}
    (hpA : p ∈ A) (hpB : p ∈ B) (hAB : (A ∩ B).card ≤ 1)
    (hxA : x ∈ A) (hxB : x ∈ B) : x = p :=
  Finset.card_le_one.mp hAB x (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
    p (Finset.mem_inter.mpr ⟨hpA, hpB⟩)

lemma pointed_triple (A : Triple) (p : Fin 8) (hp : p ∈ A)
    (hc : A.card = 3) :
    ∃ a b, p ≠ a ∧ p ≠ b ∧ a ≠ b ∧ A = {p,a,b} := by
  have he : (A.erase p).card = 2 := by
    rw [Finset.card_erase_of_mem hp, hc]
  obtain ⟨a,b,hab,heq⟩ := Finset.card_eq_two.mp he
  have hpa : p ≠ a := by
    intro h
    have : a ∈ A.erase p := by rw [heq]; simp
    simpa [h] using this
  have hpb : p ≠ b := by
    intro h
    have : b ∈ A.erase p := by rw [heq]; simp
    simpa [h] using this
  refine ⟨a,b,hpa,hpb,hab,?_⟩
  rw [← Finset.insert_erase hp, heq]

lemma pointed_quad (A : Triple) (p : Fin 8) (hp : p ∈ A)
    (hc : A.card = 4) :
    ∃ a b c, p ≠ a ∧ p ≠ b ∧ p ≠ c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      A = {p,a,b,c} := by
  have he : (A.erase p).card = 3 := by
    rw [Finset.card_erase_of_mem hp, hc]
  obtain ⟨a,b,c,hab,hac,hbc,heq⟩ := Finset.card_eq_three.mp he
  have hpa : p ≠ a := by
    intro h
    have : a ∈ A.erase p := by rw [heq]; simp
    simpa [h] using this
  have hpb : p ≠ b := by
    intro h
    have : b ∈ A.erase p := by rw [heq]; simp
    simpa [h] using this
  have hpc : p ≠ c := by
    intro h
    have : c ∈ A.erase p := by rw [heq]; simp
    simpa [h] using this
  refine ⟨a,b,c,hpa,hpb,hpc,hab,hac,hbc,?_⟩
  rw [← Finset.insert_erase hp, heq]

lemma pointed_subset (A : Triple) (p : Fin 8) (k : ℕ) (hp : p ∈ A)
    (hc : k + 1 ≤ A.card) :
    ∃ B : Triple, B ⊆ A ∧ p ∈ B ∧ B.card = k + 1 := by
  have he : k ≤ (A.erase p).card := by
    have hh := Finset.card_erase_of_mem hp
    omega
  obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq he
  refine ⟨insert p S, ?_, by simp, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hp
    · exact (Finset.mem_erase.mp (hS hx)).2
  · have hpn : p ∉ S := by
      intro h
      exact Finset.notMem_erase p A (hS h)
    rw [Finset.card_insert_of_notMem hpn, hcard]

lemma normalize_three_star (A B C : Triple) (v : Fin 8)
    (hvA : v ∈ A) (hvB : v ∈ B) (hvC : v ∈ C)
    (hcA : A.card = 3) (hcB : B.card = 3) (hcC : C.card = 3)
    (hAB : (A ∩ B).card ≤ 1) (hAC : (A ∩ C).card ≤ 1)
    (hBC : (B ∩ C).card ≤ 1) :
    ∃ p : Equiv.Perm (Fin 8), p v = 0 ∧
      A.image p = {0,1,2} ∧ B.image p = {0,3,4} ∧ C.image p = {0,5,6} := by
  obtain ⟨a,b,hva,hvb,hab,hA⟩ := pointed_triple A v hvA hcA
  obtain ⟨c,d,hvc,hvd,hcd,hB⟩ := pointed_triple B v hvB hcB
  obtain ⟨e,f,hve,hvf,hef,hC⟩ := pointed_triple C v hvC hcC
  have hcrossAB : ∀ x ∈ ({a,b} : Triple), ∀ y ∈ ({c,d} : Triple), x ≠ y := by
    intro x hx y hy hxy
    have hxA : x ∈ A := by rw [hA]; simp_all
    have hxB : x ∈ B := by rw [hB]; simp_all
    have hxv := common_point_unique hvA hvB hAB hxA hxB
    simp_all
  have hcrossAC : ∀ x ∈ ({a,b} : Triple), ∀ y ∈ ({e,f} : Triple), x ≠ y := by
    intro x hx y hy hxy
    have hxA : x ∈ A := by rw [hA]; simp_all
    have hxC : x ∈ C := by rw [hC]; simp_all
    have hxv := common_point_unique hvA hvC hAC hxA hxC
    simp_all
  have hcrossBC : ∀ x ∈ ({c,d} : Triple), ∀ y ∈ ({e,f} : Triple), x ≠ y := by
    intro x hx y hy hxy
    have hxB : x ∈ B := by rw [hB]; simp_all
    have hxC : x ∈ C := by rw [hC]; simp_all
    have hxv := common_point_unique hvB hvC hBC hxB hxC
    simp_all
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    at hcrossAB hcrossAC hcrossBC
  let f₀ : Fin 7 → Fin 8 := ![v,a,b,c,d,e,f]
  have hf₀ : Function.Injective f₀ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f₀]
  let g₀ : Fin 7 → Fin 8 := fun i => ⟨i.val, by omega⟩
  have hg₀ : Function.Injective g₀ := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair f₀ g₀ hf₀ hg₀
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have hp3 := hp 3
  have hp4 := hp 4
  have hp5 := hp 5
  have hp6 := hp 6
  refine ⟨p, ?_, ?_, ?_, ?_⟩ <;> simp_all [f₀,g₀,hA,hB,hC]

lemma normalize_quad_star (A B C : Triple) (v : Fin 8)
    (hvA : v ∈ A) (hvB : v ∈ B) (hvC : v ∈ C)
    (hcA : A.card = 4) (hcB : B.card = 3) (hcC : C.card = 3)
    (hAB : (A ∩ B).card ≤ 1) (hAC : (A ∩ C).card ≤ 1)
    (hBC : (B ∩ C).card ≤ 1) :
    ∃ p : Equiv.Perm (Fin 8), p v = 0 ∧
      A.image p = {0,1,2,3} ∧ B.image p = {0,4,5} ∧ C.image p = {0,6,7} := by
  obtain ⟨a,b,c,hva,hvb,hvc,hab,hac,hbc,hA⟩ := pointed_quad A v hvA hcA
  obtain ⟨d,e,hvd,hve,hde,hB⟩ := pointed_triple B v hvB hcB
  obtain ⟨f,g,hvf,hvg,hfg,hC⟩ := pointed_triple C v hvC hcC
  have hcrossAB : ∀ x ∈ ({a,b,c} : Triple), ∀ y ∈ ({d,e} : Triple), x ≠ y := by
    intro x hx y hy hxy
    have hxA : x ∈ A := by rw [hA]; simp_all
    have hxB : x ∈ B := by rw [hB]; simp_all
    have hxv := common_point_unique hvA hvB hAB hxA hxB
    simp_all
  have hcrossAC : ∀ x ∈ ({a,b,c} : Triple), ∀ y ∈ ({f,g} : Triple), x ≠ y := by
    intro x hx y hy hxy
    have hxA : x ∈ A := by rw [hA]; simp_all
    have hxC : x ∈ C := by rw [hC]; simp_all
    have hxv := common_point_unique hvA hvC hAC hxA hxC
    simp_all
  have hcrossBC : ∀ x ∈ ({d,e} : Triple), ∀ y ∈ ({f,g} : Triple), x ≠ y := by
    intro x hx y hy hxy
    have hxB : x ∈ B := by rw [hB]; simp_all
    have hxC : x ∈ C := by rw [hC]; simp_all
    have hxv := common_point_unique hvB hvC hBC hxB hxC
    simp_all
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    at hcrossAB hcrossAC hcrossBC
  let f₀ : Fin 8 → Fin 8 := ![v,a,b,c,d,e,f,g]
  have hf₀ : Function.Injective f₀ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f₀]
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair f₀ id hf₀ Function.injective_id
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have hp3 := hp 3
  have hp4 := hp 4
  have hp5 := hp 5
  have hp6 := hp 6
  have hp7 := hp 7
  refine ⟨p, ?_, ?_, ?_, ?_⟩ <;> simp_all [f₀,hA,hB,hC]

/-- The three root blocks cover all labels; any root block cannot grow
while meeting the other two in at most one point. Each check has256 cases. -/
theorem quad_root_maximal_a : ∀ T : Triple,
    ({0,1,2,3} : Triple) ⊆ T →
    (T ∩ {0,4,5}).card ≤ 1 → (T ∩ {0,6,7}).card ≤ 1 → T = {0,1,2,3} := by
  decide +kernel

theorem quad_root_maximal_b : ∀ T : Triple,
    ({0,4,5} : Triple) ⊆ T →
    (T ∩ {0,1,2,3}).card ≤ 1 → (T ∩ {0,6,7}).card ≤ 1 → T = {0,4,5} := by
  decide +kernel

theorem quad_root_maximal_c : ∀ T : Triple,
    ({0,6,7} : Triple) ⊆ T →
    (T ∩ {0,1,2,3}).card ≤ 1 → (T ∩ {0,4,5}).card ≤ 1 → T = {0,6,7} := by
  decide +kernel

theorem root_no_other_incident_line : ∀ T : Triple,
    3 ≤ T.card → 0 ∈ T → T ∉ rootStar →
    (∀ R ∈ rootStar, (T ∩ R).card ≤ 1) → False := by
  decide +kernel

lemma degree_zero_of_root (L : Family) (hroot : rootStar ⊆ L)
    (hlarge : ∀ T ∈ L, 3 ≤ T.card) (hpair : pairSeparated L) :
    degree L 0 = 3 := by
  have hh : L.filter (fun T => 0 ∈ T) = rootStar := by
    apply Finset.ext
    intro T
    constructor
    · intro hT
      rcases Finset.mem_filter.mp hT with ⟨hTL,hzero⟩
      by_contra hn
      apply root_no_other_incident_line T (hlarge T hTL) hzero hn
      intro R hR
      apply hpair hTL (hroot hR)
      intro heq
      exact hn (heq.symm ▸ hR)
    · intro hT
      exact Finset.mem_filter.mpr ⟨hroot hT, by
        have : ∀ R ∈ rootStar, (0 : Fin 8) ∈ R := by decide +kernel
        exact this T hT⟩
  unfold degree
  rw [hh]
  decide +kernel

lemma exists_three_incident (L : Family) (v : Fin 8) (h : 3 ≤ degree L v) :
    ∃ A ∈ L, ∃ B ∈ L, ∃ C ∈ L,
      v ∈ A ∧ v ∈ B ∧ v ∈ C ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  have hh : 2 < (L.filter fun T => v ∈ T).card := by
    change 3 ≤ (L.filter fun T => v ∈ T).card at h
    omega
  obtain ⟨A,hA,B,hB,C,hC,hAB,hAC,hBC⟩ := Finset.two_lt_card.mp hh
  exact ⟨A,(Finset.mem_filter.mp hA).1,B,(Finset.mem_filter.mp hB).1,
    C,(Finset.mem_filter.mp hC).1,(Finset.mem_filter.mp hA).2,
    (Finset.mem_filter.mp hB).2,(Finset.mem_filter.mp hC).2,hAB,hAC,hBC⟩

lemma exists_two_other_incident (L : Family) (v : Fin 8) (A : Triple)
    (hA : A ∈ L) (hvA : v ∈ A) (h : 3 ≤ degree L v) :
    ∃ B ∈ L, ∃ C ∈ L, v ∈ B ∧ v ∈ C ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  have hAI : A ∈ L.filter (fun T => v ∈ T) :=
    Finset.mem_filter.mpr ⟨hA,hvA⟩
  have hh : 1 < ((L.filter fun T => v ∈ T).erase A).card := by
    rw [Finset.card_erase_of_mem hAI]
    change 3 ≤ (L.filter fun T => v ∈ T).card at h
    omega
  obtain ⟨B,hB,C,hC,hBC⟩ := Finset.one_lt_card.mp hh
  rcases Finset.mem_erase.mp hB with ⟨hBA,hB⟩
  rcases Finset.mem_erase.mp hC with ⟨hCA,hC⟩
  exact ⟨B,(Finset.mem_filter.mp hB).1,C,(Finset.mem_filter.mp hC).1,
    (Finset.mem_filter.mp hB).2,(Finset.mem_filter.mp hC).2,
    Ne.symm hBA,Ne.symm hCA,hBC⟩

lemma root_subset_of_images (L : Family) (p : Equiv.Perm (Fin 8))
    {A B C : Triple} (hA : A ∈ L) (hB : B ∈ L) (hC : C ∈ L)
    (ha : A.image p = {0,1,2}) (hb : B.image p = {0,3,4})
    (hc : C.image p = {0,5,6}) : rootStar ⊆ relabel p L := by
  intro T hT
  have hA' : A.image p ∈ relabel p L := Finset.mem_image.mpr ⟨A,hA,rfl⟩
  have hB' : B.image p ∈ relabel p L := Finset.mem_image.mpr ⟨B,hB,rfl⟩
  have hC' : C.image p ∈ relabel p L := Finset.mem_image.mpr ⟨C,hC,rfl⟩
  simp only [rootStar, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl
  · simpa only [ha] using hA'
  · simpa only [hb] using hB'
  · simpa only [hc] using hC'

lemma min_size_relabel (p : Equiv.Perm (Fin 8)) {L : Family}
    (h : ∀ T ∈ L, 3 ≤ T.card) : ∀ T ∈ relabel p L, 3 ≤ T.card := by
  intro T hT
  rcases Finset.mem_image.mp hT with ⟨S,hS,rfl⟩
  rw [card_image_perm]
  exact h S hS

lemma min_degree_relabel (p : Equiv.Perm (Fin 8)) {L : Family}
    (h : ∀ v, (∃ T ∈ L, v ∈ T) → 3 ≤ degree L v) :
    ∀ v, (∃ T ∈ relabel p L, v ∈ T) → 3 ≤ degree (relabel p L) v := by
  intro v hv
  obtain ⟨w,rfl⟩ := p.surjective v
  rcases hv with ⟨T,hT,hv⟩
  rcases Finset.mem_image.mp hT with ⟨S,hS,rfl⟩
  rw [degree_relabel]
  exact h w ⟨S,hS,(mem_image_perm p S w).mp hv⟩

/-- Large lines cannot occur in a minimum-degree-three core on eight labels. -/
theorem all_lines_are_triples (L : Family)
    (hlarge : ∀ T ∈ L, 3 ≤ T.card) (hpair : pairSeparated L)
    (hdegree : ∀ v, (∃ T ∈ L, v ∈ T) → 3 ≤ degree L v) :
    ∀ T ∈ L, T.card = 3 := by
  intro A hA
  have hmin := hlarge A hA
  by_contra hneq
  have hfour : 4 ≤ A.card := by omega
  obtain ⟨v,hvA⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  obtain ⟨B,hB,C,hC,hvB,hvC,hAB,hAC,hBC⟩ :=
    exists_two_other_incident L v A hA hvA (hdegree v ⟨A,hA,hvA⟩)
  obtain ⟨A',hA'A,hvA',hcA'⟩ := pointed_subset A v 3 hvA hfour
  obtain ⟨B',hB'B,hvB',hcB'⟩ := pointed_subset B v 2 hvB (hlarge B hB)
  obtain ⟨C',hC'C,hvC',hcC'⟩ := pointed_subset C v 2 hvC (hlarge C hC)
  obtain ⟨p,hpv,ha,hb,hc⟩ := normalize_quad_star A' B' C' v hvA' hvB' hvC'
    hcA' hcB' hcC'
    ((inter_card_mono hA'A hB'B).trans (hpair hA hB hAB))
    ((inter_card_mono hA'A hC'C).trans (hpair hA hC hAC))
    ((inter_card_mono hB'B hC'C).trans (hpair hB hC hBC))
  have hmono (S T : Triple) (hST : S ⊆ T) : S.image p ⊆ T.image p :=
    Finset.image_subset_image hST
  have hab : (A.image p ∩ B'.image p).card ≤ 1 := by
    rw [inter_card_image_perm]
    exact (inter_card_mono (fun _ hx => hx) hB'B).trans (hpair hA hB hAB)
  have hac : (A.image p ∩ C'.image p).card ≤ 1 := by
    rw [inter_card_image_perm]
    exact (inter_card_mono (fun _ hx => hx) hC'C).trans (hpair hA hC hAC)
  have hba : (B.image p ∩ A'.image p).card ≤ 1 := by
    rw [inter_card_image_perm]
    exact (inter_card_mono (fun _ hx => hx) hA'A).trans (hpair hB hA hAB.symm)
  have hbc : (B.image p ∩ C'.image p).card ≤ 1 := by
    rw [inter_card_image_perm]
    exact (inter_card_mono (fun _ hx => hx) hC'C).trans (hpair hB hC hBC)
  have hca : (C.image p ∩ A'.image p).card ≤ 1 := by
    rw [inter_card_image_perm]
    exact (inter_card_mono (fun _ hx => hx) hA'A).trans (hpair hC hA hAC.symm)
  have hcb : (C.image p ∩ B'.image p).card ≤ 1 := by
    rw [inter_card_image_perm]
    exact (inter_card_mono (fun _ hx => hx) hB'B).trans (hpair hC hB hBC.symm)
  have ha' : A.image p = {0,1,2,3} := quad_root_maximal_a _ (ha ▸ hmono _ _ hA'A)
    (by simpa only [hb] using hab) (by simpa only [hc] using hac)
  have hb' : B.image p = {0,4,5} := quad_root_maximal_b _ (hb ▸ hmono _ _ hB'B)
    (by simpa only [ha] using hba) (by simpa only [hc] using hbc)
  have hc' : C.image p = {0,6,7} := quad_root_maximal_c _ (hc ▸ hmono _ _ hC'C)
    (by simpa only [ha] using hca) (by simpa only [hb] using hcb)
  have hroot : quadRootStar ⊆ relabel p L := by
    intro T hT
    have hA' : A.image p ∈ relabel p L := Finset.mem_image.mpr ⟨A,hA,rfl⟩
    have hB' : B.image p ∈ relabel p L := Finset.mem_image.mpr ⟨B,hB,rfl⟩
    have hC' : C.image p ∈ relabel p L := Finset.mem_image.mpr ⟨C,hC,rfl⟩
    simp only [quadRootStar, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl
    · simpa only [ha'] using hA'
    · simpa only [hb'] using hB'
    · simpa only [hc'] using hC'
  apply no_quad_root_core (relabel p L) hroot
    (min_size_relabel p hlarge) (pairSeparated_relabel p hpair)
  intro x hx
  apply min_degree_relabel p hdegree x
  refine ⟨{0,1,2,3}, hroot (by simp [quadRootStar]), ?_⟩
  have hsub : quadFirstGroup ⊆ ({0,1,2,3} : Triple) := by decide +kernel
  exact hsub hx

theorem every_used_point_has_degree_three (L : Family)
    (htriples : ∀ T ∈ L, T.card = 3) (hpair : pairSeparated L)
    (hdegree : ∀ v, (∃ T ∈ L, v ∈ T) → 3 ≤ degree L v) :
    ∀ v, (∃ T ∈ L, v ∈ T) → degree L v = 3 := by
  intro v hv
  obtain ⟨A,hA,B,hB,C,hC,hvA,hvB,hvC,hAB,hAC,hBC⟩ :=
    exists_three_incident L v (hdegree v hv)
  obtain ⟨p,hpv,ha,hb,hc⟩ := normalize_three_star A B C v hvA hvB hvC
    (htriples A hA) (htriples B hB) (htriples C hC)
    (hpair hA hB hAB) (hpair hA hC hAC) (hpair hB hC hBC)
  have hroot := root_subset_of_images L p hA hB hC ha hb hc
  have hd := degree_zero_of_root (relabel p L) hroot
    (min_size_relabel p (fun T hT => (htriples T hT).ge))
    (pairSeparated_relabel p hpair)
  have hh := degree_relabel p L v
  rw [hpv] at hh
  exact hh.symm.trans hd

lemma sum_degree (L : Family) :
    (∑ v : Fin 8, degree L v) = ∑ T ∈ L, T.card := by
  simp only [degree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  simp

theorem normalized_core_classification (L : Family) (hroot : rootStar ⊆ L)
    (htriples : ∀ T ∈ L, T.card = 3) (hpair : pairSeparated L)
    (hdegree : ∀ v, (∃ T ∈ L, v ∈ T) → degree L v = 3) :
    ∃ p : Equiv.Perm (Fin 8),
      relabel p L = canonicalSeven ∨ relabel p L = paperMacLane := by
  have hused : ∀ v : Fin 8, v ≠ 7 → ∃ T ∈ rootStar, v ∈ T := by
    decide +kernel
  have hdegrees : ∀ v : Fin 8, v ≠ 7 → degree L v = 3 := by
    intro v hv
    obtain ⟨T,hT,hvT⟩ := hused v hv
    exact hdegree v ⟨T,hroot hT,hvT⟩
  have hneigh : ∀ v ∈ neighbors, degree L v = 3 := by
    intro v hv
    have hnot : ∀ x ∈ neighbors, (x : Fin 8) ≠ 7 := by decide +kernel
    exact hdegrees v (hnot v hv)
  have hsum := sum_degree L
  have hRHS : (∑ T ∈ L, T.card) = 3 * L.card := by
    rw [Finset.sum_congr rfl (fun T hT => htriples T hT)]
    simp [Nat.mul_comm]
  rw [hRHS] at hsum
  by_cases hseven : ∃ T ∈ L, (7 : Fin 8) ∈ T
  · have hd7 := hdegree 7 hseven
    have hall : ∀ v : Fin 8, degree L v = 3 := by
      intro v
      by_cases hv : v = 7
      · simpa [hv] using hd7
      · exact hdegrees v hv
    have hcard : L.card = 8 := by
      have hs : (∑ v : Fin 8, degree L v) = 24 := by simp [hall]
      omega
    obtain ⟨p,hp⟩ := eight_root_core L hroot htriples hcard hpair hneigh hd7
    exact ⟨p,Or.inr hp⟩
  · have hnone : ∀ T ∈ L, (7 : Fin 8) ∉ T := by
      intro T hT hv
      exact hseven ⟨T,hT,hv⟩
    have hd7 : degree L 7 = 0 := by
      unfold degree
      have hh : L.filter (fun T => (7 : Fin 8) ∈ T) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        exact hnone
      rw [hh]
      rfl
    have hformula : ∀ v : Fin 8, degree L v = if v = 7 then 0 else 3 := by
      intro v
      split_ifs with hv
      · simpa [hv] using hd7
      · exact hdegrees v hv
    have hcard : L.card = 7 := by
      have hs : (∑ v : Fin 8, degree L v) = 21 := by
        simp only [hformula]
        decide +kernel
      omega
    obtain ⟨p,hp⟩ := seven_root_core L hroot htriples hnone hcard hpair hneigh
    exact ⟨p,Or.inl hp⟩

/-- Complete combinatorial classification of every nonempty minimum-degree
three incidence core on at most eight labels, including variable line sizes. -/
theorem classify_incidence_core (L : Family) (hne : L.Nonempty)
    (hlarge : ∀ T ∈ L, 3 ≤ T.card) (hpair : pairSeparated L)
    (hdegree : ∀ v, (∃ T ∈ L, v ∈ T) → 3 ≤ degree L v) :
    ∃ p : Equiv.Perm (Fin 8),
      relabel p L = canonicalSeven ∨ relabel p L = paperMacLane := by
  have htriples := all_lines_are_triples L hlarge hpair hdegree
  have hexact := every_used_point_has_degree_three L htriples hpair hdegree
  obtain ⟨T,hT⟩ := hne
  have hTpos : 0 < T.card := by rw [htriples T hT]; decide
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hTpos
  obtain ⟨A,hA,B,hB,C,hC,hvA,hvB,hvC,hAB,hAC,hBC⟩ :=
    exists_three_incident L v (hdegree v ⟨T,hT,hv⟩)
  obtain ⟨p,hpv,ha,hb,hc⟩ := normalize_three_star A B C v hvA hvB hvC
    (htriples A hA) (htriples B hB) (htriples C hC)
    (hpair hA hB hAB) (hpair hA hC hAC) (hpair hB hC hBC)
  have hroot := root_subset_of_images L p hA hB hC ha hb hc
  have htriples' : ∀ T ∈ relabel p L, T.card = 3 := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨T,hT,rfl⟩
    rw [card_image_perm]
    exact htriples T hT
  have hexact' : ∀ v, (∃ T ∈ relabel p L, v ∈ T) →
      degree (relabel p L) v = 3 := by
    intro v hv
    obtain ⟨w,rfl⟩ := p.surjective v
    rcases hv with ⟨S,hS,hv⟩
    rcases Finset.mem_image.mp hS with ⟨T,hT,rfl⟩
    rw [degree_relabel]
    exact hexact w ⟨T,hT,(mem_image_perm p T w).mp hv⟩
  obtain ⟨q,hq⟩ := normalized_core_classification (relabel p L) hroot htriples'
    (pairSeparated_relabel p hpair) hexact'
  refine ⟨p.trans q, ?_⟩
  rwa [relabel_trans]

end Papers.RationalityTen.SmallTripleCores
