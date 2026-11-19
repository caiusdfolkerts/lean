module
public import Papers.RationalityTenBasisExtensionCNF
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace Papers.RationalityTen.BasisReconstruction

open Finset BasisFamilies BasisExtensionCNF

abbrev Point := Fin 8

def extensionFamily {k t : ℕ} (old : Finset (Finset Point))
    (U : Fin k → Finset Point) (newIndex : Fin t → Fin k) (code : ℕ) :
    Finset (Finset Point) :=
  old ∪ ((univ.filter fun j : Fin t => code.testBit j.val = true).image
    fun j => U (newIndex j))

theorem extensionFamily_eq {k t rank : ℕ} {ground : Finset Point}
    (M : BasisFamily ground rank) (U : Fin k → Finset Point) (e : Point)
    (old : Finset (Finset Point)) (newIndex : Fin t → Fin k) (code : ℕ)
    (hcomplete : ∀ A ∈ M.bases, ∃ i, U i = A)
    (hold : ∀ i, e ∉ U i → (U i ∈ M.bases ↔ U i ∈ old))
    (holdcomplete : ∀ A ∈ old, ∃ i, U i = A)
    (holdavoid : ∀ A ∈ old, e ∉ A)
    (hnew : ∀ i, e ∈ U i → ∃ j, newIndex j = i)
    (hmatch : ModelMatch M U newIndex code) :
    M.bases = extensionFamily old U newIndex code := by
  ext A
  constructor
  · intro hA
    obtain ⟨i,rfl⟩ := hcomplete A hA
    by_cases he : e ∈ U i
    · obtain ⟨j,hj⟩ := hnew i he
      apply mem_union_right
      apply mem_image.mpr
      refine ⟨j,mem_filter.mpr ⟨mem_univ _,?_⟩,congrArg U hj⟩
      exact (hmatch j).mp (hj.symm ▸ hA)
    · exact mem_union_left _ ((hold i he).mp hA)
  · intro hA
    rcases mem_union.mp hA with hA | hA
    · obtain ⟨i,hi⟩ := holdcomplete A hA
      rw [← hi] at hA ⊢
      exact (hold i (holdavoid _ hA)).mpr hA
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hA
      exact (hmatch j).mpr (mem_filter.mp hj).2

def groundPrefix (n : ℕ) : Finset Point := univ.filter fun x => x.val < n

@[simp] theorem mem_groundPrefix (n : ℕ) (x : Point) : x ∈ groundPrefix n ↔ x.val < n := by
  simp [groundPrefix]

@[simp] theorem groundPrefix_zero : groundPrefix 0 = ∅ := by ext x; simp

theorem groundPrefix_erase_last (n : ℕ) (hn : n < 8) :
    (groundPrefix (n+1)).erase ⟨n,hn⟩ = groundPrefix n := by
  ext x
  simp only [mem_erase,mem_groundPrefix,ne_eq,Fin.mk.injEq]
  constructor
  · rintro ⟨hx,hlt⟩
    have hne : x.val ≠ n := fun h => hx (Fin.ext h)
    omega
  · intro hx
    refine ⟨?_,by omega⟩
    intro he
    have hval : x.val = n := congrArg Fin.val he
    omega

def FixesOutside (p : Equiv.Perm Point) (n : ℕ) : Prop :=
  ∀ x : Point, n ≤ x.val → p x = x

theorem fixesOutside_refl (n : ℕ) : FixesOutside (Equiv.refl Point) n := by
  intro x hx
  rfl

theorem fixesOutside_trans {p q : Equiv.Perm Point} {n : ℕ}
    (hp : FixesOutside p n) (hq : FixesOutside q n) :
    FixesOutside (p.trans q) n := by
  intro x hx
  simp only [Equiv.trans_apply,hp x hx,hq x hx]

theorem fixesOutside_mono {p : Equiv.Perm Point} {n m : ℕ}
    (hp : FixesOutside p n) (hnm : n ≤ m) : FixesOutside p m :=
  fun x hx => hp x (hnm.trans hx)

theorem fixesOutside_symm {p : Equiv.Perm Point} {n : ℕ}
    (hp : FixesOutside p n) : FixesOutside p.symm n := by
  intro x hx
  apply p.injective
  rw [p.apply_symm_apply,hp x hx]

theorem mem_groundPrefix_perm {p : Equiv.Perm Point} {n : ℕ}
    (hp : FixesOutside p n) (x : Point) : p x ∈ groundPrefix n ↔ x ∈ groundPrefix n := by
  simp only [mem_groundPrefix]
  constructor
  · intro hx
    by_contra h
    have h' : n ≤ x.val := by omega
    rw [hp x h'] at hx
    omega
  · intro hx
    by_contra h
    have h' : n ≤ (p x).val := by omega
    have heq := hp (p x) h'
    have hxx : p x = x := p.injective heq
    rw [hxx] at h'
    omega

theorem groundPrefix_image {p : Equiv.Perm Point} {n : ℕ}
    (hp : FixesOutside p n) : (groundPrefix n).image p = groundPrefix n := by
  ext x
  constructor
  · rintro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact (mem_groundPrefix_perm hp y).mpr hy
  · intro hx
    refine mem_image.mpr ⟨p.symm x,?_,p.apply_symm_apply x⟩
    exact (mem_groundPrefix_perm (fixesOutside_symm hp) x).mpr hx

def relabelFamily (p : Equiv.Perm Point) (B : Finset (Finset Point)) :=
  B.image fun A => A.image p

@[simp] theorem relabelFamily_refl (B : Finset (Finset Point)) :
    relabelFamily (Equiv.refl Point) B = B := by
  simp [relabelFamily]

theorem relabelFamily_trans (p q : Equiv.Perm Point) (B : Finset (Finset Point)) :
    relabelFamily q (relabelFamily p B) = relabelFamily (p.trans q) B := by
  simp only [relabelFamily,image_image,Function.comp_def,Equiv.trans_apply]
  rfl

def IsomorphicWithin (n : ℕ) (A B : Finset (Finset Point)) : Prop :=
  ∃ p : Equiv.Perm Point, FixesOutside p n ∧ relabelFamily p A = B

theorem isomorphicWithin_refl (n : ℕ) (A : Finset (Finset Point)) :
    IsomorphicWithin n A A :=
  ⟨Equiv.refl Point,fixesOutside_refl n,relabelFamily_refl A⟩

theorem isomorphicWithin_trans {n : ℕ} {A B C : Finset (Finset Point)}
    (hAB : IsomorphicWithin n A B) (hBC : IsomorphicWithin n B C) :
    IsomorphicWithin n A C := by
  obtain ⟨p,hp,hpAB⟩ := hAB
  obtain ⟨q,hq,hqBC⟩ := hBC
  refine ⟨p.trans q,fixesOutside_trans hp hq,?_⟩
  rw [← relabelFamily_trans,hpAB,hqBC]

def castGround {g h : Finset Point} {r : ℕ}
    (M : BasisFamily g r) (heq : g = h) : BasisFamily h r := heq ▸ M

@[simp] theorem castGround_bases {g h : Finset Point} {r : ℕ}
    (M : BasisFamily g r) (heq : g = h) : (castGround M heq).bases = M.bases := by
  cases heq
  rfl

def relabelWithin {n r : ℕ} (M : BasisFamily (groundPrefix n) r)
    (p : Equiv.Perm Point) (hp : FixesOutside p n) : BasisFamily (groundPrefix n) r :=
  castGround (relabel M p) (groundPrefix_image hp)

@[simp] theorem relabelWithin_bases {n r : ℕ} (M : BasisFamily (groundPrefix n) r)
    (p : Equiv.Perm Point) (hp : FixesOutside p n) :
    (relabelWithin M p hp).bases = relabelFamily p M.bases := by
  simp [relabelWithin,relabelFamily,relabel]

end Papers.RationalityTen.BasisReconstruction
