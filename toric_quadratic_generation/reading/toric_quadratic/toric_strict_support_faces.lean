module
public import PaperVerification.ToricFiniteSupportPerturbation
public import PaperVerification.ToricFiniteConeFamily
public import Mathlib.Tactic.NormNum
@[expose] public section

/-!
# Strict supporting functions on coordinate faces

Strict support on a cone can be refined to strict support on any of its
coordinate faces. The proof perturbs by the sum of the omitted dual
coordinates and preserves every other strict inequality by an explicit
finite perturbation lemma.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Sum of the real dual coordinates selected by a finite set of integral
basis rays. -/
def raySelectorFunctional {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (s : Finset (Lattice n)) : Ambient n →ₗ[ℝ] ℝ :=
  ∑ i ∈ basisRayIndices b s, (integralBasisReal b).coord i

theorem raySelectorFunctional_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (s : Finset (Lattice n)) (j : Fin n) :
    raySelectorFunctional b s (embed n (b j)) = if b j ∈ s then 1 else 0 := by
  rw [← integralBasisReal_apply b j]
  simp [raySelectorFunctional, basisRayIndices, Module.Basis.coord_apply,
    Module.Basis.repr_self_apply, Finsupp.single_apply]

/-- Strict support on a smooth cone extends to every actual ray-subset
face, with the same prescribed coefficients on the whole finite ray set. -/
theorem exists_strict_support_subset {n : ℕ}
    (R s t : Finset (Lattice n)) (a : Lattice n → ℝ)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hs : s ⊆ Finset.univ.image b)
    (hts : t ⊆ s) (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (heq : ∀ v ∈ s, ℓ (embed n v) = a v)
    (hlt : ∀ v ∈ R, v ∉ s → ℓ (embed n v) < a v) :
    ∃ k : Ambient n →ₗ[ℝ] ℝ,
      (∀ v ∈ t, k (embed n v) = a v) ∧
      (∀ v ∈ R, v ∉ t → k (embed n v) < a v) := by
  let g : Ambient n →ₗ[ℝ] ℝ := -raySelectorFunctional b (s \ t)
  have hg (v : Lattice n) (hv : v ∈ s) :
      g (embed n v) = if v ∈ t then 0 else -1 := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hs hv)
    simp only [g, LinearMap.neg_apply, raySelectorFunctional_basis]
    by_cases hit : b i ∈ t
    · simp [Finset.mem_sdiff, hv, hit]
    · simp [Finset.mem_sdiff, hv, hit]
  have hactive : ∀ u ∈ ({t} : Finset (Finset (Lattice n))), ∀ v ∈ u,
      ℓ (embed n v) = a v ∧ g (embed n v) = (0 : Lattice n → ℝ) v := by
    intro u hu v hv
    have hut := Finset.mem_singleton.mp hu
    subst u
    refine ⟨heq v (hts hv), ?_⟩
    simp only [hg v (hts hv), if_pos hv, Pi.zero_apply]
  have hinactive : ∀ u ∈ ({t} : Finset (Finset (Lattice n))), ∀ v ∈ R, v ∉ u →
      ℓ (embed n v) < a v ∨
      (ℓ (embed n v) = a v ∧ g (embed n v) < (0 : Lattice n → ℝ) v) := by
    intro u hu v hv hvu
    have hut := Finset.mem_singleton.mp hu
    subst u
    by_cases hvs : v ∈ s
    · right
      refine ⟨heq v hvs, ?_⟩
      simp only [hg v hvs, if_neg hvu, Pi.zero_apply]
      norm_num
    · exact Or.inl (hlt v hv hvs)
  obtain ⟨ε, hε, hsupport⟩ := finite_lexicographic_support_perturbation
    {t} R a 0 (fun _ => ℓ) (fun _ => g) hactive hinactive
  refine ⟨ℓ + ε • g, ?_⟩
  simpa only [Pi.zero_apply, mul_zero, add_zero] using
    hsupport t (Finset.mem_singleton_self t)

/-- Strict support supplied on a finite smooth cone family descends to the
entire fan obtained by taking all its coordinate faces. -/
theorem strictSupport_fanOfFiniteSmoothCones {n : ℕ}
    (C : Finset (Finset (Lattice n)))
    (hsmooth : ∀ s ∈ C, ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      s ⊆ Finset.univ.image b)
    (hinter : ∀ s ∈ C, ∀ t ∈ C,
      latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t))
    (hcover : ∀ x : Ambient n, ∃ s ∈ C, x ∈ latticeRayCone s)
    (R : Finset (Lattice n)) (hR : ∀ s ∈ C, s ⊆ R)
    (a : Lattice n → ℝ)
    (hsupport : ∀ s ∈ C, ∃ ℓ : Ambient n →ₗ[ℝ] ℝ,
      (∀ v ∈ s, ℓ (embed n v) = a v) ∧
      (∀ v ∈ R, v ∉ s → ℓ (embed n v) < a v)) :
    (fanOfFiniteSmoothCones C hsmooth hinter hcover).IsStrictSupport a := by
  let «Σ» := fanOfFiniteSmoothCones C hsmooth hinter hcover
  intro t ht
  obtain ⟨s, hs, hts⟩ := (mem_finiteConeFamilyClosure C t).mp ht
  obtain ⟨b, hb⟩ := hsmooth s hs
  obtain ⟨ℓ, heq, hlt⟩ := hsupport s hs
  obtain ⟨k, hkeq, hklt⟩ := exists_strict_support_subset R s t a b hb hts ℓ heq hlt
  refine ⟨k, hkeq, ?_⟩
  intro v hv hvt
  obtain ⟨u, hu, hvu⟩ := («Σ».mem_rays_iff v).mp hv
  obtain ⟨z, hz, huz⟩ := (mem_finiteConeFamilyClosure C u).mp hu
  exact hklt v (hR z hz (huz hvu)) hvt

end PaperVerification.ToricGeometry
