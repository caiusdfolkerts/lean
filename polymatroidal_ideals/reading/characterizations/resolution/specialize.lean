import Characterizations.Resolution.Basic

/-! Exact specialization of actual finite free matrices along a regular quotient. -/

noncomputable section
namespace Characterizations.Resolution
open Classical Finset
universe u v w z
variable {R S : Type u} [CommRing R] [CommRing S]
  {J : Type v} {L : Type w} {M : Type z}
  [Fintype J] [Fintype L] [Fintype M]

lemma free_apply_eq_sum (f : (J → R) →ₗ[R] (L → R)) (x : J → R) (a : L) :
    f x a = ∑ b, x b * f (Pi.single b 1) a := by
  have hx : x = ∑ b, x b • Pi.single b (1 : R) := by
    funext b
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp

def specialize (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R)) :
    (J → S) →ₗ[S] (L → S) where
  toFun x a := ∑ b, x b * φ (f (Pi.single b 1) a)
  map_add' x y := by ext a; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by ext a; simp [mul_assoc, Finset.mul_sum]

lemma specialize_apply (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R))
    (x : J → S) (a : L) : specialize φ f x a =
      ∑ b, x b * φ (f (Pi.single b 1) a) := rfl

@[simp] lemma specialize_single (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R))
    (b : J) (a : L) : specialize φ f (Pi.single b 1) a = φ (f (Pi.single b 1) a) := by
  simp [specialize, Pi.single_apply]

lemma specialize_map (φ : R →+* S) (f : (J → R) →ₗ[R] (L → R)) (x : J → R) :
    specialize φ f (fun j => φ (x j)) = fun a => φ (f x a) := by
  ext a
  rw [specialize_apply, free_apply_eq_sum]
  simp

lemma specialize_exact (φ : R →+* S) (hφ : Function.Surjective φ) (t : R)
    (ht : φ t = 0) (hker : ∀ a, φ a = 0 → ∃ b, a = t * b)
    (f : (J → R) →ₗ[R] (L → R)) (g : (L → R) →ₗ[R] (M → R))
    (hex : LinearMap.range f = LinearMap.ker g)
    (hsat : ∀ y : M → R, t • y ∈ LinearMap.range g → y ∈ LinearMap.range g) :
    LinearMap.range (specialize φ f) = LinearMap.ker (specialize φ g) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : J → R, (fun j => φ (y j)) = x := by
      choose y hy using fun j => hφ (x j)
      exact ⟨y, funext hy⟩
    rw [← hy, specialize_map, LinearMap.mem_ker, specialize_map]
    have hf : g (f y) = 0 := LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self f y)
    ext a
    simp [hf]
  · intro hz
    obtain ⟨x, hx⟩ : ∃ x : L → R, (fun j => φ (x j)) = z := by
      choose x hx using fun j => hφ (z j)
      exact ⟨x, funext hx⟩
    have hg : ∀ a, φ (g x a) = 0 := by
      have h := LinearMap.mem_ker.mp hz
      rw [← hx, specialize_map] at h
      exact congrFun h
    choose y hy using fun a => hker (g x a) (hg a)
    have hgy : g x = t • y := by ext a; exact hy a
    obtain ⟨w, hw⟩ := hsat y ⟨x, hgy⟩
    have hcycle : x - t • w ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hw, hgy, sub_self]
    obtain ⟨q, hq⟩ := hex.symm ▸ hcycle
    refine ⟨fun j => φ (q j), ?_⟩
    rw [specialize_map, hq]
    ext a
    simpa [ht] using congrFun hx a

lemma saturated_range_of_exact (f : (J → R) →ₗ[R] (L → R))
    (g : (L → R) →ₗ[R] (M → R))
    (hex : LinearMap.range f = LinearMap.ker g) (t : R)
    (ht : Function.Injective (fun a : R => t * a)) :
    ∀ y : L → R, t • y ∈ LinearMap.range f → y ∈ LinearMap.range f := by
  intro y hy
  rw [hex, LinearMap.mem_ker] at hy ⊢
  rw [map_smul] at hy
  ext a
  apply ht
  simpa using congrFun hy a

def scalarFree (f : (J → R) →ₗ[R] R) : (J → R) →ₗ[R] (Unit → R) :=
  LinearMap.pi (fun _ => f)

@[simp] lemma scalarFree_apply (f : (J → R) →ₗ[R] R) (x : J → R) (a : Unit) :
    scalarFree f x a = f x := rfl

@[simp] lemma scalarFree_ker (f : (J → R) →ₗ[R] R) :
    LinearMap.ker (scalarFree f) = LinearMap.ker f := by
  ext x
  simp only [LinearMap.mem_ker, funext_iff, scalarFree_apply, Pi.zero_apply, implies_true]
  exact ⟨fun h => h (), fun h _ => h⟩

def specializeScalar (φ : R →+* S) (f : (J → R) →ₗ[R] R) : (J → S) →ₗ[S] S :=
  (LinearMap.proj ()).comp (specialize φ (scalarFree f))

@[simp] lemma specializeScalar_single (φ : R →+* S) (f : (J → R) →ₗ[R] R) (b : J) :
    specializeScalar φ f (Pi.single b 1) = φ (f (Pi.single b 1)) := by
  exact specialize_single φ (scalarFree f) b ()

lemma specializeScalar_map (φ : R →+* S) (f : (J → R) →ₗ[R] R) (x : J → R) :
    specializeScalar φ f (fun j => φ (x j)) = φ (f x) :=
  congrFun (specialize_map φ (scalarFree f) x) ()

lemma specializeScalar_ker (φ : R →+* S) (f : (J → R) →ₗ[R] R) :
    LinearMap.ker (specialize φ (scalarFree f)) =
      LinearMap.ker (specializeScalar φ f) := by
  ext x
  simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply]
  exact ⟨fun h => h (), fun h a => by cases a; exact h⟩

lemma specializeScalar_range (φ : R →+* S) (hφ : Function.Surjective φ)
    (f : (J → R) →ₗ[R] R) (I : Ideal R) (hf : LinearMap.range f = I) :
    LinearMap.range (specializeScalar φ f) = Ideal.map φ I := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨z,hz⟩ : ∃ z : J → R, (fun j => φ (z j)) = x := by
      choose z hz using fun j => hφ (x j)
      exact ⟨z,funext hz⟩
    rw [← hz,specializeScalar_map]
    exact Ideal.mem_map_of_mem φ (hf ▸ LinearMap.mem_range_self f z)
  · intro hy
    obtain ⟨z,hz,hzy⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hy
    obtain ⟨x,hx⟩ := hf.symm ▸ hz
    refine ⟨fun j => φ (x j),?_⟩
    rw [specializeScalar_map,hx,hzy]

end Characterizations.Resolution
