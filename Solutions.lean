/-
  # TD Lean/Mathlib — AI, Proof and Formalization Days
  ENS de Lyon, 17 juin 2026

  SOLUTIONS
  (Ce fichier est le miroir de `Exercices.lean` : une solution par exercice `sorry`,
   dans le même ordre et les mêmes sections.)
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.FLT.Three

noncomputable section

variable (P Q R S : Prop)

/- ## Implication -/

example : P → Q → P := by
  intro hP _
  exact hP

example : P → (P → Q) → Q := by
  intro hP h
  exact h hP

example : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 hP
  exact h2 (h1 hP)

example : (P → Q) → ((P → Q) → P) → Q := by
  intro h1 h2
  exact h1 (h2 h1)

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro h1 h2 h3
  exact h1 (fun q => h3 (h2 q))

/- ## Négation, True, False -/

example : P → ¬¬P := by
  intro hP h
  exact h hP

example : (P → Q) → ¬Q → ¬P := by
  intro h hnQ hP
  exact hnQ (h hP)

example : P → ¬P → False := by
  intro hP hnP
  exact hnP hP

example : (¬Q → ¬P) → P → Q := by
  intro h hP
  by_contra hQ
  exact h hQ hP

/- ## Conjonction et disjonction -/

example : P ∧ Q → Q := by
  intro h
  exact h.2

example : (P → Q → R) → P ∧ Q → R := by
  intro h ⟨hP, hQ⟩
  exact h hP hQ

example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro ⟨hP, _⟩ ⟨_, hR⟩
  exact ⟨hP, hR⟩

example : P ∨ Q ↔ Q ∨ P := by
  constructor
  · rintro (hP | hQ)
    · right; exact hP
    · left; exact hQ
  · rintro (hQ | hP)
    · right; exact hQ
    · left; exact hP

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    exact ⟨fun hP => h (Or.inl hP), fun hQ => h (Or.inr hQ)⟩
  · intro ⟨hnP, hnQ⟩ hPQ
    rcases hPQ with hP | hQ
    · exact hnP hP
    · exact hnQ hQ

-- De Morgan (sens ← via le tiers exclu, avec `by_cases`)
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · right; intro hQ; exact h ⟨hP, hQ⟩
    · left; exact hP
  · rintro (hnP | hnQ) ⟨hP, hQ⟩
    · exact hnP hP
    · exact hnQ hQ

/- ## Équivalence -/

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  exact h1.trans h2

example : P ↔ P ∧ True := by
  constructor
  · intro hP; exact ⟨hP, trivial⟩
  · intro ⟨hP, _⟩; exact hP

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hpq hrs
  rw [hpq, hrs]

example : ¬(P ↔ ¬P) := by
  intro h
  have hnP : ¬P := fun hP => h.mp hP hP
  exact hnP (h.mpr hnP)

/- # Quantificateurs -/

variable (α : Type*) (f g : α → Prop)

example : (∀ x, f x ∧ g x) → ∀ x, f x := by
  intro h x
  exact (h x).1

example : (∀ x, f x ∧ g x) ↔ (∀ x, f x) ∧ (∀ x, g x) := by
  constructor
  · intro h; exact ⟨fun x => (h x).1, fun x => (h x).2⟩
  · intro ⟨h1, h2⟩ x; exact ⟨h1 x, h2 x⟩

example : (∃ x, f x ∨ g x) ↔ (∃ x, f x) ∨ (∃ x, g x) := by
  constructor
  · rintro ⟨x, hx | hx⟩
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨x, Or.inl hx⟩
    · exact ⟨x, Or.inr hx⟩

example (h : ¬ ∀ x, f x) : ∃ x, ¬ f x := by
  by_contra h'
  push Not at h'
  exact h h'

example : (∀ x, f x) ↔ ¬ (∃ x, ¬ f x) := by
  constructor
  · rintro h ⟨x, hx⟩; exact hx (h x)
  · intro h x; by_contra hx; exact h ⟨x, hx⟩

example : (∃ x, f x) ↔ ¬ (∀ x, ¬ f x) := by
  constructor
  · rintro ⟨x, hx⟩ h; exact h x hx
  · intro h; by_contra h'; push Not at h'; exact h h'

/- # Ensembles et fonctions -/

example (s t : Set α) : s ⊆ s ∪ t := by
  intro x hx
  exact Or.inl hx

example (s t : Set α) : s ∩ t = t ∩ s := by
  ext x
  constructor
  · rintro ⟨hs, ht⟩; exact ⟨ht, hs⟩
  · rintro ⟨ht, hs⟩; exact ⟨hs, ht⟩

example (s t u : Set α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  ext x
  constructor
  · rintro ⟨hs, ht | hu⟩
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨hs, hu⟩
  · rintro (⟨hs, ht⟩ | ⟨hs, hu⟩)
    · exact ⟨hs, Or.inl ht⟩
    · exact ⟨hs, Or.inr hu⟩

example {β : Type*} (f : α → β) (s t : Set α) :
    f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩

example {β : Type*} (f : α → β) (s t : Set β) :
    f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := by
  ext x; simp

example {β : Type*} (f : α → β) (t : Set β) : f ⁻¹' tᶜ = (f ⁻¹' t)ᶜ := by
  ext x
  simp [Set.mem_preimage, Set.mem_compl_iff]

example {β : Type*} {f : α → β} (hf : Function.Injective f) (s t : Set α) :
    f '' (s ∩ t) = f '' s ∩ f '' t := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxs, hxt⟩, rfl⟩
    exact ⟨⟨x, hxs, rfl⟩, ⟨x, hxt, rfl⟩⟩
  · rintro ⟨⟨x, hxs, rfl⟩, ⟨x', hxt, hxx'⟩⟩
    have : x = x' := hf hxx'.symm
    subst this
    exact ⟨x, ⟨hxs, hxt⟩, rfl⟩

/- # Structures algébriques -/

/- ## Groupes -/

-- Noyau trivial si injectif
example {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (a : G) (h : f a = 1) : a = 1 := by
  apply hf
  rw [h, f.map_one]

-- (ab)^n = a^n * b^n dans un monoïde commutatif
example {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (a * b), ih, pow_succ a, pow_succ b]
    exact mul_mul_mul_comm (a ^ n) (b ^ n) a b

-- Groupe d'exposant 2 ⟹ commutatif
example {G : Type*} [Group G] (h : ∀ a : G, a ^ 2 = 1) (a b : G) : a * b = b * a := by
  have hself : ∀ x : G, x⁻¹ = x := by
    intro x
    have hx : x * x = 1 := by have := h x; rwa [pow_two] at this
    exact (eq_inv_of_mul_eq_one_left hx).symm
  calc a * b = (a * b)⁻¹ := (hself (a * b)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hself a, hself b]

-- La préimage d'un sous-groupe préserve l'inclusion
example {G H : Type*} [Group G] [Group H] (φ : G →* H) (S T : Subgroup H)
    (hST : S ≤ T) : S.comap φ ≤ T.comap φ := by
  intro x hx
  rw [Subgroup.mem_comap] at hx ⊢
  exact hST hx

-- Sous-groupe conjugué xHx⁻¹
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := ⟨1, H.one_mem, by group⟩
  inv_mem' := by
    rintro a ⟨h, hh, rfl⟩
    exact ⟨h⁻¹, H.inv_mem hh, by group⟩
  mul_mem' := by
    rintro a b ⟨h₁, hh₁, rfl⟩ ⟨h₂, hh₂, rfl⟩
    exact ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, by group⟩

/- ## Anneaux et corps -/

-- Factorisation de a³ - b³
example {R : Type*} [CommRing R] (a b : R) :
    a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring

-- Les unités de ℤ sont exactement ±1
example (x : ℤˣ) : x = 1 ∨ x = -1 := by
  have hdvd : (↑x : ℤ) ∣ 1 := ⟨↑x⁻¹, by exact_mod_cast (Units.mul_inv x).symm⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

-- f préserve les unités
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a : R) (h : IsUnit a) :
    IsUnit (f a) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨Units.map f.toMonoidHom u, rfl⟩

-- (a⁻¹)⁻¹ = a pour a ≠ 0
example {K : Type*} [Field K] (a : K) (ha : a ≠ 0) : (a⁻¹)⁻¹ = a := by
  apply mul_left_cancel₀ (inv_ne_zero ha)
  rw [mul_inv_cancel₀ (inv_ne_zero ha), inv_mul_cancel₀ ha]

-- Dans ℤ/7ℤ : 3⁻¹ = 5
example : (3 : ZMod 7)⁻¹ = 5 := by decide

-- Simplification dans un corps
example {K : Type*} [Field K] (a b c : K) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have key : a⁻¹ * (a * b) = a⁻¹ * (a * c) := congr_arg (a⁻¹ * ·) h
  rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ha, one_mul, one_mul] at key

/- # Analyse et topologie -/

/- ## Continuité -/

example : Continuous (fun x : ℝ => Real.cos x + x ^ 2) := by fun_prop

example {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x) :=
  hf.mul hg

/- ## Dérivées -/

example : Differentiable ℝ (fun x : ℝ => x ^ 3) := by fun_prop

example : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
  ext x; simp [mul_comm]

/- ## Topologie -/

example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  hs.preimage hf

example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : IsCompact s) :
    IsCompact (f '' s) :=
  hs.image hf

/- # Chercher dans Mathlib -/

example (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c :=
  h1.trans h2

example (m n : ℤ) (hm : 2 ∣ m) (hn : 2 ∣ n) : 2 ∣ m + n :=
  dvd_add hm hn

example (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b :=
  Nat.gcd_mul_lcm a b

example : Irrational Real.pi :=
  irrational_pi

example : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree

/- # Deux preuves plus ambitieuses -/

/- ## Construction de ℤ à partir de ℕ × ℕ -/

def rZ : ℕ × ℕ → ℕ × ℕ → Prop := fun (a, b) (c, d) ↦ a + d = c + b

theorem rZ_iff (a b c d : ℕ) : rZ (a, b) (c, d) ↔ a + d = c + b := Iff.rfl
theorem rZ_iff' (x y : ℕ × ℕ) : rZ x y ↔ x.1 + y.2 = y.1 + x.2 := Iff.rfl

theorem rZ_reflexive : ∀ x : ℕ × ℕ, rZ x x := by
  rintro ⟨a, b⟩
  simp [rZ_iff]

theorem rZ_symmetric : ∀ {x y : ℕ × ℕ}, rZ x y → rZ y x := by
  intro x y h
  simp only [rZ_iff'] at *
  lia

theorem rZ_transitive : ∀ {x y z : ℕ × ℕ}, rZ x y → rZ y z → rZ x z := by
  intro x y z h1 h2
  simp only [rZ_iff'] at *
  lia

instance rZSetoid : Setoid (ℕ × ℕ) where
  r := rZ
  iseqv := ⟨rZ_reflexive, rZ_symmetric, rZ_transitive⟩

@[simp] theorem rZ_equiv_def (a b c d : ℕ) : (a, b) ≈ (c, d) ↔ a + d = c + b := Iff.rfl

abbrev ZZ := Quotient rZSetoid

namespace ZZ

instance : Zero ZZ := ⟨⟦(0, 0)⟧⟩
instance : One  ZZ := ⟨⟦(1, 0)⟧⟩

def neg : ZZ → ZZ :=
  Quotient.lift (fun x : ℕ × ℕ ↦ (⟦(x.2, x.1)⟧ : ZZ)) (by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    apply Quotient.sound
    simp only [rZ_equiv_def] at h ⊢; lia)

instance : Neg ZZ := ⟨neg⟩

@[simp] theorem neg_def (a b : ℕ) : -(⟦(a, b)⟧ : ZZ) = ⟦(b, a)⟧ := rfl

def add_aux (x y : ℕ × ℕ) : ZZ := ⟦(x.1 + y.1, x.2 + y.2)⟧

theorem add_aux_sound (x₁ y₁ x₂ y₂ : ℕ × ℕ) (h₁ : x₁ ≈ x₂) (h₂ : y₁ ≈ y₂) :
    add_aux x₁ y₁ = add_aux x₂ y₂ := by
  obtain ⟨a, b⟩ := x₁; obtain ⟨c, d⟩ := y₁
  obtain ⟨e, f⟩ := x₂; obtain ⟨g, h⟩ := y₂
  simp only [add_aux, rZ_equiv_def] at *
  apply Quotient.sound
  simp only [rZ_equiv_def]; lia

def add : ZZ → ZZ → ZZ := Quotient.lift₂ add_aux add_aux_sound

instance : Add ZZ := ⟨add⟩

@[simp] theorem add_def (a b c d : ℕ) :
    (⟦(a, b)⟧ + ⟦(c, d)⟧ : ZZ) = ⟦(a + c, b + d)⟧ := rfl

theorem add_comm' (x y : ZZ) : x + y = y + x := by
  refine Quotient.inductionOn₂ x y ?_
  rintro ⟨a, b⟩ ⟨c, d⟩
  simp only [add_def]
  apply Quotient.sound
  simp only [rZ_equiv_def]; lia

end ZZ

#check Int.cast

/- ## Théorème de Schröder-Bernstein -/

section SchroederBernstein

open Set Function Classical

variable {α β : Type*} [Nonempty β] (f : α → β) (g : β → α)

private def sbAux : ℕ → Set α
  | 0     => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

private def sbSet := ⋃ n, sbAux f g n

private def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

private theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have h1 : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]; use 0
    rw [sbAux, mem_diff]; exact ⟨mem_univ _, hx⟩
  have h2 : ∃ y, g y = x := by simp at h1; exact h1
  exact invFun_eq h2

private theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂ (hxeq : h x₁ = h x₂)
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm; apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply _root_.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by rw [hxeq, sb_right_inv f g x₂nA]
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]; use n + 1
      simp [sbAux]; exact ⟨x₁, hn, x₂eq.symm⟩
    rw [if_pos x₁A, if_pos x₂A] at hxeq; exact hf hxeq
  push Not at xA
  rw [if_neg xA.1, if_neg xA.2] at hxeq
  rw [← sb_right_inv f g xA.1, hxeq, sb_right_inv f g xA.2]

private theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by rw [A_def, sbSet, mem_iUnion]; exact ⟨n, xmem⟩
    rw [h_def, sbFun, if_pos this]; exact hg hx
  use g y
  rw [h_def, sbFun, if_neg gyA]
  apply leftInverse_invFun hg

theorem schroeder_bernstein {f : α → β} {g : β → α}
    (hf : Injective f) (hg : Injective g) : ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩

end SchroederBernstein

end
