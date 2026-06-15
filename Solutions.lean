/-
  # TD Lean/Mathlib — AI, Proof and Formalization Days
  ENS de Lyon, 17 juin 2026

  SOLUTIONS
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Module.PID
import Mathlib.NumberTheory.FLT.Three

noncomputable section

variable (P Q R : Prop)

-- have : résultat intermédiaire
example (h1 : P → Q) (h2 : Q → R) (hP : P) : R := by
  have hQ : Q := h1 hP
  exact h2 hQ

-- P → Q → P
example : P → Q → P := by
  intro hP _
  exact hP

-- Modus Ponens
example : P → (P → Q) → Q := by
  intro hP h
  exact h hP

-- Transitivité de →
example : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 hP
  exact h2 (h1 hP)

-- P → ¬¬P
example : P → ¬¬P := by
  intro hP h
  exact h hP

-- Contraposée
example : (P → Q) → ¬Q → ¬P := by
  intro h hnQ hP
  exact hnQ (h hP)

-- ∨ symétrique
example : P ∨ Q ↔ Q ∨ P := by
  constructor
  · rintro (hP | hQ)
    · right; exact hP
    · left; exact hQ
  · rintro (hQ | hP)
    · right; exact hQ
    · left; exact hP

-- De Morgan
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    exact ⟨fun hP => h (Or.inl hP), fun hQ => h (Or.inr hQ)⟩
  · intro ⟨hnP, hnQ⟩ hPQ
    rcases hPQ with hP | hQ
    · exact hnP hP
    · exact hnQ hQ

-- Quantificateurs
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

-- Négation des quantificateurs
example (h : ¬ ∀ x, f x) : ∃ x, ¬ f x := by
  by_contra h'
  push Not at h'
  exact h h'

-- Ensembles et fonctions
variable {β : Type*}

-- s ∩ t = t ∩ s
example (s t : Set α) : s ∩ t = t ∩ s := by
  ext x
  constructor
  · rintro ⟨hs, ht⟩; exact ⟨ht, hs⟩
  · rintro ⟨ht, hs⟩; exact ⟨hs, ht⟩

-- Image d'une union
example (f : α → β) (s t : Set α) :
    f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩

-- Préimage et complémentaire
example (f : α → β) (t : Set β) : f ⁻¹' tᶜ = (f ⁻¹' t)ᶜ := by
  ext x
  simp [Set.mem_preimage, Set.mem_compl_iff]

-- Image de l'intersection = intersection des images (f injective)
example {f : α → β} (hf : Function.Injective f) (s t : Set α) :
    f '' (s ∩ t) = f '' s ∩ f '' t := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxs, hxt⟩, rfl⟩
    exact ⟨⟨x, hxs, rfl⟩, ⟨x, hxt, rfl⟩⟩
  · rintro ⟨⟨x, hxs, rfl⟩, ⟨x', hxt, hxx'⟩⟩
    have : x = x' := hf hxx'.symm
    subst this
    exact ⟨x, ⟨hxs, hxt⟩, rfl⟩

-- Arithmétique

-- 4 ∣ ab si 2 ∣ a et 2 ∣ b
example (a b : ℤ) (ha : 2 ∣ a) (hb : 2 ∣ b) : 4 ∣ a * b := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨l, hl⟩ := hb
  exact ⟨k * l, by rw [hk, hl]; ring⟩

-- a ∣ 3b² - 5c si a ∣ b et a ∣ c
example (a b c : ℤ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ 3 * b ^ 2 - 5 * c := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  exact ⟨3 * a * k ^ 2 - 5 * l, by rw [hk, hl]; ring⟩

-- gcd divise la somme
example (a b : ℕ) : Nat.gcd a b ∣ a + b :=
  Nat.dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)

-- Bézout
example (a b : ℤ) : ∃ u v : ℤ, u * a + v * b = Int.gcd a b :=
  ⟨Int.gcdA a b, Int.gcdB a b, by linear_combination -(Int.gcd_eq_gcd_ab a b)⟩

-- Nombres premiers

-- p premier, p ∣ aⁿ ⟹ p ∣ a
example (p a n : ℕ) (hp : Nat.Prime p) (h : p ∣ a ^ n) : p ∣ a :=
  hp.dvd_of_dvd_pow h

-- p premier, p ∣ abc ⟹ p ∣ a ∨ p ∣ b ∨ p ∣ c
example (p a b c : ℕ) (hp : Nat.Prime p) (h : p ∣ a * b * c) :
    p ∣ a ∨ p ∣ b ∨ p ∣ c := by
  rcases hp.dvd_mul.mp h with hab | hc
  · rcases hp.dvd_mul.mp hab with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hc)

-- Groupes

-- Noyau trivial si injectif
example {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (a : G) (h : f a = 1) : a = 1 := by
  apply hf
  rw [h, f.map_one]

-- (ab)^n = a^n * b^n dans un monoïde commutatif (par récurrence)
example {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (a * b), ih, pow_succ a, pow_succ b]
    exact mul_mul_mul_comm (a ^ n) (b ^ n) a b

-- Conjugaison
example {G H : Type*} [Group G] [Group H] (f : G →* H) (a g : G) :
    f (g * a * g⁻¹) = f g * f a * (f g)⁻¹ := by
  rw [f.map_mul, f.map_mul, f.map_inv]

-- Anneaux

-- f(a² + b²) = f(a)² + f(b)²
example {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) :
    f (a ^ 2 + b ^ 2) = f a ^ 2 + f b ^ 2 := by
  simp [map_add, map_pow]

-- f préserve les unités
example {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : R) (h : IsUnit a) :
    IsUnit (f a) :=
  h.map f

-- Dans ℤ/5ℤ : 2 * 3 = 1
example : (2 : ZMod 5) * 3 = 1 := by decide

-- Calculer 2 ^ 100 mod 7
example : (2 : ZMod 7) ^ 100 = 2 := by native_decide

-- Corps

-- (a⁻¹)⁻¹ = a pour a ≠ 0
example {K : Type*} [Field K] (a : K) (_ha : a ≠ 0) : (a⁻¹)⁻¹ = a :=
  inv_inv a

-- Dans ℤ/7ℤ : 3⁻¹ = 5
example : (3 : ZMod 7)⁻¹ = 5 := by decide

-- Simplification dans un corps
example {K : Type*} [Field K] (a b c : K) (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  mul_left_cancel₀ ha h

-- Modules

-- (-1) • v = -v
example {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) : (-1 : ℝ) • v = -v :=
  neg_one_smul ℝ v

-- Stabilité par addition d'un sous-module
example {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V)
    (u v : V) (hu : u ∈ S) (hv : v ∈ S) : u + v ∈ S :=
  S.add_mem hu hv

-- Stabilité par action scalaire d'un sous-module
example {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V)
    (r : ℝ) (v : V) (hv : v ∈ S) : r • v ∈ S :=
  S.smul_mem r hv

-- Analyse et topologie

-- Continuité

-- cos x + x ^ 2 est continue
example : Continuous (fun x : ℝ => Real.cos x + x ^ 2) := by fun_prop

-- f * g continue si f et g continues
example {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x) :=
  hf.mul hg

-- Dérivées

-- x ^ 3 est dérivable
example : Differentiable ℝ (fun x : ℝ => x ^ 3) := by fun_prop

-- deriv (x ^ 2) = 2 * x
example : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
  ext x; simp [mul_comm]

-- Topologie

-- Préimage d'un fermé est fermée
example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  hs.preimage hf

-- Image d'un compact est compacte
example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : IsCompact s) :
    IsCompact (f '' s) :=
  hs.image hf

-- Chercher dans Mathlib

-- Si a ∣ b et b ∣ c, alors a ∣ c
example (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c :=
  h1.trans h2

-- pgcd(a, b) * ppcm(a, b) = a * b
example (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b :=
  Nat.gcd_mul_lcm a b

-- π est irrationnel
example : Irrational Real.pi :=
  irrational_pi

-- La somme de deux nombres pairs est paire
example (m n : ℤ) (hm : 2 ∣ m) (hn : 2 ∣ n) : 2 ∣ m + n :=
  hm.add hn

-- Le dernier théorème de Fermat pour n = 3
example : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree

-- Deux preuves plus ambitieuses

-- Construction de ℤ

def rZ : ℕ × ℕ → ℕ × ℕ → Prop := fun (a, b) (c, d) ↦ a + d = c + b

theorem rZ_reflexive : ∀ x : ℕ × ℕ, rZ x x := fun _ ↦ rfl

theorem rZ_symmetric : ∀ {x y : ℕ × ℕ}, rZ x y → rZ y x := fun h ↦ h.symm

theorem rZ_transitive : ∀ {x y z : ℕ × ℕ}, rZ x y → rZ y z → rZ x z := by
  intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ h1 h2
  unfold rZ at *; lia

instance rZSetoid : Setoid (ℕ × ℕ) where
  r := rZ
  iseqv := ⟨rZ_reflexive, rZ_symmetric, rZ_transitive⟩

@[simp] theorem rZ_equiv_def (a b c d : ℕ) : (a, b) ≈ (c, d) ↔ a + d = c + b := Iff.rfl

abbrev ZZ := Quotient rZSetoid

namespace ZZ

instance : Zero ZZ := ⟨⟦(0, 0)⟧⟩
instance : One  ZZ := ⟨⟦(1, 0)⟧⟩
instance : Neg  ZZ := ⟨Quotient.lift (fun x : ℕ × ℕ ↦ (⟦(x.2, x.1)⟧ : ZZ))
  (by intro ⟨a, b⟩ ⟨c, d⟩ h; apply Quotient.sound
      simp only [rZ_equiv_def] at h ⊢; lia)⟩

def add_aux (x y : ℕ × ℕ) : ZZ := ⟦(x.1 + y.1, x.2 + y.2)⟧

theorem add_aux_sound (x₁ y₁ x₂ y₂ : ℕ × ℕ) (h₁ : x₁ ≈ x₂) (h₂ : y₁ ≈ y₂) :
    add_aux x₁ y₁ = add_aux x₂ y₂ := by
  obtain ⟨a₁, b₁⟩ := x₁; obtain ⟨a₂, b₂⟩ := x₂
  obtain ⟨c₁, d₁⟩ := y₁; obtain ⟨c₂, d₂⟩ := y₂
  apply Quotient.sound
  simp only [rZ_equiv_def] at h₁ h₂ ⊢; lia

def add : ZZ → ZZ → ZZ := Quotient.lift₂ add_aux add_aux_sound
instance : Add ZZ := ⟨add⟩

@[simp] theorem add_def (a b c d : ℕ) :
    (⟦(a, b)⟧ + ⟦(c, d)⟧ : ZZ) = ⟦(a + c, b + d)⟧ := rfl

theorem add_comm' (x y : ZZ) : x + y = y + x := by
  refine Quotient.inductionOn₂ x y ?_
  rintro ⟨a, b⟩ ⟨c, d⟩
  simp
  apply Quotient.sound
  simp
  lia

end ZZ

-- Le résultat final : ZZ est isomorphe à ℤ en tant qu'anneaux
-- (preuve complète dans les notes de cours)
#check Int.cast  -- le morphisme canonique ℤ → R

-- Théorème de Schröder-Bernstein
-- Source : Mathematics in Lean, J. Avigad et al., chapitre 4, section 3.
-- https://leanprover-community.github.io/mathematics_in_lean/

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
