/-
  # Lean/Mathlib tutorial — AI, Proof and Formalization Days
  ENS de Lyon, June 17, 2026

  SOLUTIONS
  (This file mirrors `Exercices.lean`: one solution per `sorry` exercise,
   in the same order and the same sections.)
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.FLT.Three

noncomputable section

variable (P Q R : Prop)

/- ## Implication -/

example : P → Q → P := by
  intro hP _
  exact hP

-- Modus ponens
example : P → (P → Q) → Q := by
  intro hP h
  exact h hP

example : (P → Q) → (Q → R) → P → R := by
  intro h1 h2 hP
  exact h2 (h1 hP)

/- ## Negation, True, False -/

example : P → ¬¬P := by
  intro hP h
  exact h hP

example : (P → Q) → ¬Q → ¬P := by
  intro h hnQ hP
  exact hnQ (h hP)

-- The converse of the contrapositive (classical: use `by_contra`)
example : (¬Q → ¬P) → P → Q := by
  intro h hP
  by_contra hQ
  exact h hQ hP

/- ## Conjunction and disjunction -/

example : (P → Q → R) → P ∧ Q → R := by
  intro h ⟨hP, hQ⟩
  exact h hP hQ

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
    exact ⟨fun hP ↦ h (Or.inl hP), fun hQ ↦ h (Or.inr hQ)⟩
  · intro ⟨hnP, hnQ⟩ hPQ
    rcases hPQ with hP | hQ
    · exact hnP hP
    · exact hnQ hQ

-- The other De Morgan law (the → direction requires excluded middle: try `by_cases`)
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · right; intro hQ; exact h ⟨hP, hQ⟩
    · left; exact hP
  · rintro (hnP | hnQ) ⟨hP, hQ⟩
    · exact hnP hP
    · exact hnQ hQ

/- ## Equivalence -/

-- Transitivity of ↔
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  exact Iff.trans h1 h2

example : ¬(P ↔ ¬P) := by
  intro h
  have hnP : ¬P := fun hP ↦ Iff.mp h hP hP
  exact hnP (Iff.mpr h hnP)

/- # Quantifiers -/

variable (α : Type*) (f g : α → Prop)

example : (∀ x, f x ∧ g x) → ∀ x, f x := by
  intro h x
  exact And.left (h x)

example : (∀ x, f x ∧ g x) ↔ (∀ x, f x) ∧ (∀ x, g x) := by
  constructor
  · intro h; exact ⟨fun x ↦ And.left (h x), fun x ↦ And.right (h x)⟩
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

/- # Sets and functions -/

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
    have : x = x' := hf (Eq.symm hxx')
    subst this
    exact ⟨x, ⟨hxs, hxt⟩, rfl⟩

/- # Algebraic structures -/

/- ## Groups -/

-- Trivial kernel if injective
example {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (a : G) (h : f a = 1) : a = 1 := by
  apply hf
  rw [h, map_one f]

-- (ab)^n = a^n * b^n in a commutative monoid
example {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (a * b), ih, pow_succ a, pow_succ b]
    exact mul_mul_mul_comm (a ^ n) (b ^ n) a b

-- Exponent-2 group ⟹ commutative
example {G : Type*} [Group G] (h : ∀ a : G, a ^ 2 = 1) (a b : G) : a * b = b * a := by
  have hself : ∀ x : G, x⁻¹ = x := by
    intro x
    have hx : x * x = 1 := by have := h x; rwa [pow_two] at this
    exact Eq.symm (eq_inv_of_mul_eq_one_left hx)
  calc a * b = (a * b)⁻¹ := Eq.symm (hself (a * b))
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hself a, hself b]

-- The preimage of a subgroup preserves inclusion
example {G H : Type*} [Group G] [Group H] (φ : G →* H) (S T : Subgroup H)
    (hST : S ≤ T) : S.comap φ ≤ T.comap φ := by
  intro x hx
  rw [Subgroup.mem_comap] at hx ⊢
  exact hST hx

/- ## Rings and fields -/

-- Factorization of a³ - b³
example {R : Type*} [CommRing R] (a b : R) :
    a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring

-- (a⁻¹)⁻¹ = a for a ≠ 0
example {K : Type*} [Field K] (a : K) (ha : a ≠ 0) : (a⁻¹)⁻¹ = a := by
  apply mul_left_cancel₀ (inv_ne_zero ha)
  rw [mul_inv_cancel₀ (inv_ne_zero ha), inv_mul_cancel₀ ha]

-- Cancellation in a field
example {K : Type*} [Field K] (a b c : K) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have key : a⁻¹ * (a * b) = a⁻¹ * (a * c) := congr_arg (a⁻¹ * ·) h
  rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ ha, one_mul, one_mul] at key

-- The units of ℤ are exactly ±1 (a bit harder)
example (x : ℤˣ) : (x : ℤ) = 1 ∨ (x : ℤ) = -1 := by
  -- ↑x divides 1 (witness ↑x⁻¹), so ↑x is a unit of ℤ, hence ↑x = ±1
  have hdvd : (↑x : ℤ) ∣ 1 := ⟨↑x⁻¹, Eq.symm (Units.mul_inv x)⟩
  exact Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)

/- # Analysis and topology -/

/- ## Continuity -/

example : Continuous (fun x : ℝ ↦ Real.cos x + x ^ 2) := by fun_prop

example {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ f x * g x) :=
  Continuous.mul hf hg

/- ## Derivatives -/

-- A sum of differentiable functions is differentiable (`fun_prop` also works)
example : Differentiable ℝ (fun x : ℝ ↦ x ^ 3 + x) :=
  Differentiable.add (differentiable_pow 3) differentiable_id

example : deriv (fun x : ℝ ↦ x ^ 2) = fun x ↦ 2 * x := by
  ext x; simp [mul_comm]

/- ## Topology -/

example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  IsClosed.preimage hf hs

example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : IsCompact s) :
    IsCompact (f '' s) :=
  IsCompact.image hs hf

-- Bolzano: a continuous function that changes sign on [0, 1] has a zero there
example (f : ℝ → ℝ) (hf : Continuous f) (h0 : f 0 < 0) (h1 : 0 < f 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = 0 := by
  -- the IVT: the interval [f 0, f 1] is contained in the image of [0, 1]
  have hsub := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) (Continuous.continuousOn hf)
  -- 0 lies in [f 0, f 1] since f 0 < 0 < f 1
  have h0mem : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := Set.mem_Icc.mpr ⟨le_of_lt h0, le_of_lt h1⟩
  -- so 0 is in the image: extract a preimage point
  obtain ⟨x, hx, hfx⟩ := hsub h0mem
  exact ⟨x, hx, hfx⟩

/- # Searching Mathlib -/

example (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c :=
  dvd_trans h1 h2

example (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b :=
  Nat.gcd_mul_lcm a b

example : Irrational Real.pi :=
  irrational_pi

example : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree

/- # Two more ambitious proofs -/

/- ## Construction of ℤ from ℕ × ℕ -/

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

/- ## Schröder-Bernstein theorem -/

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
    · symm; apply this (Eq.symm hxeq) (Or.symm xA) (Or.resolve_left xA x₁A)
    have x₂A : x₂ ∈ A := by
      apply Iff.mp _root_.not_imp_self
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by rw [hxeq, sb_right_inv f g x₂nA]
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]; use n + 1
      simp [sbAux]; exact ⟨x₁, hn, Eq.symm x₂eq⟩
    rw [if_pos x₁A, if_pos x₂A] at hxeq; exact hf hxeq
  push Not at xA
  rw [if_neg (And.left xA), if_neg (And.right xA)] at hxeq
  rw [← sb_right_inv f g (And.left xA), hxeq, sb_right_inv f g (And.right xA)]

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
