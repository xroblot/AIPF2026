/-
  # TD Lean/Mathlib — AI, Proof and Formalization Days
  ENS de Lyon, 17 juin 2026

  References:
  * Formalising Mathematics 2024, K. Buzzard
  * Theorem Proving in Lean 4, J. Avigad et al.
  * Mathematics in Lean, J. Avigad & P. Massot
  * M2 Lyon 2024-25, S. Morel, F. Nuccio, X. Roblot
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

/-
  # Premiers pas

  Lean est un assistant de preuve : il vérifie que vos preuves sont correctes.
-/

-- Lean vérifie les types en temps réel
#check Nat.add_comm   -- ∀ (n m : ℕ), n + m = m + n

-- Lean peut aussi calculer
#eval 2 ^ 10          -- 1024

/-
  # Propositions et preuves

  Les propositions vivent dans le type `Prop`.
  La tactique `sorry` accepte n'importe quel but sans le prouver.
-/

variable (P Q R : Prop)

/-
  ## Implication

  Tactiques : `intro`, `exact`, `apply`
-/

example : P → P := by
  intro hP
  exact hP

example (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP

-- La tactique `have` introduit un résultat intermédiaire nommé
example (h1 : P → Q) (h2 : Q → R) (hP : P) : R := by
  have hQ : Q := h1 hP
  exact h2 hQ

/- TODO -/

example : P → Q → P := by
  sorry

example : P → (P → Q) → Q := by
  sorry

example : (P → Q) → (Q → R) → P → R := by
  sorry

/- END TODO -/

/-
  ## Négation, True, False

  `¬P` est *définie* comme `P → False`.
-/

-- En logique classique (la logique par défaut dans Lean), ¬¬P → P est prouvable
-- Tactique `by_contra` : suppose ¬P et cherche une contradiction
example : ¬¬P → P := by
  intro h
  by_contra hP
  apply h
  exact hP

/- TODO -/

example : P → ¬¬P := by
  sorry

example : (P → Q) → ¬Q → ¬P := by
  sorry

/- END TODO -/

/-
  ## Conjonction et disjonction

  Tactiques : `constructor`, `obtain`, `left`, `right`, `rcases`
-/

-- `obtain ⟨hP, hQ⟩ := h` déconstruit `h : P ∧ Q` en deux hypothèses
-- `exact ⟨hQ, hP⟩` construit une preuve de `Q ∧ P`
example : P ∧ Q → Q ∧ P := by
  intro h
  obtain ⟨hP, hQ⟩ := h
  exact ⟨hQ, hP⟩

example : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hP | hQ
  · right; exact hP
  · left; exact hQ

-- `constructor` décompose un but `A ↔ B` en deux implications `A → B` et `B → A`
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨hP, hQ⟩; exact ⟨hQ, hP⟩
  · intro ⟨hQ, hP⟩; exact ⟨hP, hQ⟩

/- TODO -/

example : P ∨ Q ↔ Q ∨ P := by
  sorry

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry

/- END TODO -/

/-
  # Quantificateurs

  `∀ x : α, P x` : "pour tout x, P x"   — tactique `intro`
  `∃ x : α, P x` : "il existe x tel que P x"  — tactique `use`

  Utiliser `\forall` et `\exists` pour écrire `∀` et `∃`.
-/

variable (α : Type*) (f g : α → Prop)

example (h : ∀ x : α, f x) (a : α) : f a := by
  apply h

example (a : α) (h : f a) : ∃ x, f x := by
  use a

example (h : ∀ x, f x → g x) (h' : ∃ x, f x) : ∃ x, g x := by
  obtain ⟨a, ha⟩ := h'
  exact ⟨a, h a ha⟩

/- TODO -/

example : (∀ x, f x ∧ g x) → ∀ x, f x := by
  sorry

example : (∀ x, f x ∧ g x) ↔ (∀ x, f x) ∧ (∀ x, g x) := by
  sorry

example : (∃ x, f x ∨ g x) ↔ (∃ x, f x) ∨ (∃ x, g x) := by
  sorry

-- Négation des quantificateurs
example (h : ¬ ∀ x, f x) : ∃ x, ¬ f x := by
  sorry

/- END TODO -/

/-
  # Ensembles et fonctions

  `f '' s`   = image de `s` par `f`  = { f x | x ∈ s }
  `f ⁻¹' t`  = préimage de `t` par `f` = { x | f x ∈ t }

  Tactiques utiles : `ext`, `rintro`, `simp`
  Pour `f '' (s ∪ t)` : penser à `rintro ⟨x, hx | hx, rfl⟩`
-/

#print Function.Injective

-- La composition de deux injections est injective
example {β γ : Type*} {f : α → β} {g : β → γ}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  intro a b hab
  apply hf
  apply hg
  exact hab

-- L'image d'une intersection est contenue dans l'intersection des images
-- Dans un pattern `⟨x, hx, rfl⟩`, le `rfl` signifie qu'une des hypothèses est de la forme
-- `y = f x` : Lean substitue immédiatement y par f x dans tout le but
example {β : Type*} (f : α → β) (s t : Set α) :
    f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y hy
  obtain ⟨x, ⟨hxs, hxt⟩, rfl⟩ := hy
  exact ⟨⟨x, hxs, rfl⟩, ⟨x, hxt, rfl⟩⟩

/- TODO -/

-- `ext` réduit une égalité d'ensembles à une équivalence membre à membre :
-- après `ext x`, le but devient `x ∈ s ↔ x ∈ t`.
-- s ∩ t = t ∩ s
-- Indice : après `ext x`, utiliser `constructor` et `rintro`
example (s t : Set α) : s ∩ t = t ∩ s := by
  sorry

-- L'image d'une union est l'union des images
-- Indice pour →  : `rintro ⟨x, hx | hx, rfl⟩`
-- Indice pour ← : `rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)`
example {β : Type*} (f : α → β) (s t : Set α) :
    f '' (s ∪ t) = f '' s ∪ f '' t := by
  sorry

-- La préimage commute avec le complémentaire
-- Mode facile : ext x puis simp, sinon à la main
example {β : Type*} (f : α → β) (t : Set β) :
    f ⁻¹' tᶜ = (f ⁻¹' t)ᶜ := by
  sorry

-- Si f est injective, image(s ∩ t) = image(s) ∩ image(t)
-- Indice pour ← : `rintro ⟨⟨x, hxs, rfl⟩, ⟨x', hxt, hxx'⟩⟩`, puis `hf` et `subst`
example {β : Type*} {f : α → β} (hf : Function.Injective f) (s t : Set α) :
    f '' (s ∩ t) = f '' s ∩ f '' t := by
  sorry

/- END TODO -/

/-
  # Arithmétique et divisibilité

  `a ∣ b` signifie "a divise b". Utiliser `\|` pour écrire `∣`.
-/

-- Pièges liés au type
example : (1 : ℕ) - 3 = 0 := by norm_num      -- pas -2 !
example : (2 : ℝ) / 0 = 0 := by norm_num      -- convention Lean
example (a b : ℕ) (h : b ≤ a) : a - b + b = a := Nat.sub_add_cancel h

-- n(n+1) est toujours pair : preuve par cas pair/impair
example (n : ℤ) : 2 ∣ n * (n + 1) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (n + 1), by rw [hk]; ring⟩
  · exact ⟨n * (k + 1), by rw [hk]; ring⟩

/- TODO -/

-- Si 2 ∣ a et 2 ∣ b, alors 4 ∣ a * b
example (a b : ℤ) (ha : 2 ∣ a) (hb : 2 ∣ b) : 4 ∣ a * b := by
  sorry

-- Si a ∣ b et a ∣ c, montrer a ∣ 3 * b ^ 2 - 5 * c
example (a b c : ℤ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ 3 * b ^ 2 - 5 * c := by
  sorry

-- Le pgcd divise la somme
example (a b : ℕ) : Nat.gcd a b ∣ a + b := by
  sorry

-- Identité de Bézout (chercher le bon lemme avec `exact?`)
example (a b : ℤ) : ∃ u v : ℤ, u * a + v * b = Int.gcd a b := by
  sorry

/- END TODO -/

/-
  # Nombres premiers
-/

example : Nat.Prime 17 := by norm_num

#check Nat.Prime.dvd_mul

example (p a b : ℕ) (hp : Nat.Prime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  hp.dvd_mul.mp h

/- TODO -/

-- Si p premier et p ∣ aⁿ, alors p ∣ a
example (p a n : ℕ) (hp : Nat.Prime p) (h : p ∣ a ^ n) : p ∣ a := by
  sorry

-- Si p premier et p ∣ a * b * c, que peut-on conclure ?
-- (Ne pas chercher un lemme : raisonner à partir de `Nat.Prime.dvd_mul`)
example (p a b c : ℕ) (hp : Nat.Prime p) (h : p ∣ a * b * c) :
    p ∣ a ∨ p ∣ b ∨ p ∣ c := by
  sorry

/- END TODO -/

/-
  # Structures algébriques

  Lean/Mathlib représente les structures algébriques par des **classes de types**.
  Par exemple, écrire `[Group G]` signifie "G est muni d'une structure de groupe".

  Les structures forment une hiérarchie :
    Monoid → Group → CommGroup
    Ring → CommRing → Field
    AddCommGroup + scalaires → Module (généralise espace vectoriel)

  Lean sait que les types familiers sont munis de ces structures :
-/

example : CommRing ℤ := inferInstance
example : Field ℝ    := inferInstance
example : Field ℂ    := inferInstance

-- Pour p premier, ℤ/pℤ est un corps
example : Field (ZMod 5) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact inferInstance

/-
  ## Groupes

  Un morphisme de groupes `f : G →* H` vérifie `f (a * b) = f a * f b`.
  Lean déduit automatiquement `f 1 = 1` et `f (a⁻¹) = f(a)⁻¹`.
-/

#check MonoidHom.map_one
#check MonoidHom.map_mul
#check MonoidHom.map_inv

-- f(1_G) = 1_H
example {G H : Type*} [Group G] [Group H] (f : G →* H) : f 1 = 1 :=
  f.map_one

#check eq_inv_of_mul_eq_one_left

-- f(a⁻¹) = f(a)⁻¹
-- Idée : montrer f(a) * f(a⁻¹) = 1, puis conclure par `eq_inv_of_mul_eq_one_left`
example {G H : Type*} [Group G] [Group H] (f : G →* H) (a : G) :
    f a⁻¹ = (f a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← f.map_mul, inv_mul_cancel, f.map_one]

/- TODO -/

-- Si f est injectif, alors : f(a) = 1 ⟹ a = 1
example {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (a : G) (h : f a = 1) : a = 1 := by
  sorry

-- Dans un monoïde commutatif, (a * b)^n = a^n * b^n
-- Prouver par récurrence sur n.
-- Indice : `pow_succ x n : x ^ (n + 1) = x ^ n * x` et `mul_mul_mul_comm`
example {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n := by
  sorry

-- f envoie les conjugués sur les conjugués : f(g * a * g⁻¹) = f(g) * f(a) * f(g)⁻¹
example {G H : Type*} [Group G] [Group H] (f : G →* H) (a g : G) :
    f (g * a * g⁻¹) = f g * f a * (f g)⁻¹ := by
  sorry

/- END TODO -/

/-
  ## Anneaux

  Un morphisme d'anneaux `f : R →+* S` envoie 1 sur 1 et préserve +, *.
  L'exemple fondamental : la réduction modulo n, `Int.castRingHom (ZMod n)`.
-/

#check Int.castRingHom (ZMod 5)
#check RingHom.map_mul
#check RingHom.map_add
#check RingHom.map_pow

-- Un morphisme d'anneaux préserve à la fois + et *
example {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) :
    f (a ^ 2 + b ^ 2) = f a ^ 2 + f b ^ 2 := by
  rw [map_add, map_pow, map_pow] -- simp fonctionne aussi !

/- TODO -/

-- f préserve les unités
example {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : R) (h : IsUnit a) :
    IsUnit (f a) := by
  sorry

-- Dans ℤ/5ℤ : 2 * 3 = 1
example : (2 : ZMod 5) * 3 = 1 := by
  sorry

-- Petit théorème de Fermat
example (a : ZMod 5) : a ^ 5 = a := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ZMod.pow_card a

-- `decide` vérifie les propositions décidables par calcul dans le noyau de Lean (lent).
-- `native_decide` compile en code natif et utilise GMP pour l'arithmétique : bien plus rapide.
-- Calculer 2 ^ 100 mod 7
example : (2 : ZMod 7) ^ 100 = 2 := by
  native_decide

/- END TODO -/

/-
  ## Corps

  Un corps est un anneau commutatif où tout élément non nul est inversible.
  La convention Lean : `0⁻¹ = 0`.

  Le lemme central : `mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0`
-/

-- Dans un corps, produit nul implique facteur nul
example {K : Type*} [Field K] (a b : K) (h : a * b = 0) : a = 0 ∨ b = 0 :=
  mul_eq_zero.mp h

/- TODO -/

-- L'inverse de l'inverse est l'élément lui-même (pour a ≠ 0)
-- Indice : `inv_inv`
example {K : Type*} [Field K] (a : K) (ha : a ≠ 0) : (a⁻¹)⁻¹ = a := by
  sorry

-- Dans ℤ/7ℤ, trouver l'inverse de 3
-- (indice : decide)
example : (3 : ZMod 7)⁻¹ = 5 := by
  sorry

-- Dans un corps, simplification : si a ≠ 0 et a * b = a * c, alors b = c
-- Indice : `mul_left_cancel₀`
example {K : Type*} [Field K] (a b c : K) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  sorry

/- END TODO -/

/-
  ## Modules

  Un R-module généralise la notion d'espace vectoriel :
  l'anneau de scalaires R remplace le corps.

  Exemples :
  - Tout groupe abélien est un ℤ-module
  - Un K-espace vectoriel est un K-module
  - ℤ/nℤ est un ℤ-module

  L'action scalaire s'écrit `r • v`.
-/

#check smul_add   -- r • (a + b) = r • a + r • b
#check add_smul   -- (r + s) • a = r • a + s • a
#check mul_smul   -- (r * s) • a = r • (s • a)
#check one_smul   -- (1 : R) • a = a
#check zero_smul  -- (0 : R) • a = 0
#check smul_zero  -- r • (0 : M) = 0

/- TODO -/

-- (-1) • v = -v
-- Indice : `neg_one_smul`
example {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) : (-1 : ℝ) • v = -v := by
  sorry

-- Un sous-module est stable par addition
example {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V)
    (u v : V) (hu : u ∈ S) (hv : v ∈ S) : u + v ∈ S := by
  sorry

-- Un sous-module est stable par action scalaire
example {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V)
    (r : ℝ) (v : V) (hv : v ∈ S) : r • v ∈ S := by
  sorry

/- END TODO -/

/-
  # Analyse et topologie

  **Note sur les filtres** : dans Mathlib, les limites sont définies via les *filtres*.
  Par exemple, `Filter.Tendsto f (nhds a) (nhds b)` signifie `f(x) → b` quand `x → a`.
  Cette abstraction unifie les limites en un point, à l'infini, les suites convergentes, etc.
  Elle est centrale dans Mathlib, même si nous n'entrons pas dans ces détails ici.
-/

/-
  ## Continuité

  `Continuous f`      : f est continue partout
  `ContinuousAt f x`  : f est continue en x
  `ContinuousOn f s`  : f est continue sur l'ensemble s

  La tactique `fun_prop` prouve la continuité des fonctions usuelles automatiquement.
-/

-- fun_prop en action
example : Continuous (fun x : ℝ => x ^ 2 + 1) := by fun_prop
example : Continuous (fun x : ℝ => Real.sin (Real.exp x)) := by fun_prop

-- La composition de deux fonctions continues est continue
example {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := hg.comp hf

/- TODO -/

-- x ↦ cos x + x ^ 2 est continue
example : Continuous (fun x : ℝ => Real.cos x + x ^ 2) := by
  sorry

-- Si f et g sont continues, x ↦ f x * g x est continue
example {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x) := by
  sorry

/- END TODO -/

-- Théorème des valeurs intermédiaires
#check intermediate_value_uIcc

/-
  ## Dérivées

  `HasDerivAt f f' x`   : f est dérivable en x, de dérivée f'
  `deriv f x`           : la dérivée de f en x
  `Differentiable ℝ f`  : f est dérivable partout

  `fun_prop` vérifie aussi la différentiabilité.
-/

-- Dérivées des fonctions usuelles
example : deriv Real.sin = Real.cos := by ext x; simp [Real.deriv_sin]
example : deriv Real.exp = Real.exp := by ext x; simp [Real.deriv_exp]

-- fun_prop vérifie la différentiabilité
example : Differentiable ℝ (fun x : ℝ => Real.cos (Real.sin x) * Real.exp x) := by fun_prop

/- TODO -/

-- x ↦ x ^ 3 est dérivable
example : Differentiable ℝ (fun x : ℝ => x ^ 3) := by
  sorry

-- La dérivée de x ↦ x ^ 2 est x ↦ 2 * x
-- Indice : commencer par `ext x`, puis `simp`
example : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
  sorry

/- END TODO -/

-- Théorème fondamental de l'analyse
#check intervalIntegral.integral_eq_sub_of_hasDerivAt

/-
  ## Topologie

  `IsOpen s`    : s est un ouvert
  `IsClosed s`  : s est un fermé
  `IsCompact s` : s est compact
-/

-- Exemples d'ouverts et de fermés
example : IsOpen (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo
example : IsClosed (Set.Icc (0 : ℝ) 1) := isClosed_Icc

-- La préimage d'un ouvert par une fonction continue est ouverte
example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : IsOpen s) :
    IsOpen (f ⁻¹' s) := hs.preimage hf

/- TODO -/

-- La préimage d'un fermé par une fonction continue est fermée
example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) := by
  sorry

-- L'image d'un compact par une fonction continue est compacte
example {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} (hs : IsCompact s) :
    IsCompact (f '' s) := by
  sorry

/- END TODO -/

-- Heine-Cantor : continue sur un compact → uniformément continue
#check IsCompact.uniformContinuousOn_of_continuous

-- Heine-Borel : compact ↔ fermé et borné (dans ℝⁿ)
#check Metric.isCompact_iff_isClosed_bounded

/-
  # Chercher dans Mathlib

  Mathlib contient des milliers de lemmes. Voici les outils pour les trouver.

  ## Outils interactifs (dans l'éditeur)

  `exact?`  — cherche un lemme qui prouve exactement le but courant
  `apply?`  — cherche un lemme dont la conclusion correspond au but
  `simp?`   — trouve les lemmes de simp qui ferment ou simplifient le but

  ## Moteurs de recherche

  * **Mathlib docs** : https://leanprover-community.github.io/mathlib4_docs
    Recherche par nom, type, module.

  * **Loogle** : https://loogle.lean-lang.org
    Recherche par motif de type. Exemple : `?a ∣ ?b → ?a ∣ ?b * ?c`

  * **LeanSearch** : https://leansearch.net
    Recherche en langage naturel. Exemple : "prime divides product"
-/

-- Exercice : trouver et utiliser le bon lemme dans chaque cas
-- (utiliser `exact?` ou les moteurs de recherche)

/- TODO -/

-- Si a ∣ b et b ∣ c, alors a ∣ c
example (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  sorry

-- pgcd(a, b) * ppcm(a, b) = a * b
example (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b := by
  sorry

-- π est irrationnel
example : Irrational Real.pi := by
  sorry

-- La somme de deux nombres pairs est paire
example (m n : ℤ) (hm : 2 ∣ m) (hn : 2 ∣ n) : 2 ∣ m + n := by
  sorry

-- Le dernier théorème de Fermat pour n = 3
-- (`FermatLastTheoremFor n` signifie : ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a^n + b^n ≠ c^n)
example : FermatLastTheoremFor 3 := by
  sorry

/- END TODO -/

/-
  # Deux preuves plus ambitieuses

  ## Construction de ℤ à partir de ℕ × ℕ

  L'idée : un entier `a - b` est représenté par la paire `(a, b) ∈ ℕ × ℕ`.
  Deux paires `(a, b)` et `(c, d)` représentent le même entier si `a - b = c - d`,
  ce qui s'écrit sans soustraction : `a + d = c + b`.

  On définit ainsi une relation d'équivalence sur `ℕ × ℕ`, et `ℤ` en est le quotient.
-/

-- La relation d'équivalence
def rZ : ℕ × ℕ → ℕ × ℕ → Prop := fun (a, b) (c, d) ↦ a + d = c + b

-- Reformulations utiles
theorem rZ_iff (a b c d : ℕ) : rZ (a, b) (c, d) ↔ a + d = c + b := Iff.rfl
theorem rZ_iff' (x y : ℕ × ℕ) : rZ x y ↔ x.1 + y.2 = y.1 + x.2 := Iff.rfl

/- TODO -/

-- rZ est réflexive
theorem rZ_reflexive : ∀ x : ℕ × ℕ, rZ x x := by
  sorry

-- rZ est symétrique
theorem rZ_symmetric : ∀ {x y : ℕ × ℕ}, rZ x y → rZ y x := by
  sorry

-- rZ est transitive
-- Indice : `lia`
theorem rZ_transitive : ∀ {x y z : ℕ × ℕ}, rZ x y → rZ y z → rZ x z := by
  sorry

/- END TODO -/

-- On en fait un Setoid (structure d'équivalence reconnue par Lean)
instance rZSetoid : Setoid (ℕ × ℕ) where
  r := rZ
  iseqv := ⟨rZ_reflexive, rZ_symmetric, rZ_transitive⟩

@[simp] theorem rZ_equiv_def (a b c d : ℕ) : (a, b) ≈ (c, d) ↔ a + d = c + b := Iff.rfl

-- Notre version de ℤ : le type quotient
abbrev ZZ := Quotient rZSetoid

namespace ZZ

-- 0 et 1 dans ZZ  (`⟦x⟧` est la notation pour la classe de x)
instance : Zero ZZ := ⟨⟦(0, 0)⟧⟩
instance : One  ZZ := ⟨⟦(1, 0)⟧⟩

-- Négation : (a, b) ↦ (b, a)  — définie via Quotient.lift
def neg : ZZ → ZZ :=
  Quotient.lift (fun x : ℕ × ℕ ↦ (⟦(x.2, x.1)⟧ : ZZ)) (by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    apply Quotient.sound
    simp only [rZ_equiv_def] at h ⊢; lia)

instance : Neg ZZ := ⟨neg⟩

@[simp] theorem neg_def (a b : ℕ) : -(⟦(a, b)⟧ : ZZ) = ⟦(b, a)⟧ := rfl

-- Addition : (a, b) + (c, d) = (a+c, b+d)
def add_aux (x y : ℕ × ℕ) : ZZ := ⟦(x.1 + y.1, x.2 + y.2)⟧

/- TODO -/

-- Montrer que add_aux est compatible avec la relation (nécessaire pour Quotient.lift₂)
theorem add_aux_sound (x₁ y₁ x₂ y₂ : ℕ × ℕ) (h₁ : x₁ ≈ x₂) (h₂ : y₁ ≈ y₂) :
    add_aux x₁ y₁ = add_aux x₂ y₂ := by
  sorry

-- Définir l'addition sur ZZ via Quotient.lift₂
def add : ZZ → ZZ → ZZ := Quotient.lift₂ add_aux add_aux_sound

instance : Add ZZ := ⟨add⟩

@[simp] theorem add_def (a b c d : ℕ) :
    (⟦(a, b)⟧ + ⟦(c, d)⟧ : ZZ) = ⟦(a + c, b + d)⟧ := rfl

-- Montrer que l'addition est commutative
-- Indice : `Quotient.inductionOn₂`
theorem add_comm' (x y : ZZ) : x + y = y + x := by
  sorry

/- END TODO -/

end ZZ

-- Le résultat final : ZZ est isomorphe à ℤ en tant qu'anneaux
-- (preuve complète dans les notes de cours)
#check Int.cast  -- le morphisme canonique ℤ → R

/-
  ## Théorème de Schröder-Bernstein

  Si `f : α → β` et `g : β → α` sont toutes deux injectives,
  il existe une bijection `h : α → β`.

  https://en.wikipedia.org/wiki/Schröder–Bernstein_theorem

  Source : *Mathematics in Lean*, J. Avigad et al., chapitre 4, section 3.
  https://leanprover-community.github.io/mathematics_in_lean/
-/

section SchroederBernstein

open Set Function Classical

variable {α β : Type*} [Nonempty β] (f : α → β) (g : β → α)

private def sbAux : ℕ → Set α
  | 0     => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

private def sbSet := ⋃ n, sbAux f g n

private def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

/- TODO -/

-- Si x ∉ sbSet, alors x est dans l'image de g, donc invFun g est bien une inverse droite
-- Indice : montrer d'abord `x ∈ g '' univ` par contraposée (cas n=0 de sbAux),
--          puis utiliser `invFun_eq`
private theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  sorry

-- sbFun est injective si f l'est
-- Stratégie : `set A := sbSet f g`, `set h := sbFun f g`, `by_cases` sur `x₁ ∈ A ∨ x₂ ∈ A`,
--             `wlog` pour supposer x₁ ∈ A, puis `push Not` pour le cas ¬(x₁∈A ∨ x₂∈A)
private theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  sorry

-- sbFun est surjective si g l'est
-- Stratégie : `by_cases` sur `g y ∈ A`, puis `leftInverse_invFun`
private theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  sorry

-- Théorème principal : assembler les trois lemmes ci-dessus
theorem schroeder_bernstein {f : α → β} {g : β → α}
    (hf : Injective f) (hg : Injective g) : ∃ h : α → β, Bijective h := by
  sorry

/- END TODO -/

end SchroederBernstein

end
