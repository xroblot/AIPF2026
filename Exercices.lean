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
  ## Raccourcis clavier

  | Raccourci     | Symbole | Raccourci     | Symbole |
  |---------------|---------|---------------|---------|
  | `\to`         |   `→`   | `\iff`        |   `↔`   |
  | `\and`        |   `∧`   | `\or`         |   `∨`   |
  | `\not`        |   `¬`   | `\ne`         |   `≠`   |
  | `\forall`     |   `∀`   | `\exists`     |   `∃`   |
  | `\<`          |   `⟨`   | `\>`          |   `⟩`   |
  | `\in`         |   `∈`   | `\notin`      |   `∉`   |
  | `\sub`        |   `⊆`   | `\|`          |   `∣`   |
  | `\union`      |   `∪`   | `\inter`      |   `∩`   |
  | `\N`          |   `ℕ`   | `\Z`          |   `ℤ`   |
  | `\R`          |   `ℝ`   | `\C`          |   `ℂ`   |
  | `\alpha`      |   `α`   | `\beta`       |   `β`   |
  | `\smul`       |   `•`   | `\le`         |   `≤`   |
  | `\-1`         |   `⁻¹`  | `\comp`       |   `∘`   |
-/

/-
  # Propositions et preuves

  Les propositions vivent dans le type `Prop`.
  La tactique `sorry` accepte n'importe quel but sans le prouver.
-/

variable (P Q R S : Prop)

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

-- La tactique `have` introduit un résultat intermédiaire qu'on peut nommer
example (h1 : P → Q) (h2 : Q → R) (hP : P) : R := by
  have hQ : Q := h1 hP
  exact h2 hQ

-- La tactique `rfl` prouve une égalité réflexive
example : P = P := by
  rfl

-- La tactique `trivial` prouve `True` (et d'autres buts évidents)
example : True := by
  trivial

-- La tactique `exfalso` remplace le but par `False` (ex falso quodlibet)
example : False → P := by
  intro h
  exfalso
  exact h

/- TODO -/

example : P → Q → P := by
  sorry

example : P → (P → Q) → Q := by
  sorry

example : (P → Q) → (Q → R) → P → R := by
  sorry

example : (P → Q) → ((P → Q) → P) → Q := by
  sorry

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  sorry

/- END TODO -/

/-
  ## Négation, True, False

  `¬P` est *définie* comme `P → False`.
  La tactique `change` remplace le but par un terme *définitionnellement* égal.
-/

-- `change` permet de déplier la définition de ¬ explicitement
example : ¬True → False := by
  change (True → False) → False
  intro h
  exact h trivial

-- Tactique `by_contra` : suppose ¬P et cherche une contradiction
example : ¬¬P → P := by
  intro h
  by_contra hP
  apply h
  exact hP

-- Tactique `by_cases` : raisonnement par cas sur P ∨ ¬P (tiers exclu)
example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · exact hP
  · exfalso; exact h hP

/- TODO -/

example : P → ¬¬P := by
  sorry

example : (P → Q) → ¬Q → ¬P := by
  sorry

example : P → ¬P → False := by
  sorry

example : (¬Q → ¬P) → P → Q := by
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
  · right
    exact hP
  · left
    exact hQ

-- `constructor` décompose un but `A ↔ B` en deux implications `A → B` et `B → A`
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨hP, hQ⟩
    exact ⟨hQ, hP⟩
  · intro ⟨hQ, hP⟩
    exact ⟨hP, hQ⟩

/- TODO -/

example : P ∧ Q → Q := by
  sorry

example : (P → Q → R) → P ∧ Q → R := by
  sorry

example : P ∧ Q → Q ∧ R → P ∧ R := by
  sorry

example : P ∨ Q ↔ Q ∨ P := by
  sorry

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry

-- Loi de De Morgan (sens ← nécessite le tiers exclu)
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry

/- END TODO -/

/-
  ## Équivalence

  `P ↔ Q` peut aussi se déconstruire avec `obtain ⟨h1, h2⟩ := h`.
-/

-- Déconstruire ↔ avec obtain
example : (P ↔ Q) → (Q ↔ P) := by
  intro ⟨hpq, hqp⟩
  exact ⟨hqp, hpq⟩

/- TODO -/

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  sorry

example : P ↔ P ∧ True := by
  sorry

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry

example : ¬(P ↔ ¬P) := by
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

example : (∀ x, f x) ↔ ¬ (∃ x, ¬ f x) := by
  sorry

example : (∃ x, f x) ↔ ¬ (∀ x, ¬ f x) := by
  sorry

/- END TODO -/

/-
  # Ensembles et fonctions

  `s ⊆ t`    : s est sous-ensemble de t  — prouver avec `intro x hx`
  `f '' s`   = image de `s` par `f`      = { f x | x ∈ s }
  `f ⁻¹' t`  = préimage de `t` par `f`  = { x | f x ∈ t }

  Tactiques utiles : `ext`, `rintro`, `simp`
  Pour `f '' (s ∪ t)` : penser à `rintro ⟨x, hx | hx, rfl⟩`
-/

-- Prouver `s ⊆ t` : introduire un élément avec `intro x hx`
example (s t u : Set α) (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  intro x hx
  exact htu (hst hx)

-- `ext x` réduit une égalité d'ensembles `s = t` à `x ∈ s ↔ x ∈ t`
example (s : Set α) : s ∩ s = s := by
  ext x
  constructor
  · rintro ⟨hx, _⟩; exact hx
  · intro hx; exact ⟨hx, hx⟩

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
-- `y = f x` : Lean substitue immédiatement y par f x partout
example {β : Type*} (f : α → β) (s t : Set α) :
    f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y hy
  obtain ⟨x, ⟨hxs, hxt⟩, rfl⟩ := hy
  exact ⟨⟨x, hxs, rfl⟩, ⟨x, hxt, rfl⟩⟩

/- TODO -/

-- s ⊆ s ∪ t
example (s t : Set α) : s ⊆ s ∪ t := by
  sorry

-- s ∩ t = t ∩ s
-- Indice : `ext x`, puis `constructor` et `rintro ⟨h1, h2⟩`
example (s t : Set α) : s ∩ t = t ∩ s := by
  sorry

-- Distributivité de ∩ sur ∪
example (s t u : Set α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  sorry

-- L'image d'une union est l'union des images
-- Indice pour →  : `rintro ⟨x, hx | hx, rfl⟩`
-- Indice pour ← : `rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)`
example {β : Type*} (f : α → β) (s t : Set α) :
    f '' (s ∪ t) = f '' s ∪ f '' t := by
  sorry

-- La préimage respecte l'intersection : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t
-- Mode facile : `ext x` puis `simp`
example {β : Type*} (f : α → β) (s t : Set β) :
    f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := by
  sorry

-- La préimage commute avec le complémentaire
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
  # Structures algébriques

  Lean/Mathlib représente les structures algébriques par des **classes de types**.
  Par exemple, écrire `[Group G]` signifie "G est muni d'une structure de groupe".

  Les structures forment une hiérarchie :
    Monoid → Group → CommGroup
    Ring → CommRing → Field
    AddCommGroup + scalaires → Module (généralise espace vectoriel)
-/

/-
  **Synthèse d'instances**

  Lean maintient une base de données d'*instances* de classes de types.
  Quand on veut appliquer un lemme dont la signature contient `[CommRing R]`,
  Lean cherche automatiquement une instance de `CommRing R` dans cette base
  pour le type `R` en question — c'est la *synthèse d'instances*.
  La commande `inferInstance` déclenche explicitement cette recherche
  (utile pour vérifier qu'une instance existe ou la fournir manuellement).
-/

example : CommRing ℤ := inferInstance
example : Field ℝ    := inferInstance
example : Field ℂ    := inferInstance

/-
  **Ce qui peut être une instance** : seules les *classes de types* peuvent figurer dans cette base.
  Une proposition ordinaire (comme `Nat.Prime 5 : Prop`) ne peut pas y apparaître directement.
  C'est pourquoi on utilise `Fact P` : c'est une classe de types avec un seul champ `out : P`,
  qui permet d'enregistrer une proposition dans la base d'instances.
-/
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

-- La tactique `group` prouve les identités valables dans *tout* groupe (analogue de `ring`)
example {G : Type*} [Group G] (x y z : G) :
    x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by group

-- La tactique `abel` fait de même dans un groupe abélien (noté additivement)
example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by abel

/- TODO -/

-- Si f est injectif, alors : f(a) = 1 → a = 1
example {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (a : G) (h : f a = 1) : a = 1 := by
  sorry

-- Dans un monoïde commutatif, (a * b) ^ n = a ^ n * b ^ n
-- Indice : `pow_succ x n : x ^ (n + 1) = x ^ n * x` et `mul_mul_mul_comm`
--
-- La tactique `simp` simplifie le but en appliquant une base de lemmes automatiquement.
-- `simp?` fait la même chose mais affiche les lemmes utilisés — utile pour comprendre
-- ou pour remplacer `simp` par un appel plus explicite.
--
-- Squelette de la récurrence :
--   induction n with
--   | zero   => simp        -- cas de base : (a*b)^0 = 1 = 1*1
--   | succ n ih => ...
example {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n := by
  sorry

-- Dans un groupe où tout élément vérifie a^2 = 1, la multiplication est commutative.
-- Démarche : montrer d'abord que tout élément est son propre inverse, i.e. ∀ x, x⁻¹ = x.
--   Pour cela : x * x = 1 (car x^2 = 1), puis utiliser `eq_inv_of_mul_eq_one_left`.
--   Ensuite : a * b = (a * b)⁻¹ = b⁻¹ * a⁻¹ = b * a.
--   (`mul_inv_rev` donne (a * b)⁻¹ = b⁻¹ * a⁻¹)
example {G : Type*} [Group G] (h : ∀ a : G, a ^ 2 = 1) (a b : G) : a * b = b * a := by
  sorry

-- La préimage d'un sous-groupe par un morphisme préserve l'inclusion
-- `S.comap φ` est la préimage de S par φ (un sous-groupe de G)
-- Indice secondaire : `Subgroup.mem_comap` (a ∈ S.comap φ ↔ φ a ∈ S)
example {G H : Type*} [Group G] [Group H] (φ : G →* H) (S T : Subgroup H)
    (hST : S ≤ T) : S.comap φ ≤ T.comap φ := by
  sorry

-- Construction du sous-groupe conjugué xHx⁻¹
-- Il faut remplir les trois preuves de stabilité (neutre, inverse, produit).
-- Indices secondaires : `H.one_mem`, `H.inv_mem`, `H.mul_mem` (stabilité de H lui-même)
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by sorry
  inv_mem' := by sorry
  mul_mem' := by sorry

/- END TODO -/

/-
  ## Anneaux et corps

  La tactique `ring` prouve les identités algébriques dans un `CommRing`.
  Un morphisme d'anneaux `f : R →+* S` préserve +, * et 1 (`map_add`, `map_mul`, `map_pow`).
  Un corps (`Field`) est un `CommRing` où tout non-nul est inversible ; convention : `0⁻¹ = 0`.
-/

-- La commutativité est une hypothèse, pas un théorème : `Ring` ≠ `CommRing`
example {R : Type*} [CommRing R] (a b : R) : a * b = b * a := mul_comm a b

-- `ring` prouve les identités polynomiales dans un `CommRing`
example {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

-- Un morphisme d'anneaux préserve les puissances et les sommes
example {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) :
    f (a ^ 2 + b ^ 2) = f a ^ 2 + f b ^ 2 := by
  rw [map_add, map_pow, map_pow]

-- Dans un corps, produit nul implique facteur nul
example {K : Type*} [Field K] (a b : K) (h : a * b = 0) : a = 0 ∨ b = 0 :=
  mul_eq_zero.mp h

/- TODO -/

-- Factorisation de a³ - b³ (utiliser `ring`)
-- Le même énoncé est faux dans un `Ring` non commutatif : `ring` nécessite `CommRing`
example {R : Type*} [CommRing R] (a b : R) :
    a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by
  sorry

-- Les unités de ℤ sont exactement ±1
#check @Units.mul_inv     -- x * x⁻¹ = 1 dans ℤˣ
#check isUnit_of_dvd_one  -- a ∣ 1 → IsUnit a
#check Int.isUnit_iff     -- IsUnit n ↔ n = 1 ∨ n = -1
example (x : ℤˣ) : x = 1 ∨ x = -1 := by
  sorry

-- f préserve les unités
-- Indice : `IsUnit a` se déconstruit en une unité (`obtain ⟨u, rfl⟩ := h`) ;
--   `Units.map f.toMonoidHom` envoie une unité de R sur une unité de S
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a : R) (h : IsUnit a) :
    IsUnit (f a) := by
  sorry

-- L'inverse de l'inverse est l'élément lui-même (pour a ≠ 0)
-- Indice : `inv_ne_zero`, `mul_inv_cancel₀`, `inv_mul_cancel₀`
example {K : Type*} [Field K] (a : K) (ha : a ≠ 0) : (a⁻¹)⁻¹ = a := by
  sorry

-- Simplification à gauche dans un corps : a ≠ 0, a * b = a * c → b = c
-- Indice : multiplier par a⁻¹ à gauche, puis `mul_assoc` et `inv_mul_cancel₀`
example {K : Type*} [Field K] (a b c : K) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
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

-- `Continuous` coïncide avec la définition classique ε-δ (dans un espace métrique)
example {f : ℝ → ℝ} : Continuous f ↔
    ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

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

-- `simp` sait aussi calculer une dérivée en un point
example : deriv (fun x : ℝ => x ^ 5) 6 = 5 * 6 ^ 4 := by simp

-- fun_prop vérifie la différentiabilité
example : Differentiable ℝ (fun x : ℝ => Real.cos (Real.sin x) * Real.exp x) := by fun_prop

-- Deux grands théorèmes du calcul différentiel
#check exists_deriv_eq_zero        -- Théorème de Rolle
#check exists_hasDerivAt_eq_slope  -- Théorème des accroissements finis

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

-- Théorème des bornes : une fonction continue sur un compact non vide atteint son minimum
#check IsCompact.exists_isMinOn

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

-- Exercice : trouver et utiliser le bon lemme dans chaque cas.
-- Contrairement au reste du TD — où les indices ne donnent jamais le lemme final —
-- ici le but EST de dénicher le lemme qui clôt le but en une ligne.
-- (utiliser `exact?` ou les moteurs de recherche ci-dessus)

/- TODO -/

-- Si a ∣ b et b ∣ c, alors a ∣ c
example (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  sorry

-- La somme de deux nombres pairs est paire
example (m n : ℤ) (hm : 2 ∣ m) (hn : 2 ∣ n) : 2 ∣ m + n := by
  sorry

-- pgcd(a, b) * ppcm(a, b) = a * b
example (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b := by
  sorry

-- π est irrationnel
example : Irrational Real.pi := by
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

/-
  Les trois preuves ci-dessous ont la même structure : décomposer les paires
  (`rintro ⟨a, b⟩ ...` ou `intro`), déplier `rZ` en une égalité arithmétique
  (via `rZ_iff` / `rZ_iff'`), puis conclure par arithmétique linéaire avec `lia`.
-/

/- TODO -/

-- rZ est réflexive
-- Indice : `rintro ⟨a, b⟩`, puis `simp [rZ_iff]`
theorem rZ_reflexive : ∀ x : ℕ × ℕ, rZ x x := by
  sorry

-- rZ est symétrique
-- (x et y sont implicites : les introduire avec `intro x y h`)
theorem rZ_symmetric : ∀ {x y : ℕ × ℕ}, rZ x y → rZ y x := by
  sorry

-- rZ est transitive
-- Indice : `intro x y z h1 h2`, puis `simp only [rZ_iff'] at *` et `lia`
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

/-
  Pour définir une opération sur un quotient, on la définit d'abord sur les
  représentants (`add_aux`), puis on prouve qu'elle ne dépend pas du choix des
  représentants (`add_aux_sound`) : c'est ce qui permet à `Quotient.lift₂` de la
  faire « descendre » au quotient. Pour prouver une égalité *entre classes*, on
  utilise `Quotient.sound` (deux représentants équivalents ont la même classe).
-/

/- TODO -/

-- Montrer que add_aux est compatible avec la relation (nécessaire pour Quotient.lift₂)
-- Indice : décomposer les quatre paires, déplier les hypothèses avec
--   `simp only [add_aux, rZ_equiv_def] at *`, puis `apply Quotient.sound` et `lia`
theorem add_aux_sound (x₁ y₁ x₂ y₂ : ℕ × ℕ) (h₁ : x₁ ≈ x₂) (h₂ : y₁ ≈ y₂) :
    add_aux x₁ y₁ = add_aux x₂ y₂ := by
  sorry

-- Définir l'addition sur ZZ via Quotient.lift₂
def add : ZZ → ZZ → ZZ := Quotient.lift₂ add_aux add_aux_sound

instance : Add ZZ := ⟨add⟩

@[simp] theorem add_def (a b c d : ℕ) :
    (⟦(a, b)⟧ + ⟦(c, d)⟧ : ZZ) = ⟦(a + c, b + d)⟧ := rfl

-- Montrer que l'addition est commutative
-- `Quotient.inductionOn₂` ramène un but portant sur deux classes à un but sur
-- leurs représentants : `refine Quotient.inductionOn₂ x y ?_`, puis `rintro ⟨a, b⟩ ⟨c, d⟩`.
-- Conclure avec `simp only [add_def]`, `apply Quotient.sound` et `lia`.
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

  **Idée de la preuve.** On partitionne `α` en deux : l'ensemble `sbSet` des
  éléments « venant du côté f » (définis par itération de `g ∘ f` à partir des
  points hors de l'image de `g`), et son complémentaire. On construit `sbFun` qui
  applique `f` sur `sbSet` et l'inverse `g⁻¹` ailleurs. Il reste à montrer que
  `sbFun` est injective puis surjective (donc bijective) — c'est l'objet des trois
  lemmes ci-dessous, assemblés à la fin.
-/

section SchroederBernstein

open Set Function Classical

variable {α β : Type*} [Nonempty β] (f : α → β) (g : β → α)

-- `sbAux n` est le n-ième niveau de la construction :
--   sbAux 0     = α \ g(β)          (éléments de α qui ne sont pas dans l'image de g)
--   sbAux (n+1) = g(f(sbAux n))     (propagation par g ∘ f)
def sbAux : ℕ → Set α
  | 0     => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

-- `sbSet` = ⋃ sbAux n  (la réunion de tous les niveaux)
-- Intuition : ce sont les éléments de α qui "viennent du côté f"
def sbSet := ⋃ n, sbAux f g n

-- `sbFun` est la bijection cherchée :
--   sur sbSet, on utilise f  (côté "f")
--   ailleurs,  on utilise g⁻¹ (g est injective, donc inversible sur son image)
def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

/- TODO -/

-- Si x ∉ sbSet, alors x est dans l'image de g, donc invFun g est bien une inverse droite
-- Indice : montrer d'abord `x ∈ g '' univ` par contraposée (cas n=0 de sbAux),
--          puis utiliser `invFun_eq`
theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  sorry

-- sbFun est injective si f l'est
-- Stratégie : `set A := sbSet f g`, `set h := sbFun f g`, `by_cases` sur `x₁ ∈ A ∨ x₂ ∈ A`,
--             `wlog` pour supposer x₁ ∈ A, puis `push Not` pour le cas ¬(x₁∈A ∨ x₂∈A)
theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  sorry

-- sbFun est surjective si g l'est
-- Stratégie : `by_cases` sur `g y ∈ A`, puis `leftInverse_invFun`
theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  sorry

-- Théorème principal : assembler les trois lemmes ci-dessus
-- Indice : `Bijective` se déconstruit en `Injective ∧ Surjective` ; fournir le témoin
--   `sbFun f g` puis les deux lemmes, via `exact ⟨_, _, _⟩`
theorem schroeder_bernstein {f : α → β} {g : β → α}
    (hf : Injective f) (hg : Injective g) : ∃ h : α → β, Bijective h := by
  sorry

/- END TODO -/

end SchroederBernstein

end
