---
Título: Limite_de_sucesiones_no_decrecientes.lean
Autor:  José A. Alonso
---

En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante una función (u : ℕ → ℝ) de forma que u(n) es uₙ.

En Lean, se define que a es el límite de la sucesión u, por
<pre lang="text">
   def limite (u: ℕ → ℝ) (a: ℝ) :=
     ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
<pre lang="text">
donde se usa la notación |x| para el valor absoluto de x
<pre lang="text">
   notation `|`x`|` := abs x
</pre>
y que la sucesión u es no decreciente por
<pre lang="text">
   def no_decreciente (u : ℕ → ℝ) :=
     ∀ n m, n ≤ m → u n ≤ u m
</pre>

Demostrar que si u es una sucesión no decreciente y su límite es a, entonces u(n) ≤ a para todo n.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
import tactic

variable {u : ℕ → ℝ}
variable (a : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def no_decreciente (u : ℕ → ℝ) :=
  ∀ n m, n ≤ m → u n ≤ u m

example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
import tactic

variable {u : ℕ → ℝ}
variable (a : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def no_decreciente (u : ℕ → ℝ) :=
  ∀ n m, n ≤ m → u n ≤ u m

-- 1ª demostración
example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
begin
  intro n,
  by_contradiction H,
  push_neg at H,
  replace H : u n - a > 0 := sub_pos.mpr H,
  cases h (u n - a) H with m hm,
  let k := max n m,
  specialize hm k (le_max_right _ _),
  specialize h' n k (le_max_left _ _),
  replace hm : |u k - a| < u k - a, by
    calc |u k - a| < u n - a : hm
               ... ≤ u k - a : sub_le_sub_right h' a,
  rw ← not_le at hm,
  apply hm,
  exact le_abs_self (u k - a),
end

-- 2ª demostración
example
  (h : limite u a)
  (h' : no_decreciente u)
  : ∀ n, u n ≤ a :=
begin
  intro n,
  by_contradiction H,
  push_neg at H,
  cases h (u n - a) (by linarith) with m hm,
  specialize hm (max n m) (le_max_right _ _),
  specialize h' n (max n m) (le_max_left _ _),
  rw abs_lt at hm,
  linarith,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Limite_de_sucesiones_no_decrecientes.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Limite_de_sucesiones_no_decrecientes
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u a ⟷ (∀ε>0. ∃N. ∀k≥N. ¦u k - a¦ < ε)"

definition no_decreciente :: "(nat ⇒ real) ⇒ bool"
  where "no_decreciente u ⟷ (∀ n m. n ≤ m ⟶ u n ≤ u m)"

(* 1ª demostración *)
lemma
  assumes "limite u a"
          "no_decreciente u"
  shows   "∀ n. u n ≤ a"
proof (rule allI)
  fix n
  show "u n ≤ a"
  proof (rule ccontr)
    assume "¬ u n ≤ a"
    then have "a < u n"
      by (rule not_le_imp_less)
    then have H : "u n - a > 0"
      by (simp only: diff_gt_0_iff_gt)
    then obtain m where hm : "∀p≥m. ¦u p - a¦ < u n - a"
      using assms(1) limite_def by blast
    let ?k = "max n m"
    have "n ≤ ?k"
      by (simp only: assms(2) no_decreciente_def)
    then have "u n ≤ u ?k"
      using assms(2) no_decreciente_def by blast
    have "¦u ?k - a¦ < u n - a"
      by (simp only: hm)
    also have "… ≤ u ?k - a"
      using ‹u n ≤ u ?k› by (rule diff_right_mono)
    finally have "¦u ?k - a¦ < u ?k - a"
      by this
    then have "¬ u ?k - a ≤ ¦u ?k - a¦"
      by (simp only: not_le_imp_less)
    moreover have "u ?k - a ≤ ¦u ?k - a¦"
      by (rule abs_ge_self)
    ultimately show False
      by (rule notE)
  qed
qed

(* 2ª demostración *)
lemma
  assumes "limite u a"
          "no_decreciente u"
  shows   "∀ n. u n ≤ a"
proof (rule allI)
  fix n
  show "u n ≤ a"
  proof (rule ccontr)
    assume "¬ u n ≤ a"
    then have H : "u n - a > 0"
      by simp
    then obtain m where hm : "∀p≥m. ¦u p - a¦ < u n - a"
      using assms(1) limite_def by blast
    let ?k = "max n m"
    have "¦u ?k - a¦ < u n - a"
      using hm by simp
    moreover have "u n ≤ u ?k"
      using assms(2) no_decreciente_def by simp
    ultimately have "¦u ?k - a¦ < u ?k - a"
      by simp
    then show False
      by simp
  qed
qed

(* 3ª demostración *)
lemma
  assumes "limite u a"
          "no_decreciente u"
  shows   "∀ n. u n ≤ a"
proof
  fix n
  show "u n ≤ a"
  proof (rule ccontr)
    assume "¬ u n ≤ a"
    then obtain m where hm : "∀p≥m. ¦u p - a¦ < u n - a"
      using assms(1) limite_def by fastforce
    let ?k = "max n m"
    have "¦u ?k - a¦ < u n - a"
      using hm by simp
    moreover have "u n ≤ u ?k"
      using assms(2) no_decreciente_def by simp
    ultimately show False
      by simp
  qed
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
