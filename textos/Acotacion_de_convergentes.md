---
Título: Las sucessiones convergentes están acotadas
Autor:  José A. Alonso
---

Demostrar u es una sucesión convergente, entonces está acotada; es decir,
<pre lang="text">
    ∃ k b, ∀ n, n ≥ k → |u n| ≤ b
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variable {u : ℕ → ℝ}
variable {a : ℝ}

notation `|`x`|` := abs x

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| ≤ ε

-- (convergente u) expresa que u es convergente.
def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

example
  (h : convergente u)
  : ∃ k b, ∀ n, n ≥ k → |u n| ≤ b :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variable {u : ℕ → ℝ}
variable {a : ℝ}

notation `|`x`|` := abs x

-- (limite u c) expresa que el límite de u es c.
def limite (u : ℕ → ℝ) (c : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - c| ≤ ε

-- (convergente u) expresa que u es convergente.
def convergente (u : ℕ → ℝ) :=
  ∃ a, limite u a

-- 1ª demostración
example
  (h : convergente u)
  : ∃ k b, ∀ n, n ≥ k → |u n| ≤ b :=
begin
  cases h with a ua,
  cases ua 1 zero_lt_one with k h,
  use [k, 1 + |a|],
  intros n hn,
  specialize h n hn,
  calc |u n|
       = |u n - a + a|   : congr_arg abs (eq_add_of_sub_eq rfl)
   ... ≤ |u n - a| + |a| : abs_add (u n - a) a
   ... ≤ 1 + |a|         : add_le_add_right h _
end

-- 2ª demostración
example
  (h : convergente u)
  : ∃ k b, ∀ n, n ≥ k → |u n| ≤ b :=
begin
  cases h with a ua,
  cases ua 1 zero_lt_one with k h,
  use [k, 1 + |a|],
  intros n hn,
  specialize h n hn,
  calc |u n|
       = |u n - a + a|   : by ring_nf
   ... ≤ |u n - a| + |a| : abs_add (u n - a) a
   ... ≤ 1 + |a|         : by linarith,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Acotacion_de_convergentes.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Acotacion_de_convergentes
imports Main HOL.Real
begin

(* (limite u c) expresa que el límite de u es c. *)
definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "limite u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ ≤ ε)"

(* (convergente u) expresa que u es convergente. *)
definition convergente :: "(nat ⇒ real) ⇒ bool" where
  "convergente u ⟷ (∃ a. limite u a)"

(* 1ª demostración *)
lemma
  assumes "convergente u"
  shows   "∃ k b. ∀n≥k. ¦u n¦ ≤ b"
proof -
  obtain a where "limite u a"
    using assms convergente_def by blast
  then obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ 1"
    using limite_def zero_less_one by blast
  have "∀n≥k. ¦u n¦ ≤ 1 + ¦a¦"
  proof (intro allI impI)
    fix n
    assume hn : "n ≥ k"
    have "¦u n¦ = ¦u n - a + a¦"     by simp
    also have "… ≤ ¦u n - a¦ + ¦a¦" by simp
    also have "… ≤ 1 + ¦a¦"         by (simp add: hk hn)
    finally show "¦u n¦ ≤ 1 + ¦a¦"  .
  qed
  then show "∃ k b. ∀n≥k. ¦u n¦ ≤ b"
    by (intro exI)
qed

(* 2ª demostración *)
lemma
  assumes "convergente u"
  shows   "∃ k b. ∀n≥k. ¦u n¦ ≤ b"
proof -
  obtain a where "limite u a"
    using assms convergente_def by blast
  then obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ 1"
    using limite_def zero_less_one by blast
  have "∀n≥k. ¦u n¦ ≤ 1 + ¦a¦"
    using hk by fastforce
  then show "∃ k b. ∀n≥k. ¦u n¦ ≤ b"
    by auto
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
