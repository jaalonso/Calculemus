---
Título: Las sucesiones acotadas por cero son nulas
Autor:  José A. Alonso
---

Demostrar que las sucesiones acotadas por cero son nulas.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
import tactic

variable (u : ℕ → ℝ)

notation `|`x`|` := abs x

example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
import tactic

variable (u : ℕ → ℝ)

notation `|`x`|` := abs x

-- 1ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
begin
  intro n,
  rw ← abs_eq_zero,
  specialize h n,
  apply le_antisymm,
  { exact h, },
  { exact abs_nonneg (u n), },
end

-- 2ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
begin
  intro n,
  rw ← abs_eq_zero,
  specialize h n,
  exact le_antisymm h (abs_nonneg (u n)),
end

-- 3ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
begin
  intro n,
  rw ← abs_eq_zero,
  exact le_antisymm (h n) (abs_nonneg (u n)),
end

-- 4ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
begin
  intro n,
  exact abs_eq_zero.mp (le_antisymm (h n) (abs_nonneg (u n))),
end

-- 5ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
λ n, abs_eq_zero.mp (le_antisymm (h n) (abs_nonneg (u n)))

-- 6ª demostración
example
  (h : ∀ n, |u n| ≤ 0)
  : ∀ n, u n = 0 :=
by finish
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_sucesiones_acotadas_por_cero_son_nulas.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_sucesiones_acotadas_por_cero_son_nulas
imports Main HOL.Real
begin

(* 1ª demostración *)
lemma
  fixes a :: "nat ⇒ real"
  assumes "∀n. ¦a n¦ ≤ 0"
  shows   "∀n. a n = 0"
proof (rule allI)
  fix n
  have "¦a n¦ = 0"
  proof (rule antisym)
    show "¦a n¦ ≤ 0"
      using assms by (rule allE)
  next
    show " 0 ≤ ¦a n¦"
      by (rule abs_ge_zero)
  qed
  then show "a n = 0"
    by (simp only: abs_eq_0_iff)
qed

(* 2ª demostración *)
lemma
  fixes a :: "nat ⇒ real"
  assumes "∀n. ¦a n¦ ≤ 0"
  shows   "∀n. a n = 0"
proof (rule allI)
  fix n
  have "¦a n¦ = 0"
  proof (rule antisym)
    show "¦a n¦ ≤ 0" try
      using assms by (rule allE)
  next
    show " 0 ≤ ¦a n¦"
      by simp
  qed
  then show "a n = 0"
    by simp
qed

(* 3ª demostración *)
lemma
  fixes a :: "nat ⇒ real"
  assumes "∀n. ¦a n¦ ≤ 0"
  shows   "∀n. a n = 0"
proof (rule allI)
  fix n
  have "¦a n¦ = 0"
    using assms by auto
  then show "a n = 0"
    by simp
qed

(* 4ª demostración *)
lemma
  fixes a :: "nat ⇒ real"
  assumes "∀n. ¦a n¦ ≤ 0"
  shows   "∀n. a n = 0"
using assms by auto

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
