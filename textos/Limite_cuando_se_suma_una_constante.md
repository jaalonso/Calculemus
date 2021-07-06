---
Título: Límite con suma de constante
Autor:  José A. Alonso
---

En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante una función (u : ℕ → ℝ) de forma que u(n) es uₙ.

Se define que a es el límite de la sucesión u, por
<pre lang="text">
   def limite : (ℕ → ℝ) → ℝ → Prop :=
   λ u a, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
</pre>
donde se usa la notación |x| para el valor absoluto de x
<pre lang="text">
   notation `|`x`|` := abs x
</pre>

Demostrar que si el límite de la sucesión u(i) es a y c ∈ ℝ, entonces el límite de u(i)+c es a+c.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
import tactic

variables {u : ℕ → ℝ}
variables {a c : ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (h : limite u a)
  : limite (λ i, u i + c) (a + c) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
import tactic

variables {u : ℕ → ℝ}
variables {a c : ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ i, u i + c) (a + c) :=
begin
  intros ε hε,
  dsimp,
  cases h ε hε with k hk,
  use k,
  intros n hn,
  calc |u n + c - (a + c)|
       = |u n - a|         : by norm_num
   ... < ε                 : hk n hn,
end

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ i, u i + c) (a + c) :=
begin
  intros ε hε,
  dsimp,
  cases h ε hε with k hk,
  use k,
  intros n hn,
  convert hk n hn using 2,
  ring,
end

-- 3ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ i, u i + c) (a + c) :=
begin
  intros ε hε,
  convert h ε hε,
  by norm_num,
end

-- 4ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ i, u i + c) (a + c) :=
λ ε hε, (by convert h ε hε; norm_num)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Limite_cuando_se_suma_una_constante.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Limite_cuando_se_suma_una_constante
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

(* 1ª demostración *)

lemma
  assumes "limite u a"
  shows   "limite (λ i.  u i + c)  (a + c)"
proof (unfold limite_def)
  show "∀ε>0. ∃k. ∀n≥k. ¦u n + c - (a + c)¦ < ε"
  proof (intro allI impI)
    fix ε :: real
    assume "0 < ε"
    then have "∃k. ∀n≥k. ¦u n - a¦ < ε"
      using assms limite_def by simp
    then obtain k where "∀n≥k. ¦u n - a¦ < ε"
      by (rule exE)
    then have "∀n≥k. ¦u n + c - (a + c)¦ < ε"
      by simp
    then show "∃k. ∀n≥k. ¦u n + c - (a + c)¦ < ε"
      by (rule exI)
  qed
qed

(* 2ª demostración *)

lemma
  assumes "limite u a"
  shows   "limite (λ i.  u i + c)  (a + c)"
  using assms limite_def
  by simp

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
