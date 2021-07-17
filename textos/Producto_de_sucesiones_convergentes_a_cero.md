---
Título: Producto de sucesiones convergentes a cero
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

Demostrar que si las sucesiones u(n) y v(n) convergen a cero, entonces u(n)·v(n) también converge a cero.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
import tactic

variables {u v : ℕ → ℝ}
variables {: ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
import tactic

variables {u v : ℕ → ℝ}
variables {: ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
begin
  intros ε hε,
  cases hu ε hε with U hU,
  cases hv 1 zero_lt_one with V hV,
  set N := max U V with hN,
  use N,
  intros n hn,
  specialize hU n (le_of_max_le_left hn),
  specialize hV n (le_of_max_le_right hn),
  rw sub_zero at *,
  calc |(u * v) n|
       = |u n * v n|   : rfl
   ... = |u n| * |v n| : abs_mul (u n) (v n)
   ... < ε * 1         : mul_lt_mul'' hU hV (abs_nonneg (u n)) (abs_nonneg (v n))
   ... = ε             : mul_one ε,
end

-- 2ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
begin
  intros ε hε,
  cases hu ε hε with U hU,
  cases hv 1 (by linarith) with V hV,
  set N := max U V with hN,
  use N,
  intros n hn,
  specialize hU n (le_of_max_le_left hn),
  specialize hV n (le_of_max_le_right hn),
  rw sub_zero at *,
  calc |(u * v) n|
       = |u n * v n|   : rfl
   ... = |u n| * |v n| : abs_mul (u n) (v n)
   ... < ε * 1         : by { apply mul_lt_mul'' hU hV ; simp [abs_nonneg] }
   ... = ε             : mul_one ε,
end

-- 3ª demostración
-- ===============

example
  (hu : limite u 0)
  (hv : limite v 0)
  : limite (u * v) 0 :=
begin
  intros ε hε,
  cases hu ε hε with U hU,
  cases hv 1 (by linarith) with V hV,
  set N := max U V with hN,
  use N,
  intros n hn,
  have hUN : U ≤ N := le_max_left U V,
  have hVN : V ≤ N := le_max_right U V,
  specialize hU n (by linarith),
  specialize hV n (by linarith),
  rw sub_zero at ⊢ hU hV,
  rw pi.mul_apply,
  rw abs_mul,
  convert mul_lt_mul'' hU hV _ _, simp,
  all_goals {apply abs_nonneg},
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_de_sucesiones_convergentes_a_cero.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Producto_de_sucesiones_convergentes_a_cero
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

lemma
  assumes "limite u 0"
          "limite v 0"
  shows   "limite (λ n. u n * v n) 0"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume  hε : "0 < ε"
  then obtain U where hU : "∀n≥U. ¦u n - 0¦ < ε"
    using assms(1) limite_def
    by auto
  obtain V where hV : "∀n≥V. ¦v n - 0¦ < 1"
    using hε assms(2) limite_def
    by fastforce
  have "∀n≥max U V. ¦u n * v n - 0¦ < ε"
  proof (intro allI impI)
    fix n
    assume hn : "max U V ≤ n"
    then have "U ≤ n"
      by simp
    then have "¦u n - 0¦ < ε"
      using hU by blast
    have hnV : "V ≤ n"
      using hn by simp
    then have "¦v n - 0¦ < 1"
      using hV by blast
    have "¦u n * v n - 0¦ = ¦(u n - 0) * (v n - 0)¦"
      by simp
    also have "… = ¦u n - 0¦ * ¦v n - 0¦"
      by (simp add: abs_mult)
    also have "… < ε * 1"
      using ‹¦u n - 0¦ < ε› ‹¦v n - 0¦ < 1›
      by (rule abs_mult_less)
    also have "… = ε"
      by simp
    finally show "¦u n * v n - 0¦ < ε"
      by this
  qed
  then show "∃k. ∀n≥k. ¦u n * v n - 0¦ < ε"
    by (rule exI)
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
