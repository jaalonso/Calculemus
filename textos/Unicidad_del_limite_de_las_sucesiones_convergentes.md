---
Título: Unicidad del límite de las sucesiones convergentes
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

Demostrar que cada sucesión tiene como máximo un límite.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables {u : ℕ → ℝ}
variables {a b : ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variables {u : ℕ → ℝ}
variables {a b : ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
begin
  by_contra h,
  wlog hab : a < b,
  { have : a < b ∨ a = b ∨ b < a := lt_trichotomy a b,
    tauto },
  set ε := b - a with hε,
  specialize ha (ε/2),
  have hε2 : ε/2 > 0 := by linarith,
  specialize ha hε2,
  cases ha with A hA,
  cases hb (ε/2) (by linarith) with B hB,
  set N := max A B with hN,
  have hAN : A ≤ N := le_max_left A B,
  have hBN : B ≤ N := le_max_right A B,
  specialize hA N hAN,
  specialize hB N hBN,
  rw abs_lt at hA hB,
  linarith,
end

-- 2ª demostración
-- ===============

example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
begin
  by_contra h,
  wlog hab : a < b,
  { have : a < b ∨ a = b ∨ b < a := lt_trichotomy a b,
    tauto },
  set ε := b - a with hε,
  cases ha (ε/2) (by linarith) with A hA,
  cases hb (ε/2) (by linarith) with B hB,
  set N := max A B with hN,
  have hAN : A ≤ N := le_max_left A B,
  have hBN : B ≤ N := le_max_right A B,
  specialize hA N hAN,
  specialize hB N hBN,
  rw abs_lt at hA hB,
  linarith,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Unicidad_del_limite_de_las_sucesiones_convergentes.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Unicidad_del_limite_de_las_sucesiones_convergentes
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

lemma aux :
  assumes "limite u a"
          "limite u b"
  shows   "b ≤ a"
proof (rule ccontr)
  assume "¬ b ≤ a"
  let ?ε = "b - a"
  have "0 < ?ε/2"
    using ‹¬ b ≤ a› by auto
  obtain A where hA : "∀n≥A. ¦u n - a¦ < ?ε/2"
    using assms(1) limite_def ‹0 < ?ε/2› by blast
  obtain B where hB : "∀n≥B. ¦u n - b¦ < ?ε/2"
    using assms(2) limite_def ‹0 < ?ε/2› by blast
  let ?C = "max A B"
  have hCa : "∀n≥?C. ¦u n - a¦ < ?ε/2"
    using hA by simp
  have hCb : "∀n≥?C. ¦u n - b¦ < ?ε/2"
    using hB by simp
  have "∀n≥?C. ¦a - b¦ < ?ε"
  proof (intro allI impI)
    fix n assume "n ≥ ?C"
    have "¦a - b¦ = ¦(a - u n) + (u n - b)¦" by simp
    also have "… ≤ ¦u n - a¦ + ¦u n - b¦" by simp
    finally show "¦a - b¦ < b - a"
      using hCa hCb ‹n ≥ ?C› by fastforce
  qed
  then show False by fastforce
qed

theorem
  assumes "limite u a"
          "limite u b"
  shows   "a = b"
proof (rule antisym)
  show "a ≤ b" using assms(2) assms(1) by (rule aux)
next
  show "b ≤ a" using assms(1) assms(2) by (rule aux)
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
