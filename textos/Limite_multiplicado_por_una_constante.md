---
Título: Límite multiplicado por una constante
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

Demostrar que que si el límite de u(i) es a, entonces el de c·u(i) es c·a.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
import tactic

variables (u v : ℕ → ℝ)
variables (a c : ℝ)

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (h : limite u a)
  : limite (λ n, c * (u n)) (c * a) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
import tactic

variables (u v : ℕ → ℝ)
variables (a c : ℝ)

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ n, c * (u n)) (c * a) :=
begin
  by_cases hc : c = 0,
  { subst hc,
    intros ε hε,
    by finish, },
  { intros ε hε,
    have hc' : 0 < |c| := abs_pos.mpr hc,
    have hεc : 0 < ε / |c| := div_pos hε hc',
    specialize h (ε/|c|) hεc,
    cases h with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    dsimp only,
    rw ← mul_sub,
    rw abs_mul,
    rw ← lt_div_iff' hc',
    exact hN, }
end

-- 2ª demostración
-- ===============

example
  (h : limite u a)
  : limite (λ n, c * (u n)) (c * a) :=
begin
  by_cases hc : c = 0,
  { subst hc,
    intros ε hε,
    by finish, },
  { intros ε hε,
    have hc' : 0 < |c| := by finish,
    have hεc : 0 < ε / |c| := div_pos hε hc',
    cases h (ε/|c|) hεc with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    dsimp only,
    rw [← mul_sub, abs_mul, ← lt_div_iff' hc'],
    exact hN, }
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Limite_multiplicado_por_una_constante.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Limite_multiplicado_por_una_constante
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

lemma
  assumes "limite u a"
  shows   "limite (λ n. c * u n) (c * a)"
proof (unfold limite_def)
  show "∀ε>0. ∃k. ∀n≥k. ¦c * u n - c * a¦ < ε"
  proof (intro allI impI)
    fix ε :: real
    assume "0 < ε"
    show "∃k. ∀n≥k. ¦c * u n - c * a¦ < ε"
    proof (cases "c = 0")
      assume "c = 0"
      then show "∃k. ∀n≥k. ¦c * u n - c * a¦ < ε"
        by (simp add: ‹0 < ε›)
    next
      assume "c ≠ 0"
      then have "0 < ¦c¦"
        by simp
      then have "0 < ε/¦c¦"
        by (simp add: ‹0 < ε›)
      then obtain N where hN : "∀n≥N. ¦u n - a¦ < ε/¦c¦"
        using assms limite_def
        by auto
      have "∀n≥N. ¦c * u n - c * a¦ < ε"
      proof (intro allI impI)
        fix n
        assume "n ≥ N"
        have "¦c * u n - c * a¦ = ¦c * (u n - a)¦"
          by argo
        also have "… = ¦c¦ * ¦u n - a¦"
          by (simp only: abs_mult)
        also have "… < ¦c¦ * (ε/¦c¦)"
          using hN ‹n ≥ N› ‹0 < ¦c¦›
          by (simp only: mult_strict_left_mono)
        finally show "¦c * u n - c * a¦ < ε"
          using ‹0 < ¦c¦›
          by auto
      qed
      then show "∃k. ∀n≥k. ¦c * u n - c * a¦ < ε"
        by (rule exI)
    qed
  qed
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
