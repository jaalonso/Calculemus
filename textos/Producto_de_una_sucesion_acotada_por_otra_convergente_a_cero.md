---
Título: Producto de una sucesión acotada por otra convergente a cero
Autor:  José A. Alonso
---

Demostrar que el producto de una sucesión acotada por una convergente a 0 también converge a 0.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
import tactic

variables (u v : ℕ → ℝ)
variable  (a : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (c : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

def acotada (a : ℕ → ℝ) :=
∃ B, ∀ n, |a n| ≤ B

example
  (hU : acotada u)
  (hV : limite v 0)
  : limite (u*v) 0 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
import tactic

variables (u v : ℕ → ℝ)
variable  (a : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (c : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

def acotada (a : ℕ → ℝ) :=
∃ B, ∀ n, |a n| ≤ B

-- 1ª demostración
example
  (hU : acotada u)
  (hV : limite v 0)
  : limite (u*v) 0 :=
begin
  cases hU with B hB,
  have hBnoneg : 0 ≤ B,
    calc 0 ≤ |u 0| : abs_nonneg (u 0)
       ... ≤ B     : hB 0,
  by_cases hB0 : B = 0,
  { subst hB0,
    intros ε hε,
    use 0,
    intros n hn,
    simp_rw [sub_zero] at *,
    calc |(u * v) n|
         = |u n * v n|   : congr_arg abs (pi.mul_apply u v n)
     ... = |u n| * |v n| : abs_mul (u n) (v n)
     ... ≤ 0 * |v n|     : mul_le_mul_of_nonneg_right (hB n) (abs_nonneg (v n))
     ... = 0             : zero_mul (|v n|)
     ... < ε             : hε, },
  { change B ≠ 0 at hB0,
    have hBpos : 0 < B := (ne.le_iff_lt hB0.symm).mp hBnoneg,
    intros ε hε,
    cases hV (ε/B) (div_pos hε hBpos) with N hN,
    use N,
    intros n hn,
    simp_rw [sub_zero] at *,
    calc |(u * v) n|
         = |u n * v n|    : congr_arg abs (pi.mul_apply u v n)
     ... = |u n| * |v n|  : abs_mul (u n) (v n)
     ... ≤ B * |v n|      : mul_le_mul_of_nonneg_right (hB n) (abs_nonneg _)
     ... < B * (ε/B)      : mul_lt_mul_of_pos_left (hN n hn) hBpos
     ... = ε              : mul_div_cancel' ε hB0 },
end

-- 2ª demostración
example
  (hU : acotada u)
  (hV : limite v 0)
  : limite (u*v) 0 :=
begin
  cases hU with B hB,
  have hBnoneg : 0 ≤ B,
    calc 0 ≤ |u 0| : abs_nonneg (u 0)
       ... ≤ B     : hB 0,
  by_cases hB0 : B = 0,
  { subst hB0,
    intros ε hε,
    use 0,
    intros n hn,
    simp_rw [sub_zero] at *,
    calc |(u * v) n|
         = |u n| * |v n| : by finish [abs_mul]
     ... ≤ 0 * |v n|     : mul_le_mul_of_nonneg_right (hB n) (abs_nonneg (v n))
     ... = 0             : by ring
     ... < ε             : hε, },
  { change B ≠ 0 at hB0,
    have hBpos : 0 < B := (ne.le_iff_lt hB0.symm).mp hBnoneg,
    intros ε hε,
    cases hV (ε/B) (div_pos hε hBpos) with N hN,
    use N,
    intros n hn,
    simp_rw [sub_zero] at *,
    calc |(u * v) n|
         = |u n| * |v n|  : by finish [abs_mul]
     ... ≤ B * |v n|      : mul_le_mul_of_nonneg_right (hB n) (abs_nonneg _)
     ... < B * (ε/B)      : by finish
     ... = ε              : mul_div_cancel' ε hB0 },
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Producto_de_una_sucesion_acotada_por_otra_convergente_a_cero.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Producto_de_una_sucesion_acotada_por_otra_convergente_a_cero
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

definition acotada :: "(nat ⇒ real) ⇒ bool"
  where "acotada u ⟷ (∃B. ∀n. ¦u n¦ ≤ B)"

lemma
  assumes "acotada u"
          "limite v 0"
  shows   "limite (λn. u n * v n) 0"
proof -
  obtain B where hB : "∀n. ¦u n¦ ≤ B"
    using assms(1) acotada_def by auto
  then have hBnoneg : "0 ≤ B" by auto
  show "limite (λn. u n * v n) 0"
  proof (cases "B = 0")
    assume "B = 0"
    show "limite (λn. u n * v n) 0"
    proof (unfold limite_def; intro allI impI)
      fix ε :: real
      assume "0 < ε"
      have "∀n≥0. ¦u n * v n - 0¦ < ε"
      proof (intro allI impI)
        fix n :: nat
        assume "n ≥ 0"
        show "¦u n * v n - 0¦ < ε"
          using ‹0 < ε› ‹B = 0› hB by auto
      qed
      then show "∃k. ∀n≥k. ¦u n * v n - 0¦ < ε"
        by (rule exI)
    qed
  next
    assume "B ≠ 0"
    then have hBpos : "0 < B"
      using hBnoneg by auto
    show "limite (λn. u n * v n) 0"
    proof (unfold limite_def; intro allI impI)
      fix ε :: real
      assume "0 < ε"
      then have "0 < ε/B"
        by (simp add: hBpos)
      then obtain N where hN : "∀n≥N. ¦v n - 0¦ < ε/B"
        using assms(2) limite_def by auto
      have "∀n≥N. ¦u n * v n - 0¦ < ε"
      proof (intro allI impI)
        fix n :: nat
        assume "n ≥ N"
        have "¦v n¦ < ε/B"
          using ‹N ≤ n› hN by auto
        have "¦u n * v n - 0¦ = ¦u n¦ * ¦v n¦"
          by (simp add: abs_mult)
        also have "… ≤ B * ¦v n¦"
          by (simp add: hB mult_right_mono)
        also have "… < B * (ε/B)"
          using ‹¦v n¦ < ε/B› hBpos
          by (simp only: mult_strict_left_mono)
        also have "… = ε"
          using ‹B ≠ 0› by simp
        finally show "¦u n * v n - 0¦ < ε"
          by this
      qed
      then show "∃k. ∀n≥k. ¦u n * v n - 0¦ < ε"
        by (rule exI)
    qed
  qed
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
