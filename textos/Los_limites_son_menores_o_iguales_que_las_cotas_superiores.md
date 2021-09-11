---
Título: Los límites son menores o iguales que las cotas superiores
Autor:  José A. Alonso
---

En Lean, se puede definir que a es el límite de la sucesión u por
<pre lang="text">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
</pre>
y que a es una cota superior de  u por
<pre lang="text">
   def cota_superior (u : ℕ → ℝ) (a : ℝ) :=
     ∀ n, u n ≤ a
</pre>

Demostrar que si x es el límite de la sucesión u e y es una cota superior de u, entonces x ≤ y.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variable  (u : ℕ → ℝ)
variables (x y : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε

def cota_superior (u : ℕ → ℝ) (a : ℝ) :=
  ∀ n, u n ≤ a

example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variable  (u : ℕ → ℝ)
variables (x y : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε

def cota_superior (u : ℕ → ℝ) (a : ℝ) :=
  ∀ n, u n ≤ a

lemma aux :
  (∀ ε > 0, y ≤ x + ε) → y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split ; linarith,
end

-- 1º demostración
example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
begin
  apply aux,
  intros ε hε,
  cases hx ε hε with k hk,
  specialize hk k rfl.ge,
  replace hk : -ε < u k - x := neg_lt_of_abs_lt hk,
  replace hk : x < u k + ε := neg_lt_sub_iff_lt_add'.mp hk,
  apply le_of_lt,
  exact lt_add_of_lt_add_right hk (hy k),
end

-- 2º demostración
example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
begin
  apply aux,
  intros ε hε,
  cases hx ε hε with k hk,
  specialize hk k rfl.ge,
  apply le_of_lt,
  calc x < u k + ε : neg_lt_sub_iff_lt_add'.mp (neg_lt_of_abs_lt hk)
     ... ≤ y + ε   : add_le_add_right (hy k) ε,
end

-- 3º demostración
example
  (hx : limite u x)
  (hy : cota_superior u y)
  : x ≤ y :=
begin
  apply aux,
  intros ε hε,
  cases hx ε hε with k hk,
  specialize hk k (by linarith),
  rw abs_lt at hk,
  linarith [hy k],
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Los_limites_son_menores_o_iguales_que_las_cotas_superiores.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Los_limites_son_menores_o_iguales_que_las_cotas_superiores
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "limite u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ < ε)"

definition cota_superior :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "cota_superior u c ⟷ (∀n. u n ≤ c)"

(* 1ª demostración *)
lemma
  fixes x y :: real
  assumes "limite u x"
          "cota_superior u y"
  shows   "x ≤ y"
proof (rule field_le_epsilon)
  fix ε :: real
  assume "0 < ε"
  then obtain k where hk : "∀n≥k. ¦u n - x¦ < ε"
    using assms(1) limite_def by auto
  then have "¦u k - x¦ < ε"
    by simp
  then have "-ε < u k - x"
    by simp
  then have "x < u k + ε"
    by simp
  moreover have "u k ≤ y"
    using assms(2) cota_superior_def by simp
  ultimately show "x ≤ y + ε"
    by simp
qed

(* 2ª demostración *)
lemma
  fixes x y :: real
  assumes "limite u x"
          "cota_superior u y"
  shows   "x ≤ y"
proof (rule field_le_epsilon)
  fix ε :: real
  assume "0 < ε"
  then obtain k where hk : "∀n≥k. ¦u n - x¦ < ε"
    using assms(1) limite_def by auto
  then have "x < u k + ε"
    by auto
  moreover have "u k ≤ y"
    using assms(2) cota_superior_def by simp
  ultimately show "x ≤ y + ε"
    by simp
qed

(* 3ª demostración *)
lemma
  fixes x y :: real
  assumes "limite u x"
          "cota_superior u y"
  shows   "x ≤ y"
proof (rule field_le_epsilon)
  fix ε :: real
  assume "0 < ε"
  then obtain k where hk : "∀n≥k. ¦u n - x¦ < ε"
    using assms(1) limite_def by auto
  then show "x ≤ y + ε"
    using assms(2) cota_superior_def
    by (smt (verit) order_refl)
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
