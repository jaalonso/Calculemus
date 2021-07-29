---
Título: Límite de sucesión menor que otra sucesión
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

Demostrar que si aₙ → l, bₙ → m y aₙ ≤ bₙ para todo n, entonces l ≤ m.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
import tactic

variables (u v : ℕ → ℝ)
variables (a c : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (c : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  (hu : limite u a)
  (hv : limite v c)
  (hle : ∀ n, u n ≤ v n)
  : a ≤ c :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
import tactic

variables (u v : ℕ → ℝ)
variables (a c : ℝ)

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (c : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
example
  (hu : limite u a)
  (hv : limite v c)
  (hle : ∀ n, u n ≤ v n)
  : a ≤ c :=
begin
  apply le_of_not_lt,
  intro hlt,
  set ε := (a - c) /2 with hεac,
  have hε : 0 < ε :=
    half_pos (sub_pos.mpr hlt),
  cases hu ε hε with Nu HNu,
  cases hv ε hε with Nv HNv,
  let N := max Nu Nv,
  have HNu' : Nu ≤ N := le_max_left Nu Nv,
  have HNv' : Nv ≤ N := le_max_right Nu Nv,
  have Ha : |u N - a| < ε := HNu N HNu',
  have Hc : |v N - c| < ε := HNv N HNv',
  have HN : u N ≤ v N := hle N,
  apply lt_irrefl (a - c),
  calc a - c
       = (a - u N) + (u N - c)   : by ring
   ... ≤ (a - u N) + (v N - c)   : by simp [HN]
   ... ≤ |(a - u N) + (v N - c)| : le_abs_self ((a - u N) + (v N - c))
   ... ≤ |a - u N| + |v N - c|   : abs_add (a - u N) (v N - c)
   ... = |u N - a| + |v N - c|   : by simp only [abs_sub]
   ... < ε + ε                   : add_lt_add Ha Hc
   ... = a - c                   : add_halves (a - c),
end

-- 2ª demostración
example
  (hu : limite u a)
  (hv : limite v c)
  (hle : ∀ n, u n ≤ v n)
  : a ≤ c :=
begin
  apply le_of_not_lt,
  intro hlt,
  set ε := (a - c) /2 with hε,
  cases hu ε (by linarith) with Nu HNu,
  cases hv ε (by linarith) with Nv HNv,
  let N := max Nu Nv,
  have Ha : |u N - a| < ε :=
    HNu N (le_max_left Nu Nv),
  have Hc : |v N - c| < ε :=
    HNv N (le_max_right Nu Nv),
  have HN : u N ≤ v N := hle N,
  apply lt_irrefl (a - c),
  calc a - c
       = (a - u N) + (u N - c)   : by ring
   ... ≤ (a - u N) + (v N - c)   : by simp [HN]
   ... ≤ |(a - u N) + (v N - c)| : le_abs_self ((a - u N) + (v N - c))
   ... ≤ |a - u N| + |v N - c|   : abs_add (a - u N) (v N - c)
   ... = |u N - a| + |v N - c|   : by simp only [abs_sub]
   ... < ε + ε                   : add_lt_add Ha Hc
   ... = a - c                   : add_halves (a - c),
end

-- 3ª demostración
example
  (hu : limite u a)
  (hv : limite v c)
  (hle : ∀ n, u n ≤ v n)
  : a ≤ c :=
begin
  apply le_of_not_lt,
  intro hlt,
  set ε := (a - c) /2 with hε,
  cases hu ε (by linarith) with Nu HNu,
  cases hv ε (by linarith) with Nv HNv,
  let N := max Nu Nv,
  have Ha : |u N - a| < ε :=
    HNu N (le_max_left Nu Nv),
  have Hc : |v N - c| < ε :=
    HNv N (le_max_right Nu Nv),
  have HN : u N ≤ v N := hle N,
  apply lt_irrefl (a - c),
  calc a - c
       = (a - u N) + (u N - c)   : by ring
   ... ≤ (a - u N) + (v N - c)   : by simp [HN]
   ... ≤ |(a - u N) + (v N - c)| : by simp [le_abs_self]
   ... ≤ |a - u N| + |v N - c|   : by simp [abs_add]
   ... = |u N - a| + |v N - c|   : by simp [abs_sub]
   ... < ε + ε                   : add_lt_add Ha Hc
   ... = a - c                   : by simp,
end

-- 4ª demostración
example
  (hu : limite u a)
  (hv : limite v c)
  (hle : ∀ n, u n ≤ v n)
  : a ≤ c :=
begin
  apply le_of_not_lt,
  intro hlt,
  set ε := (a - c) /2 with hε,
  cases hu ε (by linarith) with Nu HNu,
  cases hv ε (by linarith) with Nv HNv,
  let N := max Nu Nv,
  have Ha : |u N - a| < ε :=
    HNu N (le_max_left Nu Nv),
  have Hc : |v N - c| < ε :=
    HNv N (le_max_right Nu Nv),
  have HN : u N ≤ v N := hle N,
  apply lt_irrefl (a - c),
  rw abs_lt at Ha Hc,
  linarith,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Limite_de_sucesion_menor_que_otra_sucesion.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Limite_de_sucesion_menor_que_otra_sucesion
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

(* 1ª demostración *)
lemma
  assumes "limite u a"
          "limite v c"
          "∀n. u n ≤ v n"
  shows   "a ≤ c"
proof (rule leI ; intro notI)
  assume "c < a"
  let ?ε = "(a - c) /2"
  have "0 < ?ε"
    using ‹c < a› by simp
  obtain Nu where HNu : "∀n≥Nu. ¦u n - a¦ < ?ε"
    using assms(1) limite_def ‹0 < ?ε› by blast
  obtain Nv where HNv : "∀n≥Nv. ¦v n - c¦ < ?ε"
    using assms(2) limite_def ‹0 < ?ε› by blast
  let ?N = "max Nu Nv"
  have "?N ≥ Nu"
    by simp
  then have Ha : "¦u ?N - a¦ < ?ε"
    using HNu by simp
  have "?N ≥ Nv"
    by simp
  then have Hc : "¦v ?N - c¦ < ?ε"
    using HNv by simp
  have "a - c < a - c"
  proof -
    have "a - c = (a - u ?N) + (u ?N - c)"
      by simp
    also have "… ≤ (a - u ?N) + (v ?N - c)"
      using assms(3) by auto
    also have "… ≤ ¦(a - u ?N) + (v ?N - c)¦"
      by (rule abs_ge_self)
    also have "… ≤ ¦a - u ?N¦ + ¦v ?N - c¦"
      by (rule abs_triangle_ineq)
    also have "… = ¦u ?N - a¦ + ¦v ?N - c¦"
      by (simp only: abs_minus_commute)
    also have "… < ?ε + ?ε"
      using Ha Hc by (simp only: add_strict_mono)
    also have "… = a - c"
      by (rule field_sum_of_halves)
    finally show "a - c < a - c"
      by this
  qed
  have "¬ a - c < a - c"
    by (rule less_irrefl)
  then show False
    using ‹a - c < a - c› by (rule notE)
qed

(* 2ª demostración *)
lemma
  assumes "limite u a"
          "limite v c"
          "∀n. u n ≤ v n"
  shows   "a ≤ c"
proof (rule leI ; intro notI)
  assume "c < a"
  let ?ε = "(a - c) /2"
  have "0 < ?ε"
    using ‹c < a› by simp
  obtain Nu where HNu : "∀n≥Nu. ¦u n - a¦ < ?ε"
    using assms(1) limite_def ‹0 < ?ε› by blast
  obtain Nv where HNv : "∀n≥Nv. ¦v n - c¦ < ?ε"
    using assms(2) limite_def ‹0 < ?ε› by blast
  let ?N = "max Nu Nv"
  have "?N ≥ Nu"
    by simp
  then have Ha : "¦u ?N - a¦ < ?ε"
    using HNu by simp
  then have Ha' : "u ?N - a < ?ε ∧ -(u ?N - a) < ?ε"
    by argo
  have "?N ≥ Nv"
    by simp
  then have Hc : "¦v ?N - c¦ < ?ε"
    using HNv by simp
  then have Hc' : "v ?N - c < ?ε ∧ -(v ?N - c) < ?ε"
    by argo
  have "a - c < a - c"
    using assms(3) Ha' Hc'
    by (smt (verit, best) field_sum_of_halves)
  have "¬ a - c < a - c"
    by simp
  then show False
    using ‹a - c < a - c› by simp
qed

(* 3ª demostración *)
lemma
  assumes "limite u a"
          "limite v c"
          "∀n. u n ≤ v n"
  shows   "a ≤ c"
proof (rule leI ; intro notI)
  assume "c < a"
  let ?ε = "(a - c) /2"
  have "0 < ?ε"
    using ‹c < a› by simp
  obtain Nu where HNu : "∀n≥Nu. ¦u n - a¦ < ?ε"
    using assms(1) limite_def ‹0 < ?ε› by blast
  obtain Nv where HNv : "∀n≥Nv. ¦v n - c¦ < ?ε"
    using assms(2) limite_def ‹0 < ?ε› by blast
  let ?N = "max Nu Nv"
  have "?N ≥ Nu"
    by simp
  then have Ha : "¦u ?N - a¦ < ?ε"
    using HNu by simp
  then have Ha' : "u ?N - a < ?ε ∧ -(u ?N - a) < ?ε"
    by argo
  have "?N ≥ Nv"
    by simp
  then have Hc : "¦v ?N - c¦ < ?ε"
    using HNv by simp
  then have Hc' : "v ?N - c < ?ε ∧ -(v ?N - c) < ?ε"
    by argo
  show False
    using assms(3) Ha' Hc'
    by (smt (verit, best) field_sum_of_halves)
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
