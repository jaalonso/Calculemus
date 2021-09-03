---
Título: Las sucesiones divergentes positivas no tienen límites finitos
Autor:  José A. Alonso
---

En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante una función (u : ℕ → ℝ) de forma que u(n) es uₙ.

Se define que a es el límite de la sucesión u, por
<pre lang="text">
   def limite (u: ℕ → ℝ) (a: ℝ) :=
     ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
</pre>
donde se usa la notación |x| para el valor absoluto de x
<pre lang="text">
   notation `|`x`|` := abs x
</pre>

La sucesión u diverge positivamente cuando, para cada número real A, se puede encontrar un número natural m tal que, para n > m , se tenga u(n) > A. En Lean se puede definir por
<pre lang="text">
   def diverge_positivamente (u : ℕ → ℝ) :=
     ∀ A, ∃ m, ∀ n ≥ m, u n > A
</pre>

Demostrar que si u diverge positivamente, entonces ningún número real es límite de u.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
import tactic

variable  {u : ℕ → ℝ}

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def diverge_positivamente (u : ℕ → ℝ) :=
  ∀ A, ∃ m, ∀ n ≥ m, u n > A

example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
import tactic

variable  {u : ℕ → ℝ}

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ m, ∀ n ≥ m, |u n - a| < ε

def diverge_positivamente (u : ℕ → ℝ) :=
  ∀ A, ∃ m, ∀ n ≥ m, u n > A

-- 1ª demostración
example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
begin
  push_neg,
  intros a ha,
  cases ha 1 zero_lt_one with m1 hm1,
  cases h (a+1) with m2 hm2,
  let m := max m1 m2,
  specialize hm1 m (le_max_left _ _),
  specialize hm2 m (le_max_right _ _),
  replace hm1 : u m - a < 1 := lt_of_abs_lt hm1,
  replace hm2 : 1 < u m - a := lt_sub_iff_add_lt'.mpr hm2,
  apply lt_irrefl (u m),
  calc u m < a + 1 : sub_lt_iff_lt_add'.mp hm1
       ... < u m   : lt_sub_iff_add_lt'.mp hm2,
end

-- 2ª demostración
example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
begin
  push_neg,
  intros a ha,
  cases ha 1 (by linarith) with m1 hm1,
  cases h (a+1) with m2 hm2,
  let m := max m1 m2,
  replace hm1 : |u m - a| < 1 := by finish,
  replace hm1 : u m - a < 1   := lt_of_abs_lt hm1,
  replace hm2 : u m > a + 1   := by finish,
  replace hm2 : 1 < u m - a   := lt_sub_iff_add_lt'.mpr hm2,
  apply lt_irrefl (u m),
  calc u m < a + 1 : by linarith
       ... < u m   : by linarith
end

-- 3ª demostración
example
  (h : diverge_positivamente u)
  : ¬(∃ a, limite u a) :=
begin
  push_neg,
  intros a ha,
  cases ha 1 (by linarith) with m1 hm1,
  cases h (a+1) with m2 hm2,
  let m := max m1 m2,
  specialize hm1 m (le_max_left _ _),
  specialize hm2 m (le_max_right _ _),
  rw abs_lt at hm1,
  linarith,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_sucesiones_divergentes_positivas_no_tienen_limites_finitos.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_sucesiones_divergentes_positivas_no_tienen_limites_finitos
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u a ⟷ (∀ε>0. ∃N. ∀k≥N. ¦u k - a¦ < ε)"

definition diverge_positivamente :: "(nat ⇒ real) ⇒ bool"
  where "diverge_positivamente u ⟷ (∀A. ∃m. ∀n≥m. u n > A)"

(* 1ª demostración *)
lemma
  assumes "diverge_positivamente u"
  shows   "∄a. limite u a"
proof (rule notI)
  assume "∃a. limite u a"
  then obtain a where "limite u a" try
    by auto
  then obtain m1 where hm1 : "∀n≥m1. ¦u n - a¦ < 1"
    using limite_def by fastforce
  obtain m2 where hm2 : "∀n≥m2. u n > a + 1"
    using assms diverge_positivamente_def by blast
  let ?m = "max m1 m2"
  have "u ?m < u ?m" using hm1 hm2
  proof -
    have "?m ≥ m1"
      by (rule max.cobounded1)
    have "?m ≥ m2"
      by (rule max.cobounded2)
    have "u ?m - a < 1"
      using hm1 ‹?m ≥ m1› by fastforce
    moreover have "u ?m > a + 1"
      using hm2 ‹?m ≥ m2› by simp
    ultimately show "u ?m < u ?m"
      by simp
  qed
  then show False
    by auto
qed

(* 2ª demostración *)
lemma
  assumes "diverge_positivamente u"
  shows   "∄a. limite u a"
proof (rule notI)
  assume "∃a. limite u a"
  then obtain a where "limite u a" try
    by auto
  then obtain m1 where hm1 : "∀n≥m1. ¦u n - a¦ < 1"
    using limite_def by fastforce
  obtain m2 where hm2 : "∀n≥m2. u n > a + 1"
    using assms diverge_positivamente_def by blast
  let ?m = "max m1 m2"
  have "1 < 1"
  proof -
    have "1 < u ?m - a"
      using hm2
      by (metis add.commute less_diff_eq max.cobounded2)
    also have "… < 1"
      using hm1
      by (metis abs_less_iff max_def order_refl)
    finally show "1 < 1" .
  qed
  then show False
    by auto
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
