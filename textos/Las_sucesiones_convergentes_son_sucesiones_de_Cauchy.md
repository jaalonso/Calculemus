---
Título: Las sucesiones convergentes son sucesiones de Cauchy
Autor:  José A. Alonso
---

**Nota**: El problema de hoy lo ha escrito Sara Díaz Real y es uno de los que se encuentran en su Trabajo Fin de Máster [Formalización en Lean de problemas de las Olimpiadas Internacionales de Matemáticas (IMO)](https://raw.githubusercontent.com/saradiazr11/IMO_en_Lean/main/doc/IMO_en_Lean.pdf). Concretamente, el problema se encuentra en la [página 52]((https://raw.githubusercontent.com/saradiazr11/IMO_en_Lean/main/doc/IMO_en_Lean.pdf#page=52) junto con la demostración en lenguaje natural.

En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante una función (u : ℕ → ℝ) de forma que u(n) es uₙ.

Se define

+ el valor absoluto de x por
<pre lang="text">
     notation `|`x`|` := abs x
</pre>
+ a es un límite de la sucesión u, por
<pre lang="text">
     def limite (u : ℕ → ℝ) (a : ℝ) :=
       ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| ≤ ε
</pre>
+ la sucesión u es convergente por
<pre lang="text">
     def suc_convergente (u : ℕ → ℝ) :=
       ∃ l, limite u l
</pre>
+ la sucesión u es de Cauchy por
<pre lang="text">
     def suc_cauchy (u : ℕ → ℝ) :=
       ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| ≤ ε
</pre>

Demostrar que las sucesiones convergentes son de Cauchy.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variable {u : ℕ → ℝ }

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def suc_convergente (u : ℕ → ℝ) :=
  ∃ l, limite u l

def suc_cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| ≤ ε

example
  (h : suc_convergente u)
  : suc_cauchy u :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variable {u : ℕ → ℝ }

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def suc_convergente (u : ℕ → ℝ) :=
  ∃ l, limite u l

def suc_cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| ≤ ε

-- 1ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  unfold suc_cauchy,
  intros ε hε,
  have hε2 : 0 < ε/2 := half_pos hε,
  cases h with l hl,
  cases hl (ε/2) hε2 with N hN,
  clear hε hl hε2,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : congr_arg2 (+) rfl (abs_sub_comm l (u q))
   ... ≤ ε/2 + ε/2               : add_le_add (hN p hp) (hN q hq)
   ... = ε                       : add_halves ε,
end

-- 2ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (half_pos hε) with N hN,
  clear hε hl,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : congr_arg2 (+) rfl (abs_sub_comm l (u q))
   ... ≤ ε/2 + ε/2               : add_le_add (hN p hp) (hN q hq)
   ... = ε                       : add_halves ε,
end

-- 3ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (half_pos hε) with N hN,
  clear hε hl,
  use N,
  intros p hp q hq,
  have cota1 : |u p - l| ≤ ε / 2 := hN p hp,
  have cota2 : |u q - l| ≤ ε / 2 := hN q hq,
  clear hN hp hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : by rw abs_sub_comm l (u q)
   ... ≤ ε                       : by linarith,
end

-- 4ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (half_pos hε) with N hN,
  clear hε hl,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : abs_add (u p - l) (l - u q)
   ... = |u p - l|  + |u q - l|  : by rw abs_sub_comm l (u q)
   ... ≤ ε                       : by linarith [hN p hp, hN q hq],
end

-- 5ª demostración
example
  (h : suc_convergente u)
  : suc_cauchy u :=
begin
  intros ε hε,
  cases h with l hl,
  cases hl (ε/2) (by linarith) with N hN,
  use N,
  intros p hp q hq,
  calc |u p - u q|
       = |(u p - l) + (l - u q)| : by ring_nf
   ... ≤ |u p - l|  + |l - u q|  : by simp [abs_add]
   ... = |u p - l|  + |u q - l|  : by simp [abs_sub_comm]
   ... ≤ ε                       : by linarith [hN p hp, hN q hq],
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_sucesiones_convergentes_son_sucesiones_de_Cauchy.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_sucesiones_convergentes_son_sucesiones_de_Cauchy
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

definition suc_convergente :: "(nat ⇒ real) ⇒ bool"
  where "suc_convergente u ⟷ (∃ l. limite u l)"

definition suc_cauchy :: "(nat ⇒ real) ⇒ bool"
  where "suc_cauchy u ⟷ (∀ε>0. ∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε)"

(* 1ª demostración *)
lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then have "0 < ε/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "∀n≥k. ¦u n - a¦ < ε/2"
    using ‹0 < ε / 2› limite_def by blast
  have "∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
  proof (intro allI impI)
    fix p q
    assume hp : "p ≥ k" and hq : "q ≥ k"
    then have hp' : "¦u p - a¦ < ε/2"
      using hk by blast
    have hq' : "¦u q - a¦ < ε/2"
      using hk hq by blast
    have "¦u p - u q¦ = ¦(u p - a) + (a - u q)¦"
      by simp
    also have "… ≤ ¦u p - a¦  + ¦a - u q¦"
      by simp
    also have "… = ¦u p - a¦  + ¦u q - a¦"
      by simp
    also have "… < ε/2 + ε/2"
      using hp' hq' by simp
    also have "… = ε"
      by simp
    finally show "¦u p - u q¦ < ε"
      by this
  qed
  then show "∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
    by (rule exI)
qed

(* 2ª demostración *)
lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then have "0 < ε/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "∀n≥k. ¦u n - a¦ < ε/2"
    using ‹0 < ε / 2› limite_def by blast
  have "∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
  proof (intro allI impI)
    fix p q
    assume hp : "p ≥ k" and hq : "q ≥ k"
    then have hp' : "¦u p - a¦ < ε/2"
      using hk by blast
    have hq' : "¦u q - a¦ < ε/2"
      using hk hq by blast
    show "¦u p - u q¦ < ε"
      using hp' hq' by argo
  qed
  then show "∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
    by (rule exI)
qed

(* 3ª demostración *)
lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then have "0 < ε/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "∀n≥k. ¦u n - a¦ < ε/2"
    using ‹0 < ε / 2› limite_def by blast
  have "∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
    using hk by (smt (z3) field_sum_of_halves)
  then show "∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
    by (rule exI)
qed

(* 3ª demostración *)
lemma
  assumes "suc_convergente u"
  shows   "suc_cauchy u"
proof (unfold suc_cauchy_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then have "0 < ε/2"
    by simp
  obtain a where "limite u a"
    using assms suc_convergente_def by blast
  then obtain k where hk : "∀n≥k. ¦u n - a¦ < ε/2"
    using ‹0 < ε / 2› limite_def by blast
  then show "∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε"
    by (smt (z3) field_sum_of_halves)
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
