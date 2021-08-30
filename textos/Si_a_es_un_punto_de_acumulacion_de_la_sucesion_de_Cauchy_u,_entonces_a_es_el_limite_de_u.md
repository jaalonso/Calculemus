---
Título: Si a es un punto de acumulación de la sucesión de Cauchy u, entonces a es el límite de u
Autor:  José A. Alonso
---

En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante una función (u : ℕ → ℝ) de forma que u(n) es uₙ.

Para extraer una subsucesión se aplica una función de extracción queconserva el orden; por ejemplo, la subsucesión
<pre lang="text">
   uₒ, u₂, u₄, u₆, ...
</pre>
se ha obtenido con la función de extracción φ tal que φ(n) = 2*n.

En Lean, se puede definir que φ es una función de extracción por
<pre lang="text">
   def extraccion (φ : ℕ → ℕ) :=
     ∀ n m, n < m → φ n < φ m
</pre>
que a es un límite de u por
<pre lang="text">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
</pre>
que a es un punto de acumulación de u por
<pre lang="text">
   def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
     ∃ φ, extraccion φ ∧ limite (u ∘ φ) a
</pre>
que la sucesión u es de Cauchy por
<pre lang="text">
   def suc_cauchy (u : ℕ → ℝ) :=
     ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε
</pre>

Demostrar que si u es una sucesión de Cauchy y a es un punto de acumulación de u, entonces a es el límite de u.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
open nat

variable  {u : ℕ → ℝ}
variables {a : ℝ}
variable  {φ : ℕ → ℕ}

notation `|`x`|` := abs x

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

def limite (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

def suc_cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε

example
  (hu : suc_cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
open nat

variable  {u : ℕ → ℝ}
variables {a : ℝ}
variable  {φ : ℕ → ℕ}

notation `|`x`|` := abs x

def extraccion (φ : ℕ → ℕ) :=
  ∀ n m, n < m → φ n < φ m

def limite (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

def punto_acumulacion (u : ℕ → ℝ) (a : ℝ) :=
  ∃ φ, extraccion φ ∧ limite (u ∘ φ) a

def suc_cauchy (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, |u p - u q| < ε

lemma aux1
  (h : extraccion φ)
  : ∀ n, n ≤ φ n :=
begin
  intro n,
  induction n with m HI,
  { exact nat.zero_le (φ 0), },
  { apply nat.succ_le_of_lt,
    calc m ≤ φ m        : HI
       ... < φ (succ m) : h m (m+1) (lt_add_one m), },
end

lemma aux2
  (h : extraccion φ)
  : ∀ N N', ∃ n ≥ N', φ n ≥ N :=
λ N N', ⟨max N N', ⟨le_max_right N N',
                    le_trans (le_max_left N N')
                             (aux1 h (max N N'))⟩⟩

lemma cerca_acumulacion
  (h : punto_acumulacion u a)
  : ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| < ε :=
begin
  intros ε hε N,
  rcases h with ⟨φ, hφ1, hφ2⟩,
  cases hφ2 ε hε with N' hN',
  rcases aux2 hφ1 N N' with ⟨m, hm, hm'⟩,
  exact ⟨φ m, hm', hN' _ hm⟩,
end

-- 1ª demostración
example
  (hu : suc_cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  unfold limite,
  intros ε hε,
  unfold suc_cauchy at hu,
  cases hu (ε/2) (half_pos hε) with N hN,
  use N,
  have ha' : ∃ N' ≥ N, |u N' - a| < ε/2,
    apply cerca_acumulacion ha (ε/2) (half_pos hε),
  cases ha' with N' h,
  cases h with hNN' hN',
  intros n hn,
  calc   |u n - a|
       = |(u n - u N') + (u N' - a)| : by ring_nf
   ... ≤ |u n - u N'| + |u N' - a|   : abs_add (u n - u N') (u N' - a)
   ... < ε/2 + |u N' - a|            : add_lt_add_right (hN n hn N' hNN') _
   ... < ε/2 + ε/2                   : add_lt_add_left hN' (ε / 2)
   ... = ε                           : add_halves ε
end

-- 2ª demostración
example
  (hu : suc_cauchy u)
  (ha : punto_acumulacion u a)
  : limite u a :=
begin
  intros ε hε,
  cases hu (ε/2) (by linarith) with N hN,
  use N,
  have ha' : ∃ N' ≥ N, |u N' - a| < ε/2,
    apply cerca_acumulacion ha (ε/2) (by linarith),
  rcases ha' with ⟨N', hNN', hN'⟩,
  intros n hn,
  calc  |u n - a|
      = |(u n - u N') + (u N' - a)| : by ring_nf
  ... ≤ |u n - u N'| + |u N' - a|   : by simp [abs_add]
  ... < ε                           : by linarith [hN n hn N' hNN'],
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Si_a_es_un_punto_de_acumulacion_de_la_sucesion_de_Cauchy_u,_entonces_a_es_el_limite_de_u.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory "Si_a_es_un_punto_de_acumulacion_de_la_sucesion_de_Cauchy_u,_entonces_a_es_el_limite_de_u"
imports Main HOL.Real
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u a ⟷ (∀ε>0. ∃N. ∀k≥N. ¦u k - a¦ < ε)"

definition punto_acumulacion :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "punto_acumulacion u a ⟷ (∃φ. extraccion φ ∧ limite (u ∘ φ) a)"

definition suc_cauchy :: "(nat ⇒ real) ⇒ bool"
  where "suc_cauchy u ⟷ (∀ε>0. ∃k. ∀m≥k. ∀n≥k. ¦u m - u n¦ < ε)"

(* Lemas auxiliares *)

lemma aux1 :
  assumes "extraccion φ"
  shows   "n ≤ φ n"
proof (induct n)
  show "0 ≤ φ 0" by simp
next
  fix n assume HI : "n ≤ φ n"
  then show "Suc n ≤ φ (Suc n)"
    using assms extraccion_def
    by (metis Suc_leI lessI order_le_less_subst1)
qed

lemma aux2 :
  assumes "extraccion φ"
  shows   "∀ N N'. ∃ k ≥ N'. φ k ≥ N"
proof (intro allI)
  fix N N' :: nat
  have "max N N' ≥ N' ∧ φ (max N N') ≥ N"
    by (meson assms aux1 max.bounded_iff max.cobounded2)
  then show "∃k ≥ N'. φ k ≥ N"
    by blast
qed

lemma cerca_acumulacion :
  assumes "punto_acumulacion u a"
  shows   "∀ε>0. ∀ N. ∃k≥N. ¦u k - a¦ < ε"
proof (intro allI impI)
  fix ε :: real and N :: nat
  assume "ε > 0"
  obtain φ where hφ1 : "extraccion φ"
             and hφ2 : "limite (u ∘ φ) a"
    using assms punto_acumulacion_def by blast
  obtain N' where hN' : "∀k≥N'. ¦(u ∘ φ) k - a¦ < ε"
    using hφ2 limite_def ‹ε > 0› by auto
  obtain m where "m ≥ N' ∧ φ m ≥ N"
    using aux2 hφ1 by blast
  then show "∃k≥N. ¦u k - a¦ < ε"
    using hN' by auto
qed

(* Demostración *)
lemma
  assumes "suc_cauchy u"
          "punto_acumulacion u a"
  shows   "limite u a"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "ε > 0"
  then have "ε/2 > 0"
    by simp
  then obtain N where hN : "∀m≥N. ∀n≥N. ¦u m - u n¦ < ε/2"
    using assms(1) suc_cauchy_def
    by blast
  have "∀k≥N. ¦u k - a¦ < ε"
  proof (intro allI impI)
    fix k
    assume hk : "k ≥ N"
    obtain N' where hN'1 : "N' ≥ N" and
                    hN'2 : "¦u N' - a¦ < ε/2"
      using assms(2) cerca_acumulacion ‹ε/2 > 0› by blast
    have "¦u k - a¦ = ¦(u k - u N') + (u N'  - a)¦"
      by simp
    also have "… ≤ ¦u k - u N'¦ + ¦u N'  - a¦"
      by simp
    also have "… < ε/2 + ¦u N'  - a¦"
      using hk hN hN'1 by auto
    also have "… < ε/2 + ε/2"
      using hN'2 by auto
    also have "… = ε"
      by simp
    finally show "¦u k - a¦ < ε" .
  qed
  then show "∃N. ∀k≥N. ¦u k - a¦ < ε"
    by auto
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
