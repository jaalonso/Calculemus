---
Título: Las subsucesiones tienen el mismo límite que la sucesión
Autor:  José A. Alonso
---

Para extraer una subsucesión se aplica una función de extracción que conserva el orden; por ejemplo, la subsucesión
<pre lang="text">
   uₒ, u₂, u₄, u₆, ...
</pre>
se ha obtenido con la función de extracción φ tal que φ(n) = 2*n.

En Lean, se puede definir que φ es una función de extracción por
<pre lang="text">
   def extraccion (φ : ℕ → ℕ) :=
     ∀ n m, n < m → φ n < φ m
</pre>
que v es una subsucesión de u por
<pre lang="text">
   def subsucesion (v u : ℕ → ℝ) :=
     ∃ φ, extraccion φ ∧ v = u ∘ φ
</pre>
y que a es un límite de u por
<pre lang="text">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε
</pre>

Demostrar que las subsucesiones de una sucesión convergente tienen el mismo límite que la sucesión.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
open nat

variables {u v : ℕ → ℝ}
variable  {a : ℝ}
variable  {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ):=
  ∀ n m, n < m → φ n < φ m

def subsucesion (v u : ℕ → ℝ) :=
  ∃ φ, extraccion φ ∧ v = u ∘ φ

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
open nat

variables {u v : ℕ → ℝ}
variable  {a : ℝ}
variable  {φ : ℕ → ℕ}

def extraccion (φ : ℕ → ℕ):=
  ∀ n m, n < m → φ n < φ m

def subsucesion (v u : ℕ → ℝ) :=
  ∃ φ, extraccion φ ∧ v = u ∘ φ

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ k ≥ N, |u k - a| < ε

-- En la demostración se usará el siguiente lema.
lemma aux
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

-- 1ª demostración
example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
begin
  unfold limite,
  intros ε hε,
  unfold limite at ha,
  cases ha ε hε with N hN,
  use N,
  intros n hn,
  unfold subsucesion at hv,
  rcases hv with ⟨φ, hφ1, hφ2⟩,
  rw hφ2,
  apply hN,
  apply le_trans hn,
  exact aux hφ1 n,
end

-- 2ª demostración
example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
begin
  intros ε hε,
  cases ha ε hε with N hN,
  use N,
  intros n hn,
  rcases hv with ⟨φ, hφ1, hφ2⟩,
  rw hφ2,
  apply hN,
  exact le_trans hn (aux hφ1 n),
end

-- 3ª demostración
example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
begin
  intros ε hε,
  cases ha ε hε with N hN,
  use N,
  intros n hn,
  rcases hv with ⟨φ, hφ1, hφ2⟩,
  rw hφ2,
  exact hN (φ n) (le_trans hn (aux hφ1 n)),
end

-- 4ª demostración
example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
begin
  intros ε hε,
  cases ha ε hε with N hN,
  rcases hv with ⟨φ, hφ1, hφ2⟩,
  rw hφ2,
  use N,
  exact λ n hn, hN (φ n) (le_trans hn (aux hφ1 n)),
end

-- 5ª demostración
example
  (hv : subsucesion v u)
  (ha : limite u a)
  : limite v a :=
begin
  intros ε hε,
  cases ha ε hε with N hN,
  rcases hv with ⟨φ, hφ1, hφ2⟩,
  rw hφ2,
  exact ⟨N, λ n hn, hN (φ n) (le_trans hn (aux hφ1 n))⟩,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion
imports Main HOL.Real
begin

definition extraccion :: "(nat ⇒ nat) ⇒ bool" where
  "extraccion φ ⟷ (∀ n m. n < m ⟶ φ n < φ m)"

definition subsucesion :: "(nat ⇒ real) ⇒ (nat ⇒ real) ⇒ bool"
  where "subsucesion v u ⟷ (∃ φ. extraccion φ ∧ v = u ∘ φ)"

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u a ⟷ (∀ε>0. ∃N. ∀k≥N. ¦u k - a¦ < ε)"

(* En la demostración se usará el siguiente lema *)
lemma aux :
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

(* Demostración *)
lemma
  assumes "subsucesion v u"
          "limite u a"
  shows   "limite v a"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "ε > 0"
  then obtain N where hN : "∀k≥N. ¦u k - a¦ < ε"
    using assms(2) limite_def by auto
  obtain φ where hφ1 : "extraccion φ" and hφ2 : "v = u ∘ φ"
    using assms(1) subsucesion_def by auto
  have "∀k≥N. ¦v k - a¦ < ε"
  proof (intro allI impI)
    fix k
    assume "N ≤ k"
    also have "... ≤ φ k"
      by (simp add: aux hφ1)
    finally have "N ≤ φ k" .
    have "¦v k - a¦ = ¦u (φ k) - a¦"
      using hφ2 by simp
    also have "… < ε"
      using hN ‹N ≤ φ k› by simp
    finally show "¦v k - a¦ < ε" .
  qed
  then show "∃N. ∀k≥N. ¦v k - a¦ < ε"
    by auto
qed

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
